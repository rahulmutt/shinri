//! Minimal hand-rolled JSON codec for the bench harness's JSONL result
//! files and manifests. No external JSON crate: this is a tooling crate
//! that stays small and dependency-light. The parser must never panic on
//! malformed input — the report reads files that a killed run may have
//! truncated mid-line.

/// A parsed JSON value. `Num` is integer-only (`i64`) — the harness never
/// writes fractional numbers.
#[derive(Clone, Debug, PartialEq)]
pub enum JsonVal {
    Str(String),
    Num(i64),
    Bool(bool),
    Null,
    Arr(Vec<JsonVal>),
    Obj(Vec<(String, JsonVal)>),
}

/// Escape a string per RFC 8259 and wrap it in double quotes.
pub fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Parse a single JSON object from `line`. Returns `None` on any syntax
/// error or trailing non-whitespace content after the object.
pub fn parse_object(line: &str) -> Option<Vec<(String, JsonVal)>> {
    let bytes = line.as_bytes();
    let mut p = Parser { b: bytes, i: 0 };
    p.ws();
    let obj = p.object()?;
    p.ws();
    if p.i != p.b.len() {
        return None;
    }
    match obj {
        JsonVal::Obj(fields) => Some(fields),
        _ => None,
    }
}

struct Parser<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }

    fn ws(&mut self) {
        while let Some(c) = self.peek() {
            if c == b' ' || c == b'\t' || c == b'\n' || c == b'\r' {
                self.i += 1;
            } else {
                break;
            }
        }
    }

    fn expect(&mut self, c: u8) -> Option<()> {
        if self.peek() == Some(c) {
            self.i += 1;
            Some(())
        } else {
            None
        }
    }

    fn value(&mut self) -> Option<JsonVal> {
        self.ws();
        match self.peek()? {
            b'"' => self.string().map(JsonVal::Str),
            b'{' => self.object(),
            b'[' => self.array(),
            b't' => self.literal("true", JsonVal::Bool(true)),
            b'f' => self.literal("false", JsonVal::Bool(false)),
            b'n' => self.literal("null", JsonVal::Null),
            b'-' | b'0'..=b'9' => self.number(),
            _ => None,
        }
    }

    fn literal(&mut self, word: &str, val: JsonVal) -> Option<JsonVal> {
        let wb = word.as_bytes();
        if self.b.len() >= self.i + wb.len() && &self.b[self.i..self.i + wb.len()] == wb {
            self.i += wb.len();
            Some(val)
        } else {
            None
        }
    }

    fn number(&mut self) -> Option<JsonVal> {
        let start = self.i;
        if self.peek() == Some(b'-') {
            self.i += 1;
        }
        let digits_start = self.i;
        while matches!(self.peek(), Some(b'0'..=b'9')) {
            self.i += 1;
        }
        if self.i == digits_start {
            self.i = start;
            return None;
        }
        let s = std::str::from_utf8(&self.b[start..self.i]).ok()?;
        let n: i64 = s.parse().ok()?;
        Some(JsonVal::Num(n))
    }

    fn string(&mut self) -> Option<String> {
        self.expect(b'"')?;
        let mut out = String::new();
        loop {
            let c = self.peek()?;
            self.i += 1;
            match c {
                b'"' => return Some(out),
                b'\\' => {
                    let esc = self.peek()?;
                    self.i += 1;
                    match esc {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{8}'),
                        b'f' => out.push('\u{c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let cp = self.hex4()?;
                            if (0xD800..=0xDBFF).contains(&cp) {
                                // High surrogate: expect a following \uXXXX low surrogate.
                                self.expect(b'\\')?;
                                self.expect(b'u')?;
                                let low = self.hex4()?;
                                if !(0xDC00..=0xDFFF).contains(&low) {
                                    return None;
                                }
                                let c = 0x10000 + ((cp - 0xD800) << 10) + (low - 0xDC00);
                                out.push(char::from_u32(c)?);
                            } else if (0xDC00..=0xDFFF).contains(&cp) {
                                // Lone low surrogate: invalid.
                                return None;
                            } else {
                                out.push(char::from_u32(cp)?);
                            }
                        }
                        _ => return None,
                    }
                }
                _ => {
                    // Re-decode this byte as part of a UTF-8 char (input is &str, so
                    // the bytes are valid UTF-8; step back one and consume the char).
                    self.i -= 1;
                    let rest = std::str::from_utf8(&self.b[self.i..]).ok()?;
                    let ch = rest.chars().next()?;
                    out.push(ch);
                    self.i += ch.len_utf8();
                }
            }
        }
    }

    fn hex4(&mut self) -> Option<u32> {
        if self.i + 4 > self.b.len() {
            return None;
        }
        let s = std::str::from_utf8(&self.b[self.i..self.i + 4]).ok()?;
        let v = u32::from_str_radix(s, 16).ok()?;
        self.i += 4;
        Some(v)
    }

    fn array(&mut self) -> Option<JsonVal> {
        self.expect(b'[')?;
        let mut out = Vec::new();
        self.ws();
        if self.peek() == Some(b']') {
            self.i += 1;
            return Some(JsonVal::Arr(out));
        }
        loop {
            let v = self.value()?;
            out.push(v);
            self.ws();
            match self.peek()? {
                b',' => {
                    self.i += 1;
                    self.ws();
                }
                b']' => {
                    self.i += 1;
                    return Some(JsonVal::Arr(out));
                }
                _ => return None,
            }
        }
    }

    fn object(&mut self) -> Option<JsonVal> {
        self.expect(b'{')?;
        let mut out = Vec::new();
        self.ws();
        if self.peek() == Some(b'}') {
            self.i += 1;
            return Some(JsonVal::Obj(out));
        }
        loop {
            self.ws();
            let key = self.string()?;
            self.ws();
            self.expect(b':')?;
            let v = self.value()?;
            out.push((key, v));
            self.ws();
            match self.peek()? {
                b',' => {
                    self.i += 1;
                }
                b'}' => {
                    self.i += 1;
                    return Some(JsonVal::Obj(out));
                }
                _ => return None,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escape_round_trips_control_and_unicode() {
        let s = "a\"b\\c\nd\te\u{1F600}\u{1}";
        let e = escape(s);
        assert_eq!(e, "\"a\\\"b\\\\c\\nd\\te\u{1F600}\\u0001\"");
        let obj = parse_object(&format!("{{\"k\":{e}}}")).unwrap();
        assert_eq!(obj[0].0, "k");
        assert!(matches!(&obj[0].1, JsonVal::Str(v) if v == s));
    }

    #[test]
    fn parse_flat_object_with_all_value_kinds() {
        let obj = parse_object(
            r#"{"s":"x","n":-42,"b":true,"z":null,"a":["sat","unsat"],"o":{"z3":"sat","cvc5":null}}"#,
        )
        .unwrap();
        assert_eq!(obj.len(), 6);
        assert!(matches!(&obj[1].1, JsonVal::Num(-42)));
        assert!(matches!(&obj[2].1, JsonVal::Bool(true)));
        assert!(matches!(&obj[3].1, JsonVal::Null));
        assert!(matches!(&obj[4].1, JsonVal::Arr(a) if a.len() == 2));
        assert!(matches!(&obj[5].1, JsonVal::Obj(o) if o.len() == 2));
    }

    #[test]
    fn parse_rejects_garbage() {
        assert!(parse_object("{\"k\":}").is_none());
        assert!(parse_object("not json").is_none());
        assert!(parse_object("{\"k\":\"unterminated}").is_none());
    }
}
