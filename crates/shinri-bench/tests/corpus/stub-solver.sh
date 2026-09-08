#!/bin/sh
# Stub solver for runner_e2e: behaviour is chosen by the input's basename.
# Skip leading option arguments so the same script serves as the solver
# (`--stats <file>`), as "z3" (`<file>`) and as "cvc5" (`--lang smt2 <file>`).
while [ $# -gt 1 ]; do
  case "$1" in
    --lang) shift 2 ;;
    -*) shift ;;
    *) break ;;
  esac
done
f="$1"
case "$(basename "$f")" in
  sat.smt2)   echo sat;   echo "stats: cmd=check-sat wall_ms=1 outcome=sat fence=-" >&2 ;;
  unsat.smt2) echo unsat; echo "stats: cmd=check-sat wall_ms=1 outcome=unsat fence=-" >&2 ;;
  lies.smt2)  echo sat ;;
  slow.smt2)  sleep 30; echo sat ;;
  hog.smt2)   echo "memory allocation of 4000000000 bytes failed" >&2; kill -ABRT $$ ;;
  crash.smt2) echo "thread 'main' panicked at src/lib.rs:1:1:" >&2; exit 101 ;;
  *)          echo "(error \"unknown symbol zzz\")" ;;
esac
