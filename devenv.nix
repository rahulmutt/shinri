{ pkgs, ... }:
{
  languages.rust.enable = true;
  languages.rust.channel = "stable";
  packages = [ pkgs.cargo-nextest ];
}
