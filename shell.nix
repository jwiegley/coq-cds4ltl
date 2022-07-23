args@{ version ? "coq-cds4ltl_8_15", pkgs ? null }:
(import ./default.nix args).${version}
