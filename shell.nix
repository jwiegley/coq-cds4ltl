args@{ version ? "coq-cds4ltl_8_19", pkgs ? null }:
(import ./default.nix args).${version}
