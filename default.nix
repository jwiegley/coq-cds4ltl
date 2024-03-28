args@{
  rev    ? "07262b18b97000d16a4bdb003418bd2fb067a932"
, sha256 ? "05rnlf6vvzvyhya48bql9j0b6rqmiajzx0yasal522pwi1g2m122"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let coq-cds4ltl = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-cds4ltl-${version}";
    version = "1.0";

    src = if pkgs ? coqFilterSource
          then pkgs.coqFilterSource [] ./.
          else ./.;

    buildInputs = [
      coq coq.ocaml coq.camlp5 coq.findlib
    ];
    enableParallelBuilding = true;

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    env = pkgs.buildEnv { inherit name; paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v:
        builtins.elem v [ "8.14" "8.15" "8.16" "8.17" "8.18" "8.19" ];
    };
  };

in {
  coq-cds4ltl_8_14 = coq-cds4ltl "coqPackages_8_14";
  coq-cds4ltl_8_15 = coq-cds4ltl "coqPackages_8_15";
  coq-cds4ltl_8_16 = coq-cds4ltl "coqPackages_8_16";
  coq-cds4ltl_8_17 = coq-cds4ltl "coqPackages_8_17";
  coq-cds4ltl_8_18 = coq-cds4ltl "coqPackages_8_18";
  coq-cds4ltl_8_19 = coq-cds4ltl "coqPackages_8_19";
}
