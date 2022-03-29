args@{
  rev    ? "9222ae36b208d1c6b55d88e10aa68f969b5b5244"
, sha256 ? "0dvl990alr4bb64w9b32dhzacvchpsspj8p3zqcgk7q5akvqh1mw"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let constructive-ltl = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-constructive-ltl-${version}";
    version = "1.0";

    src = if pkgs ? coqFilterSource
          then pkgs.coqFilterSource [] ./.
          else ./.;

    buildInputs = [
      coq coq.ocaml coq.camlp5 coq.findlib
    ];
    enableParallelBuilding = true;

    buildFlags = [
      "JOBS=$(NIX_BUILD_CORES)"
    ];

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    env = pkgs.buildEnv { inherit name; paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.10" "8.11" "8.12" "8.13" "8.14" "8.15" ];
    };
  };

in {
  constructive-ltl_8_10 = constructive-ltl "coqPackages_8_10";
  constructive-ltl_8_11 = constructive-ltl "coqPackages_8_11";
  constructive-ltl_8_12 = constructive-ltl "coqPackages_8_12";
  constructive-ltl_8_13 = constructive-ltl "coqPackages_8_13";
  constructive-ltl_8_14 = constructive-ltl "coqPackages_8_14";
  constructive-ltl_8_15 = constructive-ltl "coqPackages_8_15";
}
