args@{
  rev    ? "a0a69be4b5ee63f1b5e75887a406e9194012b492"
, sha256 ? "16npglnyagxa9xrf80z4wy5lbff6xhcykzr96n90l6jdf0171a79"
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
      compatibleCoqVersions = v: builtins.elem v [ "8.14" "8.15" ];
    };
  };

in {
  constructive-ltl_8_14 = constructive-ltl "coqPackages_8_14";
  constructive-ltl_8_15 = constructive-ltl "coqPackages_8_15";
}
