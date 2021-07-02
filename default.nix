args@{ packages ? "coqPackages_8_13"

, rev    ? "c74fa74867a3cce6ab8371dfc03289d9cc72a66e"
, sha256 ? "13bnmpdmh1h6pb7pfzw5w3hm6nzkg9s1kcrwgw1gmdlhivrmnx75"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

with pkgs.${packages};

pkgs.stdenv.mkDerivation rec {
  name = "coq${coq.coq-version}-ltl-${version}";
  version = "1.0";

  src =
    if pkgs ? coqFilterSource
    then pkgs.coqFilterSource [] ./.
    else ./.;

  buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib ];
  enableParallelBuilding = true;

  buildPhase = "make -j$NIX_BUILD_CORES";
  preBuild = "coq_makefile -f _CoqProject -o Makefile";
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.13" ];
 };
}
