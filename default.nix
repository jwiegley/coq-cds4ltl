args@{ packages ? "coqPackages_8_13"

, rev    ? "c71c411d8f9ec5bd746fcd925555cee5b3cdd297"
, sha256 ? "039aldz9mram45jlicab5sa83ygsj7vmzgqf04bks77f173c6pk2"
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
