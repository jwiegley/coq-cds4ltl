args@{ packages ? "coqPackages_8_13"

, rev      ? "a2b0ea6865b2346ceb015259c76e111dcca039c5"
, sha256   ? "12dgwajv3w94p13scj68c24v01p055k9hcpcsn7w9i8fys72s99d"

, pkgs     ? import (builtins.fetchTarball {
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
    compatibleCoqVersions = v:
      builtins.elem v [ "8.13" ];
 };
}
