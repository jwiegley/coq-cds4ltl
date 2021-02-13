args@{ packages ? "coqPackages_8_13"

, rev      ? "a58a0b5098f0c2a389ee70eb69422a052982d990"
, sha256   ? "1dmnm6r67q75ql96hag851438ybqlx21vfn309ir3z6n08a2qsfs"

, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
    overlays = [
      (self: super:
       let
         nixpkgs = { rev, sha256 }:
           import (super.fetchFromGitHub {
             owner = "NixOS";
             repo  = "nixpkgs";
             inherit rev sha256;
           }) { config.allowUnfree = true; };

         known-good-20191113_070954 = nixpkgs {
           rev    = "620124b130c9e678b9fe9dd4a98750968b1f749a";
           sha256 = "0xgy2rn2pxii3axa0d9y4s25lsq7d9ykq30gvg2nzgmdkmy375rr";
         };
       in
       {
         # inherit (known-good-20191113_070954) shared-mime-info;
       })
    ];
  }
}:

with pkgs.${packages};

pkgs.stdenv.mkDerivation rec {
  name = "coq${coq.coq-version}-constructive-ltl-${version}";
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
      builtins.elem v [ "8.6" "8.7" "8.8" "8.9" "8.10" "8.11" "8.12" "8.13" ];
 };
}
