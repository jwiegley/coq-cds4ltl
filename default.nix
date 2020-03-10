args@{ packages ? "coqPackages_8_10"

, rev      ? "1fe82110febdf005d97b2927610ee854a38a8f26"
, sha256   ? "08x6saa7iljyq2m0j6p9phy0v17r3p8l7vklv7y7gvhdc7a85ppi"

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
         inherit (known-good-20191113_070954) shared-mime-info;
       })
    ];
  }
}:

with pkgs.${packages};

let
  coq-haskell = pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-haskell-${version}";
    version = "1.0";

    src = pkgs.fetchFromGitHub {
      owner = "jwiegley";
      repo = "coq-haskell";
      rev = "e68b56e938f134865c837b5c090eb316867451fa";
      sha256 = "00ybvx42pax5h3s5bg623zvbh8lix7ccc6nmfzb7awsqwdcg9aan";
      # date = 2020-02-10T15:47:15-08:00;
    };

    buildInputs = [ coq.ocaml coq.camlp5 coq.findlib coq ];

    preBuild = "coq_makefile -f _CoqProject -o Makefile";

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    meta = with pkgs.stdenv.lib; {
      homepage = https://github.com/jwiegley/coq-haskell;
      description = "A library for Haskell users writing Coq programs";
      maintainers = with maintainers; [ jwiegley ];
      platforms = coq.meta.platforms;
    };

    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.5" "8.6" "8.7" "8.8" "8.9" "8.10" "8.11" ];
    };
  };

  equations = pkgs.stdenv.mkDerivation rec {

    name = "coq${coq.coq-version}-equations-${version}";
    version = "1.2.2pre";

    src =
      if coq.coq-version == "8.11" then
        pkgs.fetchFromGitHub {
          owner = "mattam82";
          repo = "Coq-Equations";
          rev = "refs/heads/8.11";
          sha256 = "1jywfhnxrjwzdsm52ys7db080cci98wjyv74kd78nc4i7d7niqgv";
        }
      else
        pkgs.fetchFromGitHub {
          owner = "mattam82";
          repo = "Coq-Equations";
          rev = "refs/heads/8.10";
          sha256 = "0j3z4l5nrbyi9zbbyqkc6kassjanwld2188mwmrbqspaypm2ys68";
        };

    buildInputs = with coq.ocamlPackages; [ ocaml camlp5 findlib coq ];

    configurePhase = "./configure.sh";

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    meta = with pkgs.stdenv.lib; {
      homepage = https://mattam82.github.io/Coq-Equations/;
      description = "A plugin for Coq to add dependent pattern-matching";
      maintainers = with maintainers; [ jwiegley ];
      platforms = coq.meta.platforms;
    };

    passthru = {
      compatibleCoqVersions = v: builtins.hasAttr v params;
    };
  };

  category-theory = pkgs.stdenv.mkDerivation rec {
    name = "category-theory";
    version = "1.0";

    src = pkgs.fetchFromGitHub {
      owner = "jwiegley";
      repo = "category-theory";
      rev = "380ff60d34c306f7005babc3dade1d96b5eeb935";
      sha256 = "1r4v5lm090i23kqa1ad39sgfph7pfl458kh8rahsh1mr6yl1cbv9";
      # date = 2020-01-12T15:09:07-08:00;
    };

    buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib equations ];
    enableParallelBuilding = true;

    buildPhase = "make JOBS=$NIX_BUILD_CORES";
    preBuild = "coq_makefile -f _CoqProject -o Makefile";
    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" "8.9" "8.10" "8.11" ];
   };
  };

in pkgs.stdenv.mkDerivation rec {
  name = "coq${coq.coq-version}-constructive-ltl-${version}";
  version = "1.0";

  src =
    if pkgs ? coqFilterSource
    then pkgs.coqFilterSource [] ./.
    else ./.;

  buildInputs = [
    coq coq.ocaml coq.camlp5 coq.findlib
    coq-haskell category-theory equations
  ];
  enableParallelBuilding = true;

  buildPhase = "make -j$NIX_BUILD_CORES";
  preBuild = "coq_makefile -f _CoqProject -o Makefile";
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" "8.9" "8.10" "8.11" ];
 };
}
