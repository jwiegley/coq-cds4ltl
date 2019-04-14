args@{ packages ? "coqPackages_8_9"

, rev      ? "d73f16d6767e99675682f822dac3017bf9af1e83"
, sha256   ? "1b5wix9kr5s3hscpl425si0zw00zzijc9xrcph6l2myh4n5nvcm0"

, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

with pkgs.${packages};

let
  coq-haskell = import ../coq-haskell args;
  # coq-haskell = pkgs.stdenv.mkDerivation rec {
  #   name = "coq${coq.coq-version}-haskell-${version}";
  #   version = "1.0";

  #   src = pkgs.fetchFromGitHub {
  #     owner = "jwiegley";
  #     repo = "coq-haskell";
  #     rev = "83a5db4b5741745ec9d522543d3616c308dfb542";
  #     sha256 = "0310sbf6i8zfvrw5mqaifnh4rdl0j64gj3j20ak533xpq1fpbd4v";
  #     # date = 2018-10-04T18:17:03-07:00;
  #   };

  #   buildInputs = [ coq.ocaml coq.camlp5 coq.findlib coq ssreflect ];

  #   preBuild = "coq_makefile -f _CoqProject -o Makefile";

  #   installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  #   meta = with pkgs.stdenv.lib; {
  #     homepage = https://github.com/jwiegley/coq-haskell;
  #     description = "A library for Haskell users writing Coq programs";
  #     maintainers = with maintainers; [ jwiegley ];
  #     platforms = coq.meta.platforms;
  #   };

  #   passthru = {
  #     compatibleCoqVersions = v: builtins.elem v [ "8.5" "8.6" "8.7" "8.8" ];
  #   };
  # };

  category-theory = import ../category-theory args;
  # category-theory = pkgs.stdenv.mkDerivation rec {
  #   name = "category-theory";
  #   version = "1.0";

  #   src = pkgs.fetchFromGitHub {
  #     owner = "jwiegley";
  #     repo = "category-theory";
  #     rev = "e204fee5b8662e414ecca13ca543fae3b19bd72a";
  #     sha256 = "15hi0vmvm42qzsh5zzw78q2l5c8bf4nis2mjbannm0m96dpmszk0";
  #     # date = 2018-10-05T10:50:15-07:00;
  #   };

  #   buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib equations ];
  #   enableParallelBuilding = true;

  #   buildPhase = "make JOBS=$NIX_BUILD_CORES";
  #   preBuild = "coq_makefile -f _CoqProject -o Makefile";
  #   installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  #   passthru = {
  #     compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" ];
  #  };
  # };

in pkgs.stdenv.mkDerivation rec {
  name = "coq${coq.coq-version}-constructive-ltl-${version}";
  version = "1.0";

  src =
    if pkgs ? coqFilterSource
    then pkgs.coqFilterSource [] ./.
    else ./.;

  buildInputs = [
    coq coq.ocaml coq.camlp5 coq.findlib
    equations coq-haskell category-theory
  ];
  enableParallelBuilding = true;

  buildPhase = "make -j$NIX_BUILD_CORES";
  preBuild = "coq_makefile -f _CoqProject -o Makefile";
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" "8.9" ];
 };
}
