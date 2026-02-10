{
  description = "Implementation in Rocq of the axiomatic system for linear temporal logic CDS4LTL";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        mkCds4ltl = rocqPkgs:
          let
            compiler = rocqPkgs.rocq-core;
            ocaml = compiler.ocamlPackages.ocaml;
            findlib = compiler.ocamlPackages.findlib;
            versionStr = compiler.version;
          in pkgs.stdenv.mkDerivation rec {
            name = "rocq${versionStr}-coq-cds4ltl-${version}";
            version = "1.0";

            src = if pkgs ? coqFilterSource
              then pkgs.coqFilterSource [] ./.
              else ./.;

            buildInputs = [
              compiler ocaml findlib
              rocqPkgs.stdlib
            ];
            enableParallelBuilding = true;

            configurePhase = "rocq makefile -f _CoqProject -o Makefile.coq";

            installFlags = [
              "COQLIB=$(out)/lib/coq/${versionStr}/"
              "COQLIBINSTALL=$(out)/lib/coq/${versionStr}/user-contrib"
              "COQPLUGININSTALL=$(OCAMLFIND_DESTDIR)"
              "DOCDIR=$(out)/share/coq/${versionStr}/"
              "COQDOCINSTALL=$(out)/share/coq/${versionStr}/user-contrib"
            ];

            env.env = pkgs.buildEnv { inherit name; paths = buildInputs; };
            passthru = {
              compatibleCoqVersions = v:
              builtins.elem v [ "9.1" ];
            };
          };

      in {
        packages = {
          coq-cds4ltl_9_1 = mkCds4ltl pkgs.rocqPackages_9_1;
          default = mkCds4ltl pkgs.rocqPackages_9_1;
        };

        devShells.default = let
          rocq = pkgs.rocqPackages_9_1;
        in pkgs.mkShell {
          buildInputs = [
            rocq.rocq-core
            rocq.rocq-core.ocamlPackages.ocaml
            rocq.rocq-core.ocamlPackages.findlib
            rocq.stdlib
            pkgs.gnumake
          ];
        };
      });
}
