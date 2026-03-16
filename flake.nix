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
        rocq = pkgs.rocqPackages_9_1;

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

        cds4ltl = mkCds4ltl rocq;

      in {
        packages = {
          coq-cds4ltl_9_1 = cds4ltl;
          default = cds4ltl;
        };

        checks = {
          build = cds4ltl;

          lint = pkgs.runCommand "coq-lint" {} ''
            ADMITTED=$({ grep -c 'Admitted\.' ${./.}/src/*.v || true; } \
              | awk -F: '{sum+=$2} END{print sum}')
            echo "Admitted proofs: $ADMITTED (baseline: 0)"
            if [ "$ADMITTED" -gt 0 ]; then
              echo "ERROR: Admitted proofs found (expected 0, got $ADMITTED)"
              exit 1
            fi
            if { grep -rn 'admit\.' ${./.}/src/*.v || true; } | grep -v 'Admitted' | grep -q .; then
              echo "ERROR: Found bare 'admit' tactic usage"
              exit 1
            fi
            touch $out
          '';

          whitespace = pkgs.runCommand "whitespace-check" {} ''
            FAIL=0
            if grep -rn ' \+$' ${./.}/src/*.v; then
              echo "ERROR: Trailing whitespace found in .v files"
              FAIL=1
            fi
            TAB=$(printf '\t')
            if grep -rn "$TAB" ${./.}/src/*.v; then
              echo "ERROR: Tab characters found in .v files (use spaces)"
              FAIL=1
            fi
            if [ "$FAIL" -ne 0 ]; then exit 1; fi
            touch $out
          '';
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            rocq.rocq-core
            rocq.rocq-core.ocamlPackages.ocaml
            rocq.rocq-core.ocamlPackages.findlib
            rocq.stdlib
            pkgs.gnumake
            pkgs.lefthook
          ];
        };
      });
}
