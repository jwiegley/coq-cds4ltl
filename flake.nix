{
  description = "Implementation in Coq of the axiomatic system for linear temporal logic CDS4LTL";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = import nixpkgs { inherit system; };
      in rec {
        packages = rec {
          coq-cds4ltl = coqPackages: with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
            name = "coq${coq.coq-version}-coq-cds4ltl-${version}";
            version = "1.0";

            src = if pkgs ? coqFilterSource
            then pkgs.coqFilterSource [] ./.
            else ./.;

            buildInputs = [
              coq coq.ocaml coq.findlib
            ] ++ pkgs.lib.optionals (coqPackages == "coqPackages_8_14" ||
                                     coqPackages == "coqPackages_8_15") [
              dpdgraph
            ];
            enableParallelBuilding = true;

            configurePhase = "coq_makefile -f _CoqProject -o Makefile.coq";

            installFlags = [
              "COQLIB=$(out)/lib/coq/${coq.coq-version}/"
              "COQLIBINSTALL=$(out)/lib/coq/${coq.coq-version}/user-contrib"
              "COQPLUGININSTALL=$(OCAMLFIND_DESTDIR)"
              "DOCDIR=$(out)/share/coq/${coq.coq-version}/"
              "COQDOCINSTALL=$(out)/share/coq/${coq.coq-version}/user-contrib"
            ];

            env.env = pkgs.buildEnv { inherit name; paths = buildInputs; };
            passthru = {
              compatibleCoqVersions = v:
              builtins.elem v [ "8.14" "8.15" "8.16" "8.17" "8.18" "8.19" ];
            };
          };

          coq-cds4ltl_8_14 = coq-cds4ltl "coqPackages_8_14";
          coq-cds4ltl_8_15 = coq-cds4ltl "coqPackages_8_15";
          coq-cds4ltl_8_16 = coq-cds4ltl "coqPackages_8_16";
          coq-cds4ltl_8_17 = coq-cds4ltl "coqPackages_8_17";
          coq-cds4ltl_8_18 = coq-cds4ltl "coqPackages_8_18";
          coq-cds4ltl_8_19 = coq-cds4ltl "coqPackages_8_19";

          default = coq-cds4ltl_8_19;
        };

        defaultPackage = packages.default;
      });
}
