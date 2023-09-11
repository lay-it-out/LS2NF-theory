{ lib,
  mkCoqDerivation,
  version ? null,
  coq,
  dune_3,
  ocaml,
  ocamlbuild,
  stdpp, ... }:

{ LS2NF =
    mkCoqDerivation {
      namePrefix = [ "coq" ];
      pname = "LS2NF";
      owner = "LS2NF";

      inherit version;

      propagatedBuildInputs =
        [ coq
          dune_3
        ] ++
        # Coq libraries
        [ stdpp
        ] ++
        # Ocaml
        [ ocaml
          ocamlbuild
        ];

      src = ./.;

      buildPhase = ''
        make
      '';

      installPhase = ''
        make doc
        mkdir -p $out/share
        mv doc_generated $out/share/
      '';

      meta = {
        description = "Coq formulation on the meta-theories of Layout-Sensitive Binary Normal Form";
      };
    };
}