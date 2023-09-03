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
        echo "Build done."
      '';

      meta = {
        description = "Coq formulation on the meta-theories of Layout-Sensitive Binary Normal Form";
      };
    };
}