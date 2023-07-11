{
  description = "LS2NF";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/master";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        lib = pkgs.lib;
        coq = pkgs.coq_8_17;
        ocamlPkgs = coq.ocamlPackages;
        coqPkgs = pkgs.coqPackages_8_17;
        version = "LS2NF:main";
      in {
        defaultPackage =
          (pkgs.callPackage ./release.nix (ocamlPkgs // coqPkgs // { inherit coq version; })).LS2NF;
      });
}