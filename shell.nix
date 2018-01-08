{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = [ (pkgs.haskell.packages.ghc822.ghcWithPackages (ps : [ ps.mtl ] )) ];
}
