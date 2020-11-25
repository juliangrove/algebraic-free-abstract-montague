# Non-reproducible "current" version:
# with (import <nixpkgs> {});
with import (fetchTarball https://github.com/NixOS/nixpkgs/archive/nixos-20.09.tar.gz) { };
let ghc = haskellPackages.ghcWithPackages (hp: with hp; [
  mtl
]);
in
stdenv.mkDerivation {
  name = "docsEnv";
  shellHook = ''
    export LANG=C.UTF-8
    export LC_ALL=C.UTF-8
    eval $(egrep ^export ${ghc}/bin/ghc)
  '';
  buildInputs = [
    ghc
  ];
}
