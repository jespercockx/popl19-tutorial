#!/bin/bash

# check dependencies: cabal and git
cabal --version || exit 1
git   --version || exit 1

# install Agda (requires GHC):
cabal install alex happy
cabal install Agda && agda-mode setup

# install standard library (requires git):
git clone https://github.com/agda/agda-stdlib.git
cd agda-stdlib
git checkout v0.17
cabal install
mkdir $HOME/.agda
echo $PWD/agda-stdlib/standard-library.agda-lib >> $HOME/.agda/libraries
echo standard-library >> $HOME/.agda/defaults

# install BNFC (also needs `alex` and `happy`):
cabal install BNFC
