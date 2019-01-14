#!/bin/bash

# check or install dependencies:
cabal --version || sudo apt-get install cabal-install || exit 1
git   --version || sudo apt-get install git           || exit 1
emacs --version || sudo apt-get install emacs         || exit 1
sudo apt-get install zlib1g-dev

# install Agda (requires GHC):
cabal update
cabal install alex happy
cabal install Agda && agda-mode setup

# install standard library (requires git):
git clone https://github.com/agda/agda-stdlib.git
cd agda-stdlib && git checkout v0.17 && cabal install
mkdir $HOME/.agda
echo $PWD/agda-stdlib/standard-library.agda-lib >> $HOME/.agda/libraries
echo standard-library >> $HOME/.agda/defaults

# install BNFC (also needs `alex` and `happy`):
cabal install BNFC
