#!/bin/bash

# check or install dependencies:
cabal --version || sudo apt-get install cabal-install || exit 1
git   --version || sudo apt-get install git           || exit 1
emacs --version || sudo apt-get install emacs         || exit 1
sudo apt-get install zlib1g-dev

# install Agda (requires GHC):
cabal update
cabal install alex happy
cabal get Agda && cd Agda-2.5.4.2 && cabal install 

# make sure agda is on the path
export PATH=$PATH:$HOME/.cabal/bin
agda --version || exit 1

# setup emacs mode
echo (setenv \"PATH\" (concat (getenv \"PATH\") \":$HOME/.cabal/bin\")) >> $HOME/.emacs
echo (setq exec-path (append exec-path \'(\"$HOME/.cabal/bin\"))) >> $HOME/.emacs
agda-mode setup

# install standard library (requires git):
git clone https://github.com/agda/agda-stdlib.git
cd agda-stdlib && git checkout v0.17 && cabal install
mkdir $HOME/.agda
echo $PWD/agda-stdlib/standard-library.agda-lib >> $HOME/.agda/libraries
echo standard-library >> $HOME/.agda/defaults

# install BNFC (also needs `alex` and `happy`):
cabal install BNFC
