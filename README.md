Correct by Construction Programming in Agda
===========================================

Agda tutorial at POPL 2019

Links
-----

* [Annoucement](https://popl19.sigplan.org/event/popl-2019-tutorialfest-t5-correct-by-construction-programming-in-agda)

* [Slides](slides/slides.html)

* [Code listing](src/html/runwhile.html)

Abstract
--------

In a dependently typed programming language you can get much stronger static guarantees about the correctness of your program than in most other languages. At the same time, dependent types enable new forms of interactive programming, by letting the types guide the construction of the program. Dependently typed languages have existed for many years, but only recently have they become usable for practical programming.

In this tutorial, you will learn how to write correct-by-construction programs in the dependently typed programming language Agda. Concretely, we will together implement a verified typechecker and interpreter for a small C-like imperative language. Along the way, We will explore several modern features of the Agda language that make this task more pleasant, such as dependent pattern matching, monads and do-notation, coinduction and copattern matching, instance arguments, sized types, and the Haskell FFI.

Prerequisites
-------------

For the exercises in this tutorial, you need to install Agda 2.5.4.2 or later, the Agda standard library v0.17 or later, and the BNFC tool. There is a [bash script](https://github.com/jespercockx/popl19-tutorial/blob/master/setup.sh) that installs all of these on a fresh installation of Ubuntu 18.04 or later. Alternatively, here are step-by-step instructions:

First, make sure you have git, cabal, and emacs installed. You also
need the `zlib` c library. On Ubuntu and related systems, the
following command should work:

```bash
sudo apt-get install git cabal-install emacs zlib1g-dev
```

Make sure that binaries installed by `cabal` are available on your
path by adding the following line to `~/.profile`:

```bash
export PATH="$PATH:$HOME/.cabal/bin"
```

To install Agda and its prerequisites:

```bash
cabal update
cabal install alex happy
cabal get Agda && cd Agda-2.5.4.2 && cabal install
agda-mode setup
```

To install the Agda standard library:

```bash
git clone https://github.com/agda/agda-stdlib.git
cd agda-stdlib && git checkout v0.17 && cabal install
mkdir $HOME/.agda
echo $PWD/standard-library.agda-lib >> $HOME/.agda/libraries
echo standard-library >> $HOME/.agda/defaults
cd ..
```

To install BNFC:

```bash
cabal install BNFC
```