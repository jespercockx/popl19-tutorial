# Makefile for While language

# List of goals not corresponding to file names.
.PHONY : default all test sdist clean distclean html

# BNFC generated parser
parser=While/Test

## Agda program
###########################################################################

# agda=agda-2.5.4.2
agda=agda
ghcflags=--ghc-flag=-i../haskell --ghc-flag=-Wwarn

# runwhile.agda must be first
agdafiles=runwhile.agda Library.agda Library/Eq.agda Library/Monad.agda Library/Print.agda AST.agda Parser.agda WellTypedSyntax.agda TypeChecker.agda Value.agda Delay.agda Interpreter.agda

default : test

all : runwhile html test

runwhile : $(agdafiles) $(parser)
	$(agda) --compile $(ghcflags) $<

test : runwhile
	make -C ../test

parser : $(parser)
	./$(parser) ../test/gcd.c

html : $(agdafiles)
	$(agda) --html $<


## Haskell parser
###########################################################################

files=Main.hs While.cf Makefile

Main : $(files) $(parser)
	ghc --make Main.hs -o Main

# Rules to build the parser:

While/Test.hs While/Lex.x While/Par.y : While.cf
	bnfc --haskell -d $<

%.hs : %.y
	happy -gcai $<
#	happy --ghc --coerce --array --info $<

%.hs : %.x
	alex --ghc $<

$(parser) : While/Test.hs While/Par.hs While/Lex.hs
	ghc --make $< -o $@

# Rules for cleaning generated files:

clean :
	-rm -f While/*.log While/*.aux While/*.hi While/*.o While/*.dvi *.hi *.o

distclean : clean
	-rm -f While/Doc.* While/Lex.* While/Par.* While/Layout.* While/Skel.* While/Print.* While/Test.* While/Abs.* While/Test While/ErrM.* While/SharedString.* While/ComposOp.* While/While.dtd While/XML.* While/*.bak
	-rmdir -p While/
	-rm -f Main.tar.gz Main

# EOF
