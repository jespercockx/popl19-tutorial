# Makefile for While language

## Variables
###########################################################################

files=Main.hs While.cf Makefile

###########################################################################

# List of goals not corresponding to file names.
.PHONY : sdist clean distclean

# 'Main' is default goal and needs to remain first goal in this file!
# The extra dependency While/Test ensures that the parser is built from While.cf

Main : $(files) While/Test
	ghc --make Main.hs -o Main

# Rules to build the parser:

While/Test.hs While/Lex.x While/Par.y : While.cf
	bnfc --haskell -d $<

%.hs : %.y
	happy -gcai $<
#	happy --ghc --coerce --array --info $<

%.hs : %.x
	alex --ghc $<

While/Test : While/Test.hs While/Par.hs While/Lex.hs
	ghc --make $< -o $@

# Rules for cleaning generated files:

clean :
	-rm -f While/*.log While/*.aux While/*.hi While/*.o While/*.dvi *.hi *.o

distclean : clean
	-rm -f While/Doc.* While/Lex.* While/Par.* While/Layout.* While/Skel.* While/Print.* While/Test.* While/Abs.* While/Test While/ErrM.* While/SharedString.* While/ComposOp.* While/While.dtd While/XML.* While/*.bak
	-rmdir -p While/
	-rm -f Main.tar.gz Main

# EOF
