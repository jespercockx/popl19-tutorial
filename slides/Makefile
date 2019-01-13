# Agda 2.5.4.2 misses the html-highlight option
# agda=agda-2.5.4.2

agda=agda --html-highlight=auto
default: slides.html

vpath reveal.js $(HOME) .

slides.html: _build/slides.md reveal.js theme.css Agda.css Makefile
	pandoc -t revealjs -V revealjs-url=$(word 2, $^) --css=Agda.css --css=theme.css --mathjax -s $< -o $@

_build/slides.md: slides.lagda.md
	$(agda) --html --html-dir=_build $<

./reveal.js:
	git clone https://github.com/hakimel/reveal.js
