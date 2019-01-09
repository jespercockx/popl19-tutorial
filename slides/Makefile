default: slides.html

vpath reveal.js $(HOME) .

slides.html: _build/slides.md reveal.js theme.css Agda.css Makefile
	pandoc -t revealjs -V revealjs-url=$(word 2, $^) --css=Agda.css --css=theme.css -V transition="linear" -V center="false" --mathjax -s $< -o $@

_build/slides.md: slides.lagda.md
	agda --html --html-dir=_build --html-highlight=auto $<

./reveal.js:
	git clone https://github.com/hakimel/reveal.js
