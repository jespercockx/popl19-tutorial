# Agda 2.5.4.2 misses the html-highlight option
# agda=agda-2.5.4.2

agda=agda --html-highlight=auto

patchTheme=patchTheme.css

default: slides.html

vpath reveal.js $(HOME) .

slides.html: _build/slides.md reveal.js theme.css Agda.css Makefile $(patchTheme)
	pandoc -t revealjs -V revealjs-url=https://cdn.jsdelivr.net/npm/reveal.js -V theme="white" --css=Agda.css --css=$(patchTheme) --mathjax -s $< -o $@

_build/slides.md: slides.lagda.md
	$(agda) --html --html-dir=_build $<

./reveal.js:
	git clone https://github.com/hakimel/reveal.js

# EOF
