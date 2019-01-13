.PHONY: all parser test slides

all : parser test slides

parser :
	make -C src

test :
	make -C test

slides :
	make -C slides

# EOF
