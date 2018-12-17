.PHONY: all parser test

all : parser test

parser :
	make -C src

test :
	make -C test

# EOF
