.PHONY: all build install clean

all: build

build:
	dune build -p typeClasses

install:
	dune install -p typeClasses

clean:
	dune clean -p typeClasses
