.PHONY: build
build:
	dune build src/effmain.exe

.PHONY: exec
exec:
	dune exec src/effmain.exe -- -v --colors $(args)

.PHONY: tests
tests:
	dune build src/ci_tests.exe && dune exec src/ci_tests.exe -- -v --colors $(args)

.PHONY: clean
clean:
	dune clean
	rm -f generated_tests/*

.PHONY: clean
format:
	dune build @fmt --auto-promote