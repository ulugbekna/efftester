.PHONY: build
build:
	dune build src/effmain.exe

.PHONY: exec
exec:
	dune exec src/effmain.exe

.PHONY: tests
tests:
	dune build src/ci_tests.exe && dune exec src/ci_tests.exe

.PHONY: clean
clean:
	dune clean
	rm -f generated_tests/*

.PHONY: clean
format:
	dune build @fmt --auto-promote