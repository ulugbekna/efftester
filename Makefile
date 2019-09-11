.PHONY: build exec run tests clean format

build:
	dune build src/effmain.exe $(dune_args)

exec:
	dune exec src/effmain.exe $(dune_args) -- -v --colors $(qcheck_args)

run: build exec

tests:
	dune build src/ci_tests.exe $(build_args) && \
	dune exec src/ci_tests.exe $(exec_args) -- -v --colors $(qcheck_args)

clean:
	dune clean
	rm -f generated_tests/*

format:
	dune build @fmt --auto-promote