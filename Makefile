all: library prover

library:
	$(MAKE) -C matching-logic

prover:
	$(MAKE) -C prover
