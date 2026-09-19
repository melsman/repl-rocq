ROCQ ?= rocq
FLAGS = -Q . Repl
.PHONY: all check clean
all: Names.vo Simulation.vo Examples.vo
Names.vo: Names.v
	$(ROCQ) compile $(FLAGS) $<
Simulation.vo: Simulation.v Names.vo
	$(ROCQ) compile $(FLAGS) $<
Examples.vo: Examples.v Names.vo
	$(ROCQ) compile $(FLAGS) $<
check: all
	$(ROCQ) check $(FLAGS) Repl.Names Repl.Simulation Repl.Examples
clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux
