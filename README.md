# REPL model correspondence in Rocq

This is a small mechanised foundation for the technical report paper [Crafting a REPL for HOT Compiled Execution](https://elsman.com/pdf/repl.pdf). The development is checked with Rocq 9.2.
Run `make` to compile and `make check` to recheck the proof objects.
The development uses only the standard library; there are no admitted proofs
or global axioms.

## Scope and theorem statements

`Names.v` models external symbol names by natural numbers and existentially
bound names by local indices. Opening replaces every bound index with a fresh
name. The intended binder scopes over both the object and the compilation-basis
contribution. External names remain rigid.

- `no_duplicate_names` proves that extending a unique loaded-name list preserves uniqueness.
- `resolution` proves that every external or local reference resolves after opening.
- `link_progress` constructs a link derivation from a well-formed object.
- `link_safety` proves that linking preserves uniqueness.
- `alpha_open` proves that changing the opening consistently renames local references while preserving external references.

The linker uses explicit disjointness and resolution premises. It allocates
names above the maximum loaded name. The renaming lemma is an opening law on
well-scoped references, not a formalisation of arbitrary finite permutations.
All bound names are conservatively retained as loaded names, including private
names. This is stronger than export-only uniqueness and prevents reuse after an
exception. Representation contracts, native addresses, relocation, and memory
allocation are not yet modelled.

`Simulation.v` separates declaration processing from session accumulation.
`process` returns an opened `declaration_result`: an optional pair of basis
contributions, an outcome, and a resulting store. `None` represents the empty
contribution. `apply_result` extends both bases for `Some` and retains them for
`None`; one `IApply` rule defines the source session transition. The lemmas
`rejection_result` and `exception_result` prove that rejected and exceptional
results contribute no bindings, with rejection also retaining the store.
The compiled relation still distinguishes rejection, normal completion, and
exceptional completion.

The paper's existential type-name binder is abstracted here: `elaborate` returns
an already opened static contribution. This refactoring does not mechanise
alpha-equivalence of source packages or freshness of type names. Those remain
obligations for an instantiation, distinct from the proved runtime-symbol
allocation properties in `Names.v`.
Static and dynamic basis extension are parameters (`addS`, `addD`). On normal
completion, `commit` represents C + C', opening the contribution at exactly the
same fresh base as the object. On an exception the bases remain unchanged,
while the store/heap and loaded objects may change.

- `compiled_preserves_names` proves name uniqueness for every compiled step, independently of compiler correctness.
- `declaration_simulation` proves matching compiled execution for a processed declaration and relates its applied result to the target state.
- `step_simulation` derives matching compiled execution and preservation of the representation relation for one source interaction.
- `session_simulation` proves the same result for finite sessions by induction, preserving the declaration/outcome trace and name uniqueness.

`correct_result` defines semantic validity of a fixed result independently
of the compilation relation, universally over represented runtime states.
`compiler_correct` requires every successful compilation derivation to produce
such a result. Normal and exceptional execution correctness are derived lemmas.
`compiled_result_links` derives linking progress and uniqueness from this
property and a represented state with unique loaded names.

The correspondence theorems are **conditional** on this declaration-level
property, static agreement extracted from representation, compilation existence
under static agreement, and agreement on rejection. Compilation existence does
not depend on a runtime heap or termination of source evaluation. These are
explicit theorem parameters; `Print Assumptions` reporting no global axioms
does not mean that the properties have been discharged for MLKit.

Compilation totality applies to every elaborating declaration in a represented
state. Execution progress applies when the source evaluation terminates,
including termination with an exception. It does not assert termination of
arbitrary Standard ML programs. The theorem establishes forward simulation;
converse simulation, divergence preservation, and resource failures remain
outside its scope. Outcomes currently distinguish rejection, normal return,
and an abstract exception value; printed values are not modelled.

`Examples.v` checks concrete fresh allocation, an imported name, and retention
of an allocated name across a presumed exceptional initialisation. These are
linker examples, not a compiler instance discharging these properties.

## Connecting this framework to the paper and MLKit

The source rules follow the paper's reading of *The Definition of Standard ML
(Revised)*, Section 8. The linker separates external imports from fresh local
names in the spirit of Cardelli's *Program Fragments, Linking, and
Modularization*. The files do not formalise either publication in full.

The declaration-level factoring follows the translation judgements in Elsman's
*A Framework for Cut-Off Incremental Recompilation and Inter-Module
Optimization*. Its structural phase properties do not themselves establish
semantic preservation.

Next, instantiate compilation bases and their extension using the incremental
compilation account in Elsman's separate-compilation work. Prove that opening
acts jointly on the basis contribution and generated code, that imports carry
compatible representation contracts, and that each compiler phase preserves
the representation relation. Those results should discharge the properties in
`Simulation.v`. In particular, the abstract `commit` parameter alone does not
prove that a concrete compiler handles bindings correctly.
