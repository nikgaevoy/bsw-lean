# BSW-Lean

A Lean 4 formalization of the Resolution proof system and the Ben-Sasson–Wigderson size–width relationship.

**Authors:** Yaroslav Alekseev, Nikita Gaevoy

## Overview

Resolution is one of the most well-studied propositional proof systems. Given an unsatisfiable CNF formula (a conjunction of clauses $C_1 \land \dots \land C_k$), one derives the empty clause $\bot$ using the single rule

$$
\frac{A \lor x \quad B \lor \neg x}{A \lor B}.
$$

This project formalizes both the **tree-like** and **DAG-like** variants of the system, proves their soundness and completeness, and establishes the classical **size–width relationship**: short refutations imply narrow refutations.

## Main results

- **Soundness and completeness** of tree-like Resolution (`Treelike.lean`) and DAG-like Resolution (`Daglike.lean`): a CNF formula is unsatisfiable iff it has a refutation in each system.
- **Size–width relationship** (`SizeWidth.lean`, theorem `width_imply_size`): if a CNF formula with clauses of width at most $W_C$ has a tree-like refutation of size at most $2^W$, then it also has a tree-like refutation of width at most $W + W_C$.

The key complexity measures (size, width) are defined inside the files where the corresponding proof system lives.

## Project layout

```
BSWLean/
├── CNF.lean              -- Variables, Literals, Clauses, CNFFormulas, Assignments, Clause.resolve
├── Substitutions.lean    -- Partial-assignment operations: restrict, split, shrink, substitute
├── Conversion.lean       -- Assignment.toClause (negation of an assignment as a clause)
├── SuperCNF.lean         -- Variable-set-agnostic wrappers (SuperLiteral, SuperClause) used
│                            for structural lemmas across different variable sets
├── Treelike.lean         -- TreeLikeResolution inductive type + soundness/completeness
├── ProofOperations.lean  -- Restrict and regularize operations on tree-like proofs
├── TinyConversions.lean  -- Bridge lemmas between SizeWidth and the rest of the code
├── Daglike.lean          -- DagLikeResolution (blackboard-based) + soundness/completeness
├── SizeWidth.lean        -- Size / width relationship for tree-like Resolution
└── main.tex              -- Accompanying write-up
```

### Key design decisions

- **Variables** are backed by `String` but wrapped in a `structure` so the underlying type can be swapped freely. Everything is parameterized by `vars : Variables` (a `Finset Variable`).
- **Literals, clauses, and CNF formulas carry their variable set as a type parameter.** This is essential for the completeness proofs but creates friction when moving between variable sets, which is why `Clause.convert`, `Clause.convert_trivial`, and `Clause.shrink` exist.
- **Tree-like Resolution** (`TreeLikeResolution`) is an inductive type with two constructors, `axiom_clause` and `resolve`. Weakening is admitted internally by the resolution rule.
- **DAG-like Resolution** uses a `Blackboard` (a `CNFFormula`) to model shared reuse of clauses. `DagLikeResolutionStep` builds up the blackboard and `DagLikeResolution` witnesses that $\bot$ appears in it.
- **`TreeLikeResolution.unsubstitute`** is `noncomputable`; recovering the pre-image clause in the axiom case relies on `Classical.choose`.
- **`SuperCNF`** provides `SuperLiteral` / `SuperClause` without a variable-set parameter, which enables `Equivalence`-based tactics where the parameterized versions become awkward.
- The headline `width_imply_size` theorem is obtained from `width_imply_size_ind_version` via **double induction**; inside the induction, the main lemma is `width_combine`.

## Building

The project uses Lean `v4.26.0-rc2` with Mathlib `v4.26.0-rc2`. Mathlib caches are fetched automatically by `lake build`.

```bash
# Build the entire project
lake build

# Type-check a specific file
lake env lean BSWLean/CNF.lean

# Update dependencies
lake update
```

## Challenges encountered during formalization

### Definitions

The hardest part was picking the right definitions for basic types such as `Literal`. A suboptimal choice cascades: lemmas about literals then fail to be solved by `aesop` / `grind`, and the proof length grows significantly.

A representative dilemma is how to state literal equality. From the user's side the ergonomic lemma is

> two literals are equal iff their variables and polarities agree.

But the LHS is a conjunction, which makes automation tricky:

- The lemma has to be registered (either as `@[simp]` or `@[aesop safe]`).
- The conjunction must be split into two premises for simplifiers to apply it.
- The order of premises matters, and different use-cases prefer different orders.
- The direction of normalization cannot be reversed because literals are the natural normal form, but constructor-based variants are incompatible with that.

The final solution registers the lemma as an `ext`-lemma rather than a simp-lemma, at the cost of requiring manual `ext` invocations when automation stalls.

### Decorators

Picking the right decorator for a lemma is genuinely hard. The `@[aesop safe/unsafe]` rules in the documentation are misleading, and there is no good way to verify that a registered lemma will fire where expected. `@[grind]` is even more opaque. Mistakes typically surface only when a later `aesop` call hits a timeout or a stack limit, and debugging them requires separating library-level rewrite loops from context-size issues.

### Context handling

Bigger theorems — notably `unsat_implies_tree_like_refutation` and those in `SizeWidth.lean` — often tripped `whnf` / `simp` timeouts because the local context was enormous. The usual fixes were restructuring the proof or sprinkling `clear` tactics. A native way to locally restrict the context would have eliminated a lot of this friction: frequently only 3 of 20 hypotheses were needed to close a subgoal that automation could otherwise handle instantly.

### Standard library gaps

Some expected lemmas were missing. For example, we had to prove by induction that `filterMap` does not increase cardinality (the `filterMap_card` lemma in `Substitutions.lean`) — the standard library has the analogue for `filter` and `map` separately, but `filterMap` is not defined as their composition and has no off-the-shelf bound.

## Tactic patterns used throughout

- `aesop` does a lot of the heavy lifting; when the default search misses, augment it with `(add safe unfold Foo)` or `(add unsafe Bar)`.
- `grind` handles most arithmetic and membership goals; annotate definitions with `@[grind .]` or `@[grind =]` to expose them to it.
- Feeding `@[simp]`, `@[aesop safe]`, or `@[grind →]` to recurring lemmas is often the difference between a two-line proof and a twenty-line one.
