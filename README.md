# Lean formalization: non-left-properness of multipointed d-spaces

This project contains a Lean 4 formalization of the logical and elementary
topological core of counterexample to left properness of the
q-model structure of multipointed d-spaces https://doi.org/10.48550/arXiv.2608.13151.

## Scope

Mathlib v4.33.1 has an abstract category/model-category infrastructure,
topological paths, path components, and the intermediate value theorem.  It
does **not** define multipointed d-spaces, the reparametrization categories
`G` and `M`, their q-model structures, or the globular colimit theorem.
Consequently the file does not pretend that these objects already exist in
mathlib.  The paper-specific results are exposed as the fields of
`GlobularCounterexample`; no `axiom` and no `sorry` is used.

The Lean kernel then checks:

1. reflection of `Joined` is equivalent to injectivity on `pi_0`;
2. a continuous two-valued invariant separates two path components;
3. the pushout map in the counterexample cannot be a q-weak equivalence;
4. the existence of the displayed pushout disproves left properness;
5. the elementary formulae for the bump path and the varying subdivision
   used in the explicit homotopy.

The imported paper-specific fields correspond exactly to the following
mathematical statements.

| Lean field | Mathematical input |
| --- | --- |
| `pushout` | the cell-attachment square is a pushout |
| `s_is_weakEquivalence` | `E_1 -> E_{>0}` induces a q-weak equivalence |
| `i_is_cofibration` | the left map is a cobase change of `Glob_P(emptyset) -> Glob_P(D^0)` |
| `invariant_continuous` | continuity of the maximum invariant |
| `invariant_two_valued`, `invariant_c`, `invariant_cb` | the invariant separates `c` and `cb` before pushout |
| `joined_after_pushout` | the explicit family `F` joins their images after pushout |
| `weak_reflects_joined` | a q-weak equivalence induces an injection on `pi_0` of every execution-path space |

Thus a fully end-to-end formalization will require a future Lean library for
multipointed d-spaces and its globular colimits.  Once those definitions and
the cited paper lemmas are available, they instantiate this interface and the
final theorem is `GlobularCounterexample.not_leftProper`.

## Compilation

With Lean and Lake installed:

```text
lake update
lake build
```

The versions are pinned to Lean 4.33.1 and mathlib v4.33.1.
