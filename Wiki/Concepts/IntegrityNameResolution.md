# Integrity Name Resolution

`Lean/Integrity.lean` checks the axiom closure of a hand-maintained list of theorem/declaration names. Until 2026-08-08 the check **failed open**: a name that did not resolve to any theorem produced an empty axiom set, which is printed and treated exactly like a clean trace. The list is now resolved before it is traced, so an unresolvable name is itself a violation, and `private` theorems are resolved through their mangled names instead of silently going unchecked.

## The hole

[Integrity.lean](../../Lean/Integrity.lean) calls `CollectAxioms.collect` on each name in `keyTheorems` and `spotCheckTheorems`. In Lean 4.29 (`Lean/Util/CollectAxioms.lean`) that function dispatches on the constant's `ConstantInfo`:

```lean
match env.checked.get.find? c with
| some (ConstantInfo.axiomInfo v)  => modify fun s => { s with axioms := s.axioms.push c }; collectExpr v.type
| some (ConstantInfo.defnInfo v)   => collectExpr v.type *> collectExpr v.value
| some (ConstantInfo.thmInfo v)    => collectExpr v.type *> collectExpr v.value
...
| none                             => pure ()   -- ← unknown name: no axioms, no error
```

The final branch is the problem. A name that is not in the environment yields `#[]`, and `#[]` is precisely what a proof with no axiom dependencies looks like. So the check reported

```
TRACE SomeNamespace.someTheorem: []
INTEGRITY CHECK: PASS
```

for a theorem that does not exist. Any typo, rename, or deletion turned that list entry into a no-op — and the entry that looked *best* in the log (empty closure) was the one being checked least.

Note `defnInfo` and `thmInfo` are handled identically: both traverse type and value. `def` vs `theorem` has no effect on axiom tracking, which is why the lists legitimately contain `def`s — an assembled `Simulation` carries an `encode` field, so it lives in `Type` and cannot be a `theorem`. The old name `keyTheorems` was a misnomer; 11 of its 22 entries are `def`s.

## What was actually slipping through

The new check fired on the first build:

```
INTEGRITY VIOLATION: 'GeneralizedShiftToTuringMachine.fullSim_general_cView' is not a
declaration in the environment (misspelled, renamed, or removed). Its axiom trace would
be vacuously empty.
```

`fullSim_general_cView` is declared `private` ([GeneralizedShiftToTuringMachine.lean:1323](../../Lean/Proofs/GeneralizedShiftToTuringMachine.lean#L1323)). Lean stores private theorems under a mangled name, so the plain name never resolved:

| name | in environment | axiom closure |
|---|---|---|
| `GeneralizedShiftToTuringMachine.fullSim_general_cView` | no | `[]` (vacuous) |
| `_private.Proofs.GeneralizedShiftToTuringMachine.0.GeneralizedShiftToTuringMachine.fullSim_general_cView` | yes | `[propext, Quot.sound, Classical.choice]` |

The theorem itself is fine — its real closure is clean, as [Edges.lean](../../Lean/Edges.lean) already claimed. But the Moore Theorem 8 chain lemma had **never actually been checked**; only its sibling `gsToTMSimulationEncoding` was.

## The fix

Two changes to [Integrity.lean](../../Lean/Integrity.lean):

1. **`resolveDecl`** — resolves a listed name to the constant that exists. Plain lookup first; if that fails, scan for private theorems whose `privateToUserName?` matches. Returns *all* matches so ambiguity is reported rather than silently resolved.
2. **A resolution pass before any trace.** Every name in both lists is resolved up front. Zero matches → `INTEGRITY VIOLATION` (build fails). More than one match → `INTEGRITY VIOLATION` (ambiguous). Exactly one → traced, with `RESOLVED <written> -> <mangled> (private)` logged when the two differ.

## Example: passes before, fails after

Add one typo'd name to the key list — `rule110SimulatesRule125`, a rule that does not exist (the Rule 110 Klein orbit is {110, 124, 137, 193}):

```lean
private def keyTheorems : List Name := [
  ...
  `ElementaryCellularAutomaton.rule110SimulatesRule125,   -- typo: no such theorem
  `ElementaryCellularAutomaton.rule110SimulatesRule124,
  ...
]
```

Before — `lake build` succeeds, and the log even shows the cleanest possible closure:

```
info: Integrity.lean:91:0: TRACE ElementaryCellularAutomaton.rule110SimulatesRule125: []
info: Integrity.lean:91:0: INTEGRITY CHECK: PASS
Build completed successfully.
```

After — the build fails:

```
error: Integrity.lean:114:0: INTEGRITY VIOLATION:
  'ElementaryCellularAutomaton.rule110SimulatesRule125' is not a declaration in the
  environment (misspelled, renamed, or removed). Its axiom trace would be vacuously empty.
error: build failed
```

The same failure now covers the realistic version of this: renaming or deleting a proof without updating `Integrity.lean`, which previously downgraded the entry to a silent no-op.

## Scope of the guarantee

This closes a *fail-open* gap in the axiom check; it does not widen what is checked. A theorem that is simply absent from `keyTheorems` is still unchecked (it is compiled and kernel-replayed by `leanchecker`, but its axiom closure is not explicitly traced). Keeping that list complete remains a manual obligation — see the maintenance note in [CLAUDE.md](../../CLAUDE.md).

## Verification

`Scripts/verify_integrity.sh` after the change: import sync PASS, `INTEGRITY CHECK: PASS` with 22 traces (including the newly-real `fullSim_general_cView` trace), sorry: 1 (tracked, `Proofs/CockeMinsky.lean:397`), kernel replay PASS.

## See also

- [ProofIntegrity](ProofIntegrity.md) — the full trust model these checks implement
- [Status](../Status.md) — current proved/sorry inventory
