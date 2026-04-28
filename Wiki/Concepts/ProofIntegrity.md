# Proof Integrity

Trust model for LLM-generated Lean proofs in the UniversalityDB project.

## The problem

An LLM generating Lean proofs can produce results that type-check but are meaningless. The known escape hatches are:

1. **Custom axioms.** `axiom cheat : False` allows proving anything. More subtly, `axiom myProp : P` silently assumes P without marking the theorem as conditional.
2. **sorry / admit.** Lean's built-in proof holes. A proof containing either is incomplete, but the file still compiles.
3. **Weakened definitions.** If the theorem says `theorem foo : Simulation TM GS` but the LLM rewrote `Simulation` to require nothing, the proof is trivially true and formally meaningless.
4. **native_decide abuse.** `native_decide` compiles a decision procedure to native code and runs it outside the kernel. Unlike `decide` (which produces a kernel-verified proof certificate), `native_decide` trusts compiled code. There have been soundness bugs in `native_decide` in Lean's history.
5. **unsafe keyword.** `unsafe def` bypasses the type checker entirely.
6. **@[implemented_by] and @[extern] attributes.** Both replace a function's compiled implementation — `@[implemented_by]` with Lean code, `@[extern]` with C code via FFI. An LLM could write a correct-looking `def encode` but attach `@[implemented_by cheatImpl]` so that `native_decide` sees a different function than what appears in the source.
7. **Kernel-weakening options.** Certain `set_option` calls can change what the Lean kernel accepts.
8. **Free hypotheses.** A theorem with type `(h : SomeUnprovenProp) → Conclusion` is *conditionally* proved — not closed. The proof term needs `h` supplied by the caller. If `SomeUnprovenProp` is itself unproved, the conclusion only holds modulo that assumption. A theorem can satisfy 1-7 above (no axioms, no sorry, etc.) and still not actually prove its claimed conclusion in any unconditional sense.

## The solution

Lean's type checker is the arbiter of correctness. If the goal statement is sound and the proof term type-checks without escape hatches, the result is correct regardless of who or what produced it. The following rules close the escape hatches.

### Rule 1: Lock the goal

The theorem statement (type signature) is the human's responsibility. The LLM fills the proof body. A locked goal is a `sorry`-ed theorem whose type signature the LLM must fill without modification.

### Rule 2: Lock the dependencies

Definitions in the dependency graph of a locked theorem are also locked. If the LLM can change `Simulation` or `TuringMachine`, it can make the goal trivially true. Changes to locked definitions require explicit human approval.

### Rule 3: No custom axioms

No `axiom` declarations permitted. Unproved claims must be stated as hypothesis parameters in the theorem's type signature so the dependency is visible. This is the pattern used in `CockeMinsky.lean`:

```lean
def CockeMinskyStepSimulation (machine : Machine) : Prop :=
  ∀ (config config' : Configuration),
    step machine config = some config' →
    ∃ (n : Nat),
      tagExactSteps (cockeMinskyTag machine) (cockeMinskyConfigurationEncode machine config) n =
      some (cockeMinskyConfigurationEncode machine config')

theorem wolfram23Universal
    (h_cm : ∀ (machine : Machine), CockeMinskyStepSimulation machine)
    (h_smith : SmithSimulation) :
    IsUniversal wolfram23 := by
  ...
```

The hypothesis is a `def`, not an `axiom`. It appears in the theorem's type signature. The theorem is honest about what it assumes.

### Rule 3a: No unsafe

No `unsafe def` or `unsafe instance`. There is no legitimate use for `unsafe` in proof code.

### Rule 3b: No @[implemented_by] or @[extern]

No `@[implemented_by]` or `@[extern]` attributes. Both replace a function's compiled implementation — `@[implemented_by]` with Lean code, `@[extern]` with C code via FFI. Either can make `native_decide` see a different function than what appears in the source.

### Rule 4: No sorry or admit

Every remaining `sorry` tracked in `Wiki/Status.md` with file, line, theorem name, and reason.

### Rule 5: native_decide policy

- **`decide`** (preferred): produces a kernel-verified proof certificate. Slow but trustworthy.
- **`native_decide`** (permitted): compiles and runs native code. Fast but trusts the compiler and runtime.

`native_decide` permitted for finite exhaustive checks. Not permitted as the sole proof of a universally quantified claim over an unbounded type. Exception: a finite check combined with a structural argument that extends it universally.

### Rule 6: No kernel-weakening options

No `set_option` calls that affect kernel acceptance. Performance and display options permitted.

### Rule 7: No removing proved results

Deleting or weakening a proved theorem requires human approval.

### Rule 8: Verification infrastructure is locked

`Lean/Integrity.lean` and `Scripts/verify_integrity.sh` must not be modified without human approval. These enforce the rules above. The verification script fails if Integrity.lean output is absent from the build, preventing silent removal.

## Threat model

| Threat | Example | Prevention | Detection |
|---|---|---|---|
| Custom axiom | `axiom cheat : False` | Rule 3 | `CollectAxioms.collect` on key theorems catches it transitively |
| sorry left in proof | `sorry` buried in a helper lemma | Rule 4 | `lake build` compiler warnings (authoritative); `#print axioms` shows `sorryAx` |
| admit left in proof | `admit` | Rule 4 | `lake build` compiler warnings (admit = sorry in Lean 4) |
| unsafe definition | `unsafe def encode ...` | Rule 3a | Lean's kernel rejects any theorem that depends on an unsafe definition ("invalid declaration, it uses unsafe declaration") |
| implemented_by override | `@[implemented_by cheatImpl]` | Rule 3b | Only threatens correctness via `native_decide`, which `CollectAxioms` catches as `_native` axiom |
| extern FFI override | `@[extern "evil_c_func"]` | Rule 3b | Same: only matters via `native_decide`; `CollectAxioms` catches it |
| Weakened definition | Rewriting `Simulation` to require nothing | Rule 2 | Human review of definition diffs |
| Changed goal statement | Modifying theorem type signature | Rule 1 | Human review + diff |
| native_decide on fake finite type | Artificial `Fintype` instance | Rule 5 | Human review of `Decidable` instances |
| Kernel option abuse | `set_option` weakening kernel | Rule 6 | `set_option` affects elaboration, not kernel; `leanchecker` validates against kernel independently |
| Removed theorem | Deleting an existing result | Rule 7 | `git diff` review |
| Incorrect definition | `step` doesn't match the intended math | Cross-validation | Run same examples in Lean and Wolfram ([CrossValidation notebook](../Notebooks/CrossValidation.md)) |

## Foundational assumption

The entire trust model rests on one assumption: **Lean 4's kernel is correct.** The kernel is small (~5,000 lines of C++), based on well-studied type theory (CIC with quotient types).

Three levels of assurance for this assumption:

1. **`leanchecker`** (built into Lean 4.28+, run by our verification script) — replays all declarations through the kernel independently, providing a second check beyond normal compilation. This catches metaprogramming that might have smuggled declarations past the elaborator.

2. **[Lean4Lean](https://github.com/digama0/lean4lean)** — a complete independent typechecker for Lean 4, written in Lean itself. It can re-verify all of Lean's mathlib library. Because it is written in Lean, it is itself amenable to formal verification — enabling proofs about the correctness of the kernel's type theory.

3. **Formal metatheory** — the Lean4Lean project is actively formalizing the metatheory of Lean's type system (CIC with quotient types), with the goal of proving soundness of the kernel itself. This work is being presented at POPL 2026 (WITS workshop).

For this project, `leanchecker` (level 1) is sufficient and is run automatically. Lean4Lean (level 2) can be used for higher assurance on flagship results if needed.

`native_decide` and `@[implemented_by]` are outside the kernel. They inject results the kernel does not check. This is why Rules 3b and 5 exist.

## Cross-validation: Lean vs. Wolfram

The rules above guarantee proof correctness given correct definitions. But **are the definitions correct?** Does the Lean `GeneralizedShift.step` compute what Moore's generalized shift computes?

This is a specification question. It cannot be settled formally. But it can be tested: run the same machine on the same input in both Lean (`#eval`) and Wolfram (built-in steppers), compare results across many inputs.

| Lean definition | Wolfram counterpart |
|---|---|
| `BiInfiniteTuringMachine.step wolfram23` | `TuringMachine[{3, 3, rule}, init, t]` |
| `GeneralizedShift.step (fromBiTM wolfram23)` | `ResourceFunction["GeneralizedShift"][...]` |
| `Tag.step exampleTag2` | `ResourceFunction["TagSystem"][{2, prods}, init, t]` |
| `CyclicTagSystem.step exampleCTS` | `ResourceFunction["CyclicTagSystem"][appendants, init, t]` |
| `ElementaryCellularAutomaton.step rule110` | `CellularAutomaton[110, init, 1]` |

Agreement on many inputs provides empirical evidence that the definitions are correct. Disagreement on any input proves a bug.

## Verification procedure

Run `Scripts/verify_integrity.sh`. It uses Lean's own tools — no grep or string parsing.

**Step 1 — Build** (`lake build`):

`Integrity.lean` imports all project modules and automatically scans every theorem-kind constant in those modules. No curated list — every theorem is checked. For each theorem:

1. **Axiom check**: `CollectAxioms.collect` (Lean's API for tracing axiom dependencies) returns the transitive closure of axioms used. The only axioms permitted are:
   - `propext`, `Quot.sound`, `Classical.choice` — Lean's three standard axioms
   - `sorryAx` — sorry used (tracked, not a failure for now)
   - `*._native.*` — native_decide computational axioms

   Any other axiom triggers `logError`, which makes the build fail.

2. **Hypothesis check**: identifies all explicit Prop-typed parameters in the theorem's type signature (using `Lean.Meta.forallTelescope` and `Lean.Meta.isProp`). These are propositions the caller must supply proofs of — they are unproved assumptions.

The build output reports for the entire project: how many theorems are *absolutely proven* (zero Prop hypotheses — the conclusion holds unconditionally) versus *conditionally proven* (has Prop hypotheses — the conclusion holds modulo those hypotheses).

This operates on Lean's parsed AST via the `Environment` API — no source text parsing, no comment ambiguity, no curated list to maintain.

`lake build` also reports every `sorry` and `admit` as a compiler warning with exact file and line.

**Step 2 — Kernel replay** (`leanchecker`):

`leanchecker` (built into Lean 4.28+) replays all compiled declarations through Lean's kernel, catching anything that metaprogramming might have smuggled past the elaborator. This is the standard tool recommended by Lean's official documentation for proof validation.

**Why no grep for `@[implemented_by]`, `@[extern]`, `set_option`:**

These only threaten proof correctness when `native_decide` is used — and when it is, `CollectAxioms.collect` reports the resulting `_native` axiom in the theorem's dependency closure. Without `native_decide`, `@[implemented_by]` only affects compiled code performance, not proof validity (the kernel always verifies the logical definition). `set_option` affects elaboration, not the kernel — `leanchecker` replays against the kernel independently.

**CI integration:** The script exits non-zero on failure and requires no interactivity. It can be added to a GitHub Actions workflow as-is:

```yaml
- name: Verify proof integrity
  run: Scripts/verify_integrity.sh
```

**Human review** (not automatable):
1. Goal statements are mathematically sound.
2. Locked definitions have not been weakened.
3. `native_decide` usage is appropriate.
4. Custom `Decidable` instances (if any) are correct.
5. Explicit hypotheses are correct formalisations of the cited results.

## Troubleshooting

When `Scripts/verify_integrity.sh` fails, the output tells you which check failed. Here's what each failure means and how to resolve it.

**`INTEGRITY VIOLATION: '...' depends on unexpected axioms: [...]`**
`CollectAxioms.collect` found an axiom in a theorem's dependency closure that isn't `propext`, `Quot.sound`, `Classical.choice`, `sorryAx`, or a `_native` axiom. This means a custom axiom is being used transitively. The output shows which axiom and which theorem. Find and remove the axiom declaration, or convert it to a hypothesis parameter in the theorem type signature.

**`INTEGRITY CHECK: PASS` not found / `FAIL: Integrity.lean output not found`**
`Integrity.lean` didn't compile or wasn't included in the build. Check in order: (1) `Integrity` is listed in `Lean/lakefile.lean` roots, (2) `Lean/Integrity.lean` is unmodified (Rule 8), (3) stale build cache — run `cd Lean && lake clean` then re-run the script.

**`FAIL: lake build exited with code N`**
The Lean build itself failed. This could be an integrity violation (`Integrity.lean` emits `logError` which makes the build fail) or a normal build error (syntax error, type error). Read the build output above this line to determine the cause.

**`FAIL: leanchecker rejected declarations`**
`leanchecker` found a declaration that the kernel does not accept. This typically indicates metaprogramming that manipulated the environment to inject a declaration that bypasses kernel checking. Investigate the reported declaration.

**sorry warnings**
Sorry warnings are reported but do not cause failure. The script prints the count and asks you to verify it matches the inventory in `Wiki/Status.md`. If the count differs, either the inventory is stale or an untracked sorry was introduced.

## Informal proof extraction

Given a verified Lean proof, an LLM can produce an informal proof readable by mathematicians. Each step should follow from the previous one by a stated reason, the argument should be self-contained, and any explicit hypotheses should be flagged as assumptions. The informal proof explains why the proof works; the formal proof guarantees that it does.

## See also

- [SimulationEncoding](SimulationEncoding.md) — the core Lean abstraction being verified
- [Overhead](Overhead.md) — spatial and temporal cost formalization
- [ComputationalMachine](ComputationalMachine.md) — the vertex type
