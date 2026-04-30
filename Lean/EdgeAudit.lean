/-
  EdgeAudit — print the edge registry's audit trail at build time.

  This is a separate module from `Integrity.lean` (locked by Rule 8 of
  Wiki/Concepts/ProofIntegrity.md). Together with `Integrity.lean`, this
  gives the human auditor one place to read every registered edge:
  source/target machines, paper reference, external hypotheses, axiom
  closure of the wrapping `def`.

  For every entry in `UniversalityGraph.edgeRegistry`, we:
    1. Look up the named theorem in the environment.
    2. Run `CollectAxioms.collect` to enumerate its axiom dependencies.
    3. Cross-check the declared `status`/`hypotheses` against the closure.

  Integrity violations (e.g. an `unconditional` edge whose closure contains
  `sorryAx`) emit `logError` and fail the build.
-/

import Lean
import Edges

open Lean Elab Command UniversalityGraph

private def standardAxioms : List Name :=
  [`propext, `Quot.sound, `Classical.choice]

private def hasNativeComponent : Name → Bool
  | .anonymous => false
  | .str parent s => s == "_native" || hasNativeComponent parent
  | .num parent _ => hasNativeComponent parent

private def isTrackedAxiom (n : Name) : Bool :=
  n == `sorryAx || hasNativeComponent n

private def statusToString : EdgeStatus → String
  | .unconditional => "unconditional"
  | .conditional   => "conditional"

run_cmd do
  let env ← getEnv
  let mut violations := 0
  IO.println "── Universality Graph: edge registry audit ──"
  for entry in edgeRegistry do
    -- Look up the wrapping `def`
    if !env.contains entry.theoremName then
      logError m!"EDGE AUDIT: registered theorem '{entry.theoremName}' not found in environment"
      violations := violations + 1
      continue
    -- Axiom closure
    let (_, s) := (CollectAxioms.collect entry.theoremName).run env |>.run {}
    let unexpected := s.axioms.filter fun ax =>
      ax ∉ standardAxioms && !isTrackedAxiom ax
    let tracked := s.axioms.filter isTrackedAxiom
    -- Cross-check: unconditional edges should not depend on sorryAx
    if entry.status == .unconditional && tracked.any (· == `sorryAx) then
      logError m!"EDGE AUDIT: '{entry.shortName}' is registered as unconditional but its axiom closure contains sorryAx"
      violations := violations + 1
    if unexpected.size > 0 then
      logError m!"EDGE AUDIT: '{entry.shortName}' depends on unexpected axioms: {unexpected}"
      violations := violations + 1
    -- Print one summary line per edge
    let hypList := if entry.hypotheses.isEmpty then "(none)" else String.intercalate ", " entry.hypotheses
    let trackedStr := if tracked.isEmpty then "" else s!" tracked={tracked.toList}"
    logInfo m!"EDGE [{entry.shortName}] {statusToString entry.status} | {entry.sourceDescription} → {entry.targetDescription}\n  paper: {entry.paperReference}\n  parameters: {entry.parameters}\n  hypotheses: {hypList}\n  axioms: {s.axioms.toList}{trackedStr}\n  notes: {entry.notes}"
  if violations == 0 then
    IO.println s!"── EDGE AUDIT: PASS ({edgeRegistry.length} edges) ──"
  else
    logError m!"EDGE AUDIT: {violations} violation(s)"
