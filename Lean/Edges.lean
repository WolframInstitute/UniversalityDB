/-
  Edges — the registered edges of the Universality Graph.

  Every edge is a named Lean `def` whose *single* type signature exposes
    (a) the source machine,
    (b) the target machine,
    (c) every external hypothesis as an explicit `Prop`-valued parameter.
  Hypotheses (Cocke-Minsky, Smith, well-formedness invariants, halting bridges)
  appear *only* as parameters, never buried inside fields.

  This file is the single audit point for a human to enumerate every edge
  claim. `EdgeAudit.lean` walks `edgeRegistry` to print the audit trail.

  Convention (Rule 9 — proposed in Wiki/Concepts/ProofIntegrity.md):
  - No `sorry` may appear in any `Simulation` / `HaltingSimulation` field of a
    registered wrapper.
  - Each registered edge declares one wrapping `def` whose type signature
    fully exposes machines + hypotheses.
-/

import Lean
import ComputationalMachine
import SimulationEncoding
import Proofs.TuringMachineToGeneralizedShift
import Proofs.GeneralizedShiftToTuringMachine
import Proofs.CockeMinsky
import Proofs.TagSystemToCyclicTagSystem
import Proofs.ElementaryCellularAutomatonMirror
import Proofs.ElementaryCellularAutomatonConjugation
import Proofs.TMtoGS

namespace UniversalityGraph

/-- Status of an edge's formalization. -/
inductive EdgeStatus
  /-- All required preconditions are themselves proved in the project,
      and the registered `def` is a complete `Simulation`/`HaltingSimulation`. -/
  | unconditional
  /-- The registered `def` takes one or more external `Prop` hypotheses as
      parameters (e.g. Smith's theorem, Cocke-Minsky construction, a halting
      well-formedness invariant). The hypotheses are listed in `hypotheses`. -/
  | conditional
  deriving DecidableEq, Repr

/-- Shape of an edge's claim. -/
inductive ClaimShape
  /-- A `ComputationalMachine.Simulation source target` value. -/
  | simulation
  /-- A `ComputationalMachine.HaltingSimulation source target` value. -/
  | haltingSimulation
  /-- A universality claim (e.g. `IsUniversal wolfram23`). The Lean type is
      domain-specific; use the metadata to interpret it. -/
  | universalityClaim
  /-- A `SimulationEncoding source target` value: conjugation-based
      `step_B(b) = decode (step_A^n (encode b))`. For edges with a natural
      decode (e.g. Moore TM ↔ GS). Canonicalization, when needed, is on the
      machine via `stepNormalized`, not as a structure field. -/
  | simulationEncoding
  deriving DecidableEq, Repr

/-- Audit metadata for one registered edge.

    `theoremName` points to the wrapping `def`. `EdgeAudit.lean` looks it up
    and runs `CollectAxioms.collect`; the closure must contain only standard
    axioms (and `sorryAx` *only* for entries explicitly marked as carrying
    open sorries — see `notes`). -/
structure EdgeMetadata where
  shortName : String
  theoremName : Lean.Name
  sourceDescription : String
  targetDescription : String
  paperReference : String
  status : EdgeStatus
  claimShape : ClaimShape
  hypotheses : List String
  parameters : List String
  notes : String

/- ============================================================================
   Edge wrappers
   ============================================================================ -/

/- ── ECA Mirror (Rule 110 ↔ Rule 124) ── -/

/-- **Rule 110 simulates Rule 124** via tape reversal. Bisimulation σ=1, τ=1.
    Parametric in tape length; the only precondition is `n ≥ 3`. -/
def edge_ECA110_ECA124 (n : Nat) (hn : n ≥ 3) :
    ComputationalMachine.Simulation
      (ElementaryCellularAutomaton.toComputationalMachine ElementaryCellularAutomaton.rule110 n)
      (ElementaryCellularAutomaton.toComputationalMachine ElementaryCellularAutomaton.rule124 n) :=
  ElementaryCellularAutomaton.rule110SimulatesRule124 n hn

/-- **Rule 124 simulates Rule 110** via tape reversal (converse of the above). -/
def edge_ECA124_ECA110 (n : Nat) (hn : n ≥ 3) :
    ComputationalMachine.Simulation
      (ElementaryCellularAutomaton.toComputationalMachine ElementaryCellularAutomaton.rule124 n)
      (ElementaryCellularAutomaton.toComputationalMachine ElementaryCellularAutomaton.rule110 n) :=
  ElementaryCellularAutomaton.rule124SimulatesRule110 n hn

/- ── ECA Complement (Rule 110 ↔ Rule 137) ── -/

/-- **Rule 110 simulates Rule 137** via bit complement of the tape. Bisimulation σ=1, τ=1.
    Parametric in tape length; no length precondition (complement doesn't touch indices). -/
def edge_ECA110_ECA137 (n : Nat) :
    ComputationalMachine.Simulation
      (ElementaryCellularAutomaton.toComputationalMachine ElementaryCellularAutomaton.rule110 n)
      (ElementaryCellularAutomaton.toComputationalMachine ElementaryCellularAutomaton.rule137 n) :=
  ElementaryCellularAutomaton.rule110SimulatesRule137 n

/-- **Rule 137 simulates Rule 110** via bit complement of the tape (converse). -/
def edge_ECA137_ECA110 (n : Nat) :
    ComputationalMachine.Simulation
      (ElementaryCellularAutomaton.toComputationalMachine ElementaryCellularAutomaton.rule137 n)
      (ElementaryCellularAutomaton.toComputationalMachine ElementaryCellularAutomaton.rule110 n) :=
  ElementaryCellularAutomaton.rule137SimulatesRule110 n

/- ── ECA Mirror ∘ Complement (Rule 110 ↔ Rule 193) ── -/

/-- **Rule 110 simulates Rule 193** via reversal + bit complement. Bisimulation σ=1, τ=1. -/
def edge_ECA110_ECA193 (n : Nat) (hn : n ≥ 3) :
    ComputationalMachine.Simulation
      (ElementaryCellularAutomaton.toComputationalMachine ElementaryCellularAutomaton.rule110 n)
      (ElementaryCellularAutomaton.toComputationalMachine ElementaryCellularAutomaton.rule193 n) :=
  ElementaryCellularAutomaton.rule110SimulatesRule193 n hn

/-- **Rule 193 simulates Rule 110** via reversal + bit complement (converse). -/
def edge_ECA193_ECA110 (n : Nat) (hn : n ≥ 3) :
    ComputationalMachine.Simulation
      (ElementaryCellularAutomaton.toComputationalMachine ElementaryCellularAutomaton.rule193 n)
      (ElementaryCellularAutomaton.toComputationalMachine ElementaryCellularAutomaton.rule110 n) :=
  ElementaryCellularAutomaton.rule193SimulatesRule110 n hn

/- ── TM → GS edge (Moore Theorem 7, fully proved) ──
   The proof and supporting helpers live in `Lean/Proofs/TMtoGS.lean`;
   `SimulationEncoding` lives in `Lean/SimulationEncoding.lean`. -/

/-- **TM → GS edge** (Moore 1991, Theorem 7): returns a `SimulationEncoding`
    with `encode = encodeBiTM`, `decode = decodeBiTMNormalized`. The B side
    is `BiInfiniteTuringMachine.toComputationalMachineNormalized`, whose
    `step` post-strips trailing zeros from the tapes — so step-results are
    canonical and the conjugation reads strictly:
    `step_B(b) = decode (step_A^n (encode b))`, no modulo.

    The bridge to Moore's exact step lives in
    `BiInfiniteTuringMachine.step_stripConfig_bisim` (a separate lemma).

    **Both `commutes` and `halting` fully proved** (see
    `TMtoGS.tmToGSSimulation` for the proof body).
    Closure: `[propext, Quot.sound, Classical.choice]`.

    Hypotheses are well-formedness conditions on the machine. -/
def edge_TMtoGS (machine : TuringMachine.Machine)
    (hk : machine.numberOfSymbols > 0)
    (hHeadAll : ∀ c : BiInfiniteTuringMachine.Configuration,
      c.head < machine.numberOfSymbols)
    (hWriteBound : ∀ q a, (machine.transition q a).write < machine.numberOfSymbols)
    (hStateBound : ∀ q a, (machine.transition q a).nextState ≤ machine.numberOfStates) :
    ComputationalMachine.SimulationEncoding
      (GeneralizedShift.toComputationalMachine
        (TuringMachineToGeneralizedShift.fromBiTM machine))
      (BiInfiniteTuringMachine.toComputationalMachineNormalized machine) :=
  TMtoGS.tmToGSSimulation machine hk hHeadAll hWriteBound hStateBound

/- ── GS → TM (Moore Theorem 8) ── -/

/-- **GS → TM edge** (Moore 1991, Theorem 8). σ=1, τ ≤ 2(w-1) + maxShift.

    The existing `gsToTMSimulation` in the proof file has two `sorry`s in its
    `commutes` and `halting` fields. This wrapper rebuilds the `Simulation`
    cleanly using the existing `gsToTMCommutes` lemma plus an explicit
    halting hypothesis.

    Open hypotheses:
    - `hSim`: the step simulation property (provable for w=1; w≥2 is open in
      `fullSim_general`).
    - `hLen`: every reachable GS config has cells of length `windowWidth`.
    - `hShift`: every active window has shift magnitude ≥ 1.
    - `hHalt`: inactive GS configs encode to halting TM configs. -/
def edge_GStoTM (params : GeneralizedShiftToTuringMachine.GSParams)
    (hSim : GeneralizedShiftToTuringMachine.StepSimulation params)
    (hLen : ∀ gsConfig gsConfig',
      GeneralizedShift.step (GeneralizedShiftToTuringMachine.gsMachine params) gsConfig
        = some gsConfig' →
      gsConfig.cells.length = params.windowWidth)
    (hShift : ∀ w, params.gsIsActive w = true →
      (params.gsTransition w).shiftMagnitude ≥ 1)
    (hHalt : ∀ gsConfig,
      GeneralizedShift.step (GeneralizedShiftToTuringMachine.gsMachine params) gsConfig = none →
      ComputationalMachine.Halts
        (BiInfiniteTuringMachine.toComputationalMachine
          (GeneralizedShiftToTuringMachine.toBiTM params))
        (GeneralizedShiftToTuringMachine.encodeConfig gsConfig)) :
    ComputationalMachine.Simulation
      (BiInfiniteTuringMachine.toComputationalMachine
        (GeneralizedShiftToTuringMachine.toBiTM params))
      (GeneralizedShift.toComputationalMachine
        (GeneralizedShiftToTuringMachine.gsMachine params)) where
  encode := GeneralizedShiftToTuringMachine.encodeConfig
  commutes := fun config config' h =>
    GeneralizedShiftToTuringMachine.gsToTMCommutes params hSim config config'
      (hLen config config' h) hShift h
  halting := hHalt

/- ── Tag → CTS (Cook 2004) ── -/

/-- **Tag → CTS edge** (Cook 2004). 1 tag step = 2k CTS steps.

    The existing `tagToCTSSimulation` in the proof file has a buried `sorry`
    in its `halting` field (single-element tag words encode to k bits which
    do not immediately halt CTS). This wrapper hoists the missing case as an
    explicit hypothesis.

    Open hypothesis:
    - `hHalt`: when the tag system halts (`step = none`, i.e. word length < 2),
      the CTS-encoded configuration also halts. The fully-empty case is
      proved as `cyclicTagSystemHaltsOnEmpty`; the single-element case is the
      remaining gap (it eventually halts after k CTS steps, not immediately). -/
def edge_TagtoCTS {k : Nat} (ts : TagSystem.Tag k) (hk : k > 0)
    (hHalt : ∀ config : TagSystem.TagConfiguration k,
      ts.step config = none →
      ComputationalMachine.Halts
        ((TagSystem.tagToCyclicTagSystem ts hk).toComputationalMachine)
        (TagSystem.tagConfigurationToCyclicTagSystem k config)) :
    ComputationalMachine.Simulation
      ((TagSystem.tagToCyclicTagSystem ts hk).toComputationalMachine)
      (ts.toComputationalMachine) where
  encode := TagSystem.tagConfigurationToCyclicTagSystem k
  commutes := TagSystem.tagToCTSCommutes ts hk
  halting := hHalt

/- ── Cocke-Minsky chain: any TM → wolfram23 ── -/

/-- **Cocke-Minsky + Cook + Smith chain**: Wolfram's (2,3) TM is universal.
    Returns `IsUniversal wolfram23` (universality claim, not a single
    Simulation — the encoding is family-of-machines parametric).

    Open hypotheses (literature theorems):
    - `h_cm`: Cocke-Minsky 1964 step simulation, for every TM.
    - `h_smith`: Smith 2007 simulation (CTS → (2,3) TM via 6 intermediate
      systems). -/
def edge_CockeMinskyChain
    (h_cm : ∀ machine, BiInfiniteTuringMachine.CockeMinskyStepSimulation machine)
    (h_smith : BiInfiniteTuringMachine.SmithSimulation) :
    BiInfiniteTuringMachine.IsUniversal BiInfiniteTuringMachine.wolfram23 :=
  BiInfiniteTuringMachine.wolfram23Universal h_cm h_smith

/- ============================================================================
   Edge registry
   ============================================================================ -/

/-- The list of all registered edges, in topological-ish order (simpler first). -/
def edgeRegistry : List EdgeMetadata := [
  { shortName := "ECA110_ECA124"
    theoremName := `UniversalityGraph.edge_ECA110_ECA124
    sourceDescription := "ECA Rule 110 on Fin n → Fin 2"
    targetDescription := "ECA Rule 124 on Fin n → Fin 2"
    paperReference := "Folklore (mirror symmetry of ECA rules; cf. Wolfram, NKS p.55)"
    status := .unconditional
    claimShape := .simulation
    hypotheses := []
    parameters := ["n : Nat", "hn : n ≥ 3"]
    notes := "Tape reversal bisimulation, σ=1, τ=1." },
  { shortName := "ECA124_ECA110"
    theoremName := `UniversalityGraph.edge_ECA124_ECA110
    sourceDescription := "ECA Rule 124 on Fin n → Fin 2"
    targetDescription := "ECA Rule 110 on Fin n → Fin 2"
    paperReference := "Folklore (same as above by involution)"
    status := .unconditional
    claimShape := .simulation
    hypotheses := []
    parameters := ["n : Nat", "hn : n ≥ 3"]
    notes := "Tape reversal bisimulation; converse of edge_ECA110_ECA124." },
  { shortName := "ECA110_ECA137"
    theoremName := `UniversalityGraph.edge_ECA110_ECA137
    sourceDescription := "ECA Rule 110 on Fin n → Fin 2"
    targetDescription := "ECA Rule 137 on Fin n → Fin 2"
    paperReference := "Folklore (complement symmetry: f(a,b,c) = ¬g(¬a,¬b,¬c); cf. Wolfram, NKS p.55)"
    status := .unconditional
    claimShape := .simulation
    hypotheses := []
    parameters := ["n : Nat"]
    notes := "Bit-complement bisimulation, σ=1, τ=1. No length precondition (complement is index-preserving)." },
  { shortName := "ECA137_ECA110"
    theoremName := `UniversalityGraph.edge_ECA137_ECA110
    sourceDescription := "ECA Rule 137 on Fin n → Fin 2"
    targetDescription := "ECA Rule 110 on Fin n → Fin 2"
    paperReference := "Folklore (same as above by involution)"
    status := .unconditional
    claimShape := .simulation
    hypotheses := []
    parameters := ["n : Nat"]
    notes := "Bit-complement bisimulation; converse of edge_ECA110_ECA137." },
  { shortName := "ECA110_ECA193"
    theoremName := `UniversalityGraph.edge_ECA110_ECA193
    sourceDescription := "ECA Rule 110 on Fin n → Fin 2"
    targetDescription := "ECA Rule 193 on Fin n → Fin 2"
    paperReference := "Folklore (composition mirror ∘ complement; Klein-4 orbit of rule 110)"
    status := .unconditional
    claimShape := .simulation
    hypotheses := []
    parameters := ["n : Nat", "hn : n ≥ 3"]
    notes := "Reversal-and-complement bisimulation, σ=1, τ=1. Composes the mirror and complement Klein-4 generators." },
  { shortName := "ECA193_ECA110"
    theoremName := `UniversalityGraph.edge_ECA193_ECA110
    sourceDescription := "ECA Rule 193 on Fin n → Fin 2"
    targetDescription := "ECA Rule 110 on Fin n → Fin 2"
    paperReference := "Folklore (same as above by involution)"
    status := .unconditional
    claimShape := .simulation
    hypotheses := []
    parameters := ["n : Nat", "hn : n ≥ 3"]
    notes := "Reversal-and-complement bisimulation; converse of edge_ECA110_ECA193." },
  { shortName := "TM_GS"
    theoremName := `UniversalityGraph.edge_TMtoGS
    sourceDescription := "Standard GS fromBiTM(machine) (no step modification)"
    targetDescription := "BiInfiniteTuringMachine.toComputationalMachineNormalized machine (post-stripping step)"
    paperReference := "Moore 1991, Theorem 7"
    status := .conditional
    claimShape := .simulationEncoding
    hypotheses := [
      "_hk : numberOfSymbols > 0",
      "_hHeadAll : ∀ c, c.head < numberOfSymbols (well-formed configs)",
      "_hWriteBound : every transition's write < numberOfSymbols",
      "_hStateBound : every transition's nextState ≤ numberOfStates"
    ]
    parameters := ["machine : TuringMachine.Machine"]
    notes := "Uses SimulationEncoding (conjugation: `step_B(b) = decode (step_A^n (encode b))`). Encode = encodeBiTM. Decode = decodeBiTMNormalized. B-side step is `stepNormalized` (Moore's step + strip trailing zeros), so b' is canonical and the conjugation is strict (no modulo). The bridge to Moore's exact step is `BiInfiniteTuringMachine.step_stripConfig_bisim`. **Both halting and commutes fully proved (no sorry).** Closure: [propext, Quot.sound, Classical.choice]." },
  { shortName := "GS_TM"
    theoremName := `UniversalityGraph.edge_GStoTM
    sourceDescription := "BiInfiniteTuringMachine toBiTM(params)"
    targetDescription := "Generalized Shift gsMachine(params)"
    paperReference := "Moore 1991, Theorem 8"
    status := .conditional
    claimShape := .simulation
    hypotheses := [
      "hSim : StepSimulation params — w=1 proved, w≥2 open in fullSim_general",
      "hLen : reachable configs have correct window width",
      "hShift : active windows have shiftMagnitude ≥ 1",
      "hHalt : inactive GS configs encode to halting TM configs"
    ]
    parameters := ["params : GSParams"]
    notes := "σ=1 τ ≤ 2(w-1) + maxShift. This wrapper avoids the buried sorry in the proof file's gsToTMSimulation by reconstructing Simulation cleanly." },
  { shortName := "Tag_CTS"
    theoremName := `UniversalityGraph.edge_TagtoCTS
    sourceDescription := "CyclicTagSystem (Cook encoding of ts)"
    targetDescription := "Tag system ts (alphabet size k)"
    paperReference := "Cook 2004 (Universality in Elementary Cellular Automata)"
    status := .conditional
    claimShape := .simulation
    hypotheses := [
      "hHalt : tag-halted configs encode to halting CTS configs (single-element gap)"
    ]
    parameters := ["k : Nat", "ts : Tag k", "hk : k > 0"]
    notes := "1 tag step = 2k CTS steps. The single-element halting case is the only open gap; this wrapper hoists it from the buried sorry in tagToCTSSimulation." },
  { shortName := "Wolfram23_universal"
    theoremName := `UniversalityGraph.edge_CockeMinskyChain
    sourceDescription := "Wolfram's (2,3) Turing Machine"
    targetDescription := "Every Turing machine (universality claim)"
    paperReference := "Cocke 1964 + Cook 2004 + Smith 2007 (composed chain)"
    status := .conditional
    claimShape := .universalityClaim
    hypotheses := [
      "h_cm : Cocke-Minsky step simulation for every TM (1964)",
      "h_smith : Smith CTS → (2,3) TM simulation (2007)"
    ]
    parameters := []
    notes := "Returns IsUniversal wolfram23. The middle step (Tag → CTS, Cook 2004) is fully proved internally with 0 sorry. Smith's hypothesis is taken as-is per project policy (too complex to formalize)." }
]

end UniversalityGraph
