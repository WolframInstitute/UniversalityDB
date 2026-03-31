/-
  ElementaryCellularAutomaton.Defs

  Elementary cellular automata on periodic tapes.

  An ECA rule is a function from 3-bit neighborhoods to bits.
  Rules are identified by their Wolfram rule number (0..255).
  The configuration is a periodic tape of length n (Fin n → Fin 2).
-/

namespace ElementaryCellularAutomaton

def ruleTable (ruleNumber : Nat) (a b c : Fin 2) : Fin 2 :=
  let index := a.val * 4 + b.val * 2 + c.val
  ⟨(ruleNumber >>> index) % 2, Nat.mod_lt _ (by omega)⟩

def rule110 : Fin 2 → Fin 2 → Fin 2 → Fin 2 := ruleTable 110
def rule124 : Fin 2 → Fin 2 → Fin 2 → Fin 2 := ruleTable 124
def rule137 : Fin 2 → Fin 2 → Fin 2 → Fin 2 := ruleTable 137

def step (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2) (n : Nat) (tape : Fin n → Fin 2) :
    Fin n → Fin 2 :=
  fun i => rule
    (tape ⟨(i.val + n - 1) % n, Nat.mod_lt _ (by have := i.isLt; omega)⟩)
    (tape i)
    (tape ⟨(i.val + 1) % n, Nat.mod_lt _ (by have := i.isLt; omega)⟩)

def iterate (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2) (n : Nat) (tape : Fin n → Fin 2) :
    Nat → (Fin n → Fin 2)
  | 0 => tape
  | k + 1 => step rule n (iterate rule n tape k)

end ElementaryCellularAutomaton
