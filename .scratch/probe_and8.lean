import Clean.Circuit
import Clean.Gadgets.Xor.ByteXorTable
import Clean.Utils.Primes

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace ProbeAnd8
open Xor (ByteXorTable)
open FieldUtils

structure Inputs (F : Type) where
  x: F
  y: F
deriving ProvableStruct

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.val < 256 ∧ y.val < 256

def Spec (input : Inputs (F p)) (z : F p) :=
  let ⟨x, y⟩ := input
  z.val = x.val &&& y.val

def main (input : Var Inputs (F p)) : Circuit (F p) (fieldVar (F p)) := do
  let ⟨x, y⟩ := input
  let and ← witness fun eval => (eval x).val &&& (eval y).val
  let xor := x + y - 2*and
  lookup ByteXorTable (x, y, xor)
  return and

instance elaborated : ElaboratedCircuit (F p) Inputs field where
  main
  localLength _ := 1
  output _ i := var ⟨i⟩

theorem soundness_probe : Soundness (F p) elaborated Assumptions Spec := by
  intro i env ⟨ x_var, y_var ⟩ ⟨ x, y ⟩ h_input h_assumptions h_xor
  simp_all only [circuit_norm, main, Assumptions, Spec, ByteXorTable, Inputs.mk.injEq]
  -- What is h_input now?
  trace "{h_input}"
  -- What is h_xor now?
  trace "{h_xor}"
  -- What is h_assumptions now?
  trace "{h_assumptions}"
  -- What is the goal?
  sorry

end ProbeAnd8
