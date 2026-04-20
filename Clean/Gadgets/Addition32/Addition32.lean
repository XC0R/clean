import Clean.Gadgets.Addition32.Addition32Full
import Clean.Types.U32
import Clean.Gadgets.Addition32.Theorems
import Clean.Utils.Primes

namespace Gadgets.Addition32
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod256 floorDiv256)

structure Inputs (F : Type) where
  x: U32 F
  y: U32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var U32 (F p)) := do
  let ⟨x, y⟩ := input
  let ⟨z, _⟩ ← Addition32Full.circuit {x, y, carryIn := 0}
  return z

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def Spec (input : Inputs (F p)) (z : U32 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = (x.value + y.value) % 2^32 ∧ z.Normalized

-- def c := main (p:=p_babybear) default
-- #eval c.localLength
-- #eval c.output
instance elaborated : ElaboratedCircuit (F p) Inputs U32 where
  main := main
  localLength _ := 8
  output _ i0 := ⟨var ⟨i0⟩, var ⟨i0 + 2⟩, var ⟨i0 + 4⟩, var ⟨i0 + 6⟩ ⟩

set_option maxHeartbeats 800000 in
theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i₀ env input_var input h_input h_assumptions h_holds
  subst h_input
  rw [show ElaboratedCircuit.output input_var i₀ = (main input_var i₀).1 from rfl]
  delta elaborated at h_holds
  delta main at h_holds ⊢
  simp only [circuit_norm, Addition32Full.circuit] at h_holds ⊢
  change Addition32Full.Assumptions (Addition32Full.Inputs.mk (eval env input_var.x) (eval env input_var.y) 0) →
    Addition32Full.Spec (Addition32Full.Inputs.mk (eval env input_var.x) (eval env input_var.y) 0)
      (Addition32Full.Outputs.mk
        (eval env (Addition32Full.main { x := input_var.x, y := input_var.y, carryIn := 0 } i₀).1.z)
        (Expression.eval env (Addition32Full.main { x := input_var.x, y := input_var.y, carryIn := 0 } i₀).1.carryOut))
    at h_holds
  simp_all [Addition32Full.Assumptions, Addition32Full.Spec, Assumptions, Spec,
    circuit_norm, explicit_provable_type, toVars, fromElements, U32.Normalized, IsBool]

set_option maxHeartbeats 800000 in
theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro i₀ env input_var h_env input h_input h_assumptions
  subst h_input
  delta elaborated at h_env ⊢
  delta main at h_env ⊢
  simp only [circuit_norm, Addition32Full.circuit] at h_env ⊢
  change Addition32Full.Assumptions (Addition32Full.Inputs.mk (eval env input_var.x) (eval env input_var.y) 0)
  simp_all [Addition32Full.Assumptions, Assumptions,
    circuit_norm, explicit_provable_type, toVars, fromElements, U32.Normalized, IsBool]

def circuit : FormalCircuit (F p) Inputs U32 where
  Assumptions
  Spec
  soundness
  completeness
end Gadgets.Addition32
