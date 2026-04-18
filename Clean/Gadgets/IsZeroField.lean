import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics

namespace Gadgets.IsZeroField

variable {F : Type} [Field F] [DecidableEq F]

/--
Main circuit that checks if a field element is zero.
Returns 1 if the input is 0, otherwise returns 0.
-/
def main (x : Var field F) : Circuit F (Var field F) := do
  -- When x ≠ 0, we need x_inv such that x * x_inv = 1
  -- When x = 0, x_inv can be anything (we use 0)
  let xInv ← witness fun env =>
    if x.eval env = 0 then 0 else (x.eval env : F)⁻¹

  let isZero <== 1 - x*xInv -- If x is zero, isZero is one
  isZero * x === 0  -- If x is not zero, isZero is zero

  return isZero

instance elaborated : ElaboratedCircuit F field field where
  main
  localLength _ := 2  -- 2 witnesses: isZero and x_inv

def Assumptions (_ : F) : Prop := True

def Spec (x : F) (output : F) : Prop :=
  output = if x = 0 then 1 else 0

theorem soundness : Soundness F elaborated Assumptions (Spec (F:=F)) := by
  circuit_proof_start
  delta main at h_holds ⊢
  simp only [circuit_norm] at *
  obtain ⟨h1, h2⟩ := h_holds
  subst h_input
  split
  · simp_all
  · rename_i h_ne
    have : env.get (i₀ + 1) = 0 := by
      by_contra h
      exact h_ne (or_iff_not_imp_left.mp (mul_eq_zero.mp (show _ = _ from h2)) h)
    exact this

theorem completeness : Completeness F elaborated Assumptions := by
  circuit_proof_start
  delta main at h_env ⊢
  simp only [circuit_norm, explicit_provable_type] at *
  refine ⟨h_env.2, ?_⟩
  rw [h_env.2, h_env.1]
  simp only [h_input]
  split
  · simp_all
  · rename_i h
    have h_inv := @mul_inv_cancel₀ F _ input h
    erw [h_inv]; ring

def circuit : FormalCircuit F field field := {
  elaborated with Assumptions, Spec := Spec (F:=F), soundness, completeness
}

end Gadgets.IsZeroField
