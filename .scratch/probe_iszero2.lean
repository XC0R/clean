import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics

namespace Probe.IsZeroField

variable {F : Type} [Field F] [DecidableEq F]

def main (x : Var field F) : Circuit F (Var field F) := do
  let xInv ← witness fun env =>
    if x.eval env = 0 then 0 else (x.eval env : F)⁻¹
  let isZero <== 1 - x*xInv
  isZero * x === 0
  return isZero

instance elaborated : ElaboratedCircuit F field field where
  main
  localLength _ := 2

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

end Probe.IsZeroField
