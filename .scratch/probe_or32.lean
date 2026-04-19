import Clean.Utils.Tactics
import Clean.Types.U32
import Clean.Gadgets.Or.Or8

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough : Fact (p > 512)]

namespace ProbeOr32
open Gadgets.Or

structure Inputs (F : Type) where
  x : U32 F
  y : U32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var U32 (F p))  := do
  let ⟨x, y⟩ := input
  let z0 ← Or8.circuit ⟨x.x0, y.x0⟩
  let z1 ← Or8.circuit ⟨x.x1, y.x1⟩
  let z2 ← Or8.circuit ⟨x.x2, y.x2⟩
  let z3 ← Or8.circuit ⟨x.x3, y.x3⟩
  return ⟨z0, z1, z2, z3⟩

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def Spec (input : Inputs (F p)) (z : U32 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = x.value ||| y.value ∧ z.Normalized

@[reducible]
instance elaborated : ElaboratedCircuit (F p) Inputs U32 where
  main
  localLength _ := 4

set_option maxHeartbeats 1600000
theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  have l_components := U32.or_componentwise h_assumptions.1 h_assumptions.2
  delta main at *
  -- Decompose subcircuit soundness in BOTH h_holds and goal
  simp only [circuit_norm, Or8.circuit] at h_holds ⊢
  -- Now decompose
  rcases h_holds with ⟨h1, h2, h3, h4⟩
  -- Cast to reduce match
  replace h1 : Or8.Assumptions ⟨Expression.eval env input_var_x.x0, Expression.eval env input_var_y.x0⟩ →
    Or8.Spec ⟨Expression.eval env input_var_x.x0, Expression.eval env input_var_y.x0⟩
      (Expression.eval env (Or8.main ⟨input_var_x.x0, input_var_y.x0⟩ i₀).1) := h1
  replace h2 : Or8.Assumptions ⟨Expression.eval env input_var_x.x1, Expression.eval env input_var_y.x1⟩ →
    Or8.Spec ⟨Expression.eval env input_var_x.x1, Expression.eval env input_var_y.x1⟩
      (Expression.eval env (Or8.main ⟨input_var_x.x1, input_var_y.x1⟩ (i₀ + 1)).1) := h2
  replace h3 : Or8.Assumptions ⟨Expression.eval env input_var_x.x2, Expression.eval env input_var_y.x2⟩ →
    Or8.Spec ⟨Expression.eval env input_var_x.x2, Expression.eval env input_var_y.x2⟩
      (Expression.eval env (Or8.main ⟨input_var_x.x2, input_var_y.x2⟩ (i₀ + 1 + 1)).1) := h3
  replace h4 : Or8.Assumptions ⟨Expression.eval env input_var_x.x3, Expression.eval env input_var_y.x3⟩ →
    Or8.Spec ⟨Expression.eval env input_var_x.x3, Expression.eval env input_var_y.x3⟩
      (Expression.eval env (Or8.main ⟨input_var_x.x3, input_var_y.x3⟩ (i₀ + 1 + 1 + 1)).1) := h4
  -- Destructure and process
  rcases input_x with ⟨x0, x1, x2, x3⟩
  rcases input_y with ⟨y0, y1, y2, y3⟩
  rcases input_var_x with ⟨x0v, x1v, x2v, x3v⟩
  rcases input_var_y with ⟨y0v, y1v, y2v, y3v⟩
  simp only [U32.Normalized] at *
  simp only [explicit_provable_type, toVars, fromElements] at h_input ⊢ l_components
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, U32.mk.injEq] at h_input ⊢ l_components
  rcases h_input with ⟨⟨hx0, hx1, hx2, hx3⟩, hy0, hy1, hy2, hy3⟩
  dsimp only [Or8.Assumptions, Or8.Spec] at h1 h2 h3 h4
  rw [hx0, hy0] at h1; rw [hx1, hy1] at h2; rw [hx2, hy2] at h3; rw [hx3, hy3] at h4
  have h1 := h1 (by omega)
  have h2 := h2 (by omega)
  have h3 := h3 (by omega)
  have h4 := h4 (by omega)
  -- Goal should now be in terms that match h1..h4
  simp only [U32.value] at ⊢ l_components
  simp only [h1.2, h2.2, h3.2, h4.2]
  simp only [h1.1, h2.1, h3.1, h4.1, l_components]
  ring_nf
  simp

end ProbeOr32
end
