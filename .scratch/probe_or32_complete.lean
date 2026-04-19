import Clean.Utils.Tactics
import Clean.Types.U32
import Clean.Gadgets.Or.Or8

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough : Fact (p > 512)]

namespace ProbeOr32C
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

@[reducible]
instance elaborated : ElaboratedCircuit (F p) Inputs U32 where
  main
  localLength _ := 4

set_option maxHeartbeats 1600000
theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  delta main at *
  simp only [circuit_norm, Or8.circuit] at ⊢
  -- Goal should have Or8.Assumptions with match expressions
  -- Cast via change or just use rcases/simp
  rcases input_x with ⟨x0, x1, x2, x3⟩
  rcases input_y with ⟨y0, y1, y2, y3⟩
  simp only [explicit_provable_type, toVars, fromElements] at h_input ⊢
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, U32.mk.injEq] at h_input ⊢
  simp only [U32.Normalized] at h_assumptions
  -- Goal should have Or8.Assumptions ⟨eval x_i, eval y_i⟩
  -- Need to show each Or8.Assumptions holds
  -- h_input gives eval xi = xi etc.
  rcases h_input with ⟨⟨hx0, hx1, hx2, hx3⟩, hy0, hy1, hy2, hy3⟩
  -- For completeness, the goal has Or8.Assumptions with ProvableTypeList match
  -- Instead of unfolding, use the same cast trick
  -- Goal structure: Or8.Assumptions (match...) ∧ Or8.Assumptions (match...) ∧ ...
  -- Replace with: Or8.Assumptions ⟨eval_x0, eval_y0⟩ ∧ ...
  -- Use change with eval expressions (defeq to match)
  change Or8.Assumptions ⟨Expression.eval env input_var_x.x0, Expression.eval env input_var_y.x0⟩ ∧
    Or8.Assumptions ⟨Expression.eval env input_var_x.x1, Expression.eval env input_var_y.x1⟩ ∧
    Or8.Assumptions ⟨Expression.eval env input_var_x.x2, Expression.eval env input_var_y.x2⟩ ∧
    Or8.Assumptions ⟨Expression.eval env input_var_x.x3, Expression.eval env input_var_y.x3⟩
  simp only [Or8.Assumptions, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  omega

end ProbeOr32C
end
