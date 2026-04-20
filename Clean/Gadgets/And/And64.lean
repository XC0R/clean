import Clean.Utils.Primes
import Clean.Types.U64
import Clean.Gadgets.And.And8

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

namespace Gadgets.And.And64
structure Inputs (F : Type) where
  x: U64 F
  y: U64 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var U64 (F p))  := do
  let ⟨x, y⟩ := input
  let z0 ← And8.circuit ⟨ x.x0, y.x0 ⟩
  let z1 ← And8.circuit ⟨ x.x1, y.x1 ⟩
  let z2 ← And8.circuit ⟨ x.x2, y.x2 ⟩
  let z3 ← And8.circuit ⟨ x.x3, y.x3 ⟩
  let z4 ← And8.circuit ⟨ x.x4, y.x4 ⟩
  let z5 ← And8.circuit ⟨ x.x5, y.x5 ⟩
  let z6 ← And8.circuit ⟨ x.x6, y.x6 ⟩
  let z7 ← And8.circuit ⟨ x.x7, y.x7 ⟩
  return U64.mk z0 z1 z2 z3 z4 z5 z6 z7

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def Spec (input : Inputs (F p)) (z : U64 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = x.value &&& y.value ∧ z.Normalized

instance elaborated : ElaboratedCircuit (F p) Inputs U64 where
  main
  localLength _ := 8
  output _ i := varFromOffset U64 i

omit [Fact (Nat.Prime p)] p_large_enough in
theorem soundness_to_u64 {x y z : U64 (F p)}
  (x_norm : x.Normalized) (y_norm : y.Normalized)
  (h_eq :
    z.x0.val = x.x0.val &&& y.x0.val ∧
    z.x1.val = x.x1.val &&& y.x1.val ∧
    z.x2.val = x.x2.val &&& y.x2.val ∧
    z.x3.val = x.x3.val &&& y.x3.val ∧
    z.x4.val = x.x4.val &&& y.x4.val ∧
    z.x5.val = x.x5.val &&& y.x5.val ∧
    z.x6.val = x.x6.val &&& y.x6.val ∧
    z.x7.val = x.x7.val &&& y.x7.val) : Spec { x, y } z := by
  simp only [Spec]
  have ⟨ hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7 ⟩ := x_norm
  have ⟨ hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7 ⟩ := y_norm

  have z_norm : z.Normalized := by
    simp only [U64.Normalized, h_eq]
    exact ⟨ Nat.and_lt_two_pow (n:=8) _ hy0, Nat.and_lt_two_pow (n:=8) _ hy1,
      Nat.and_lt_two_pow (n:=8) _ hy2, Nat.and_lt_two_pow (n:=8) _ hy3,
      Nat.and_lt_two_pow (n:=8) _ hy4, Nat.and_lt_two_pow (n:=8) _ hy5,
      Nat.and_lt_two_pow (n:=8) _ hy6, Nat.and_lt_two_pow (n:=8) _ hy7 ⟩

  suffices z.value = x.value &&& y.value from ⟨ this, z_norm ⟩
  simp only [U64.value_xor_horner, x_norm, y_norm, z_norm, h_eq]
  repeat rw [and_xor_sum]
  repeat assumption

set_option maxHeartbeats 3200000 in
theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  have x_norm := h_assumptions.1
  have y_norm := h_assumptions.2
  delta main at *
  simp only [circuit_norm, And8.circuit] at h_holds ⊢
  rcases h_holds with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases input_x with ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩
  rcases input_y with ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩
  rcases input_var_x with ⟨x0v, x1v, x2v, x3v, x4v, x5v, x6v, x7v⟩
  rcases input_var_y with ⟨y0v, y1v, y2v, y3v, y4v, y5v, y6v, y7v⟩
  simp only [explicit_provable_type, toVars, fromElements] at h_input ⊢
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, U64.mk.injEq] at h_input ⊢
  rcases h_input with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩, hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7⟩
  simp only [U64.Normalized] at h_assumptions
  obtain ⟨⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := h_assumptions
  dsimp only [And8.Assumptions, And8.Spec] at h1 h2 h3 h4 h5 h6 h7 h8
  rw [hx0, hy0] at h1; rw [hx1, hy1] at h2; rw [hx2, hy2] at h3; rw [hx3, hy3] at h4
  rw [hx4, hy4] at h5; rw [hx5, hy5] at h6; rw [hx6, hy6] at h7; rw [hx7, hy7] at h8
  have h1 := h1 ⟨ha0, hb0⟩
  have h2 := h2 ⟨ha1, hb1⟩
  have h3 := h3 ⟨ha2, hb2⟩
  have h4 := h4 ⟨ha3, hb3⟩
  have h5 := h5 ⟨ha4, hb4⟩
  have h6 := h6 ⟨ha5, hb5⟩
  have h7 := h7 ⟨ha6, hb6⟩
  have h8 := h8 ⟨ha7, hb7⟩
  apply soundness_to_u64 x_norm y_norm
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  delta main at *
  simp only [circuit_norm, And8.circuit] at ⊢
  rcases input_x with ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩
  rcases input_y with ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩
  simp only [explicit_provable_type, toVars, fromElements] at h_input ⊢
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, U64.mk.injEq] at h_input ⊢
  simp only [U64.Normalized] at h_assumptions
  rcases h_input with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩, hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7⟩
  change And8.Assumptions ⟨Expression.eval env input_var_x.x0, Expression.eval env input_var_y.x0⟩ ∧
    And8.Assumptions ⟨Expression.eval env input_var_x.x1, Expression.eval env input_var_y.x1⟩ ∧
    And8.Assumptions ⟨Expression.eval env input_var_x.x2, Expression.eval env input_var_y.x2⟩ ∧
    And8.Assumptions ⟨Expression.eval env input_var_x.x3, Expression.eval env input_var_y.x3⟩ ∧
    And8.Assumptions ⟨Expression.eval env input_var_x.x4, Expression.eval env input_var_y.x4⟩ ∧
    And8.Assumptions ⟨Expression.eval env input_var_x.x5, Expression.eval env input_var_y.x5⟩ ∧
    And8.Assumptions ⟨Expression.eval env input_var_x.x6, Expression.eval env input_var_y.x6⟩ ∧
    And8.Assumptions ⟨Expression.eval env input_var_x.x7, Expression.eval env input_var_y.x7⟩
  simp only [And8.Assumptions, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
    hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7]
  omega

def circuit : FormalCircuit (F p) Inputs U64 where
  Assumptions
  Spec
  soundness
  completeness

end Gadgets.And.And64
