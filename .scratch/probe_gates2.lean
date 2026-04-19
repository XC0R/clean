import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Gadgets.Equality
import Clean.Gadgets.Boolean

-- Reproduce Gates XOR circuit pattern
section
variable {p : ℕ} [Fact p.Prime]

def testMain (input : Var fieldPair (F p)) : Circuit (F p) (Var field (F p)) := do
  let a := input.1
  let b := input.2
  let out <== a + b - 2*a*b
  return out

-- Check: what does localLength_eq need?
-- It should prove: (main input offset).2.localLength = localLength input
-- Try native_decide or rfl
example (input : Var fieldPair (F p)) : (testMain input 0).2.localLength = 1 := by
  simp [testMain, circuit_norm]

example (input : Var fieldPair (F p)) : (testMain input 0).2.localLength = 1 := by
  rfl
end
