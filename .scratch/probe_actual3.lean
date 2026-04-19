import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

variable {S : Type*} [DecidableEq S]

def Transition2 (S : Type*) := S × S
instance [DecidableEq S] : DecidableEq (Transition2 S) := instDecidableEqProd

def countTransitionInPath3 [DecidableEq S] (t : Transition2 S) (path : List S) : ℕ :=
  (path.zip path.tail).count t

-- Try unfolding Transition2
example (x y : S) :
    @List.count (Transition2 S) instBEqOfDecidableEq (x, y) [(x, y)] = 1 := by
  simp [Transition2]

-- Or use unfold
example (x y : S) :
    List.count (α := Transition2 S) (x, y) [(x, y)] = 1 := by
  unfold Transition2 at *
  simp

-- Or native_decide?
example (x y : S) :
    List.count (α := Transition2 S) (x, y) [(x, y)] = 1 := by
  show List.count (α := S × S) (x, y) [(x, y)] = 1
  simp

example (x y : S) :
    List.count (α := Transition2 S) (x, y) [(x, y)] = 1 := by
  exact List.count_singleton_self
