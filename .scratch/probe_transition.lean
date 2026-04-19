import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

def Transition (S : Type*) := S × S
instance [DecidableEq S] : DecidableEq (Transition S) := instDecidableEqProd

variable {S : Type*} [DecidableEq S]

-- Does List.count_singleton_self work with Transition S?
example (x y : S) : List.count ((x, y) : Transition S) [(x, y)] = 1 := by
  exact List.count_singleton_self

-- Does simp work?
example (x y : S) : List.count ((x, y) : Transition S) [(x, y)] = 1 := by
  simp

-- What about non-equal?
example (h h2 x y : S) (h_ne : ((h, h2) : Transition S) ≠ (x, y)) :
    List.count ((x, y) : Transition S) ((h, h2) :: rest) =
    List.count ((x, y) : Transition S) rest := by
  simp [h_ne]
