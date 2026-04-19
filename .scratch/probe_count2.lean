import Mathlib.Data.List.Basic

variable {S : Type*} [DecidableEq S]

-- Test 1: count singleton
example (x y : S) : List.count (x, y) [(x, y)] = 1 := by
  simp

-- Test 2: count cons with by_cases
example (h h2 : S) (x y : S) (t2 : List S) (h_eq : ¬(h, h2) = (x, y)) :
    List.count (x, y) ((h, h2) :: (h2 :: (t2 ++ [y])).zip (t2 ++ [y])) =
    List.count (x, y) ((h2 :: (t2 ++ [y])).zip (t2 ++ [y])) := by
  simp [List.count_cons, h_eq]

-- Test 3: the _other variant with congr
example (h h2 : S) (t : S × S) (t2 : List S) (y : S) :
    List.count t ((h, h2) :: (h2 :: (t2 ++ [y])).zip (t2 ++ [y])) =
    List.count t ((h, h2) :: (h2 :: t2).zip t2) → True := by
  intro; trivial
