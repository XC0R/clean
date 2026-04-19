import Mathlib.Data.List.Basic

variable {S : Type*} [DecidableEq S]

-- What does List.zip [s, s] [s, s].tail look like?
example (s : S) : ([s, s].zip [s, s].tail) = [(s, s)] := by
  simp [List.zip, List.tail, List.zipWith]

-- What does List.zip [a, b, a] [a, b, a].tail look like?
example (a b : S) : ([a, b, a].zip [a, b, a].tail) = [(a, b), (b, a)] := by
  simp [List.zip, List.tail, List.zipWith]

-- Full: count t in [s, s].zip [s, s].tail ≤ R t for self-loop
example (s : S) (R : S × S → ℕ) (t : S × S) (h_edge : R (s, s) > 0)
    (h_t : t = (s, s)) : List.count t ([s, s].zip [s, s].tail) ≤ R t := by
  subst h_t
  simp [List.zip, List.tail, List.zipWith]

example (s : S) (R : S × S → ℕ) (t : S × S) (h_edge : R (s, s) > 0)
    (h_t : t ≠ (s, s)) : List.count t ([s, s].zip [s, s].tail) ≤ R t := by
  simp [List.zip, List.tail, List.zipWith, h_t]
