import Clean.Gadgets.IsZeroField

namespace Gadgets.IsZeroField.Probe

variable {F : Type} [Field F] [DecidableEq F]

-- Try to understand what circuit_proof_start produces
-- and what main looks like after unfolding

-- Let's check the main definition output
#check @main

-- Probe: soundness with manual unfolding
theorem soundness_probe : Soundness F elaborated Assumptions (Spec (F:=F)) := by
  circuit_proof_start
  -- After circuit_proof_start, what do we have?
  -- Let's try unfolding main
  simp only [main] at *
  split
  · rename_i h_zero
    simp only [h_zero] at *
    norm_num at *
    assumption
  �� aesop

end Gadgets.IsZeroField.Probe
