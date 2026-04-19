import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Field

-- Probe: does `rfl` or `decide` work for localLength_eq?
-- Goal: ElaboratedCircuit.localLength unit (...) = 0
-- The issue is simp doesn't unfold ElaboratedCircuit.localLength

-- Check what ElaboratedCircuit.localLength actually computes
#check @ElaboratedCircuit.localLength
