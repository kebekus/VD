import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real


-- This should go to Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem log_pos_iff'' : 0 < log x ↔ 1 < |x| := by
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg h]
    exact log_pos_iff h
  · simp at h
    rw [abs_of_neg h, ← Real.log_neg_eq_log]
    apply log_pos_iff
    simp [h, le_of_lt]
