import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real


-- This should go to Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem log_pos_iff' (hx : 0 ≤ x) : 0 < log x ↔ 1 < x := by
  by_cases h : x = 0
  · rw [h]; simp
  · rw [← log_one]
    apply log_lt_log_iff zero_lt_one
    exact lt_of_le_of_ne hx fun a ↦ h (id (Eq.symm a))

theorem log_pos_iff'' : 0 < log x ↔ 1 < |x| := by
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg h]
    exact log_pos_iff' h
  · simp at h
    rw [abs_of_neg h, ←Real.log_neg_eq_log]
    apply log_pos_iff'
    simp [h, le_of_lt]
