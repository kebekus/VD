import VD.divisor

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral


noncomputable def AnalyticOnNhd.zeroDivisor
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (hf : AnalyticOnNhd ℂ f U) :
  Divisor U where

  toFun := by
    intro z
    if hz : z ∈ U then
      exact ((hf z hz).order.toNat : ℤ)
    else
      exact 0

  supportInU := by
    intro z hz
    simp at hz
    by_contra h₂z
    simp [h₂z] at hz

  locallyFiniteInU := by
    intro z hz

    apply eventually_nhdsWithin_iff.2
    rw [eventually_nhds_iff]

    rcases AnalyticAt.eventually_eq_zero_or_eventually_ne_zero (hf z hz) with h|h
    · rw [eventually_nhds_iff] at h
      obtain ⟨N, h₁N, h₂N, h₃N⟩ := h
      use N
      constructor
      · intro y h₁y _
        by_cases h₃y : y ∈ U
        · simp [h₃y]
          right
          rw [AnalyticAt.order_eq_top_iff (hf y h₃y)]
          rw [eventually_nhds_iff]
          use N
        · simp [h₃y]
      · tauto

    · rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at h
      obtain ⟨N, h₁N, h₂N, h₃N⟩ := h
      use N
      constructor
      · intro y h₁y h₂y
        by_cases h₃y : y ∈ U
        · simp [h₃y]
          left
          rw [AnalyticAt.order_eq_zero_iff (hf y h₃y)]
          exact h₁N y h₁y h₂y
        · simp [h₃y]
      · tauto
