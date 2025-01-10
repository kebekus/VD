import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open Real Filter MeasureTheory intervalIntegral

/-- An even function is interval integrable (with respect to the volume measure)
    on every interval iff it is interval integrable (with respect to the volume
    measure) on every interval of the form [0,x], for positive x. -/

-- This should go to Mathlib.MeasureTheory.Integral.IntervalIntegral

theorem intervalIntegrable_of_even
  {f : ℝ → ℝ}
  (hf : ∀ x, f x = f (-x))
  : (∀ x, 0 < x → IntervalIntegrable f volume 0 x) ↔ (∀ x y, IntervalIntegrable f volume x y) := by
  constructor
  · intro h₂f
    -- Lemma: Prove statement first in case where x = 0
    have : ∀ t, IntervalIntegrable f volume 0 t := by
      intro t
      rcases lt_trichotomy t 0 with h|h|h
      · rw [IntervalIntegrable.iff_comp_neg]
        conv => arg 1; intro t; rw [← hf]
        simp [h₂f (-t) (by norm_num [h])]
      · rw [h]
      · exact h₂f t h
    -- Split integral and apply lemma
    intro x y
    exact IntervalIntegrable.trans (b := 0) (IntervalIntegrable.symm (this x)) (this y)
  · tauto


/-- An odd function is interval integrable (with respect to the volume measure)
    on every interval iff it is interval integrable (with respect to the volume
    measure) on every interval of the form [0,x], for positive x. -/

-- This should go to Mathlib.MeasureTheory.Integral.IntervalIntegral

theorem intervalIntegrable_of_odd
  {f : ℝ → ℝ}
  (hf : ∀ x, -f x = f (-x)) :
  (∀ x, 0 < x → IntervalIntegrable f volume 0 x) ↔ (∀ x y, IntervalIntegrable f volume x y) := by
  constructor
  · intro h₂f
    -- Lemma: Prove statement first in case where x = 0
    have : ∀ t, IntervalIntegrable f volume 0 t := by
      intro t
      rcases lt_trichotomy t 0 with h|h|h
      · rw [IntervalIntegrable.iff_comp_neg]
        conv => arg 1; intro t; rw [← hf]
        apply IntervalIntegrable.neg
        simp [h₂f (-t) (by norm_num [h])]
      · rw [h]
      · exact h₂f t h
    -- Split integral and apply lemma
    intro x y
    exact IntervalIntegrable.trans (b := 0) (IntervalIntegrable.symm (this x)) (this y)
  · tauto


/- The real logarithm is interval integrable (with respect to the volume
measure) on every interval. -/

-- This should go to Mathlib.Analysis.SpecialFunctions.Integrals

@[simp]
theorem intervalIntegral.intervalIntegrable_log'
  {x y : ℝ} : IntervalIntegrable log volume x y := by
  -- Log is even, so it suffices to consider the case 0 < x and y = 0
  apply (intervalIntegrable_of_even (fun x ↦ Eq.symm (log_neg_eq_log x))).1

  intro x hx
  -- Split integral
  apply IntervalIntegrable.trans (b := 1)
  · -- Show integrability on [0…1] using non-negativity of the derivative
    rw [← neg_neg log]
    apply IntervalIntegrable.neg
    apply intervalIntegrable_deriv_of_nonneg
    · exact (continuous_mul_log.continuousOn.sub continuous_id.continuousOn).neg
    · intro s hs; norm_num at hs
      convert ((hasDerivAt_mul_log hs.left.ne.symm).sub (hasDerivAt_id s)).neg using 1
      norm_num
    · intro s hs; norm_num at hs; simp
      exact (log_nonpos_iff hs.left).mpr hs.right.le
  · -- Show integrability on [1…t] by continuity
    apply ContinuousOn.intervalIntegrable
    apply (ContinuousOn.mono Real.continuousOn_log)
    simp
    exact Set.not_mem_uIcc_of_lt zero_lt_one hx
