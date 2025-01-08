import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Measure.Restrict

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

-- The following theorem was suggested by Gareth Ma on Zulip


theorem logInt
  {t : ℝ}
  (ht : 0 < t) :
  ∫ x in (0 : ℝ)..t, log x = t * log t - t := by
  rw [← integral_add_adjacent_intervals (b := 1)]
  trans (-1) + (t * log t - t + 1)
  · congr
    · -- ∫ x in 0..1, log x = -1, same proof as before
      rw [integral_eq_sub_of_hasDerivAt_of_tendsto (f := fun x ↦ x * log x - x) (fa := 0) (fb := -1)]
      · simp
      · simp
      · intro x hx
        norm_num at hx
        convert (hasDerivAt_mul_log hx.left.ne.symm).sub (hasDerivAt_id x) using 1
        norm_num
      · rw [← neg_neg log]
        apply IntervalIntegrable.neg
        apply intervalIntegrable_deriv_of_nonneg (g := fun x ↦ -(x * log x - x))
        · exact (continuous_mul_log.continuousOn.sub continuous_id.continuousOn).neg
        · intro x hx
          norm_num at hx
          convert ((hasDerivAt_mul_log hx.left.ne.symm).sub (hasDerivAt_id x)).neg using 1
          norm_num
        · intro x hx
          norm_num at hx
          rw [Pi.neg_apply, Left.nonneg_neg_iff]
          exact (log_nonpos_iff hx.left).mpr hx.right.le
      · have := tendsto_log_mul_rpow_nhds_zero zero_lt_one
        simp_rw [rpow_one, mul_comm] at this
        -- tendsto_nhdsWithin_of_tendsto_nhds should be under Tendsto namespace
        convert this.sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
        norm_num
      · rw [(by simp : -1 = 1 * log 1 - 1)]
        apply tendsto_nhdsWithin_of_tendsto_nhds
        exact (continuousAt_id.mul (continuousAt_log one_ne_zero)).sub continuousAt_id
    · -- ∫ x in 1..t, log x = t * log t + 1, just use integral_log_of_pos
      rw [integral_log_of_pos zero_lt_one ht]
      norm_num
  · abel
  · -- log is integrable on [[0, 1]]
    rw [← neg_neg log]
    apply IntervalIntegrable.neg
    apply intervalIntegrable_deriv_of_nonneg (g := fun x ↦ -(x * log x - x))
    · exact (continuous_mul_log.continuousOn.sub continuous_id.continuousOn).neg
    · intro x hx
      norm_num at hx
      convert ((hasDerivAt_mul_log hx.left.ne.symm).sub (hasDerivAt_id x)).neg using 1
      norm_num
    · intro x hx
      norm_num at hx
      rw [Pi.neg_apply, Left.nonneg_neg_iff]
      exact (log_nonpos_iff hx.left).mpr hx.right.le
  · -- log is integrable on [[1, t]]
    simp [Set.mem_uIcc, ht]
