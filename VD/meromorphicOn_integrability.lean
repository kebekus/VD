import Mathlib.Analysis.Analytic.Meromorphic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import VD.analyticAt
import VD.divisor
import VD.intervalIntegrability
import VD.logpos
import VD.meromorphicAt
import VD.meromorphicOn_divisor
import VD.specialFunctions_CircleIntegral_affine
import VD.stronglyMeromorphicOn
import VD.stronglyMeromorphicOn_eliminate
import VD.mathlibAddOn

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral


theorem MeromorphicOn.integrable_log_abs_f₀
  {f : ℂ → ℂ}
  {r : ℝ}
  -- WARNING: Not optimal. This needs to go
  (hr : 0 < r)
  -- WARNING: Not optimal. It suffices to be meromorphic on the Sphere
  (h₁f : MeromorphicOn f (Metric.closedBall (0 : ℂ) r)) :
  IntervalIntegrable (fun z ↦ log ‖f (circleMap 0 r z)‖) MeasureTheory.volume 0 (2 * π) := by

  by_cases h₂f : ∃ u : (Metric.closedBall (0 : ℂ) r), (h₁f u u.2).order ≠ ⊤
  · have h₁U : IsCompact (Metric.closedBall (0 : ℂ) r) := isCompact_closedBall 0 r

    have h₂U : IsConnected (Metric.closedBall (0 : ℂ) r) := by
      constructor
      · exact Metric.nonempty_closedBall.mpr (le_of_lt hr)
      · exact (convex_closedBall (0 : ℂ) r).isPreconnected

    -- This is where we use 'ball' instead of sphere. However, better
    -- results should make this assumption unnecessary.
    have h₃U : interior (Metric.closedBall (0 : ℂ) r) ≠ ∅ := by
      rw [interior_closedBall, ← Set.nonempty_iff_ne_empty]
      use 0; simp [hr];
      repeat exact Ne.symm (ne_of_lt hr)

    have h₃f : Set.Finite (Function.support h₁f.divisor) := by
      exact Divisor.finiteSupport h₁U h₁f.divisor

    obtain ⟨g, h₁g, h₂g, h₃g⟩ := MeromorphicOn.decompose_log h₁U h₂U h₃U h₁f h₂f
    have : (fun z ↦ log ‖f (circleMap 0 r z)‖) = (fun z ↦ log ‖f z‖) ∘ (circleMap 0 r) := by
      rfl
    rw [this]
    have : Metric.sphere (0 : ℂ) |r| ⊆ Metric.closedBall (0 : ℂ) r := by
      rw [abs_of_pos hr]
      apply Metric.sphere_subset_closedBall

    rw [integrability_congr_changeDiscrete this h₃g]

    apply IntervalIntegrable.add
    --
    apply Continuous.intervalIntegrable
    apply continuous_iff_continuousAt.2
    intro x
    have : (fun x => log ‖g (circleMap 0 r x)‖) = log ∘ Complex.abs ∘ g ∘ (fun x ↦ circleMap 0 r x) :=
      rfl
    rw [this]
    apply ContinuousAt.comp
    apply Real.continuousAt_log
    · simp
      have : (circleMap 0 r x) ∈ (Metric.closedBall (0 : ℂ) r) := by
        apply circleMap_mem_closedBall
        exact le_of_lt hr
      exact h₂g ⟨(circleMap 0 r x), this⟩
    apply ContinuousAt.comp
    · apply Continuous.continuousAt Complex.continuous_abs
    apply ContinuousAt.comp
    · have : (circleMap 0 r x) ∈ (Metric.closedBall (0 : ℂ) r) := by
        apply circleMap_mem_closedBall (0 : ℂ) (le_of_lt hr) x
      apply (h₁g (circleMap 0 r x) this).continuousAt
    apply Continuous.continuousAt (continuous_circleMap 0 r)
    --
    have h {x : ℝ} : (Function.support fun s => (h₁f.divisor s) * log ‖circleMap 0 r x - s‖) ⊆ h₃f.toFinset := by
      intro x; simp; tauto
    simp_rw [finsum_eq_sum_of_support_subset _ h]
    have : (fun x => ∑ s ∈ h₃f.toFinset, (h₁f.divisor s) * log ‖circleMap 0 r x - s‖) = (∑ s ∈ h₃f.toFinset, fun x => (h₁f.divisor s) * log ‖circleMap 0 r x - s‖) := by
      ext x; simp
    rw [this]
    apply IntervalIntegrable.sum h₃f.toFinset
    intro s hs
    apply IntervalIntegrable.const_mul

    apply intervalIntegrable_logAbs_circleMap_sub_const
    exact Ne.symm (ne_of_lt hr)

  · push_neg at h₂f

    let F := h₁f.makeStronglyMeromorphicOn
    have : (fun z => log ‖f z‖) =ᶠ[Filter.codiscreteWithin (Metric.closedBall 0 r)] (fun z => log ‖F z‖) := by
      -- WANT: apply Filter.eventuallyEq.congr
      let A := (makeStronglyMeromorphicOn_changeDiscrete'' h₁f)
      obtain ⟨s, h₁s, h₂s⟩ := eventuallyEq_iff_exists_mem.1 A
      rw [eventuallyEq_iff_exists_mem]
      use s
      constructor
      · exact h₁s
      · intro x hx
        simp_rw [h₂s hx, F]
    have hU : Metric.sphere (0 : ℂ) |r| ⊆ Metric.closedBall 0 r := by
      rw [abs_of_pos hr]
      exact Metric.sphere_subset_closedBall
    have t₀ : (fun z => log ‖f (circleMap 0 r z)‖) =  (fun z => log ‖f z‖) ∘ circleMap 0 r := by
      rfl
    rw [t₀]
    clear t₀
    rw [integrability_congr_changeDiscrete hU this]

    have : ∀ x ∈ Metric.closedBall 0 r, F x = 0 := by
      intro x hx
      let A := h₂f ⟨x, hx⟩
      rw [← makeStronglyMeromorphicOn_changeOrder h₁f hx] at A
      let B := ((stronglyMeromorphicOn_of_makeStronglyMeromorphicOn h₁f) x hx).order_eq_zero_iff.not.1
      simp [A] at B
      assumption
    have : (fun z => log ‖F z‖) ∘ circleMap 0 r = 0 := by
      funext x
      simp
      left
      apply this
      simp [abs_of_pos hr]
    simp_rw [this]
    apply intervalIntegral.intervalIntegrable_const


theorem MeromorphicOn.integrable_log_abs_f
  {f : ℂ → ℂ}
  {r : ℝ}
  -- WARNING: Not optimal. It suffices to be meromorphic on the Sphere
  (h₁f : MeromorphicOn f (Metric.closedBall (0 : ℂ) |r|)) :
  IntervalIntegrable (fun z ↦ log ‖f (circleMap 0 r z)‖) MeasureTheory.volume 0 (2 * π) := by

  by_cases h₁r : r = 0
  · rw [h₁r]
    simp
  · by_cases h₂r : 0 < r
    · have : |r| = r := by
        exact abs_of_pos h₂r
      rw [this] at h₁f
      exact MeromorphicOn.integrable_log_abs_f₀ h₂r h₁f
    · have t₀ : 0 < -r := by
        have hr_neg : r < 0 := by
          apply lt_of_le_of_ne
          exact le_of_not_lt h₂r
          exact h₁r
        linarith
      have : |r| = -r := by
        apply abs_of_neg
        exact Left.neg_pos_iff.mp t₀
      rw [this] at h₁f
      let A := MeromorphicOn.integrable_log_abs_f₀ t₀ h₁f

      let B := integrability_congr_negRadius (f := fun z => log ‖f z‖) (r := -r)
      let C := B A
      simp at C
      simpa


theorem MeromorphicOn.integrable_logpos_abs_f
  {f : ℂ → ℂ}
  {r : ℝ}
  -- WARNING: Not optimal. It suffices to be meromorphic on the Sphere
  (h₁f : MeromorphicOn f (Metric.closedBall (0 : ℂ) |r|)) :
  IntervalIntegrable (fun z ↦ logpos ‖f (circleMap 0 r z)‖) MeasureTheory.volume 0 (2 * π) := by

  simp_rw [logpos_norm]
  simp_rw [mul_add]

  apply IntervalIntegrable.add
  apply IntervalIntegrable.const_mul
  exact MeromorphicOn.integrable_log_abs_f h₁f

  apply IntervalIntegrable.const_mul
  apply IntervalIntegrable.norm
  exact MeromorphicOn.integrable_log_abs_f h₁f
