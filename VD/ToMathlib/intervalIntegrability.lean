import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalAverage
import VD.ToMathlib.analyticAt_preimgCodiscrete

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral


theorem ae_of_restrVol_le_codiscreteWithin {U : Set ℝ} (hU : MeasurableSet U) :
    ae (volume.restrict U) ≤ codiscreteWithin U := by
  intro s hs
  have := discreteTopology_of_codiscreteWithin hs
  rw [mem_ae_iff, Measure.restrict_apply' hU]
  apply Set.Countable.measure_zero (TopologicalSpace.separableSpace_iff_countable.1
    TopologicalSpace.SecondCountableTopology.to_separableSpace)

theorem intervalIntegrable_congr_codiscreteWithin {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    {f₁ f₂ : ℝ → E} (hf : f₁ =ᶠ[codiscreteWithin (Ι a b)] f₂) :
    IntervalIntegrable f₁ volume a b ↔ IntervalIntegrable f₂ volume a b := by
  constructor
  · intro hf₁
    apply hf₁.congr
    rw [eventuallyEq_iff_exists_mem] at *
    obtain ⟨s, h₁s, h₂s⟩ := hf
    use s, ae_of_restrVol_le_codiscreteWithin measurableSet_Ioc h₁s, h₂s
  · rw [eventuallyEq_comm] at hf
    intro hf₁
    apply hf₁.congr
    rw [eventuallyEq_iff_exists_mem] at *
    obtain ⟨s, h₁s, h₂s⟩ := hf
    use s, ae_of_restrVol_le_codiscreteWithin measurableSet_Ioc h₁s, h₂s

open Complex in
/-- The circleMap is real analytic. -/
theorem analyticOnNhd_circleMap {c : ℂ} {R : ℝ} :
    AnalyticOnNhd ℝ (circleMap c R) Set.univ := by
  intro z hz
  apply analyticAt_const.add
  apply analyticAt_const.mul
  rw [(by rfl : (fun θ ↦ exp (↑θ * I) : ℝ → ℂ) = cexp ∘ (fun θ : ℝ ↦ (θ * I)))]
  apply analyticAt_cexp.restrictScalars.comp ((ofRealCLM.analyticAt z).mul (by fun_prop))

theorem circleMap_preimg_codiscrete {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    map (circleMap c R) (codiscrete ℝ) ≤ (codiscreteWithin (Metric.sphere c |R|)) := by
  intro s hs
  apply analyticOnNhd_circleMap.preimg_codiscrete
  · intro x hx
    by_contra hCon
    obtain ⟨a, ha⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hCon
    have := ha.deriv.eq_of_nhds
    simp [hR] at this
  · rwa [Set.image_univ, range_circleMap]

theorem circleIntegrable_congr_codiscreteWithin {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℂ}
    (hf : f₁ =ᶠ[codiscreteWithin (Metric.sphere c |R|)] f₂) :
    CircleIntegrable f₁ c R → CircleIntegrable f₂ c R := by
  by_cases hR : R = 0
  · rw [hR]
    simp
  apply (intervalIntegrable_congr_codiscreteWithin _).1
  rw [eventuallyEq_iff_exists_mem]
  use (circleMap c R)⁻¹' {z | f₁ z = f₂ z}, codiscreteWithin.mono
    (by simp only [Set.subset_univ]) (circleMap_preimg_codiscrete hR hf), (by tauto)

theorem intervalIntegral.integral_congr_ae_restict {a b : ℝ} {f g : ℝ → E} {μ : Measure ℝ}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
  intervalIntegral.integral_congr_ae (ae_imp_of_ae_restrict h)

theorem intervalIntegral.integral_congr_codiscreteWithin {a b : ℝ} {f₁ f₂ : ℝ → ℝ}
    (hf : f₁ =ᶠ[codiscreteWithin (Ι a b)] f₂) :
    ∫ (x : ℝ) in a..b, f₁ x = ∫ (x : ℝ) in a..b, f₂ x :=
  integral_congr_ae_restict (ae_of_restrVol_le_codiscreteWithin measurableSet_uIoc hf)

theorem intervalAverage_congr_codiscreteWithin {a b : ℝ} {f₁ f₂ : ℝ → ℝ}
    (hf : f₁ =ᶠ[codiscreteWithin (Ι a b)] f₂) :
    ⨍ (x : ℝ) in a..b, f₁ x = ⨍ (x : ℝ) in a..b, f₂ x := by
  rw [interval_average_eq, intervalIntegral.integral_congr_codiscreteWithin hf,
    ← interval_average_eq]

theorem circleIntegral_congr_codiscreteWithin {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℂ}
    (hf : f₁ =ᶠ[codiscreteWithin (Metric.sphere c |R|)] f₂) (hR : R ≠ 0) :
    (∮ z in C(c, R), f₁ z) = (∮ z in C(c, R), f₂ z) := by
  apply integral_congr_ae_restict
  apply ae_of_restrVol_le_codiscreteWithin measurableSet_uIoc
  simp only [deriv_circleMap, smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero,
    circleMap_eq_center_iff, hR, Complex.I_ne_zero, or_self, or_false]
  exact codiscreteWithin.mono (by tauto) (circleMap_preimg_codiscrete hR hf)
