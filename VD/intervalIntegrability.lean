import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.Periodic
import VD.codiscreteWithin

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral


/- Integral and Integrability up to changes on codiscrete sets -/

theorem d
  {U S : Set ℂ}
  {c : ℂ}
  {r : ℝ}
  (hr : r ≠ 0)
  (hU : Metric.sphere c |r| ⊆ U)
  (hS : S ∈ Filter.codiscreteWithin U) :
  Countable ((circleMap c r)⁻¹' Sᶜ) := by

  have : (circleMap c r)⁻¹' (S ∪ Uᶜ)ᶜ = (circleMap c r)⁻¹' Sᶜ := by
    simp [(by simpa : (circleMap c r)⁻¹' U = ⊤)]
  rw [← this]

  apply Set.Countable.preimage_circleMap _ c hr
  have : DiscreteTopology ((S ∪ Uᶜ)ᶜ : Set ℂ) := by
    rw [discreteTopology_subtype_iff]
    rw [mem_codiscreteWithin] at hS; simp at hS

    intro x hx
    rw [← mem_iff_inf_principal_compl, (by ext z; simp; tauto : S ∪ Uᶜ = (U \ S)ᶜ)]
    rw [Set.compl_union, compl_compl] at hx
    exact hS x hx.2

  apply TopologicalSpace.separableSpace_iff_countable.1
  exact TopologicalSpace.SecondCountableTopology.to_separableSpace


theorem integrability_congr_changeDiscrete₀
  {f₁ f₂ : ℂ → ℝ}
  {U : Set ℂ}
  {r : ℝ}
  (hU : Metric.sphere 0 |r| ⊆ U)
  (hf : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
  IntervalIntegrable (f₁ ∘ (circleMap 0 r)) MeasureTheory.volume 0 (2 * π) → IntervalIntegrable (f₂ ∘ (circleMap 0 r)) MeasureTheory.volume 0 (2 * π) := by
  intro hf₁

  by_cases hr : r = 0
  · unfold circleMap
    rw [hr]
    simp
    have : f₂ ∘ (fun (θ : ℝ) ↦ 0) = (fun r ↦ f₂ 0) := by
      exact rfl
    rw [this]
    simp

  · apply IntervalIntegrable.congr hf₁
    rw [Filter.eventuallyEq_iff_exists_mem]
    use (circleMap 0 r)⁻¹' {z | f₁ z = f₂ z}
    constructor
    · apply Set.Countable.measure_zero (d hr hU hf)
    · tauto


theorem integrability_congr_changeDiscrete
  {f₁ f₂ : ℂ → ℝ}
  {U : Set ℂ}
  {r : ℝ}
  (hU : Metric.sphere (0 : ℂ) |r| ⊆ U)
  (hf : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
  IntervalIntegrable (f₁ ∘ (circleMap 0 r)) MeasureTheory.volume 0 (2 * π) ↔ IntervalIntegrable (f₂ ∘ (circleMap 0 r)) MeasureTheory.volume 0 (2 * π) := by

  constructor
  · exact integrability_congr_changeDiscrete₀ hU hf
  · exact integrability_congr_changeDiscrete₀ hU (EventuallyEq.symm hf)


theorem integral_congr_changeDiscrete
  {f₁ f₂ : ℂ → ℝ}
  {U : Set ℂ}
  {r : ℝ}
  (hr : r ≠ 0)
  (hU : Metric.sphere 0 |r| ⊆ U)
  (hf : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
  ∫ (x : ℝ) in (0)..(2 * π), f₁ (circleMap 0 r x) = ∫ (x : ℝ) in (0)..(2 * π), f₂ (circleMap 0 r x) := by

  apply intervalIntegral.integral_congr_ae
  rw [eventually_iff_exists_mem]
  use (circleMap 0 r)⁻¹' {z | f₁ z = f₂ z}
  constructor
  · apply Set.Countable.measure_zero (d hr hU hf)
  · tauto


lemma circleMap_neg
  {r x : ℝ} :
  circleMap 0 (-r) x = circleMap 0 r (x + π) := by
  unfold circleMap
  simp [add_mul, Complex.exp_add]


theorem integrability_congr_negRadius
  {f : ℂ → ℝ}
  {r : ℝ} :
  IntervalIntegrable (fun (θ : ℝ) ↦ f (circleMap 0   r  θ)) MeasureTheory.volume 0 (2 * π) →
  IntervalIntegrable (fun (θ : ℝ) ↦ f (circleMap 0 (-r) θ)) MeasureTheory.volume 0 (2 * π) := by

  intro h
  simp_rw [circleMap_neg]
  have t₀ : Function.Periodic (fun (θ : ℝ) ↦ f (circleMap 0   r  θ)) (2 * π) := by
    intro x
    simp
    congr 1
    exact periodic_circleMap 0 r x
  rw [← zero_add (2 * π)] at h
  have B := t₀.intervalIntegrable two_pi_pos h (π) (3 * π)
  let A := IntervalIntegrable.comp_add_right B π
  simp at A
  have : 3 * π - π = 2 * π := by
    ring
  rw [this] at A
  exact A


theorem integrabl_congr_negRadius
  {f : ℂ → ℝ}
  {r : ℝ} :
  ∫ (x : ℝ) in (0)..(2 * π), f (circleMap 0 r x) = ∫ (x : ℝ) in (0)..(2 * π), f (circleMap 0 (-r) x) := by

  simp_rw [circleMap_neg]
  have t₀ : Function.Periodic (fun (θ : ℝ) ↦ f (circleMap 0   r  θ)) (2 * π) := by
    intro x
    simp
    congr 1
    exact periodic_circleMap 0 r x
  have B := intervalIntegral.integral_comp_add_right (a := 0) (b := 2 * π) (fun θ => f (circleMap 0 r θ)) π
  rw [B]
  let X := t₀.intervalIntegral_add_eq 0 (0 + π)
  simp at X
  rw [X]
  simp
  rw [add_comm]

theorem ae_of_restrVol_le_codiscreteWithin {U : Set ℝ} (hU : MeasurableSet U) :
    (MeasureTheory.ae (volume.restrict U)) ≤ (Filter.codiscreteWithin U) := by
  intro s hs
  have := discreteTopology_of_codiscreteWithin hs
  rw [mem_ae_iff, Measure.restrict_apply' hU]
  apply Set.Countable.measure_zero (TopologicalSpace.separableSpace_iff_countable.1
    TopologicalSpace.SecondCountableTopology.to_separableSpace)

theorem intervalIntegrable_congr_codiscreteWithin
    {E : Type u_3} [NormedAddCommGroup E] {a b : ℝ} {f₁ f₂ : ℝ → E} (hf : f₁ =ᶠ[Filter.codiscreteWithin (Ι a b)] f₂) :
    IntervalIntegrable f₁ MeasureTheory.volume a b ↔
      IntervalIntegrable f₂ MeasureTheory.volume a b := by
  constructor
  · intro hf₁
    apply IntervalIntegrable.congr hf₁
    rw [Filter.eventuallyEq_iff_exists_mem] at *
    obtain ⟨s, h₁s, h₂s⟩ := hf
    use s, ae_of_restrVol_le_codiscreteWithin measurableSet_Ioc h₁s, h₂s
  · rw [eventuallyEq_comm] at hf
    intro hf₁
    apply IntervalIntegrable.congr hf₁
    rw [Filter.eventuallyEq_iff_exists_mem] at *
    obtain ⟨s, h₁s, h₂s⟩ := hf
    use s, ae_of_restrVol_le_codiscreteWithin measurableSet_Ioc h₁s, h₂s

-- TODO: Show that preimage of codiscrete is codiscrete
/-
theorem yy {c : ℂ} {R : ℝ} :
    Filter.map (circleMap c R) (Filter.codiscrete ℝ) ≤ (Filter.codiscreteWithin (Metric.sphere c R)) := by
  intro s hs
  simp only [mem_map]
  rw [mem_codiscrete]
  intro x
  rw [disjoint_principal_right, compl_compl]
  simp_rw [mem_codiscreteWithin, disjoint_principal_right] at hs
  let y := circleMap c R x
  have hy : y ∈ Metric.sphere c R := by sorry
  let h₂y := hs y hy

  sorry
-/

/-
theorem circleIntegrable_congr_codiscreteWithin
    {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℂ} (hf : f₁ =ᶠ[Filter.codiscreteWithin (Metric.sphere c R)] f₂) :
    CircleIntegrable f₁ c R → CircleIntegrable f₂ c R := by
  apply (intervalIntegrable_congr_codiscreteWithin _).1
  rw [Filter.eventuallyEq_iff_exists_mem]
  use (circleMap c R)⁻¹' {z | f₁ z = f₂ z}, Filter.codiscreteWithin.mono (U₁ := Ι 0 (2 * π))
    (by simp) (yy hf), (by tauto)
-/

/-
theorem intervalIntegral_congr_codiscreteWithin
    {a b : ℝ} {f₁ f₂ : ℝ → ℝ} (hf : f₁ =ᶠ[Filter.codiscreteWithin (Ι a b)] f₂) :
  ∫ (x : ℝ) in a..b, f₁ x = ∫ (x : ℝ) in a..b, f₂ x := by
  apply intervalIntegral.integral_congr_ae
  sorry

theorem intervalAverage_congr_codiscreteWithin
    {a b : ℝ} {f₁ f₂ : ℝ → ℝ} (hf : f₁ =ᶠ[Filter.codiscreteWithin (Ι a b)] f₂) :
  ⨍ (x : ℝ) in a..b, f₁ x = ⨍ (x : ℝ) in a..b, f₂ x := by
  rw [interval_average_eq, intervalIntegral_congr_codiscreteWithin hf,
    ← interval_average_eq]
-/
