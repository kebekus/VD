import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Order.Filter.Bases
import Mathlib.Order.Filter.EventuallyConst
import VD.codiscreteWithin

open Filter Topology Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}

/-- Preimages of codiscrete sets, local version: if `f` is analytic at `x` and
  not locally constant, then the preimage of any punctured neighbourhood of
  `f x` is a punctured neighbourhood of `x`. -/
theorem AnalyticAt.preimg_of_puncNhd {x : 𝕜} {f : 𝕜 → E} {s : Set E} (hf : AnalyticAt 𝕜 f x)
    (h₂f : ¬Filter.EventuallyConst f (𝓝 x)) (hs : s ∈ 𝓝[≠] f x) :
    f ⁻¹' s ∈ 𝓝[≠] x := by
  have : insert (f x) s ∈ 𝓝 (f x) := by
    rw [mem_nhds_iff]
    obtain ⟨u, h₁u, h₂u, h₃u⟩ := mem_nhdsWithin.1 hs
    use u
    tauto
  have : ∀ᶠ (z : 𝕜) in 𝓝 x, f z ∈ insert (f x) s := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds this]
    tauto
  have : ∀ᶠ (z : 𝕜) in 𝓝[≠] x, f z ∈ insert (f x) s := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [this]
    intro a
    tauto
  by_contra h
  erw [Filter.not_eventually] at h
  have ZZ := Filter.Frequently.and_eventually h this
  have A : ∀ z, f z ∉ s ∧ f z ∈ insert (f x) s → f z = f x := by
    intro z ⟨h₁z, h₂z⟩
    rw [Set.mem_insert_iff] at h₂z
    tauto
  have ZZ' := ZZ.mono A
  rw [hf.frequently_eq_iff_eventually_eq] at ZZ'
  have : Filter.EventuallyConst f (𝓝 x) := by
    rw [Filter.eventuallyConst_iff_exists_eventuallyEq]
    use f x
    exact ZZ'
  tauto
  fun_prop

/-- Preimages of codiscrete sets, local filter version: if `f` is analytic at
  `x` and not locally constant, then the push-forward of the punctured
  neighbourhood filter `𝓝[≠] x` is less than or equal to the punctured
  neighbourhood filter `𝓝[≠] f x`. -/
theorem AnalyticAt.map_of_puncNhdFilter {x : 𝕜} {f : 𝕜 → E} (hf : AnalyticAt 𝕜 f x)
    (h₂f : ¬Filter.EventuallyConst f (𝓝 x)) :
    (𝓝[≠] x).map f ≤ (𝓝[≠] f x) := fun _ hs ↦ mem_map.1 (preimg_of_puncNhd hf h₂f hs)

/-- Preimages of codiscrete sets: if `f` is analytic on a neighbourhood of `U`
  and not locally constant, then the preimage of any subset that codiscrete within `f '' U`
  is codiscrete within `U`.

  Applications will almost certainly employ the theorem `Filter.codiscreteWithin.mono`.
-/
theorem AnalyticOnNhd.preimg_codiscrete {U : Set 𝕜} {s : Set E} {f : 𝕜 → E}
    (hf : AnalyticOnNhd 𝕜 f U) (h₂f : ∀ x ∈ U, ¬EventuallyConst f (𝓝 x)) (hs : s ∈ codiscreteWithin (f '' U)):
    f ⁻¹' s ∈ codiscreteWithin U := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right, Set.compl_diff] at *
  intro x hx
  let A := (hf x hx).preimg_of_puncNhd (h₂f x hx) (hs (f x) (by tauto))
  have : f ⁻¹' (s ∪ (f '' U)ᶜ) ⊆  f ⁻¹' s ∪ Uᶜ := by
    rw [preimage_union, preimage_compl]
    refine union_subset_union_right (f ⁻¹' s) ?_
    intro x hx
    simp_all
    tauto
  exact mem_of_superset A this

/-- Preimages of codiscrete sets, filter version: if `f` is analytic on a neighbourhood of `U`
  and not locally constant, then the push-forward of the filter of sets codiscrete within `U` is
  less than or equal to the filter of sets codiscrete within `f '' U`.

  Applications will almost certainly employ the theorem `Filter.codiscreteWithin.mono`.
-/
theorem AnalyticOnNhd.map_of_codiscreteWithinFilter {U : Set 𝕜} {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U)
    (h₂f : ∀ x ∈ U, ¬EventuallyConst f (𝓝 x)) :
    Filter.map f (Filter.codiscreteWithin U) ≤ (Filter.codiscreteWithin (f '' U)) :=
  fun _ hs ↦ mem_map.1 (preimg_codiscrete hf h₂f hs)
