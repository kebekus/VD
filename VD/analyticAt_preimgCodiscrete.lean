import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Order.Filter.Bases
import Mathlib.Order.Filter.EventuallyConst

open Filter Topology Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}


theorem yy {x : 𝕜} {f : 𝕜 → E}
    (hf : AnalyticAt 𝕜 f x)
    (h₂f : ¬Filter.EventuallyConst f (𝓝 x)) :
    (𝓝[≠] x).map f ≤ (𝓝[≠] f x) := by
  intro s hs
  simp only [mem_map]
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

theorem zz {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f ⊤) :
    Filter.map f (Filter.codiscrete 𝕜) ≤ (Filter.codiscrete E) := by
  intro s hs
  simp only [mem_map]
  rw [mem_codiscrete]
  intro x
  rw [disjoint_principal_right, compl_compl]
  simp_rw [mem_codiscrete, disjoint_principal_right] at hs
  simp at hs
  let y := f x
  have hy : y ∈ (⊤ : Set E) := by sorry
  let h₂y := hs y

  let ZZ := yy hf h₂y
  sorry
