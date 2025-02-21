import Mathlib.Topology.DiscreteSubset
import VD.ToMathlib.codiscreteWithin

open Filter Set Topology

/-- In a T1Space, punctured neighborhoods are stable under removing finite sets
of points. -/
theorem punctNhd_of_punctNhd_diff_finite {X : Type*} [TopologicalSpace X] [T1Space X]
    {x : X} {U s : Set X} (hU : U ∈ 𝓝[≠] x) (hs : Finite s) :
    U \ s ∈ 𝓝[≠] x := by
  rw [mem_nhdsWithin] at hU ⊢
  obtain ⟨t, ht, h₁ts, h₂ts⟩ := hU
  use t \ (s \ {x})
  constructor
  · rw [← isClosed_compl_iff, compl_diff]
    exact hs.diff.isClosed.union (isClosed_compl_iff.2 ht)
  · simp_all only [mem_diff, mem_singleton_iff, not_true_eq_false, and_false, not_false_eq_true,
      and_self, true_and]
    intro z hz
    simp_all only [mem_inter_iff, mem_diff, mem_singleton_iff, not_and, not_not, mem_compl_iff]
    tauto

/-- Helper lemma for `codiscreteWithin_iff_locallyFiniteComplementWithinU`: A
set `s` is codiscreteWithin `U` iff every point `z ∈ U` has
a punctured neighborhood that does not intersect `U \ s`. -/
lemma codiscreteWithin_iff_locallyEmptyComplementWithinU {X : Type*} [TopologicalSpace X]
    {U s : Set X} :
    (s ∈ codiscreteWithin U) ↔ (∀ z ∈ U, ∃ t ∈ 𝓝[≠] z, t ∩ (U \ s) = ∅) := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right]
  constructor
  · intro h z h₁z
    use (U \ s)ᶜ, (h z h₁z)
    simp
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    rw [← exists_mem_subset_iff]
    use t, h₁t, fun _ h₁x ↦ (disjoint_left.1 (disjoint_iff_inter_eq_empty.2 h₂t)) h₁x

/-- In a T1Space, a set `s` is codiscreteWithin `U` iff it has locally finite
complement within `U`. More precisely: `s` is codiscreteWithin `U` iff every
point `z ∈ U` has a punctured neighborhood intersect `U \ s` in only finitely
many points. -/
theorem codiscreteWithin_iff_locallyFiniteComplementWithin {X : Type*} [TopologicalSpace X] [T1Space X]
    {U s : Set X} :
    (s ∈ codiscreteWithin U) ↔ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ (U \ s)) := by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithinU]
  constructor
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    use insert z t, insert_mem_nhds_iff.mpr h₁t
    by_cases hz : z ∈ U \ s
    · rw [inter_comm, inter_insert_of_mem hz, inter_comm, h₂t]
      simp
    · rw [inter_comm, inter_insert_of_not_mem hz, inter_comm, h₂t]
      simp
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    use t \ (t ∩ (U \ s)), punctNhd_of_punctNhd_diff_finite (mem_nhdsWithin_of_mem_nhds h₁t) h₂t
    simp

/-- If `U` is closed and `s` is codiscrete within `U`, then `U \ s` is closed.-/
theorem closed_compl_of_codiscreteWithin {X : Type u_1} [TopologicalSpace X]
    {U s : Set X} (hs : s ∈ codiscreteWithin U) (hU : IsClosed U) :
    IsClosed (U \ s) := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually]
  intro x hx
  by_cases h₁x : x ∈ U
  · rw [mem_codiscreteWithin] at hs
    filter_upwards [eventually_nhdsWithin_iff.1 (disjoint_principal_right.1 (hs x h₁x))]
    intro a ha
    by_cases h₂a : a = x
    · simp [hx, h₂a]
    · have W := ha h₂a
      simp only [mem_diff, not_and, not_not] at W
      by_cases h₃a : a ∈ U
      · tauto
      · by_contra hCon
        tauto
  · rw [eventually_iff_exists_mem]
    use Uᶜ, hU.compl_mem_nhds h₁x
    intro y hy
    simp only [mem_compl_iff, mem_diff, not_and, not_not]
    tauto
