import Mathlib.Topology.DiscreteSubset
import VD.ToMathlib.codiscreteWithin

open Filter Set Topology

/-- A set `s` is codiscreteWithin `U` iff it has locally finite complement
  within `U`. More precisely: `s` is codiscreteWithin `U` iff every point
  `z ∈ U` has a punctured neighborhood that does not intersect `U \ s`. -/
theorem codiscreteWithin_iff_locallyFiniteComplementWithinU {X : Type u_1} [TopologicalSpace X]
    {U s : Set X} :
    (s ∈ Filter.codiscreteWithin U) ↔ (∀ z ∈ U, ∃ t ∈ 𝓝[≠] z, t ∩ (U \ s) = ∅) := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right]
  constructor
  · intro h z h₁z
    use (U \ s)ᶜ, (h z h₁z)
    simp
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    rw [← exists_mem_subset_iff]
    use t, h₁t, fun _ h₁x ↦ (disjoint_left.1 (disjoint_iff_inter_eq_empty.2 h₂t)) h₁x

lemma xx {X : Type u_1} [TopologicalSpace X] [T1Space X]
    {x : X} {U s : Set X} (hU : U ∈ 𝓝[≠] x) (hs : Set.Finite s) :
    U \ s ∈ 𝓝[≠] x := by
  rw [mem_nhdsWithin] at hU ⊢
  obtain ⟨t, ht, h₁ts, h₂ts⟩ := hU
  use t \ (s \ {x})
  constructor
  · rw [← isClosed_compl_iff]
    rw [Set.compl_diff]
    apply IsClosed.union
    · apply Finite.isClosed
      exact Finite.diff hs
    · exact isClosed_compl_iff.mpr ht
  · constructor
    · simp [h₁ts]
    · intro z hz
      constructor
      · apply h₂ts
        simp [hz]
        simp at hz
        tauto
      · simp at hz
        tauto

theorem codiscreteWithin_iff_locallyFiniteComplementWithinU' {X : Type u_1} [TopologicalSpace X] [T1Space X]
    {U s : Set X} :
    (s ∈ Filter.codiscreteWithin U) ↔ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ (U \ s)) := by
  rw [codiscreteWithin_iff_locallyFiniteComplementWithinU]
  constructor
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    use insert z t
    constructor
    · exact insert_mem_nhds_iff.mpr h₁t
    · by_cases hz : z ∈ U \ s
      · rw [inter_comm, inter_insert_of_mem hz, inter_comm, h₂t]
        simp
      · rw [inter_comm, inter_insert_of_not_mem hz, inter_comm, h₂t]
        simp
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    use t \ (t ∩ (U \ s))
    constructor
    · apply xx
      exact mem_nhdsWithin_of_mem_nhds h₁t
      exact h₂t
    · simp
