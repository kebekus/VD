import Mathlib.Topology.DiscreteSubset


/-- Codiscreteness within `U` depends only on the intersection with `U`. -/
theorem codiscreteWithin_congr_inter
    {X : Type u_1} [TopologicalSpace X]
    {S₁ S₂ U : Set X}
    (hST : S₁ ∩ U = S₂ ∩ U) :
    S₁ ∈ Filter.codiscreteWithin U ↔ S₂ ∈ Filter.codiscreteWithin U := by
  rw [mem_codiscreteWithin, mem_codiscreteWithin, ← Set.diff_inter_self_eq_diff, hST,
    Set.diff_inter_self_eq_diff]

theorem discreteTopology_of_codiscreteWithin
    {X : Type u_1} [TopologicalSpace X]
    {U s : Set X}
    (h: s ∈ Filter.codiscreteWithin U) :
  DiscreteTopology ((sᶜ ∩ U) : Set X) := by
  rw [(by simp : ((sᶜ ∩ U) : Set X) = ((s ∪ Uᶜ)ᶜ : Set X)), discreteTopology_subtype_iff]
  simp_rw [mem_codiscreteWithin, Filter.disjoint_principal_right] at h
  intro x hx
  rw [← Filter.mem_iff_inf_principal_compl, ← Set.compl_diff]
  simp_all only [h x, Set.compl_union, compl_compl, Set.mem_inter_iff, Set.mem_compl_iff]
