import Mathlib.Topology.DiscreteSubset

theorem codiscreteWithin_congr_inter
    {X : Type u_1} [TopologicalSpace X]
    {S T U : Set X}
    (hST : S ∩ U = T ∩ U) :
    S ∈ Filter.codiscreteWithin U ↔ T ∈ Filter.codiscreteWithin U := by
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
  rw [← Filter.mem_iff_inf_principal_compl, (by ext z; simp; tauto : s ∪ Uᶜ = (U \ s)ᶜ)]
  simp_all only [h x, Set.compl_union, compl_compl, Set.mem_inter_iff, Set.mem_compl_iff]
