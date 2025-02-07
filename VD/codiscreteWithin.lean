import Mathlib.Topology.DiscreteSubset

--
theorem Set.compl_diff {α : Type u} {s t : Set α} : (t \ s)ᶜ = s ∪ tᶜ := by
  ext z
  rw [mem_compl_iff, mem_diff, not_and, not_not, mem_union]
  tauto
--

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

/-- If a set is codiscrete with `U`, then it is codiscrete within any subset of `U`. -/
theorem Filter.codiscreteWithin.mono {X : Type u_1} [TopologicalSpace X] {U₁ U₂ : Set X}
    (hU : U₁ ⊆ U₂) :
    (Filter.codiscreteWithin U₁) ≤ (Filter.codiscreteWithin U₂) := by
  intro s hs
  simp_rw [mem_codiscreteWithin, disjoint_principal_right] at hs ⊢
  exact fun x hx ↦ mem_of_superset (hs x (hU hx)) (Set.compl_subset_compl.2 (fun y hy ↦ ⟨hU hy.1, hy.2⟩))
