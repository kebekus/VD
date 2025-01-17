import Mathlib.Topology.DiscreteSubset

theorem codiscreteWithin_congr
  {X : Type u_1} [TopologicalSpace X]
  {S T U : Set X}
  (hST : S ∩ U = T ∩ U) :
  S ∈ Filter.codiscreteWithin U ↔ T ∈ Filter.codiscreteWithin U := by
  rw [mem_codiscreteWithin, mem_codiscreteWithin, ← Set.diff_inter_self_eq_diff, hST, Set.diff_inter_self_eq_diff]
