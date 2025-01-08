import Mathlib.Topology.DiscreteSubset

theorem codiscreteWithin_congr
  {X : Type u_1} [TopologicalSpace X]
  {S T U : Set X}
  (hST : S ∩ U = T ∩ U) :
  S ∈ Filter.codiscreteWithin U ↔ T ∈ Filter.codiscreteWithin U := by
  repeat rw [mem_codiscreteWithin]
  rw [← Set.diff_inter_self_eq_diff (t := S)]
  rw [← Set.diff_inter_self_eq_diff (t := T)]
  rw [hST]
