import VD.divisor
import VD.meromorphicAt
import VD.stronglyMeromorphicOn
import VD.mathlibAddOn

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral


theorem StronglyMeromorphicOn.order_ne_top
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁f : StronglyMeromorphicOn f U)
  (hU : IsConnected U)
  (h₂f : ∃ u : U, f u ≠ 0) :
  ∀ u : U, (h₁f u u.2).meromorphicAt.order ≠ ⊤ := by

  rw [← h₁f.meromorphicOn.exists_order_ne_top_iff_forall hU]
  obtain ⟨u, hu⟩ := h₂f
  use u
  rw [← (h₁f u u.2).order_eq_zero_iff] at hu
  rw [hu]
  simp


theorem MeromorphicOn.nonvanish_of_order_ne_top
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁f : MeromorphicOn f U)
  (h₂f : ∃ u : U, (h₁f u u.2).order ≠ ⊤)
  (h₁U : IsConnected U)
  (h₂U : interior U ≠ ∅) :
  ∃ u ∈ U, f u ≠ 0 := by

  by_contra hCon
  push_neg at hCon

  have : ∃ u : U, (h₁f u u.2).order = ⊤ := by
    obtain ⟨v, h₁v⟩ := Set.nonempty_iff_ne_empty'.2 h₂U
    have h₂v : v ∈ U := by apply interior_subset h₁v
    use ⟨v, h₂v⟩
    rw [MeromorphicAt.order_eq_top_iff]
    rw [eventually_nhdsWithin_iff]
    rw [eventually_nhds_iff]
    use interior U
    constructor
    · intro y h₁y h₂y
      exact hCon y (interior_subset h₁y)
    · simp [h₁v]

  let A := h₁f.exists_order_ne_top_iff_forall h₁U
  rw [← not_iff_not] at A
  push_neg at A
  have B := A.2 this
  obtain ⟨u, hu⟩ := h₂f
  tauto
