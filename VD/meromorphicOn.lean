import Mathlib.Analysis.Analytic.Meromorphic
import VD.analyticAt
import VD.divisor
import VD.meromorphicAt
import VD.stronglyMeromorphicOn
import VD.mathlibAddOn
import VD.ToMathlib.meromorphicOn

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

theorem MeromorphicOn.order_ne_top'
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁f : MeromorphicOn f U)
  (hU : IsConnected U) :
  (∃ u : U, (h₁f u u.2).order ≠ ⊤) ↔ (∀ u : U, (h₁f u u.2).order ≠ ⊤) := by

  constructor
  · intro h₂f
    let A := h₁f.clopen_of_order_eq_top
    have : PreconnectedSpace U := by
      apply isPreconnected_iff_preconnectedSpace.mp
      exact IsConnected.isPreconnected hU
    rw [isClopen_iff] at A
    rcases A with h|h
    · intro u
      have : u ∉ (∅ : Set U) := by exact fun a => a
      rw [← h] at this
      simp at this
      tauto
    · obtain ⟨u, hU⟩ := h₂f
      have A : u ∈ Set.univ := by trivial
      rw [← h] at A
      simp at A
      tauto
  · intro h₂f
    let A := hU.nonempty
    obtain ⟨v, hv⟩ := A
    use ⟨v, hv⟩
    exact h₂f ⟨v, hv⟩


theorem StronglyMeromorphicOn.order_ne_top
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁f : StronglyMeromorphicOn f U)
  (hU : IsConnected U)
  (h₂f : ∃ u : U, f u ≠ 0) :
  ∀ u : U, (h₁f u u.2).meromorphicAt.order ≠ ⊤ := by

  rw [← h₁f.meromorphicOn.order_ne_top' hU]
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

  let A := h₁f.order_ne_top' h₁U
  rw [← not_iff_not] at A
  push_neg at A
  have B := A.2 this
  obtain ⟨u, hu⟩ := h₂f
  tauto
