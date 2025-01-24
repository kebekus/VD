import Mathlib.Analysis.Analytic.Meromorphic
import VD.analyticAt
import VD.divisor
import VD.meromorphicAt
import VD.stronglyMeromorphicOn
import VD.mathlibAddOn

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

theorem MeromorphicOn.open_of_order_eq_top
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (hf : MeromorphicOn f U) :
  IsOpen { u : U | (hf u.1 u.2).order = ⊤ } := by
  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  obtain ⟨t', h₁t', h₂t', h₃t'⟩ := (eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1
    ((hf z z.2).order_eq_top_iff.1 hz)))
  use Subtype.val ⁻¹' t'
  simp [isOpen_induced h₂t', h₃t']
  intro w hw
  simp
  -- Trivial case: w = z
  by_cases h₁w : w = z
  · rwa [h₁w]
  -- Nontrivial case: w ≠ z
  rw [MeromorphicAt.order_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
  use t' \ {z.1}
  constructor
  · exact fun y h₁y _ ↦ h₁t' y (Set.mem_of_mem_diff h₁y) (Set.mem_of_mem_inter_right h₁y)
  · constructor
    · exact h₂t'.sdiff isClosed_singleton
    · apply (Set.mem_diff w).1
      exact ⟨hw, Set.mem_singleton_iff.not.1 (Subtype.coe_ne_coe.2 h₁w)⟩

theorem MeromorphicOn.open_of_order_neq_top {f : ℂ → ℂ} {U : Set ℂ} (h₁f : MeromorphicOn f U) :
    IsOpen { u : U | (h₁f u.1 u.2).order ≠ ⊤ } := by
  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  rcases (h₁f z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
  · -- Case: f is locally zero in a punctured neighborhood of z
    rw [← (h₁f z.1 z.2).order_eq_top_iff] at h
    tauto
  · -- Case: f is locally nonzero in a punctured neighborhood of z
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1
      (h.and (h₁f z.1 z.2).eventually_analyticAt))
    use Subtype.val ⁻¹' t'
    constructor
    · intro w hw
      simp
      by_cases h₁w : w = z
      · rwa [h₁w]
      · have h₂f := (h₁t' w hw) (Subtype.coe_ne_coe.mpr h₁w)
        simp [h₂f.2.meromorphicAt_order, h₂f.2.order_eq_zero_iff.2 h₂f.1]
    · exact ⟨isOpen_induced h₂t', h₃t'⟩

theorem MeromorphicOn.clopen_of_order_eq_top {f : ℂ → ℂ} {U : Set ℂ} (h₁f : MeromorphicOn f U) :
    IsClopen { u : U | (h₁f u.1 u.2).order = ⊤ } :=
  ⟨isOpen_compl_iff.1 h₁f.open_of_order_neq_top, h₁f.open_of_order_eq_top⟩


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
