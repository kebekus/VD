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
  (h₁f : MeromorphicOn f U) :
  IsOpen { u : U | (h₁f u.1 u.2).order = ⊤ } := by

  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  simp at hz

  have h₁z := hz
  rw [MeromorphicAt.order_eq_top_iff] at hz
  rw [eventually_nhdsWithin_iff] at hz
  rw [eventually_nhds_iff] at hz
  obtain ⟨t', h₁t', h₂t', h₃t'⟩ := hz
  let t : Set U := Subtype.val ⁻¹' t'
  use t
  constructor
  · intro w hw
    simp
    by_cases h₁w : w = z
    · rwa [h₁w]
    · --
      rw [MeromorphicAt.order_eq_top_iff]
      rw [eventually_nhdsWithin_iff]
      rw [eventually_nhds_iff]
      use t' \ {z.1}
      constructor
      · intro y h₁y h₂y
        apply h₁t'
        exact Set.mem_of_mem_diff h₁y
        exact Set.mem_of_mem_inter_right h₁y
      · constructor
        · apply IsOpen.sdiff h₂t'
          exact isClosed_singleton
        · rw [Set.mem_diff]
          constructor
          · exact hw
          · simp
            exact Subtype.coe_ne_coe.mpr h₁w

  · constructor
    · exact isOpen_induced h₂t'
    · exact h₃t'


theorem MeromorphicOn.open_of_order_neq_top
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁f : MeromorphicOn f U) :
  IsOpen { u : U | (h₁f u.1 u.2).order ≠ ⊤ } := by

  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  simp at hz

  let A := (h₁f z.1 z.2).eventually_eq_zero_or_eventually_ne_zero
  rcases A with h|h
  · rw [← (h₁f z.1 z.2).order_eq_top_iff] at h
    tauto
  · let A := (h₁f z.1 z.2).eventually_analyticAt
    let B := Filter.Eventually.and h A
    rw [eventually_nhdsWithin_iff] at B
    rw [eventually_nhds_iff] at B
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := B
    let t : Set U := Subtype.val ⁻¹' t'
    use t
    constructor
    · intro w hw
      simp
      by_cases h₁w : w = z
      · rwa [h₁w]
      · let B := h₁t' w hw
        simp at B
        have : (w : ℂ) ≠ (z : ℂ) := by exact Subtype.coe_ne_coe.mpr h₁w
        let C := B this
        let D := C.2.order_eq_zero_iff.2 C.1
        rw [C.2.meromorphicAt_order, D]
        simp
    · constructor
      · exact isOpen_induced h₂t'
      · exact h₃t'


theorem MeromorphicOn.clopen_of_order_eq_top
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁f : MeromorphicOn f U) :
  IsClopen { u : U | (h₁f u.1 u.2).order = ⊤ } := by

  constructor
  · rw [← isOpen_compl_iff]
    exact open_of_order_neq_top h₁f
  · exact open_of_order_eq_top h₁f


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
