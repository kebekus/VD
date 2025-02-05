import Init.Classical
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.Analytic.IsolatedZeros
import VD.leftovers.holomorphic
import VD.leftovers.analyticOnNhd_zeroSet


noncomputable def zeroDivisor
  (f : ℂ → ℂ) :
  ℂ → ℕ := by
  intro z
  by_cases hf : AnalyticAt ℂ f z
  · exact hf.order.toNat
  · exact 0


theorem analyticAtZeroDivisorSupport
  {f : ℂ → ℂ}
  {z : ℂ}
  (h : z ∈ Function.support (zeroDivisor f)) :
  AnalyticAt ℂ f z := by

  by_contra h₁f
  simp at h
  dsimp [zeroDivisor] at h
  simp [h₁f] at h


theorem zeroDivisor_eq_ord_AtZeroDivisorSupport
  {f : ℂ → ℂ}
  {z : ℂ}
  (h : z ∈ Function.support (zeroDivisor f)) :
  zeroDivisor f z = (analyticAtZeroDivisorSupport h).order.toNat := by

  unfold zeroDivisor
  simp [analyticAtZeroDivisorSupport h]



lemma toNatEqSelf_iff {n : ℕ∞} : n.toNat = n ↔ ∃ m : ℕ, m = n := by
  constructor
  · intro H₁
    rw [← ENat.some_eq_coe, ← WithTop.ne_top_iff_exists]
    by_contra H₂
    rw [H₂] at H₁
    simp at H₁
  · intro H
    obtain ⟨m, hm⟩ := H
    rw [← hm]
    simp


lemma natural_if_toNatNeZero {n : ℕ∞} : n.toNat ≠ 0 → ∃ m : ℕ, m = n := by
  rw [← ENat.some_eq_coe, ← WithTop.ne_top_iff_exists]
  contrapose; simp; tauto


theorem zeroDivisor_localDescription
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (h : z₀ ∈ Function.support (zeroDivisor f)) :
  ∃ (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ (z : ℂ) in nhds z₀, f z = (z - z₀) ^ (zeroDivisor f z₀) • g z := by

  have A : zeroDivisor f ↑z₀ ≠ 0 := by exact h
  let B := zeroDivisor_eq_ord_AtZeroDivisorSupport h
  rw [B] at A
  have C := natural_if_toNatNeZero A
  obtain ⟨m, hm⟩ := C
  have h₂m : m ≠ 0 := by
    rw [← hm] at A
    simp at A
    assumption
  rw [eq_comm] at hm
  let E := AnalyticAt.order_eq_nat_iff (analyticAtZeroDivisorSupport h) m
  let F := hm
  rw [E] at F

  have : m = zeroDivisor f z₀ := by
    rw [B, hm]
    simp
  rwa [this] at F


theorem zeroDivisor_zeroSet
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (h : z₀ ∈ Function.support (zeroDivisor f)) :
  f z₀ = 0 := by
  obtain ⟨g, _, _, h₃⟩ := zeroDivisor_localDescription h
  rw [Filter.Eventually.self_of_nhds h₃]
  simp
  left
  exact h


theorem zeroDivisor_support_iff
  {f : ℂ → ℂ}
  {z₀ : ℂ} :
  z₀ ∈ Function.support (zeroDivisor f) ↔
  f z₀ = 0 ∧
  AnalyticAt ℂ f z₀ ∧
  ∃ (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ (z : ℂ) in nhds z₀, f z = (z - z₀) ^ (zeroDivisor f z₀) • g z := by
  constructor
  · intro hz
    constructor
    · exact zeroDivisor_zeroSet hz
    · constructor
      · exact analyticAtZeroDivisorSupport hz
      · exact zeroDivisor_localDescription hz
  · intro ⟨h₁, h₂, h₃⟩
    have : zeroDivisor f z₀ = (h₂.order).toNat := by
      unfold zeroDivisor
      simp [h₂]
    simp [this]
    simp [(h₂.order_eq_nat_iff (zeroDivisor f z₀)).2 h₃]
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₃
    rw [Filter.Eventually.self_of_nhds h₃g] at h₁
    simp [h₂g] at h₁
    assumption


theorem topOnPreconnected
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (hU : IsPreconnected U)
  (h₁f : AnalyticOnNhd ℂ f U)
  (h₂f : ∃ z ∈ U, f z ≠ 0) :
  ∀ (hz : z ∈ U), (h₁f z hz).order ≠ ⊤ := by

  by_contra H
  push_neg at H
  obtain ⟨z', hz'⟩ := H
  rw [AnalyticAt.order_eq_top_iff] at hz'
  rw [← AnalyticAt.frequently_zero_iff_eventually_zero (h₁f z z')] at hz'
  have A := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero h₁f hU z' hz'
  tauto


theorem supportZeroSet
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (hU : IsPreconnected U)
  (h₁f : AnalyticOnNhd ℂ f U)
  (h₂f : ∃ z ∈ U, f z ≠ 0) :
  U ∩ Function.support (zeroDivisor f) = U ∩ f⁻¹' {0} := by

  ext x
  constructor
  · intro hx
    constructor
    · exact hx.1
    exact zeroDivisor_zeroSet hx.2
  · simp
    intro h₁x h₂x
    constructor
    · exact h₁x
    · let A := zeroDivisor_support_iff (f := f) (z₀ := x)
      simp at A
      rw [A]
      constructor
      · exact h₂x
      · constructor
        · exact h₁f x h₁x
        · have B := AnalyticAt.order_eq_nat_iff (h₁f x h₁x) (zeroDivisor f x)
          simp at B
          rw [← B]
          dsimp [zeroDivisor]
          simp [h₁f x h₁x]
          refine Eq.symm (ENat.coe_toNat ?h.mpr.right.right.right.a)
          exact topOnPreconnected hU h₁f h₂f h₁x
