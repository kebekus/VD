import Mathlib.Algebra.BigOperators.Finprod
import VD.stronglyMeromorphicAt

open Topology



theorem MeromorphicOn.analyticOnCodiscreteWithin
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (hf : MeromorphicOn f U) :
  { x | AnalyticAt ℂ f x } ∈ Filter.codiscreteWithin U := by

  rw [mem_codiscreteWithin]
  intro x hx
  simp
  rw [← Filter.eventually_mem_set]
  apply Filter.Eventually.mono (hf x hx).eventually_analyticAt
  simp
  tauto


/- Strongly MeromorphicOn -/
def StronglyMeromorphicOn
  (f : ℂ → ℂ)
  (U : Set ℂ) :=
  ∀ z ∈ U, MeromorphicNFAt f z


/- Strongly MeromorphicAt is Meromorphic -/
theorem StronglyMeromorphicOn.meromorphicOn
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (hf : StronglyMeromorphicOn f U) :
  MeromorphicOn f U := by
  intro z hz
  exact MeromorphicNFAt.meromorphicAt (hf z hz)


/- Strongly MeromorphicOn of non-negative order is analytic -/
theorem StronglyMeromorphicOn.analytic
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁f : StronglyMeromorphicOn f U)
  (h₂f : ∀ x, (hx : x ∈ U) → 0 ≤ (h₁f x hx).meromorphicAt.order) :
  AnalyticOnNhd ℂ f U := by
  intro z hz
  apply MeromorphicNFAt.analyticAt
  exact h₂f z hz
  exact h₁f z hz


/- Analytic functions are strongly meromorphic -/
theorem AnalyticOn.stronglyMeromorphicOn
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁f : AnalyticOnNhd ℂ f U) :
  StronglyMeromorphicOn f U := by
  intro z hz
  apply AnalyticAt.MeromorphicNFAt
  exact h₁f z hz


theorem stronglyMeromorphicOn_of_mul_analytic'
  {f g : ℂ → ℂ}
  {U : Set ℂ}
  (h₁g : AnalyticOnNhd ℂ g U)
  (h₂g : ∀ u : U, g u ≠ 0)
  (h₁f : StronglyMeromorphicOn f U) :
  StronglyMeromorphicOn (g * f) U := by
  intro z hz
  rw [mul_comm]
  apply (MeromorphicNFAt_of_mul_analytic (h₁g z hz) ?h₂g).mp (h₁f z hz)
  exact h₂g ⟨z, hz⟩


/- Make strongly MeromorphicOn -/
noncomputable def MeromorphicOn.makeStronglyMeromorphicOn
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (hf : MeromorphicOn f U) :
  ℂ → ℂ := by
  intro z
  by_cases hz : z ∈ U
  · exact (hf z hz).makeMeromorphicNFAt z
  · exact f z


theorem makeStronglyMeromorphicOn_changeDiscrete
  {f : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  hf.makeStronglyMeromorphicOn =ᶠ[𝓝[≠] z₀] f := by
  apply Filter.eventually_iff_exists_mem.2
  let A := (hf z₀ hz₀).eventually_analyticAt
  obtain ⟨V, h₁V, h₂V⟩  := Filter.eventually_iff_exists_mem.1 A
  use V
  constructor
  · assumption
  · intro v hv
    unfold MeromorphicOn.makeStronglyMeromorphicOn
    by_cases h₂v : v ∈ U
    · simp [h₂v]
      rw [← MeromorphicNFAt.makeStronglyMeromorphic_id]
      exact AnalyticAt.MeromorphicNFAt (h₂V v hv)
    · simp [h₂v]


theorem makeStronglyMeromorphicOn_changeDiscrete'
  {f : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  hf.makeStronglyMeromorphicOn =ᶠ[𝓝 z₀] (hf z₀ hz₀).makeMeromorphicNFAt := by
  apply Mnhds
  · apply Filter.EventuallyEq.trans (makeStronglyMeromorphicOn_changeDiscrete hf hz₀)
    exact m₂ (hf z₀ hz₀)
  · rw [MeromorphicOn.makeStronglyMeromorphicOn]
    simp [hz₀]


theorem makeStronglyMeromorphicOn_changeDiscrete''
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (hf : MeromorphicOn f U) :
  f =ᶠ[Filter.codiscreteWithin U] hf.makeStronglyMeromorphicOn := by

  rw [Filter.eventuallyEq_iff_exists_mem]
  use { x | AnalyticAt ℂ f x }
  constructor
  · exact MeromorphicOn.analyticOnCodiscreteWithin hf
  · intro x hx
    simp at hx
    rw [MeromorphicOn.makeStronglyMeromorphicOn]
    by_cases h₁x : x ∈ U
    · simp [h₁x]
      rw [← MeromorphicNFAt.makeStronglyMeromorphic_id hx.MeromorphicNFAt]
    · simp [h₁x]


theorem stronglyMeromorphicOn_of_makeStronglyMeromorphicOn
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (hf : MeromorphicOn f U) :
  StronglyMeromorphicOn hf.makeStronglyMeromorphicOn U := by
  intro z hz
  let A := makeStronglyMeromorphicOn_changeDiscrete' hf hz
  rw [meromorphicNFAt_congr A]
  exact MeromorphicNFAt_of_makeStronglyMeromorphic (hf z hz)


theorem makeStronglyMeromorphicOn_changeOrder
  {f : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
  (hf : MeromorphicOn f U)
  (hz₀ : z₀ ∈ U) :
  (stronglyMeromorphicOn_of_makeStronglyMeromorphicOn hf z₀ hz₀).meromorphicAt.order = (hf z₀ hz₀).order := by
  apply MeromorphicAt.order_congr
  exact makeStronglyMeromorphicOn_changeDiscrete hf hz₀
