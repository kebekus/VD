import Mathlib.Analysis.Meromorphic.Order

open Filter Real Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E]

lemma A {f : 𝕜 → E} {z₀ : 𝕜} (hf : ContinuousAt f z₀)
    (h₂f : f =ᶠ[𝓝[≠] z₀] 0) :
    f z₀ = 0 := by
  by_contra h
  have := (eventually_nhdsWithin_of_eventually_nhds (hf.eventually_ne h)).and h₂f
  simp [NeBot.ne'] at this

lemma B {f g : 𝕜 → E} {z₀ : 𝕜} (hf : ContinuousAt f z₀) (hg : ContinuousAt g z₀)
    (hfg : f =ᶠ[𝓝[≠] z₀] g) :
    f z₀ = g z₀ := by
  rw [← sub_eq_zero]
  apply A (hf.sub hg)
  exact hfg.sub_eq

variable [NormedSpace 𝕜 E]

theorem ContinuousAt.y {f g : 𝕜 → E} {z₀ : 𝕜} (hf : ContinuousAt f z₀) (hg : ContinuousAt f z₀) :
    f =ᶠ[𝓝[≠] z₀] g ↔ f =ᶠ[𝓝 z₀] g := by
  constructor
  · intro h
    apply eventuallyEq_nhdsWithin_of_eventuallyEq_nhds h
    sorry
  · intro h
    apply eventuallyEq_nhdsWithin_iff.mpr
    filter_upwards [h]
    tauto

theorem MeromorphicAt.order_eq_zero_iff {f : 𝕜 → E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    hf.order = 0 ↔ (∃ g, (ContinuousAt g z₀) ∧ (g z₀ ≠ 0) ∧ f =ᶠ[𝓝[≠] z₀] g ) := by
  constructor
  · intro h₂f
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (hf.order_eq_int_iff 0).1 h₂f
    use g, h₁g.continuousAt, h₂g
    simp only [zpow_zero, one_smul] at h₃g
    exact h₃g
  · intro h₂f
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₂f
    apply (hf.order_eq_int_iff 0).2
    by_cases h₁ : hf.order = ⊤
    · rw [hf.order_eq_top_iff] at h₁
      have : ∀ᶠ (z : 𝕜) in 𝓝[≠] z₀, g z = 0 := by
        filter_upwards [h₁, h₃g]
        intro a h₁a h₂a
        rw [← h₂a, h₁a]
      have : g z₀ = 0 := by

        sorry
      tauto
    sorry
-
