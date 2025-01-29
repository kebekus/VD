import Mathlib.Analysis.Analytic.Meromorphic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → 𝕜} {z₀ : 𝕜}

open Topology


/- A meromorphic function either vanishes everywhere or vanishes nowhere in a
punctured neighborhood of any given point. -/
theorem MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero {f : 𝕜 → E} (hf : MeromorphicAt f z₀) :
    (∀ᶠ z in 𝓝[≠] z₀, f z = 0) ∨ (∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0) := by
  obtain ⟨n, h⟩ := hf
  repeat rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
  rcases h.eventually_eq_zero_or_eventually_ne_zero with h₁ | h₂
  · obtain ⟨N, h₁N, h₂N, h₃N⟩ := eventually_nhds_iff.1 h₁
    left
    use N
    simp [h₂N, h₃N]
    intro y h₁y h₂y
    have A := h₁N y h₁y
    simp at A
    rcases A with h₃ | h₄
    · have C := sub_eq_zero.1 h₃.1
      tauto
    · assumption
  · obtain ⟨N, h₁N, h₂N, h₃N⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h₂)
    right
    use N
    simp [h₂N, h₃N]
    intro y h₁y h₂y
    by_contra h
    have A := h₁N y h₁y h₂y
    simp [h] at A
