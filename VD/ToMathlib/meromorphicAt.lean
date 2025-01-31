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
  rcases h.eventually_eq_zero_or_eventually_ne_zero with h₁ | h₂
  · left
    filter_upwards [nhdsWithin_le_nhds h₁, self_mem_nhdsWithin] with y h₁y h₂y
    rcases (smul_eq_zero.1 h₁y) with h₃ | h₄
    · exact False.elim (h₂y (sub_eq_zero.1 (pow_eq_zero_iff'.1 h₃).1))
    · assumption
  · right
    filter_upwards [h₂, self_mem_nhdsWithin] with y h₁y h₂y
    exact (smul_ne_zero_iff.1 h₁y).2
