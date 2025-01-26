import Mathlib.Analysis.Analytic.Meromorphic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → 𝕜} {z₀ : 𝕜}

open Topology

/-- Helper lemma for `MeromorphicAt.order_mul` -/
lemma MeromorphicAt.order_of_locallyZero_mul_meromorphic (hf : MeromorphicAt f z₀)
    (hg : MeromorphicAt g z₀) (h'f : hf.order = ⊤) :
    (hf.mul hg).order = ⊤ := by
  rw [MeromorphicAt.order_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t⟩ := h'f
  use t, fun y h₁y h₂y ↦ (by rw [Pi.mul_apply, h₁t y h₁y h₂y, zero_mul])

/-- The order is additive when multiplying meromorphic functions -/
theorem MeromorphicAt.order_mul (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) :
    (hf.mul hg).order = hf.order + hg.order := by
  -- Trivial cases: one of the functions vanishes around z₀
  by_cases h₂f : hf.order = ⊤
  · simp [hf.order_of_locallyZero_mul_meromorphic hg, h₂f]
  by_cases h₂g : hg.order = ⊤
  · simp [mul_comm f g, hg.order_of_locallyZero_mul_meromorphic hf, h₂g]
  -- Non-trivial case: both functions do not vanish around z₀
  have h₃f := (hf.order.coe_untop h₂f).symm
  have h₃g := (hg.order.coe_untop h₂g).symm
  rw [h₃f, h₃g, ← WithTop.coe_add, MeromorphicAt.order_eq_int_iff]
  obtain ⟨F, h₁F, h₂F, h₃F⟩ := (hf.order_eq_int_iff (hf.order.untop h₂f)).1 h₃f
  obtain ⟨G, h₁G, h₂G, h₃G⟩ := (hg.order_eq_int_iff (hg.order.untop h₂g)).1 h₃g
  clear h₃f h₃g
  use F * G, h₁F.mul h₁G, by simp; tauto
  rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at *
  obtain ⟨s, h₁s, h₂s, h₃s⟩ := h₃F
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := h₃G
  use s ∩ t
  constructor
  · intro y h₁y h₂y
    simp [h₁s y h₁y.1 h₂y, h₁t y h₁y.2 h₂y, zpow_add' (by left; exact sub_ne_zero_of_ne h₂y)]
    group
  · exact ⟨IsOpen.inter h₂s h₂t, Set.mem_inter h₃s h₃t⟩

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
