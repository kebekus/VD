import Mathlib.Analysis.Analytic.Meromorphic


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → 𝕜} {z₀ : 𝕜}

/-- Helper lemma for `MeromorphicAt.order_mul` -/
lemma MeromorphicAt.order_of_locallyZero_mul_meromorphic
  (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) (h'f : hf.order = ⊤) :
    (hf.mul hg).order = ⊤ := by
  rw [MeromorphicAt.order_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t⟩ := h'f
  use t
  simp
  tauto

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
