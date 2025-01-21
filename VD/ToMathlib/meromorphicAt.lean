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
  simp [h₂t]
  tauto

/-- The order is additive when multiplying meromorphic functions -/
theorem MeromorphicAt.order_mul
  (hf : MeromorphicAt f z₀)
  (hg : MeromorphicAt g z₀) :
  (hf.mul hg).order = hf.order + hg.order := by
  -- Trivial cases: one of the functions vanishes around z₀
  by_cases h₂f : hf.order = ⊤
  · simp [hf.order_of_locallyZero_mul_meromorphic hg h₂f, h₂f]
  by_cases h₂g : hg.order = ⊤
  · have : f * g = g * f := by simp_rw [mul_comm]
    simp [this, hg.order_of_locallyZero_mul_meromorphic hf h₂g, h₂g]

  -- Non-trivial case: both functions do not vanish around z₀
  have h₃f₁ := (WithTop.coe_untop hf.order h₂f).symm
  have h₃f₂ := (WithTop.coe_untop hg.order h₂g).symm
  obtain ⟨F, h₁F, h₂F, h₃F⟩ := (hf.order_eq_int_iff (hf.order.untop h₂f)).1 h₃f₁
  obtain ⟨G, h₁G, h₂G, h₃G⟩ := (hg.order_eq_int_iff (hg.order.untop h₂g)).1 h₃f₂
  rw [h₃f₁, h₃f₂, ← WithTop.coe_add, MeromorphicAt.order_eq_int_iff]
  use F * G, h₁F.mul h₁G
  constructor
  · simp; tauto
  · rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at *
    obtain ⟨t₁, h₁t₁, h₂t₁, h₃t₁⟩ := h₃F
    obtain ⟨t₂, h₁t₂, h₂t₂, h₃t₂⟩ := h₃G
    use t₁ ∩ t₂
    constructor
    · intro y h₁y h₂y
      simp [h₁t₁ y h₁y.1 h₂y, h₁t₂ y h₁y.2 h₂y, zpow_add' (by left; exact sub_ne_zero_of_ne h₂y)]
      group
    · exact ⟨IsOpen.inter h₂t₁ h₂t₂, Set.mem_inter h₃t₁ h₃t₂⟩


/-- The order multiplies by `n` when taking an analytic function to its `n`th power -/
theorem MeromorphicAt.order_pow (hf : MeromorphicAt f z₀) {n : ℕ} :
    (hf.pow n).order = n * hf.order := by
  induction' n with n hn
  · simp [AnalyticAt.order_eq_zero_iff]
  · simp [add_mul, pow_add, (hf.pow n).order_mul hf, hn]


-- TODO: `order_zpow` is not yet ported to mathlib

-- TODO: `order_inv` is not yet ported to mathlib
