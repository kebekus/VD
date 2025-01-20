import Mathlib.Analysis.Analytic.IsolatedZeros

open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}

/-- Helper lemma for `AnalyticAt.order_mul` -/
lemma AnalyticAt.order_of_locallyZero_mul_analytic {f g : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f z₀)
  (hg : AnalyticAt 𝕜 g z₀) (h'f : hf.order = ⊤) :
    (hf.mul hg).order = ⊤ := by
  rw [AnalyticAt.order_eq_top_iff, eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := h'f
  exact ⟨t, fun y hy ↦ (by rw [h₁t y hy]; ring), h₂t, h₃t⟩

/-- The order is additive when multiplying analytic functions -/
theorem AnalyticAt.order_mul {f g : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (hf.mul hg).order = hf.order + hg.order := by
  -- Trivial cases: one of the functions vanishes around z₀
  by_cases h₂f : hf.order = ⊤
  · simp [hf.order_of_locallyZero_mul_analytic hg h₂f, h₂f]
  by_cases h₂g : hg.order = ⊤
  · have : (fun x ↦ f x * g x) = (fun x ↦ g x * f x) := by simp_rw [mul_comm]
    simp [this, hg.order_of_locallyZero_mul_analytic hf h₂g, h₂g]

  -- Non-trivial case: both functions do not vanish around z₀
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := hf.order_neq_top_iff.1 h₂f
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := hg.order_neq_top_iff.1 h₂g
  rw [← ENat.coe_toNat h₂f, ← ENat.coe_toNat h₂g, ← ENat.coe_add, (hf.mul hg).order_eq_nat_iff]
  use g₁ * g₂
  constructor
  · exact h₁g₁.mul h₁g₂
  · constructor
    · simp
      tauto
    · obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 h₃g₁
      obtain ⟨s, h₁s, h₂s, h₃s⟩ := eventually_nhds_iff.1 h₃g₂
      exact eventually_nhds_iff.2
        ⟨t ∩ s, fun y hy ↦ (by rw [h₁t y hy.1, h₁s y hy.2]; simp; ring), h₂t.inter h₂s, h₃t, h₃s⟩

/-- The order multiplies by `n` when taking an analytic function to its `n`th power -/
theorem AnalyticAt.order_pow {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f z₀) {n : ℕ} :
    (hf.pow n).order = n * hf.order := by
  induction' n with n hn
  · simp [AnalyticAt.order_eq_zero_iff]
  · simp [add_mul, pow_add, (hf.pow n).order_mul hf, hn]
