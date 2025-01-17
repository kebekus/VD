import Mathlib.Analysis.Analytic.IsolatedZeros

open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}

/- An analytic function has order zero at a point iff it does not vanish there. -/
theorem AnalyticAt.order_eq_zero_iff (hf : AnalyticAt 𝕜 f z₀) :
    hf.order = 0 ↔ f z₀ ≠ 0 := by
  rw [(by rfl : (0 : ENat) = (0 : Nat)), AnalyticAt.order_eq_nat_iff hf 0]
  constructor
  · intro ⟨g, _, _, hg⟩; simpa [Filter.Eventually.self_of_nhds hg]
  · intro hz; use f; exact ⟨hf, hz, by simp⟩


/- An analytic function `f` has finite order at a point `z₀` iff locally looks
  like `(z - z₀) ^ order • g`, where `g` is analytic and does not vanish at
  `z₀`. -/
theorem AnalyticAt.order_neq_top_iff (hf : AnalyticAt 𝕜 f z₀) :
    hf.order ≠ ⊤ ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0
      ∧ f =ᶠ[𝓝 z₀] fun z ↦ (z - z₀) ^ (hf.order.toNat) • g z := by
  erw [← hf.order_eq_nat_iff]
  exact ⟨fun h₁f ↦ (ENat.coe_toNat h₁f).symm, fun h₁f ↦ ENat.coe_toNat_eq_self.mp h₁f.symm ⟩
