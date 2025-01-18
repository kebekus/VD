import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Linear
import VD.ToMathlib.analyticAt

open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}


theorem eventually_nhds_comp_composition
  {f₁ f₂ ℓ : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : ∀ᶠ (z : ℂ) in nhds (ℓ z₀), f₁ z = f₂ z)
  (hℓ : Continuous ℓ) :
  ∀ᶠ (z : ℂ) in nhds z₀, (f₁ ∘ ℓ) z = (f₂ ∘ ℓ) z := by
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 hf
  apply eventually_nhds_iff.2
  use ℓ⁻¹' t
  exact ⟨fun y hy ↦ h₁t (ℓ y) hy, h₂t.preimage hℓ, h₃t⟩


theorem AnalyticAt.order_congr
  {f₁ f₂ : ℂ → ℂ}
  {z₀ : ℂ}
  (hf₁ : AnalyticAt ℂ f₁ z₀)
  (hf : f₁ =ᶠ[𝓝 z₀] f₂) :
  hf₁.order = (hf₁.congr hf).order := by

  by_cases h₁f₁ : hf₁.order = ⊤
  · rw [h₁f₁, eq_comm, AnalyticAt.order_eq_top_iff]
    exact Filter.EventuallyEq.rw (hf₁.order_eq_top_iff.1 h₁f₁) (fun x ↦ Eq (f₂ x)) hf.symm

  rw [← ENat.coe_toNat h₁f₁, eq_comm, AnalyticAt.order_eq_nat_iff]
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (hf₁.order_eq_nat_iff hf₁.order.toNat).1 (ENat.coe_toNat h₁f₁).symm
  use g
  simpa [h₁g, h₂g] using Filter.EventuallyEq.rw h₃g (fun x ↦ Eq (f₂ x)) hf.symm


theorem AnalyticAt.localIdentity
  {f g : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : AnalyticAt ℂ f z₀)
  (hg : AnalyticAt ℂ g z₀)
  (hfg : f =ᶠ[𝓝[≠] z₀] g) :
    f =ᶠ[𝓝 z₀] g := by
  apply Filter.eventuallyEq_iff_sub.mpr
  rcases ((hf.sub hg).eventually_eq_zero_or_eventually_ne_zero) with h | h
  · exact h
  · simpa using (Filter.eventually_and.2 ⟨Filter.eventuallyEq_iff_sub.mp hfg, h⟩).exists


theorem AnalyticAt.mul₁
  {f g : ℂ → ℂ}
  {z : ℂ}
  (hf : AnalyticAt ℂ f z)
  (hg : AnalyticAt ℂ g z) :
  AnalyticAt ℂ (f * g) z := by
  exact hf.mul hg


theorem analyticAt_finprod
  {α : Type}
  {f : α → ℂ → ℂ}
  {z : ℂ}
  (hf : ∀ a, AnalyticAt ℂ (f a) z) :
  AnalyticAt ℂ (∏ᶠ a, f a) z := by
  by_cases h₁f : f.mulSupport.Finite
  · simp [finprod_eq_prod f h₁f, h₁f.toFinset.prod_fn f, h₁f.toFinset.analyticAt_prod (fun a _ ↦ hf a)]
  · simpa [finprod_of_infinite_mulSupport h₁f] using analyticAt_const


lemma AnalyticAt.zpow_nonneg
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  {n : ℤ}
  (hf : AnalyticAt ℂ f z₀)
  (hn : 0 ≤ n) :
  AnalyticAt ℂ (fun x ↦ (f x) ^ n) z₀ := by
  simp_rw [(Eq.symm (Int.toNat_of_nonneg hn) : n = OfNat.ofNat n.toNat), zpow_ofNat]
  apply AnalyticAt.pow hf


theorem AnalyticAt.zpow
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  {n : ℤ}
  (h₁f : AnalyticAt ℂ f z₀)
  (h₂f : f z₀ ≠ 0) :
  AnalyticAt ℂ (fun x ↦ (f x) ^ n) z₀ := by
  by_cases hn : 0 ≤ n
  · exact zpow_nonneg h₁f hn
  · rw [(Int.eq_neg_comm.mp rfl : n = - (- n))]
    conv => arg 2; intro x; rw [zpow_neg]
    exact (h₁f.zpow_nonneg (by linarith)).inv (zpow_ne_zero (-n) h₂f)


/- A function is analytic at a point iff it is analytic after multiplication
  with a non-vanishing analytic function -/
theorem analyticAt_of_mul_analytic
  {f g : ℂ → ℂ}
  {z₀ : ℂ}
  (h₁g : AnalyticAt ℂ g z₀)
  (h₂g : g z₀ ≠ 0) :
  AnalyticAt ℂ f z₀ ↔ AnalyticAt ℂ (f * g) z₀ := by
  constructor
  · exact fun a ↦ AnalyticAt.mul₁ a h₁g
  · intro hprod
    have : f =ᶠ[𝓝 z₀] f * g * g⁻¹ := by
      apply Filter.eventually_iff_exists_mem.mpr
      use g⁻¹' {0}ᶜ
      constructor
      · exact h₁g.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr h₂g)
      · intro y hy
        simp at hy
        simp [hy]
    rw [analyticAt_congr this]
    exact hprod.mul (h₁g.inv h₂g)
