import Mathlib.Analysis.Analytic.IsolatedZeros
import VD.ToMathlib.analyticAt

open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}


/- A function is analytic at a point iff it is analytic after multiplication
  with a non-vanishing analytic function -/
theorem analyticAt_of_mul_analytic {f g : 𝕜 → 𝕜} (h₁g : AnalyticAt 𝕜 g z₀) (h₂g : g z₀ ≠ 0) :
    AnalyticAt 𝕜 f z₀ ↔ AnalyticAt 𝕜 (f * g) z₀ := by
  constructor
  · exact fun a ↦ a.mul h₁g
  · intro hprod
    have : f =ᶠ[𝓝 z₀] f * g * g⁻¹ := by
      apply Filter.eventually_iff_exists_mem.mpr
      use g⁻¹' {0}ᶜ, h₁g.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr h₂g)
      intro y hy
      rw [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] at hy
      simp [hy]
    rw [analyticAt_congr this]
    exact hprod.mul (h₁g.inv h₂g)


lemma AnalyticAt.zpow_nonneg
  {f : 𝕜 → 𝕜}
  {n : ℤ}
  (hf : AnalyticAt 𝕜 f z₀)
  (hn : 0 ≤ n) :
  AnalyticAt 𝕜 (fun x ↦ (f x) ^ n) z₀ := by
  simp_rw [(Eq.symm (Int.toNat_of_nonneg hn) : n = OfNat.ofNat n.toNat), zpow_ofNat]
  apply AnalyticAt.pow hf


lemma AnalyticAt.zpow_nonneg'
  {f : 𝕜 → 𝕜}
  {n : ℤ}
  (hf : AnalyticAt 𝕜 f z₀)
  (hn : 0 ≤ n) :
  AnalyticAt 𝕜 (f ^ n) z₀ := hf.zpow_nonneg hn


theorem AnalyticAt.zpow
  {f : 𝕜 → 𝕜}
  {n : ℤ}
  (h₁f : AnalyticAt 𝕜 f z₀)
  (h₂f : f z₀ ≠ 0) :
  AnalyticAt 𝕜 (fun x ↦ (f x) ^ n) z₀ := by
  by_cases hn : 0 ≤ n
  · exact zpow_nonneg h₁f hn
  · rw [(Int.eq_neg_comm.mp rfl : n = - (- n))]
    conv => arg 2; intro x; rw [zpow_neg]
    exact (h₁f.zpow_nonneg (by linarith)).inv (zpow_ne_zero (-n) h₂f)


theorem AnalyticAt.localIdentity (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
(hfg : f =ᶠ[𝓝[≠] z₀] g) :
    f =ᶠ[𝓝 z₀] g := by
  rcases ((hf.sub hg).eventually_eq_zero_or_eventually_ne_zero) with h | h
  · exact Filter.eventuallyEq_iff_sub.2 h
  · simpa using (Filter.eventually_and.2 ⟨Filter.eventuallyEq_iff_sub.mp hfg, h⟩).exists



/-- The leading coefficient in the power series expansion of f around z₀, or
  zero of f vanishes identically near z₀. -/
noncomputable def AnalyticAt.leadCoeff (hf : AnalyticAt 𝕜 f z₀) : E :=
  if h : hf.order = ⊤ then 0 else ((hf.order_neq_top_iff.1 h).choose z₀)
