import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order

open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}

variable {𝕝 : Type*} [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕝 F] [IsScalarTower 𝕜 𝕝 F]

/- A function is analytic at a point iff it is analytic after scalar
  multiplication with a non-vanishing analytic function. -/
theorem analyticAt_of_smul_analytic [NormedSpace 𝕝 E] [IsScalarTower 𝕜 𝕝 E] {f : 𝕜 → 𝕝}
    (h₁f : AnalyticAt 𝕜 f z₀) (h₂f : f z₀ ≠ 0) :
    AnalyticAt 𝕜 g z₀ ↔ AnalyticAt 𝕜 (f • g) z₀ := by
  constructor
  · exact fun a ↦ h₁f.smul a
  · intro hprod
    rw [analyticAt_congr (g := (f⁻¹ • f) • g), smul_assoc]
    have := h₁f.inv h₂f
    fun_prop
    · filter_upwards [h₁f.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.2 h₂f)]
      intro y hy
      rw [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] at hy
      simp [hy]

/- A function is analytic at a point iff it is analytic after scalar
  multiplication with a non-vanishing analytic function. -/
theorem analyticAt_of_smul_analytic' [NormedSpace 𝕝 E] [IsScalarTower 𝕜 𝕝 E] {f : 𝕜 → 𝕝}
    (h₁f : AnalyticAt 𝕜 f z₀) (h₂f : f z₀ ≠ 0) :
    AnalyticAt 𝕜 g z₀ ↔ AnalyticAt 𝕜 (fun z ↦ f z • g z) z₀ :=
  analyticAt_of_smul_analytic h₁f h₂f

/- A function is analytic at a point iff it is analytic after multiplication
  with a non-vanishing analytic function. -/
theorem analyticAt_of_mul_analytic {f g : 𝕜 → 𝕝} (h₁f : AnalyticAt 𝕜 f z₀) (h₂f : f z₀ ≠ 0) :
    AnalyticAt 𝕜 g z₀ ↔ AnalyticAt 𝕜 (f * g) z₀ := by
  rw [← smul_eq_mul]
  exact analyticAt_of_smul_analytic h₁f h₂f

/- A function is analytic at a point iff it is analytic after multiplication
  with a non-vanishing analytic function. -/
theorem analyticAt_of_mul_analytic' {f g : 𝕜 → 𝕝} (h₁f : AnalyticAt 𝕜 f z₀) (h₂f : f z₀ ≠ 0) :
    AnalyticAt 𝕜 g z₀ ↔ AnalyticAt 𝕜 (fun z ↦ f z * g z) z₀ := by
  exact analyticAt_of_mul_analytic h₁f h₂f

/- The zpow of an analytic function is analytic if the exponent is nonnegative. -/
lemma AnalyticAt.zpow_nonneg {f : 𝕜 → 𝕜} {n : ℤ} (hf : AnalyticAt 𝕜 f z₀) (hn : 0 ≤ n) :
    AnalyticAt 𝕜 (f ^ n) z₀ := by
  simp_rw [(Eq.symm (Int.toNat_of_nonneg hn) : n = OfNat.ofNat n.toNat), zpow_ofNat]
  apply AnalyticAt.pow hf

/- The zpow of an analytic function is analytic if the exponent is nonnegative. -/
lemma AnalyticAt.zpow_nonneg' {f : 𝕜 → 𝕜} {n : ℤ} (hf : AnalyticAt 𝕜 f z₀) (hn : 0 ≤ n) :
    AnalyticAt 𝕜 (fun x ↦ (f x) ^ n) z₀ :=
  hf.zpow_nonneg hn

/- The zpow of an analytic function is analytic at `z₀` if the function does
not vanish there. -/
theorem AnalyticAt.zpow {f : 𝕜 → 𝕜} {n : ℤ} (h₁f : AnalyticAt 𝕜 f z₀) (h₂f : f z₀ ≠ 0) :
    AnalyticAt 𝕜 (f ^ n) z₀ := by
  by_cases hn : 0 ≤ n
  · exact zpow_nonneg h₁f hn
  · rw [(Int.eq_neg_comm.mp rfl : n = - (- n))]
    conv => arg 2; intro x; rw [zpow_neg]
    exact (h₁f.zpow_nonneg (by linarith)).inv (zpow_ne_zero (-n) h₂f)

/- The zpow of an analytic function is analytic at `z₀` if the functions does
not vanish there. -/
theorem AnalyticAt.zpow' {f : 𝕜 → 𝕜} {n : ℤ} (h₁f : AnalyticAt 𝕜 f z₀) (h₂f : f z₀ ≠ 0) :
    AnalyticAt 𝕜 (fun x ↦ (f x) ^ n) z₀ := by
  exact h₁f.zpow h₂f


theorem AnalyticAt.localIdentity (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
(hfg : f =ᶠ[𝓝[≠] z₀] g) :
    f =ᶠ[𝓝 z₀] g := by
  rcases ((hf.sub hg).eventually_eq_zero_or_eventually_ne_zero) with h | h
  · exact Filter.eventuallyEq_iff_sub.2 h
  · simpa using (Filter.eventually_and.2 ⟨Filter.eventuallyEq_iff_sub.mp hfg, h⟩).exists


/-- The leading coefficient in the power series expansion of f around z₀, or
  zero if f vanishes identically near z₀. -/
noncomputable def AnalyticAt.leadCoeff (hf : AnalyticAt 𝕜 f z₀) : E :=
  if h : hf.order = ⊤ then 0 else ((hf.order_ne_top_iff.1 h).choose z₀)
