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
  use g; simp [h₁g, h₂g]
  exact Filter.EventuallyEq.rw h₃g (fun x ↦ Eq (f₂ x)) hf.symm


theorem AnalyticAt.order_comp_CLE
  (ℓ : ℂ ≃L[ℂ] ℂ)
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : AnalyticAt ℂ f (ℓ z₀)) :
  hf.order = (hf.comp (ℓ.analyticAt z₀)).order := by

  by_cases h₁f : hf.order = ⊤
  · rw [h₁f]
    rw [AnalyticAt.order_eq_top_iff] at h₁f
    let A := eventually_nhds_comp_composition h₁f ℓ.continuous
    simp at A
    rw [AnalyticAt.order_congr (hf.comp (ℓ.analyticAt z₀)) A]

    have : AnalyticAt ℂ (0 : ℂ → ℂ) z₀ := by
      apply analyticAt_const
    have : this.order = ⊤ := by
      rw [AnalyticAt.order_eq_top_iff]
      simp
    rw [this]
  · let n := hf.order.toNat
    have hn : hf.order = n := Eq.symm (ENat.coe_toNat h₁f)
    rw [hn]
    rw [AnalyticAt.order_eq_nat_iff] at hn
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := hn
    have A := eventually_nhds_comp_composition h₃g ℓ.continuous

    have t₁ : AnalyticAt ℂ (fun z => ℓ z - ℓ z₀) z₀ := by
      apply AnalyticAt.sub
      exact ContinuousLinearEquiv.analyticAt ℓ z₀
      exact analyticAt_const
    have t₀ : AnalyticAt ℂ (fun z => (ℓ z - ℓ z₀) ^ n) z₀ := by
      exact pow t₁ n
    have : AnalyticAt ℂ (fun z ↦ (ℓ z - ℓ z₀) ^ n • g (ℓ z) : ℂ → ℂ) z₀ := by
      apply AnalyticAt.mul
      exact t₀
      apply AnalyticAt.comp h₁g
      exact ContinuousLinearEquiv.analyticAt ℓ z₀
    rw [AnalyticAt.order_congr (hf.comp (ℓ.analyticAt z₀)) A]
    simp

    rw [AnalyticAt.order_mul t₀ ((h₁g.comp (ℓ.analyticAt z₀)))]

    have : t₁.order = (1 : ℕ) := by
      rw [AnalyticAt.order_eq_nat_iff]
      use (fun _ ↦ ℓ 1)
      simp
      constructor
      · exact analyticAt_const
      · apply Filter.Eventually.of_forall
        intro x
        calc ℓ x - ℓ z₀
        _ = ℓ (x - z₀) := by
          exact Eq.symm (ContinuousLinearEquiv.map_sub ℓ x z₀)
        _ = ℓ ((x - z₀) * 1) := by
          simp
        _ = (x - z₀) * ℓ 1 := by
          rw [← smul_eq_mul, ← smul_eq_mul]
          exact ContinuousLinearEquiv.map_smul ℓ (x - z₀) 1

    have : t₀.order = n := by
      rw [AnalyticAt.order_pow t₁, this]
      simp

    rw [this]

    have : (comp h₁g (ContinuousLinearEquiv.analyticAt ℓ z₀)).order = 0 := by
      rwa [AnalyticAt.order_eq_zero_iff]
    rw [this]

    simp


theorem AnalyticAt.localIdentity
  {f g : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : AnalyticAt ℂ f z₀)
  (hg : AnalyticAt ℂ g z₀) :
  f =ᶠ[𝓝[≠] z₀] g → f =ᶠ[𝓝 z₀] g := by
  intro h
  let Δ := f - g
  have : AnalyticAt ℂ Δ z₀ := AnalyticAt.sub hf hg
  have t₁ : Δ =ᶠ[𝓝[≠] z₀] 0 := by
    exact Filter.eventuallyEq_iff_sub.mp h

  have : Δ =ᶠ[𝓝 z₀] 0 := by
    rcases (AnalyticAt.eventually_eq_zero_or_eventually_ne_zero this) with h | h
    · exact h
    · have := Filter.EventuallyEq.eventually t₁
      let A := Filter.eventually_and.2 ⟨this, h⟩
      let _ := Filter.Eventually.exists A
      tauto
  exact Filter.eventuallyEq_iff_sub.mpr this


theorem AnalyticAt.mul₁
  {f g : ℂ → ℂ}
  {z : ℂ}
  (hf : AnalyticAt ℂ f z)
  (hg : AnalyticAt ℂ g z) :
  AnalyticAt ℂ (f * g) z := by
  rw [(by rfl : f * g = (fun x ↦ f x * g x))]
  exact mul hf hg


theorem analyticAt_finprod
  {α : Type}
  {f : α → ℂ → ℂ}
  {z : ℂ}
  (hf : ∀ a, AnalyticAt ℂ (f a) z) :
  AnalyticAt ℂ (∏ᶠ a, f a) z := by
  by_cases h₁f : (Function.mulSupport f).Finite
  · rw [finprod_eq_prod f h₁f]
    rw [Finset.prod_fn h₁f.toFinset f]
    exact Finset.analyticAt_prod h₁f.toFinset (fun a _ ↦ hf a)
  · rw [finprod_of_infinite_mulSupport h₁f]
    exact analyticAt_const


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
    conv =>
      arg 2
      intro x
      rw [zpow_neg]
    exact AnalyticAt.inv (zpow_nonneg h₁f (by linarith)) (zpow_ne_zero (-n) h₂f)


/- A function is analytic at a point iff it is analytic after multiplication
  with a non-vanishing analytic function -/
theorem analyticAt_of_mul_analytic
  {f g : ℂ → ℂ}
  {z₀ : ℂ}
  (h₁g : AnalyticAt ℂ g z₀)
  (h₂g : g z₀ ≠ 0) :
  AnalyticAt ℂ f z₀ ↔ AnalyticAt ℂ (f * g) z₀ := by
  constructor
  · exact fun a => AnalyticAt.mul₁ a h₁g
  · intro hprod

    let g' := fun z ↦ (g z)⁻¹
    have h₁g' := h₁g.inv h₂g
    have h₂g' : g' z₀ ≠ 0 := by
      exact inv_ne_zero h₂g

    have : f =ᶠ[𝓝 z₀] f * g * fun x => (g x)⁻¹ := by
      unfold Filter.EventuallyEq
      apply Filter.eventually_iff_exists_mem.mpr
      use g⁻¹' {0}ᶜ
      constructor
      · apply ContinuousAt.preimage_mem_nhds
        exact AnalyticAt.continuousAt h₁g
        exact compl_singleton_mem_nhds_iff.mpr h₂g
      · intro y hy
        simp at hy
        simp [hy]
    rw [analyticAt_congr this]
    apply hprod.mul
    exact h₁g'
