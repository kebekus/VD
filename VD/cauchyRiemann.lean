import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Complex.RealDeriv
import VD.partialDeriv

variable {z : ℂ} {f : ℂ → ℂ}


theorem CauchyRiemann₁ : (DifferentiableAt ℂ f z)
  → (fderiv ℝ f z) Complex.I = Complex.I * (fderiv ℝ f z) 1 := by
  intro h
  rw [DifferentiableAt.fderiv_restrictScalars ℝ h]
  nth_rewrite 1 [← mul_one Complex.I]
  exact ContinuousLinearMap.map_smul_of_tower (fderiv ℂ f z) Complex.I 1


theorem CauchyRiemann₂ : (DifferentiableAt ℂ f z)
  → lineDeriv ℝ f z Complex.I = Complex.I * lineDeriv ℝ f z 1 := by
  intro h
  rw [DifferentiableAt.lineDeriv_eq_fderiv (h.restrictScalars ℝ)]
  rw [DifferentiableAt.lineDeriv_eq_fderiv (h.restrictScalars ℝ)]
  exact CauchyRiemann₁ h


theorem CauchyRiemann₃ : (DifferentiableAt ℂ f z)
  → (lineDeriv ℝ (Complex.reCLM ∘ f) z 1 = lineDeriv ℝ (Complex.imCLM ∘ f) z Complex.I)
    ∧ (lineDeriv ℝ (Complex.reCLM ∘ f) z Complex.I = -lineDeriv ℝ (Complex.imCLM ∘ f) z 1)
   := by

  intro h

  have ContinuousLinearMap.comp_lineDeriv : ∀ w : ℂ, ∀ l : ℂ →L[ℝ] ℝ, lineDeriv ℝ (l ∘ f) z w = l ((fderiv ℝ f z) w) := by
    intro w l
    rw [DifferentiableAt.lineDeriv_eq_fderiv]
    rw [fderiv_comp]
    simp
    fun_prop
    exact h.restrictScalars ℝ
    apply (ContinuousLinearMap.differentiableAt l).comp
    exact h.restrictScalars ℝ

  repeat
    rw [ContinuousLinearMap.comp_lineDeriv]
  rw [CauchyRiemann₁ h, Complex.I_mul]
  simp


theorem CauchyRiemann₄
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f : ℂ → F} :
  (Differentiable ℂ f) → partialDeriv ℝ Complex.I f = Complex.I • partialDeriv ℝ 1 f := by
  intro h
  unfold partialDeriv

  conv =>
    left
    intro w
    rw [DifferentiableAt.fderiv_restrictScalars ℝ (h w)]
    simp
    rw [← mul_one Complex.I]
    rw [← smul_eq_mul]
  conv =>
    right
    right
    intro w
    rw [DifferentiableAt.fderiv_restrictScalars ℝ (h w)]
  funext w
  simp

theorem CauchyRiemann₅ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F} {z : ℂ} : (DifferentiableAt ℂ f z)
  → partialDeriv ℝ Complex.I f z = Complex.I • partialDeriv ℝ 1 f z := by
  intro h
  unfold partialDeriv

  conv =>
    left
    rw [DifferentiableAt.fderiv_restrictScalars ℝ h]
    simp
    rw [← mul_one Complex.I]
    rw [← smul_eq_mul]
  conv =>
    right
    right
    rw [DifferentiableAt.fderiv_restrictScalars ℝ h]
  simp
