import Mathlib.Analysis.Complex.TaylorSeries
import VD.cauchyRiemann
import VD.holomorphicAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]


theorem HolomorphicAt_analyticAt
  [CompleteSpace F]
  {f : ℂ → F}
  {x : ℂ} :
  HolomorphicAt f x → AnalyticAt ℂ f x := by
  intro hf
  obtain ⟨s, h₁s, h₂s, h₃s⟩ := HolomorphicAt_iff.1 hf
  apply DifferentiableOn.analyticAt (s := s)
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply h₃s
  exact hz
  exact IsOpen.mem_nhds h₁s h₂s


theorem HolomorphicAt_differentiableAt
  {f : E → F}
  {x : E} :
  HolomorphicAt f x →  DifferentiableAt ℂ f x := by
  intro hf
  obtain ⟨s, _, h₂s, h₃s⟩ := HolomorphicAt_iff.1 hf
  exact h₃s x h₂s



theorem HolomorphicAt_contDiffAt
  [CompleteSpace F]
  {f : ℂ → F}
  {z : ℂ}
  (hf : HolomorphicAt f z) :
  ContDiffAt ℝ 2 f z := by

  let t := {x | HolomorphicAt f x}
  have ht : IsOpen t := HolomorphicAt_isOpen f
  have hz : z ∈ t := by exact hf

  -- ContDiffAt ℝ 2 f z
  apply ContDiffOn.contDiffAt _ ((IsOpen.mem_nhds_iff ht).2 hz)
  suffices h : ContDiffOn ℂ 2 f t from by
    apply ContDiffOn.restrict_scalars ℝ h
  apply DifferentiableOn.contDiffOn _ ht
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  exact HolomorphicAt_differentiableAt hw


theorem CauchyRiemann'₅
  {f : ℂ → F}
  {z : ℂ}
  (h : DifferentiableAt ℂ f z) :
  partialDeriv ℝ Complex.I f z = Complex.I • partialDeriv ℝ 1 f z := by
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

theorem CauchyRiemann'₆
  {f : ℂ → F}
  {z : ℂ}
  (h : HolomorphicAt f z) :
  partialDeriv ℝ Complex.I f =ᶠ[nhds z] Complex.I • partialDeriv ℝ 1 f := by

  obtain ⟨s, h₁s, hz, h₂f⟩ := HolomorphicAt_iff.1 h

  apply Filter.eventuallyEq_iff_exists_mem.2
  use s
  constructor
  · exact IsOpen.mem_nhds h₁s hz
  · intro w hw
    apply CauchyRiemann'₅
    exact h₂f w hw
