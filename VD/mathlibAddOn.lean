import Mathlib.Analysis.Analytic.Meromorphic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import VD.analyticAt
import Mathlib.Analysis.SpecialFunctions.Exp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
variable {f f₀ f₁ g : E → F}
variable {f' f₀' f₁' g' : E →L[𝕜] F}
variable (e : E →L[𝕜] F)
variable {x : E}
variable {s t : Set E}
variable {L L₁ L₂ : Filter E}

variable {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]


-- import Mathlib.Analysis.Calculus.FDeriv.Add

@[fun_prop]
theorem Differentiable.const_smul' (h : Differentiable 𝕜 f) (c : R) :
    Differentiable 𝕜 (c • f) := by
  have : c • f = fun x ↦ c • f x := rfl
  rw [this]
  exact Differentiable.const_smul h c


-- Mathlib.Analysis.Calculus.ContDiff.Basic

theorem ContDiff.const_smul' {f : E → F} (c : R) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (c • f) := by
  have : c • f = fun x ↦ c • f x := rfl
  rw [this]
  exact ContDiff.const_smul c hf



open Topology Filter

lemma Mnhds
  {α : Type}
  {f g : ℂ → α}
  {z₀ : ℂ}
  (h₁ : f =ᶠ[𝓝[≠] z₀] g)
  (h₂ : f z₀ = g z₀) :
  f =ᶠ[𝓝 z₀] g := by
  apply eventually_nhds_iff.2
  obtain ⟨t, h₁t, h₂t⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h₁)
  use t
  constructor
  · intro y hy
    by_cases h₂y : y ∈ ({z₀}ᶜ : Set ℂ)
    · exact h₁t y hy h₂y
    · simp at h₂y
      rwa [h₂y]
  · exact h₂t

-- unclear where this should go

lemma WithTopCoe
  {n : WithTop ℕ} :
  WithTop.map (Nat.cast : ℕ → ℤ) n = 0 → n = 0 := by
  rcases n with h|h
  · intro h
    contradiction
  · intro h₁
    simp only [WithTop.map, Option.map] at h₁
    have : (h : ℤ) = 0 := by
      exact WithTop.coe_eq_zero.mp h₁
    have : h = 0 := by
      exact Int.ofNat_eq_zero.mp this
    rw [this]
    rfl

lemma rwx
  {a b : WithTop ℤ}
  (ha : a ≠ ⊤)
  (hb : b ≠ ⊤) :
  a + b ≠ ⊤ := by
  simp; tauto

lemma untop_add
  {a b : WithTop ℤ}
  (ha : a ≠ ⊤)
  (hb : b ≠ ⊤) :
  (a + b).untop (rwx ha hb) = a.untop ha + (b.untop hb) := by
  rw [WithTop.untop_eq_iff]
  rw [WithTop.coe_add]
  rw [WithTop.coe_untop]
  rw [WithTop.coe_untop]

lemma untop'_of_ne_top
  {a : WithTop ℤ}
  {d : ℤ}
  (ha : a ≠ ⊤) :
  WithTop.untop' d a = a := by
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 ha
  rw [← hb]
  simp
