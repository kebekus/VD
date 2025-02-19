/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Normed.Field.Basic
import VD.ToMathlib.codiscreteWithin

/-!
# Divisors on subsets of normed fields

This file defines divisors, a standard book-keeping tool in complex analysis
used to keep track of pole/vanishing orders of meromorphic objects, typically
functions or differential forms.

## TODOs

- Restriction and extension of divisors as group morphisms
- Decomposition into positive/negative components
- Constructions: The divisor of a meromorphic function, behavior under product
  of meromorphic functions, behavior under addition, behavior under restriction
- Local finiteness of the support
- Degree
- Nevanlinna counting functions
- Construction: The divisor of a rational polynomial
-/

open Filter Set Topology

variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {U : Set 𝕜}

/-!
## Definition
-/

structure Divisor (U : Set 𝕜) where
  toFun : 𝕜 → ℤ
  supportInU : toFun.support ⊆ U
  supportDiscreteWithinU : toFun =ᶠ[Filter.codiscreteWithin U] 0

instance (U : Set 𝕜) : CoeFun (Divisor U) (fun _ ↦ 𝕜 → ℤ) where
  coe := Divisor.toFun

attribute [coe] Divisor.toFun

noncomputable def Divisor.deg (D : Divisor U) : ℤ := ∑ᶠ z, D.toFun z


/-!
## Instances and basic extensionality
-/

instance instFunLike : FunLike (Divisor U) 𝕜 ℤ where
  coe := fun D ↦ D.toFun
  coe_injective' := by
    rintro ⟨D₁, h₁D₁, h₂D₁⟩ ⟨D₂, h₁D₂, h₂D₂⟩
    simp

@[ext]
theorem ext {D₁ D₂ : Divisor U} (h : ∀ a, D₁.toFun a = D₂.toFun a) : D₁ = D₂ := DFunLike.ext _ _ h

/-!
## Ordered group structure
-/

instance instZero : Zero (Divisor U) where
  zero := ⟨fun _ ↦ 0, by simp, Eq.eventuallyEq rfl⟩

@[simp]
theorem zero_fun : (0 : Divisor U).toFun = 0 := rfl

instance : Add (Divisor U) where
  add := by
    intro D₁ D₂
    exact {
      toFun := D₁.toFun + D₂.toFun
      supportInU := by
        intro x
        contrapose
        intro hx
        have h₁x : D₁ x = 0 := Function.nmem_support.mp fun a ↦ hx (D₁.supportInU a)
        have h₂x : D₂ x = 0 := Function.nmem_support.mp fun a ↦ hx (D₂.supportInU a)
        simp [h₁x, h₂x]
      supportDiscreteWithinU := by
        apply EventuallyEq.add (f := D₁) (g := 0) (f' := D₂) (g' := 0)
        exact D₁.supportDiscreteWithinU
        exact D₂.supportDiscreteWithinU
    }

@[simp]
theorem add_fun {D₁ D₂ : Divisor U} : (D₁ + D₂).toFun = D₁.toFun + D₂.toFun := rfl

instance : Neg (Divisor U) where
  neg := by
    intro D
    exact {
      toFun := -D.toFun
      supportInU := by
        intro x hx
        simp at hx
        exact D.supportInU hx
      supportDiscreteWithinU := by
        apply EventuallyEq.neg (f := D) (g := 0)
        exact D.supportDiscreteWithinU
    }

@[simp]
theorem neg_fun {D : Divisor U} : (-D).toFun = -(D.toFun) := rfl

instance nsmul : SMul ℕ (Divisor U) where
  smul := by
    intro n D
    exact {
      toFun := fun z ↦ n * D z
      supportInU := by
        intro x hx
        simp at hx
        exact D.supportInU hx.2
      supportDiscreteWithinU := by
        filter_upwards [D.supportDiscreteWithinU]
        intro x hx
        simp [hx]
    }

@[simp]
theorem nsmul_fun {D : Divisor U} {n : ℕ} : (n • D).toFun = n • (D.toFun) := rfl

instance zsmul : SMul ℤ (Divisor U) where
  smul := fun n D ↦
    {
      toFun := fun z ↦ n * D z
      supportInU := by
        intro x hx
        simp at hx
        exact D.supportInU hx.2
      supportDiscreteWithinU := by
        filter_upwards [D.supportDiscreteWithinU]
        intro x hx
        simp [hx]
    }

@[simp]
theorem zsmul_fun {D : Divisor U} {n : ℤ} : (n • D).toFun = n • (D.toFun) := rfl

instance : LE (Divisor U) where
  le := fun D₁ D₂ ↦ D₁.toFun ≤ D₂.toFun

@[simp]
theorem le_fun {D₁ D₂ : Divisor U} : D₁ ≤ D₂ ↔ D₁.toFun ≤ D₂.toFun := ⟨(·),(·)⟩

instance : OrderedAddCommGroup (Divisor U) where
  add := (· + · )
  add_assoc := fun _ _ _ ↦ by ext; simp [add_assoc]
  zero := 0
  zero_add := fun _ ↦ by ext; simp
  add_zero := fun _ ↦ by ext; simp
  nsmul := (· • ·)
  neg := (- ·)
  zsmul := (· • ·)
  neg_add_cancel := fun _ ↦ by ext; simp
  add_comm := fun _ _ ↦ by ext; simp [add_comm]
  nsmul_zero := fun _ ↦ by ext; simp
  nsmul_succ := fun _ _ ↦ by ext; simp [add_one_mul]
  zsmul_zero' := fun _ ↦ by ext; simp
  zsmul_succ' := fun _ _ ↦ by ext; simp [add_one_mul]
  zsmul_neg' := fun _ _ ↦ by ext; simp; apply negSucc_zsmul
  le := (· ≤ ·)
  le_refl := by tauto
  le_trans := fun D₁ D₂ D₃ h₁₂ h₂₃ ↦ by simp [le_fun,
    Preorder.le_trans (D₁.toFun) (D₂.toFun) (D₃.toFun) h₁₂ h₂₃]
  le_antisymm := fun _ _ h₁₂ h₂₁ ↦ by ext x; exact Int.le_antisymm (h₁₂ x) (h₂₁ x)
  add_le_add_left := fun _ _ _ _ ↦ by simpa

/-!
## Elementary properties of the support
-/

theorem Divisor.discreteSupport (D : Divisor U) :
    DiscreteTopology D.toFun.support := by
  have : Function.support D = {x | D x = 0}ᶜ ∩ U := by
    ext x
    constructor
    · exact fun hx ↦ ⟨by tauto, D.supportInU hx⟩
    · intro hx
      rw [mem_inter_iff, mem_compl_iff, mem_setOf_eq] at hx
      tauto
  convert discreteTopology_of_codiscreteWithin (D.supportDiscreteWithinU)

theorem Divisor.closedSupport (D : Divisor U) (hU : IsClosed U) :
    IsClosed D.toFun.support := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually]
  intro x hx
  by_cases h₁x : x ∈ U
  · have Z₁ := D.supportDiscreteWithinU
    rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin] at Z₁
    filter_upwards [eventually_nhdsWithin_iff.1 (Filter.disjoint_principal_right.1 (Z₁ x h₁x))]
    intro a ha
    by_cases h₂a : a = x
    · simp [hx, h₂a]
    · have W := ha h₂a
      simp at W
      by_cases h₃a : a ∈ U
      · tauto
      · have := D.supportInU
        by_contra hCon
        tauto
  · rw [eventually_iff_exists_mem]
    use Uᶜ, hU.compl_mem_nhds h₁x
    intro y hy
    simp
    exact Function.nmem_support.mp fun a ↦ hy (D.supportInU a)

theorem Divisor.finiteSupport (D : Divisor U) (hU : IsCompact U) :
    Set.Finite D.toFun.support :=
  (hU.of_isClosed_subset (D.closedSupport hU.isClosed) D.supportInU).finite D.discreteSupport
