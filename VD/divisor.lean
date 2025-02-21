/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Normed.Field.Basic
import VD.codiscreteWithin

/-!
# Divisors on subsets of normed fields

This file defines divisors, a standard book-keeping tool in complex analysis
used to keep track of pole/vanishing orders of meromorphic objects, typically
functions or differential forms.

Throughout the present file, `𝕜` denotes a nontrivially normed field, and `U` a
subset of `𝕜`.

## TODOs

- Constructions: The divisor of a meromorphic function, behavior under product
  of meromorphic functions, behavior under addition, behavior under restriction
- Construction: The divisor of a rational polynomial
-/

open Filter Set Topology

variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {U : Set 𝕜}

/-!
## Definition

A divisor on `U` is a function `𝕜 → ℤ` whose support is discrete within `U` and
entirely contained within `U`.  The theorem
`supportDiscreteWithin_iff_locallyFiniteWithin` shows that this is equivalent to
the textbook definition, which requires the support of `f` to be locally finite
within `U`.
-/

/-- A divisor on `U` is a function `𝕜 → ℤ` whose support is discrete within `U`
and entirely contained within `U`. -/
structure Divisor (U : Set 𝕜) where
  toFun : 𝕜 → ℤ
  supportInU : toFun.support ⊆ U
  supportDiscreteWithinU : toFun =ᶠ[Filter.codiscreteWithin U] 0

theorem supportDiscreteWithin_iff_locallyFiniteWithin {f : 𝕜 → ℤ} (h : f.support ⊆ U) :
    f =ᶠ[Filter.codiscreteWithin U] 0 ↔ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support) := by
  have : f.support = (U \ {x | f x = (0 : 𝕜 → ℤ) x}) := by
    ext x
    simp only [Function.mem_support, ne_eq, Pi.zero_apply, mem_diff, mem_setOf_eq, iff_and_self]
    exact (h ·)
  rw [EventuallyEq, Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithinU, this]

/-!
## Coercion to functions and basic extensionality
-/

namespace Divisor

/-- A divisor can be coerced into a function 𝕜 → ℤ -/
instance (U : Set 𝕜) : CoeFun (Divisor U) (fun _ ↦ 𝕜 → ℤ) where
  coe := Divisor.toFun

attribute [coe] Divisor.toFun

/-- Divisors are `FunLike`: the coercion from divisors to functions is injective. -/
instance : FunLike (Divisor U) 𝕜 ℤ where
  coe := fun D ↦ D.toFun
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ ↦ by simp

/-- Helper lemma for the `ext` tactic: two divisors are equal if their
associated functions agree. -/
@[ext]
theorem ext {D₁ D₂ : Divisor U} (h : ∀ a, D₁.toFun a = D₂.toFun a) : D₁ = D₂ := DFunLike.ext _ _ h

/-!
## Lattice ordered group structure

This section equips divisors on `U` with the standard structure of an ordered
group, where addition and comparison of divisors are addition and pointwise
comparison of functions.
-/

/-- Divisors have a zero -/
instance : Zero (Divisor U) where
  zero := ⟨fun _ ↦ 0, by simp, Eq.eventuallyEq rfl⟩

/-- Helper lemma for the `simp` tactic: the function of the zero-divisor is the
zero function. -/
@[simp]
theorem zero_fun : (0 : Divisor U).toFun = 0 := rfl

/-- Divisors can be added -/
instance : Add (Divisor U) where
  add := by
    intro D₁ D₂
    exact {
      toFun := D₁.toFun + D₂.toFun
      supportInU := by
        intro x
        contrapose
        intro hx
        simp [Function.nmem_support.1 fun a ↦ hx (D₁.supportInU a),
          Function.nmem_support.1 fun a ↦ hx (D₂.supportInU a)]
      supportDiscreteWithinU := D₁.supportDiscreteWithinU.add D₂.supportDiscreteWithinU
    }

/-- Helper lemma for the `simp` tactic: the function of the sum of two divisors
is the sum of the associated functions. -/
@[simp]
lemma add_fun {D₁ D₂ : Divisor U} : (D₁ + D₂).toFun = D₁.toFun + D₂.toFun := rfl

/-- Divisors have a negative -/
instance : Neg (Divisor U) where
  neg := by
    intro D
    exact {
      toFun := -D.toFun
      supportInU := by
        intro x hx
        rw [Function.support_neg', Function.mem_support, ne_eq] at hx
        exact D.supportInU hx
      supportDiscreteWithinU := D.supportDiscreteWithinU.neg
    }

/-- Helper lemma for the `simp` tactic: the function of the negative divisor
is the negative of the associated function. -/
@[simp]
lemma neg_fun {D : Divisor U} : (-D).toFun = -(D.toFun) := rfl

/-- Divisors have scalar multiplication with natural numbers -/
instance : SMul ℕ (Divisor U) where
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

/-- Helper lemma for the `simp` tactic: the function of a scalar product
(natural number)·divisor is the scalar product of the natural number with the
associated function of the divisor. -/
@[simp]
lemma nsmul_fun {D : Divisor U} {n : ℕ} : (n • D).toFun = n • (D.toFun) := rfl

/-- Divisors have scalar multiplication with integers -/
instance : SMul ℤ (Divisor U) where
  smul := fun n D ↦
    {
      toFun := fun z ↦ n * D z
      supportInU := by
        intro x hx
        simp at hx
        exact D.supportInU hx.2
      supportDiscreteWithinU := by
        filter_upwards [D.supportDiscreteWithinU]
        intro _ hx
        simp [hx]
    }

/-- Helper lemma for the `simp` tactic: the function of a scalar product
(integer)·divisor is the scalar product of the integer with the associated
function of the divisor. -/
@[simp]
lemma zsmul_fun {D : Divisor U} {n : ℤ} : (n • D).toFun = n • (D.toFun) := rfl

/-- Divisors have a partial ordering by pointwise comparison of the associated
functions. -/
instance : LE (Divisor U) where
  le := fun D₁ D₂ ↦ D₁.toFun ≤ D₂.toFun

/-- Helper lemma for the `simp` tactic: a divisor is smaller than another one
if the same relation holds with the associated functions. -/
@[simp]
lemma le_fun {D₁ D₂ : Divisor U} : D₁ ≤ D₂ ↔ D₁.toFun ≤ D₂.toFun := ⟨(·),(·)⟩

/-- Divisors form an ordered commutative group -/
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

/-- Divisors have a partial ordering by pointwise comparison of the associated
functions. -/
instance : LT (Divisor U) where
  lt := fun D₁ D₂ ↦ D₁.toFun < D₂.toFun

/-- Helper lemma for the `simp` tactic: a divisor is smaller than another one
if the same relation holds with the associated functions. -/
@[simp]
lemma lt_fun {D₁ D₂ : Divisor U} : D₁ < D₂ ↔ D₁.toFun < D₂.toFun := ⟨(·),(·)⟩

instance : Max (Divisor U) where
  max := fun D₁ D₂ ↦
    {
      toFun := fun z ↦ max (D₁ z) (D₂ z)
      supportInU := by
        intro x
        contrapose
        intro hx
        simp [Function.nmem_support.1 fun a ↦ hx (D₁.supportInU a),
          Function.nmem_support.1 fun a ↦ hx (D₂.supportInU a)]
      supportDiscreteWithinU := by
        filter_upwards [D₁.supportDiscreteWithinU, D₂.supportDiscreteWithinU]
        intro _ h₁ h₂
        simp [h₁, h₂]
    }

@[simp]
lemma max_fun {D₁ D₂ : Divisor U} {x : 𝕜} : max D₁ D₂ x = max (D₁ x) (D₂ x) := rfl

instance : Min (Divisor U) where
  min := fun D₁ D₂ ↦
    {
      toFun := fun z ↦ min (D₁ z) (D₂ z)
      supportInU := by
        intro x
        contrapose
        intro hx
        simp [Function.nmem_support.1 fun a ↦ hx (D₁.supportInU a),
          Function.nmem_support.1 fun a ↦ hx (D₂.supportInU a)]
      supportDiscreteWithinU := by
        filter_upwards [D₁.supportDiscreteWithinU, D₂.supportDiscreteWithinU]
        intro _ h₁ h₂
        simp [h₁, h₂]
    }

@[simp]
lemma min_fun {D₁ D₂ : Divisor U} {x : 𝕜} : min D₁ D₂ x = min (D₁ x) (D₂ x) := rfl

instance : Lattice (Divisor U) where
  le := (· ≤ ·)
  le_refl := by simp
  le_trans := by exact fun D₁ D₂ D₃ h₁₂ h₂₃ x ↦ (h₁₂ x).trans (h₂₃ x)
  le_antisymm := by
    intro D₁ D₂ h₁₂ h₂₁
    ext x
    exact Int.le_antisymm (h₁₂ x) (h₂₁ x)
  sup := (max · ·)
  le_sup_left := fun D₁ D₂ x ↦ by simp
  le_sup_right := fun D₁ D₂ x ↦ by simp
  sup_le := fun D₁ D₂ D₃ h₁₃ h₂₃ x ↦ by simp [h₁₃ x, h₂₃ x]
  inf := (min · ·)
  inf_le_left := fun D₁ D₂ x ↦ by simp
  inf_le_right := fun D₁ D₂ x ↦ by simp
  le_inf := fun D₁ D₂ D₃ h₁₃ h₂₃ x ↦ by simp [h₁₃ x, h₂₃ x]

/-!
## Elementary properties of the support
-/

theorem discreteSupport (D : Divisor U) :
    DiscreteTopology D.toFun.support := by
  have : Function.support D = {x | D x = 0}ᶜ ∩ U := by
    ext x
    constructor
    · exact fun hx ↦ ⟨by tauto, D.supportInU hx⟩
    · intro hx
      rw [mem_inter_iff, mem_compl_iff, mem_setOf_eq] at hx
      tauto
  convert discreteTopology_of_codiscreteWithin (D.supportDiscreteWithinU)

theorem closedSupport (D : Divisor U) (hU : IsClosed U) :
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
    simp only [mem_compl_iff, Function.mem_support, ne_eq, Decidable.not_not]
    exact Function.nmem_support.mp fun a ↦ hy (D.supportInU a)

theorem finiteSupport (D : Divisor U) (hU : IsCompact U) :
    Set.Finite D.toFun.support :=
  (hU.of_isClosed_subset (D.closedSupport hU.isClosed) D.supportInU).finite D.discreteSupport

/-!
## Restriction
-/

noncomputable def restrict {V : Set 𝕜} (D : Divisor U) (h : V ⊆ U) :
    Divisor V where
  toFun := by
    classical
    exact fun z ↦ if hz : z ∈ V then D z else 0
  supportInU := by
    intro x hx
    simp_rw [dite_eq_ite, Function.mem_support, ne_eq, ite_eq_right_iff,
      Classical.not_imp] at hx
    exact hx.1
  supportDiscreteWithinU := by
    apply Filter.codiscreteWithin.mono h
    filter_upwards [D.supportDiscreteWithinU]
    intro x hx
    simp [hx]

noncomputable def restrict_orderHom {V : Set 𝕜} (h : V ⊆ U) : Divisor U →o Divisor V where
  toFun := fun D ↦ D.restrict h
  monotone' := by
    intro D₁ D₂ h₁₂
    simp only [le_fun, Divisor.restrict]
    intro x
    by_cases hx : x ∈ V
    <;> simp [hx, reduceDIte, h₁₂ x]

noncomputable def restrict_groupHom {V : Set 𝕜} (h : V ⊆ U) : Divisor U →+ Divisor V where
  toFun := fun D ↦ D.restrict h
  map_zero' := by
    ext x
    simp [restrict]
  map_add' := by
    intro D₁ D₂
    ext x
    by_cases hx : x ∈ V
    <;> simp [restrict, hx]

noncomputable def restrict_latticeHom {V : Set 𝕜} (h : V ⊆ U) :
    LatticeHom (Divisor U) (Divisor V) where
  toFun := fun D ↦ D.restrict h
  map_sup' := by
    intro D₁ D₂
    ext x
    by_cases hx : x ∈ V
    <;> simp [Divisor.restrict, hx]
  map_inf' := by
    intro D₁ D₂
    ext x
    by_cases hx : x ∈ V
    <;> simp [Divisor.restrict, hx]

/-!
## Derived invariants
-/

/-- The degree of a divisor is the sum of its values, or 0 if the support is
infinite. -/
noncomputable def deg (D : Divisor U) : ℤ := ∑ᶠ z, D z
