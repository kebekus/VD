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

- Extensionality lemmas
- Group structure
- Partial ordering
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

structure Divisor (U : Set 𝕜)
  where
  toFun : 𝕜 → ℤ
  supportInU : toFun.support ⊆ U
  supportDiscreteWithinU : toFun =ᶠ[Filter.codiscreteWithin U] 0

instance (U : Set 𝕜) : CoeFun (Divisor U) (fun _ ↦ 𝕜 → ℤ)
  where
  coe := Divisor.toFun

attribute [coe] Divisor.toFun

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

lemma ne_iff {D₁ D₂ : Divisor U} : D₁ ≠ D₂ ↔ ∃ a, D₁ a ≠ D₂ a := DFunLike.ne_iff

--

instance instZero : Zero (Divisor U) where
  zero := ⟨fun _ ↦ 0, by simp, Eq.eventuallyEq rfl⟩

@[simp]
theorem zero_fun : (0 : Divisor U).toFun = 0 := rfl

lemma support_add (D₁ D₂ : Divisor U) :
    (D₁.toFun + D₂.toFun).support ⊆ D₁.toFun.support ∪ D₂.toFun.support := by
  intro x
  contrapose
  intro h₁ h₂
  simp_all [h₁, h₂]

instance : Add (Divisor U) where
  add := by
    intro D₁ D₂
    exact {
      toFun := D₁.toFun + D₂.toFun
      supportInU := by
        intro x hx
        have Z := support_add D₁ D₂ hx
        rcases Z with h | h
        · exact D₁.supportInU h
        · exact D₂.supportInU h
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
theorem neg_fun {D : Divisor U} : (-D).toFun = -(D.toFun)  := rfl

instance instAddCommGroup : AddCommGroup (Divisor U) where
  add := (· + · )
  add_assoc := by
    intro _ _ _
    ext
    simp [add_assoc]
  zero := 0
  zero_add := by
    intro _
    ext
    simp
  add_zero := by
    intro _
    ext
    simp
  nsmul := by
    intro n D
    exact {
      toFun := fun z ↦ n * D z
      supportInU := by
        intro x hx
        simp at hx
        exact D.supportInU hx.2
      supportDiscreteWithinU := by
        apply EventuallyEq.mul (f := n) (g := n) (f' := D) (g' := 0)
        exact Eq.eventuallyEq rfl
        exact D.supportDiscreteWithinU
    }
  neg := (- ·)
  zsmul := by
    intro n D
    exact {
      toFun := fun z ↦ n * D z
      supportInU := by
        intro x hx
        simp at hx
        exact D.supportInU hx.2
      supportDiscreteWithinU := by
        sorry
    }
  neg_add_cancel := by
    intros
    ext z
    simp
  add_comm := by
    intro D₁ D₂
    ext
    simp
  nsmul_zero := by
    intro D
    ext z
    simp
  nsmul_succ := by
    intro n D
    ext z
    simp
    ring
  zsmul_zero' := by
    intro D
    ext
    simp
  zsmul_succ' := by
    intro n D
    ext
    simp
    ring
  zsmul_neg' := by
    intro n D
    ext
    simp
    sorry


/-
section Basic

variable [Zero M]



@[simp]
theorem mem_support_iff {f : α →₀ M} : ∀ {a : α}, a ∈ f.support ↔ f a ≠ 0 :=
  @(f.mem_support_toFun)

@[simp, norm_cast]
theorem fun_support_eq (f : α →₀ M) : Function.support f = f.support :=
  Set.ext fun _x => mem_support_iff.symm

theorem not_mem_support_iff {f : α →₀ M} {a} : a ∉ f.support ↔ f a = 0 :=
  not_iff_comm.1 mem_support_iff.symm

@[simp, norm_cast]
theorem coe_eq_zero {f : α →₀ M} : (f : α → M) = 0 ↔ f = 0 := by rw [← coe_zero, DFunLike.coe_fn_eq]

theorem ext_iff' {f g : α →₀ M} : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      classical
      exact if h : a ∈ f.support then h₂ a h else by
        have hf : f a = 0 := not_mem_support_iff.1 h
        have hg : g a = 0 := by rwa [h₁, not_mem_support_iff] at h
        rw [hf, hg]⟩

@[simp]
theorem support_eq_empty {f : α →₀ M} : f.support = ∅ ↔ f = 0 :=
  mod_cast @Function.support_eq_empty_iff _ _ _ f

theorem support_nonempty_iff {f : α →₀ M} : f.support.Nonempty ↔ f ≠ 0 := by
  simp only [Finsupp.support_eq_empty, Finset.nonempty_iff_ne_empty, Ne]

theorem card_support_eq_zero {f : α →₀ M} : #f.support = 0 ↔ f = 0 := by simp

instance instDecidableEq [DecidableEq α] [DecidableEq M] : DecidableEq (α →₀ M) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ a ∈ f.support, f a = g a) ext_iff'.symm

theorem finite_support (f : α →₀ M) : Set.Finite (Function.support f) :=
  f.fun_support_eq.symm ▸ f.support.finite_toSet

theorem support_subset_iff {s : Set α} {f : α →₀ M} :
    ↑f.support ⊆ s ↔ ∀ a ∉ s, f a = 0 := by
  simp only [Set.subset_def, mem_coe, mem_support_iff]; exact forall_congr' fun a => not_imp_comm

/-- Given `Finite α`, `equivFunOnFinite` is the `Equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
def equivFunOnFinite [Finite α] : (α →₀ M) ≃ (α → M) where
  toFun := (⇑)
  invFun f := mk (Function.support f).toFinite.toFinset f fun _a => Set.Finite.mem_toFinset _
  left_inv _f := ext fun _x => rfl
  right_inv _f := rfl

@[simp]
theorem equivFunOnFinite_symm_coe {α} [Finite α] (f : α →₀ M) : equivFunOnFinite.symm f = f :=
  equivFunOnFinite.symm_apply_apply f

@[simp]
lemma coe_equivFunOnFinite_symm {α} [Finite α] (f : α → M) : ⇑(equivFunOnFinite.symm f) = f := rfl

/--
If `α` has a unique term, the type of finitely supported functions `α →₀ β` is equivalent to `β`.
-/
@[simps!]
noncomputable def _root_.Equiv.finsuppUnique {ι : Type*} [Unique ι] : (ι →₀ M) ≃ M :=
  Finsupp.equivFunOnFinite.trans (Equiv.funUnique ι M)

@[ext]
theorem unique_ext [Unique α] {f g : α →₀ M} (h : f default = g default) : f = g :=
  ext fun a => by rwa [Unique.eq_default a]

end Basic

-/
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
