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
