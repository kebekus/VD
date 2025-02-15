import Mathlib.Analysis.SpecialFunctions.Integrals
import VD.mathlibAddOn
import VD.ToMathlib.codiscreteWithin

open Interval Topology
open Real Filter MeasureTheory intervalIntegral


structure Divisor (U : Set ℂ)
  where
  toFun : ℂ → ℤ
  supportInU : toFun.support ⊆ U
  supportDiscreteWithinU : toFun =ᶠ[Filter.codiscreteWithin U] 0

instance (U : Set ℂ) : CoeFun (Divisor U) (fun _ ↦ ℂ → ℤ)
  where
  coe := Divisor.toFun

attribute [coe] Divisor.toFun


theorem Divisor.discreteSupport
  {U : Set ℂ}
  (D : Divisor U) :
  DiscreteTopology D.toFun.support := by
  have : Function.support D = {x | D x = 0}ᶜ ∩ U := by
    ext x
    constructor
    · exact fun hx ↦ ⟨by tauto, D.supportInU hx⟩
    · intro hx
      rw [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq] at hx
      tauto
  rw [this]
  exact discreteTopology_of_codiscreteWithin (D.supportDiscreteWithinU)


theorem Divisor.closedSupport
  {U : Set ℂ}
  (hU : IsClosed U)
  (D : Divisor U) :
  IsClosed D.toFun.support := by
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_eventually]
  intro x hx
  by_cases h₁x : x ∈ U
  · have Z₁ := D.supportDiscreteWithinU
    rw [Filter.EventuallyEq, Filter.Eventually] at Z₁
    rw [mem_codiscreteWithin] at Z₁
    have Z₂ := Z₁ x h₁x
    rw [Filter.disjoint_principal_right] at Z₂
    filter_upwards [eventually_nhdsWithin_iff.1 Z₂]
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
    use Uᶜ
    constructor
    · exact IsClosed.compl_mem_nhds hU h₁x
    · intro y hy
      simp
      exact Function.nmem_support.mp fun a => hy (D.supportInU a)


theorem Divisor.finiteSupport
  {U : Set ℂ}
  (hU : IsCompact U)
  (D : Divisor U) :
  Set.Finite D.toFun.support := by
  apply IsCompact.finite
  · apply IsCompact.of_isClosed_subset hU (D.closedSupport hU.isClosed)
    exact D.supportInU
  · exact D.discreteSupport
