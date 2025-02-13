import Mathlib.Analysis.SpecialFunctions.Integrals
import VD.mathlibAddOn

open Interval Topology
open Real Filter MeasureTheory intervalIntegral


structure Divisor
  (U : Set ℂ)
  where
  toFun : ℂ → ℤ
  supportInU : toFun.support ⊆ U
  locallyFiniteInU : ∀ x ∈ U, toFun =ᶠ[𝓝[≠] x] 0

instance
  (U : Set ℂ) :
  CoeFun (Divisor U) (fun _ ↦ ℂ → ℤ) where
  coe := Divisor.toFun

attribute [coe] Divisor.toFun



theorem Divisor.discreteSupport
  {U : Set ℂ}
  (hU : IsClosed U)
  (D : Divisor U) :
  DiscreteTopology D.toFun.support := by
  apply discreteTopology_subtype_iff.mpr
  intro x hx
  apply inf_principal_eq_bot.mpr
  by_cases h₁x : x ∈ U
  · let A := D.locallyFiniteInU x h₁x
    refine mem_nhdsWithin.mpr ?_
    rw [eventuallyEq_nhdsWithin_iff] at A
    obtain ⟨U, h₁U, h₂U, h₃U⟩ := eventually_nhds_iff.1 A
    use U
    constructor
    · exact h₂U
    · constructor
      · exact h₃U
      · intro y hy
        let C := h₁U y hy.1 hy.2
        tauto
  · refine mem_nhdsWithin.mpr ?_
    use Uᶜ
    constructor
    · simpa
    · constructor
      · tauto
      · intro y _
        let A := D.supportInU
        simp at A
        simp
        exact False.elim (h₁x (A x hx))


theorem Divisor.closedSupport
  {U : Set ℂ}
  (hU : IsClosed U)
  (D : Divisor U) :
  IsClosed D.toFun.support := by

  rw [← isOpen_compl_iff]
  rw [isOpen_iff_eventually]
  intro x hx
  by_cases h₁x : x ∈ U
  · have A := D.locallyFiniteInU x h₁x
    simp [A]
    simp at hx
    let B := eventuallyEq_nhdsWithin_of_eventuallyEq_nhds A hx
    simpa
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
  · exact D.discreteSupport hU.isClosed


theorem Divisor.codiscreteWithin
  {U : Set ℂ}
  (D : Divisor U) :
  D.toFun.supportᶜ ∈ Filter.codiscreteWithin U := by

  simp_rw [mem_codiscreteWithin, disjoint_principal_right]
  intro x hx
  obtain ⟨s, hs⟩ := Filter.eventuallyEq_iff_exists_mem.1 (D.locallyFiniteInU x hx)
  apply Filter.mem_of_superset hs.1
  intro y hy
  simp [hy]
  tauto
