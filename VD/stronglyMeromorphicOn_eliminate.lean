import VD.codiscreteWithin
import VD.stronglyMeromorphicOn_ratlPolynomial

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

theorem MeromorphicOn.decompose₁
  {f : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : ℂ}
  (h₁f : MeromorphicOn f U)
  (h₂f : StronglyMeromorphicAt f z₀)
  (h₃f : h₂f.meromorphicAt.order ≠ ⊤)
  (hz₀ : z₀ ∈ U) :
  ∃ g : ℂ → ℂ, (MeromorphicOn g U)
    ∧ (AnalyticAt ℂ g z₀)
    ∧ (g z₀ ≠ 0)
    ∧ (f = g * fun z ↦ (z - z₀) ^ (h₁f.divisor z₀)) := by

  let h₁ := fun z ↦ (z - z₀) ^ (-h₁f.divisor z₀)
  have h₁h₁ : MeromorphicOn h₁ U := by
    apply MeromorphicOn.zpow
    apply AnalyticOnNhd.meromorphicOn
    apply AnalyticOnNhd.sub
    exact analyticOnNhd_id
    exact analyticOnNhd_const
  let n : ℤ := (-h₁f.divisor z₀)
  have h₂h₁ : (h₁h₁ z₀ hz₀).order = n := by
    simp_rw [(h₁h₁ z₀ hz₀).order_eq_int_iff]
    use 1
    constructor
    · apply analyticAt_const
    · constructor
      · simp
      · apply eventually_nhdsWithin_of_forall
        intro z hz
        simp [n, h₁]

  let g₁ := f * h₁
  have h₁g₁ : MeromorphicOn g₁ U := by
    apply h₁f.mul h₁h₁
  have h₂g₁ : (h₁g₁ z₀ hz₀).order = 0 := by
    rw [(h₁f z₀ hz₀).order_mul (h₁h₁ z₀ hz₀)]
    rw [h₂h₁]
    unfold n
    rw [MeromorphicOn.divisor_def₂ h₁f hz₀ h₃f]
    conv =>
      left
      left
      rw [Eq.symm (WithTop.coe_untop (h₁f z₀ hz₀).order h₃f)]
    have
      (a b c : ℤ)
      (h : a + b = c) :
      (a : WithTop ℤ) + (b : WithTop ℤ) = (c : WithTop ℤ) := by
      rw [← h]
      simp
    rw [this ((h₁f z₀ hz₀).order.untop h₃f) (-(h₁f z₀ hz₀).order.untop h₃f) 0]
    simp
    ring

  let g := (h₁g₁ z₀ hz₀).makeStronglyMeromorphicAt
  have h₂g : StronglyMeromorphicAt g z₀ := by
    exact StronglyMeromorphicAt_of_makeStronglyMeromorphic (h₁g₁ z₀ hz₀)
  have h₁g : MeromorphicOn g U := by
    intro z hz
    by_cases h₁z : z = z₀
    · rw [h₁z]
      apply h₂g.meromorphicAt
    · apply (h₁g₁ z hz).congr
      rw [eventuallyEq_nhdsWithin_iff]
      rw [eventually_nhds_iff]
      use {z₀}ᶜ
      constructor
      · intro y h₁y h₂y
        let A := m₁ (h₁g₁ z₀ hz₀) y h₁y
        unfold g
        rw [← A]
      · constructor
        · exact isOpen_compl_singleton
        · exact h₁z
  have h₃g : (h₁g z₀ hz₀).order = 0 := by
    unfold g
    let B := m₂ (h₁g₁ z₀ hz₀)
    let A := (h₁g₁ z₀ hz₀).order_congr B
    rw [← A]
    rw [h₂g₁]
  have h₄g : AnalyticAt ℂ g z₀ := by
    apply h₂g.analytic
    rw [h₃g]

  use g
  constructor
  · exact h₁g
  · constructor
    · exact h₄g
    · constructor
      · exact (h₂g.order_eq_zero_iff).mp h₃g
      · funext z
        by_cases hz : z = z₀
        · rw [hz]
          simp
          by_cases h : h₁f.divisor z₀ = 0
          · simp [h]
            have h₂h₁ : h₁ = 1 := by
              funext w
              unfold h₁
              simp [h]
            have h₃g₁ : g₁ = f := by
              unfold g₁
              rw [h₂h₁]
              simp
            have h₄g₁ : StronglyMeromorphicAt g₁ z₀ := by
              rwa [h₃g₁]
            let A := h₄g₁.makeStronglyMeromorphic_id
            unfold g
            rw [← A, h₃g₁]
          · have : (0 : ℂ) ^ h₁f.divisor z₀ = (0 : ℂ) := by
              exact zero_zpow (h₁f.divisor z₀) h
            rw [this]
            simp
            let A := h₂f.order_eq_zero_iff.not
            simp at A
            rw [← A]
            unfold MeromorphicOn.divisor at h
            simp [hz₀] at h
            exact h.1
        · simp
          let B := m₁ (h₁g₁ z₀ hz₀) z hz
          unfold g
          rw [← B]
          unfold g₁ h₁
          simp [hz]
          rw [mul_assoc]
          rw [inv_mul_cancel₀]
          simp
          apply zpow_ne_zero
          rwa [sub_ne_zero]


theorem MeromorphicOn.decompose₂
  {f : ℂ → ℂ}
  {U : Set ℂ}
  {P : Finset U}
  (hf : StronglyMeromorphicOn f U) :
  (∀ p ∈ P, (hf p p.2).meromorphicAt.order ≠ ⊤) →
    ∃ g : ℂ → ℂ, (MeromorphicOn g U)
    ∧ (∀ p : P, AnalyticAt ℂ g p)
    ∧ (∀ p : P, g p ≠ 0)
    ∧ (f = g * ∏ p : P, fun z ↦ (z - p.1.1) ^ (hf.meromorphicOn.divisor p.1.1)) := by

  apply Finset.induction (p := fun (P : Finset U) ↦
    (∀ p ∈ P, (hf p p.2).meromorphicAt.order ≠ ⊤) →
    ∃ g : ℂ → ℂ, (MeromorphicOn g U)
    ∧ (∀ p : P, AnalyticAt ℂ g p)
    ∧ (∀ p : P, g p ≠ 0)
    ∧ (f = g * ∏ p : P, fun z ↦ (z - p.1.1) ^ (hf.meromorphicOn.divisor p.1.1)))

  -- case empty
  simp
  exact hf.meromorphicOn

  -- case insert
  intro u P hu iHyp
  intro hOrder
  obtain ⟨g₀, h₁g₀, h₂g₀, h₃g₀, h₄g₀⟩ := iHyp (fun p hp ↦ hOrder p (Finset.mem_insert_of_mem hp))

  have h₀ : AnalyticAt ℂ (∏ p : P, fun z ↦ (z - p.1.1) ^ (hf.meromorphicOn.divisor p.1.1)) u := by
    have : (∏ p : P, fun z ↦ (z - p.1.1) ^ (hf.meromorphicOn.divisor p.1.1)) = (fun z => ∏ p : P, (z - p.1.1) ^ (hf.meromorphicOn.divisor p.1.1)) := by
      funext w
      simp
    rw [this]
    apply Finset.analyticAt_prod
    intro p hp
    apply AnalyticAt.zpow
    fun_prop
    by_contra hCon
    rw [sub_eq_zero] at hCon
    have : p.1 = u := by
      exact SetCoe.ext (_root_.id (Eq.symm hCon))
    rw [← this] at hu
    simp [hp] at hu

  have h₁ : (∏ p : P, fun z ↦ (z - p.1.1) ^ (hf.meromorphicOn.divisor p.1.1)) u ≠ 0 := by
    simp only [Finset.prod_apply]
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    apply zpow_ne_zero
    by_contra hCon
    rw [sub_eq_zero] at hCon
    have : p.1 = u := by
      exact SetCoe.ext (_root_.id (Eq.symm hCon))
    rw [← this] at hu
    simp [hp] at hu

  have h₅g₀ : StronglyMeromorphicAt g₀ u := by
    rw [stronglyMeromorphicAt_of_mul_analytic h₀ h₁]
    rw [← h₄g₀]
    exact hf u u.2

  have h₆g₀ : (h₁g₀ u u.2).order ≠ ⊤ := by
    by_contra hCon
    let A := (h₁g₀ u u.2).order_mul h₀.meromorphicAt
    simp_rw [← h₄g₀, hCon] at A
    simp at A
    let B := hOrder u (Finset.mem_insert_self u P)
    tauto

  obtain ⟨g, h₁g, h₂g, h₃g, h₄g⟩ := h₁g₀.decompose₁ h₅g₀ h₆g₀ u.2
  use g
  · constructor
    · exact h₁g
    · constructor
      · intro ⟨v₁, v₂⟩
        simp
        simp at v₂
        rcases v₂ with hv|hv
        · rwa [hv]
        · let A := h₂g₀ ⟨v₁, hv⟩
          rw [h₄g] at A
          rw [mul_comm, ← analyticAt_of_mul_analytic] at A
          simp at A
          exact A
          --
          simp
          apply AnalyticAt.zpow
          fun_prop
          by_contra hCon
          rw [sub_eq_zero] at hCon

          have : v₁ = u := by
            exact SetCoe.ext hCon
          rw [this] at hv
          tauto
          --
          apply zpow_ne_zero
          simp
          by_contra hCon
          rw [sub_eq_zero] at hCon
          have : v₁ = u := by
            exact SetCoe.ext hCon
          rw [this] at hv
          tauto

      · constructor
        · intro ⟨v₁, v₂⟩
          simp
          simp at v₂
          rcases v₂ with hv|hv
          · rwa [hv]
          · by_contra hCon
            let A := h₃g₀ ⟨v₁,hv⟩
            rw [h₄g] at A
            simp at A
            tauto
        · conv =>
            left
            rw [h₄g₀, h₄g]
          simp
          rw [mul_assoc]
          congr
          rw [Finset.prod_insert]
          simp
          congr
          have : (hf u u.2).meromorphicAt.order = (h₁g₀ u u.2).order := by
            have h₅g₀ : f =ᶠ[𝓝 u.1] (g₀ * ∏ p : P, fun z => (z - p.1.1) ^ (hf.meromorphicOn.divisor p.1.1)) := by
              exact Eq.eventuallyEq h₄g₀
            have h₆g₀ : f =ᶠ[𝓝[≠] u.1] (g₀ * ∏ p : P, fun z => (z - p.1.1) ^ (hf.meromorphicOn.divisor p.1.1)) := by
              exact eventuallyEq_nhdsWithin_of_eqOn fun ⦃x⦄ a => congrFun h₄g₀ x
            rw [(hf u u.2).meromorphicAt.order_congr h₆g₀]
            let C := (h₁g₀ u u.2).order_mul h₀.meromorphicAt
            rw [C]
            let D := h₀.order_eq_zero_iff.2 h₁
            let E := h₀.meromorphicAt_order
            rw [E, D]
            simp
          have : hf.meromorphicOn.divisor u = h₁g₀.divisor u := by
            unfold MeromorphicOn.divisor
            simp
            rw [this]
          rw [this]
          --
          simpa


theorem MeromorphicOn.decompose₃'
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁U : IsCompact U)
  (h₂U : IsConnected U)
  (h₁f : StronglyMeromorphicOn f U)
  (h₂f : ∃ u : U, f u ≠ 0) :
  ∃ g : ℂ → ℂ, (MeromorphicOn g U)
    ∧ (AnalyticOnNhd ℂ g U)
    ∧ (∀ u : U, g u ≠ 0)
    ∧ (f = g * ∏ᶠ u, fun z ↦ (z - u) ^ (h₁f.meromorphicOn.divisor u)) := by

  have h₃f : ∀ u : U, (h₁f u u.2).meromorphicAt.order ≠ ⊤ :=
    StronglyMeromorphicOn.order_ne_top h₁f h₂U h₂f
  have h₄f : Set.Finite (Function.support h₁f.meromorphicOn.divisor) := h₁f.meromorphicOn.divisor.finiteSupport h₁U

  let d := - h₁f.meromorphicOn.divisor.toFun
  have h₁d : d.support = (Function.support h₁f.meromorphicOn.divisor) := by
    ext x
    unfold d
    simp
  let h₁ := ∏ᶠ u, fun z ↦ (z - u) ^ (d u)
  have h₁h₁ : StronglyMeromorphicOn h₁ U := by
    intro z hz
    exact stronglyMeromorphicOn_ratlPolynomial₃ d z trivial
  have h₂h₁ : h₁h₁.meromorphicOn.divisor = d := by
    apply stronglyMeromorphicOn_divisor_ratlPolynomial_U
    rwa [h₁d]
    --
    rw [h₁d]
    exact (StronglyMeromorphicOn.meromorphicOn h₁f).divisor.supportInU
  have h₃h₁ : ∀ (z : ℂ) (hz : z ∈ U), (h₁h₁ z hz).meromorphicAt.order ≠ ⊤ := by
    intro z hz
    apply stronglyMeromorphicOn_ratlPolynomial₃order
  have h₄h₁ : ∀ (z : ℂ) (hz : z ∈ U), (h₁h₁ z hz).meromorphicAt.order = d z := by
    intro z hz
    rw [stronglyMeromorphicOn_divisor_ratlPolynomial₁]
    rwa [h₁d]

  let g' := f * h₁
  have h₁g' : MeromorphicOn g' U := h₁f.meromorphicOn.mul h₁h₁.meromorphicOn
  have h₂g' : h₁g'.divisor.toFun = 0 := by
    rw [MeromorphicOn.divisor_mul h₁f.meromorphicOn (fun z hz ↦ h₃f ⟨z, hz⟩) h₁h₁.meromorphicOn h₃h₁]
    rw [h₂h₁]
    unfold d
    simp
  have h₃g' : ∀ u : U, (h₁g' u.1 u.2).order = 0 := by
    intro u
    rw [(h₁f u.1 u.2).meromorphicAt.order_mul (h₁h₁ u.1 u.2).meromorphicAt]
    rw [h₄h₁]
    unfold d
    unfold MeromorphicOn.divisor
    simp
    have : (h₁f u.1 u.2).meromorphicAt.order = WithTop.untop' 0 (h₁f u.1 u.2).meromorphicAt.order := by
      rw [eq_comm]
      let A := h₃f u
      exact untop'_of_ne_top A
    rw [this]
    simp
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
    rw [← WithTop.coe_add]
    simp
    exact u.2

  let g := h₁g'.makeStronglyMeromorphicOn
  have h₁g : StronglyMeromorphicOn g U := stronglyMeromorphicOn_of_makeStronglyMeromorphicOn h₁g'
  have h₂g : h₁g.meromorphicOn.divisor.toFun = 0 := by
    rw [← MeromorphicOn.divisor_of_makeStronglyMeromorphicOn]
    rw [h₂g']
  have h₃g : AnalyticOnNhd ℂ g U := by
    apply StronglyMeromorphicOn.analyticOnNhd
    rw [h₂g]
    simp
    assumption
  have h₄g : ∀ u : U, g u ≠ 0 := by
    intro u
    rw [← (h₁g u.1 u.2).order_eq_zero_iff]
    rw [makeStronglyMeromorphicOn_changeOrder]
    let A := h₃g' u
    exact A
    exact u.2

  use g
  constructor
  · exact StronglyMeromorphicOn.meromorphicOn h₁g
  · constructor
    · exact h₃g
    · constructor
      · exact h₄g
      · have t₀ : StronglyMeromorphicOn (g * ∏ᶠ (u : ℂ), fun z => (z - u) ^ (h₁f.meromorphicOn.divisor u)) U := by
          apply stronglyMeromorphicOn_of_mul_analytic' h₃g h₄g
          apply stronglyMeromorphicOn_ratlPolynomial₃U

        funext z
        by_cases hz : z ∈ U
        · apply Filter.EventuallyEq.eq_of_nhds
          apply StronglyMeromorphicAt.localIdentity (h₁f z hz) (t₀ z hz)
          have h₅g : g =ᶠ[𝓝[≠] z] g' := makeStronglyMeromorphicOn_changeDiscrete h₁g' hz
          have Y' : (g' * ∏ᶠ (u : ℂ), fun z => (z - u) ^ (h₁f.meromorphicOn.divisor u)) =ᶠ[𝓝[≠] z] g * ∏ᶠ (u : ℂ), fun z => (z - u) ^ (h₁f.meromorphicOn.divisor u) := by
            apply Filter.EventuallyEq.symm
            exact Filter.EventuallyEq.mul h₅g (by simp)
          apply Filter.EventuallyEq.trans _ Y'
          unfold g'
          unfold h₁

          let A := h₁f.meromorphicOn.divisor.locallyFiniteInU z hz
          let B := eventually_nhdsWithin_iff.1 A
          obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 B

          apply eventually_nhdsWithin_iff.2
          rw [eventually_nhds_iff]
          use t
          constructor
          · intro y h₁y h₂y
            let C := h₁t y h₁y h₂y
            rw [mul_assoc]
            simp
            have : (finprod (fun u z => (z - u) ^ d u) y * finprod (fun u z => (z - u) ^ (h₁f.meromorphicOn.divisor u)) y) = 1 := by
              have t₀ : (Function.mulSupport fun u z => (z - u) ^ d u).Finite := by
                rwa [ratlPoly_mulsupport, h₁d]
              rw [finprod_eq_prod _ t₀]
              have t₁ : (Function.mulSupport fun u z => (z - u) ^ h₁f.meromorphicOn.divisor u).Finite := by
                rwa [ratlPoly_mulsupport]
              rw [finprod_eq_prod _ t₁]
              have : (Function.mulSupport fun u z => (z - u) ^ d u) = (Function.mulSupport fun u z => (z - u) ^ h₁f.meromorphicOn.divisor u) := by
                rw [ratlPoly_mulsupport]
                rw [ratlPoly_mulsupport]
                unfold d
                simp
              have : t₀.toFinset = t₁.toFinset := by congr
              rw [this]
              simp
              rw [← Finset.prod_mul_distrib]
              apply Finset.prod_eq_one
              intro x hx
              apply zpow_neg_mul_zpow_self
              have : y ∉ t₁.toFinset := by
                simp
                simp at C
                rw [C]
                simp
                tauto
              by_contra H
              rw [sub_eq_zero] at H
              rw [H] at this
              tauto

            rw [this]
            simp
          · exact ⟨h₂t, h₃t⟩
        · simp
          have : g z = g' z := by
            unfold g
            unfold MeromorphicOn.makeStronglyMeromorphicOn
            simp [hz]
          rw [this]
          unfold g'
          unfold h₁
          simp
          rw [mul_assoc]
          nth_rw 1 [← mul_one (f z)]
          congr
          have t₀ : (Function.mulSupport fun u z => (z - u) ^ d u).Finite := by
            rwa [ratlPoly_mulsupport, h₁d]
          rw [finprod_eq_prod _ t₀]
          have t₁ : (Function.mulSupport fun u z => (z - u) ^ h₁f.meromorphicOn.divisor u).Finite := by
            rwa [ratlPoly_mulsupport]
          rw [finprod_eq_prod _ t₁]
          have : (Function.mulSupport fun u z => (z - u) ^ d u) = (Function.mulSupport fun u z => (z - u) ^ h₁f.meromorphicOn.divisor u) := by
            rw [ratlPoly_mulsupport]
            rw [ratlPoly_mulsupport]
            unfold d
            simp
          have : t₀.toFinset = t₁.toFinset := by congr
          rw [this]
          simp
          rw [← Finset.prod_mul_distrib]
          rw [eq_comm]
          apply Finset.prod_eq_one
          intro x hx
          apply zpow_neg_mul_zpow_self

          have : z ∉ t₁.toFinset := by
            simp
            have : h₁f.meromorphicOn.divisor z = 0 := by
              let A := h₁f.meromorphicOn.divisor.supportInU
              simp at A
              by_contra H
              let B := A z H
              tauto
            rw [this]
            simp
            rfl
          by_contra H
          rw [sub_eq_zero] at H
          rw [H] at this
          tauto


theorem StronglyMeromorphicOn.decompose_log
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁U : IsCompact U)
  (h₂U : IsConnected U)
  (h₁f : StronglyMeromorphicOn f U)
  (h₂f : ∃ u : U, f u ≠ 0) :
  ∃ g : ℂ → ℂ, (MeromorphicOn g U)
    ∧ (AnalyticOnNhd ℂ g U)
    ∧ (∀ u : U, g u ≠ 0)
    ∧ (fun z ↦ log ‖f z‖) =ᶠ[Filter.codiscreteWithin U] fun z ↦ log ‖g z‖ + ∑ᶠ s, (h₁f.meromorphicOn.divisor s) * log ‖z - s‖ := by

  have h₃f : Set.Finite (Function.support h₁f.meromorphicOn.divisor) := by
    exact Divisor.finiteSupport h₁U (StronglyMeromorphicOn.meromorphicOn h₁f).divisor

  have hSupp₁ {z : ℂ} : (fun s ↦ (h₁f.meromorphicOn.divisor s) * log ‖z - s‖).support ⊆ h₃f.toFinset := by
    intro x
    contrapose
    simp; tauto
  simp_rw [finsum_eq_sum_of_support_subset _ hSupp₁]

  obtain ⟨g, h₁g, h₂g, h₃g, h₄g⟩ := MeromorphicOn.decompose₃' h₁U h₂U h₁f h₂f
  have hSupp₂ {z : ℂ} : ( fun (u : ℂ) ↦ (fun (z : ℂ) ↦ (z - u) ^ (h₁f.meromorphicOn.divisor u)) ).mulSupport ⊆ h₃f.toFinset := by
    intro x
    contrapose
    simp
    intro hx
    rw [hx]
    simp; tauto
  rw [finprod_eq_prod_of_mulSupport_subset _ hSupp₂] at h₄g

  use g
  simp only [h₁g, h₂g, h₃g, ne_eq, true_and, not_false_eq_true, implies_true]
  rw [Filter.eventuallyEq_iff_exists_mem]
  use {z | f z ≠ 0}
  constructor
  · have A := h₁f.meromorphicOn.divisor.codiscreteWithin
    have : {z | f z ≠ 0} ∩ U = (Function.support h₁f.meromorphicOn.divisor)ᶜ ∩ U := by
      rw [← h₁f.support_divisor h₂f h₂U]
      ext u
      simp; tauto

    rw [codiscreteWithin_congr_inter this]
    exact A

  · intro z hz
    nth_rw 1 [h₄g]
    simp
    rw [log_mul, log_prod]
    congr
    ext u
    rw [log_zpow]
    --
    intro x hx
    simp at hx
    have h₁x : x ∈ U := by
      exact h₁f.meromorphicOn.divisor.supportInU hx

    apply zpow_ne_zero
    simp

    by_contra hCon
    rw [← hCon] at hx
    unfold MeromorphicOn.divisor at hx
    rw [hCon] at hz
    simp at hz
    let A := (h₁f x h₁x).order_eq_zero_iff
    let B := A.2 hz
    simp [B] at hx
    obtain ⟨a, b⟩ := hx
    let c := b.1
    simp_rw [hCon] at c
    tauto
    --
    simp at hz
    by_contra hCon
    simp at hCon
    rw [h₄g] at hz
    simp at hz
    tauto
    --
    rw [Finset.prod_ne_zero_iff]
    intro x hx
    simp at hx
    have h₁x : x ∈ U := by
      exact h₁f.meromorphicOn.divisor.supportInU hx

    apply zpow_ne_zero
    simp

    by_contra hCon
    rw [← hCon] at hx
    unfold MeromorphicOn.divisor at hx
    rw [hCon] at hz
    simp at hz
    let A := (h₁f x h₁x).order_eq_zero_iff
    let B := A.2 hz
    simp [B] at hx
    obtain ⟨a, b⟩ := hx
    let c := b.1
    simp_rw [hCon] at c
    tauto

  exact 0


theorem MeromorphicOn.decompose_log
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁U : IsCompact U)
  (h₂U : IsConnected U)
  (h₃U : interior U ≠ ∅)
  (h₁f : MeromorphicOn f U)
  (h₂f : ∃ u : U, (h₁f u u.2).order ≠ ⊤) :
  ∃ g : ℂ → ℂ, (AnalyticOnNhd ℂ g U)
    ∧ (∀ u : U, g u ≠ 0)
    ∧ (fun z ↦ log ‖f z‖) =ᶠ[Filter.codiscreteWithin U] fun z ↦ log ‖g z‖ + ∑ᶠ s, (h₁f.divisor s) * log ‖z - s‖ := by

  let F := h₁f.makeStronglyMeromorphicOn
  have h₁F := stronglyMeromorphicOn_of_makeStronglyMeromorphicOn h₁f
  have h₂F : ∃ u : U, (h₁F.meromorphicOn u u.2).order ≠ ⊤ := by
    obtain ⟨u, hu⟩ := h₂f
    use u
    rw [makeStronglyMeromorphicOn_changeOrder h₁f u.2]
    assumption

  have t₁ : ∃ u : U, F u ≠ 0 := by
    let A := h₁F.meromorphicOn.nonvanish_of_order_ne_top h₂F h₂U h₃U
    tauto
  have t₃ : (fun z ↦ log ‖f z‖) =ᶠ[Filter.codiscreteWithin U] (fun z ↦ log ‖F z‖) := by
    -- This would be interesting for a tactic
    rw [eventuallyEq_iff_exists_mem]
    obtain ⟨s, h₁s, h₂s⟩ := eventuallyEq_iff_exists_mem.1 (makeStronglyMeromorphicOn_changeDiscrete'' h₁f)
    use s
    tauto

  obtain ⟨g, h₁g, h₂g, h₃g, h₄g⟩ := h₁F.decompose_log h₁U h₂U t₁
  use g
  constructor
  · exact h₂g
  · constructor
    · exact h₃g
    · apply t₃.trans
      rw [h₁f.divisor_of_makeStronglyMeromorphicOn]
      exact h₄g
