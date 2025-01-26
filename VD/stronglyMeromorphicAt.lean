import Mathlib.Analysis.Analytic.Meromorphic
import Mathlib.Algebra.Order.AddGroupWithTop
import VD.analyticAt
import VD.mathlibAddOn
import VD.meromorphicAt


open Topology


/- Strongly MeromorphicAt -/
def StronglyMeromorphicAt
  (f : ℂ → ℂ)
  (z₀ : ℂ) :=
  (∀ᶠ (z : ℂ) in nhds z₀, f z = 0) ∨ (∃ (n : ℤ), ∃ g : ℂ → ℂ, (AnalyticAt ℂ g z₀) ∧ (g z₀ ≠ 0) ∧ (∀ᶠ (z : ℂ) in nhds z₀, f z = (z - z₀) ^ n • g z))


lemma stronglyMeromorphicAt_of_mul_analytic'
  {f g : ℂ → ℂ}
  {z₀ : ℂ}
  (h₁g : AnalyticAt ℂ g z₀)
  (h₂g : g z₀ ≠ 0) :
  StronglyMeromorphicAt f z₀ → StronglyMeromorphicAt (f * g) z₀ := by

  intro hf
  --unfold StronglyMeromorphicAt at hf
  rcases hf with h₁f|h₁f
  · left
    rw [eventually_nhds_iff] at h₁f
    obtain ⟨t, ht⟩ := h₁f
    rw [eventually_nhds_iff]
    use t
    constructor
    · intro y hy
      simp
      left
      exact ht.1 y hy
    · exact ht.2
  · right
    obtain ⟨n, g_f, h₁g_f, h₂g_f, h₃g_f⟩ := h₁f
    use n
    use g * g_f
    constructor
    · apply AnalyticAt.mul
      exact h₁g
      exact h₁g_f
    · constructor
      · simp
        exact ⟨h₂g, h₂g_f⟩
      · rw [eventually_nhds_iff] at h₃g_f
        obtain ⟨t, ht⟩ := h₃g_f
        rw [eventually_nhds_iff]
        use t
        constructor
        · intro y hy
          simp
          rw [ht.1]
          simp
          ring
          exact hy
        · exact ht.2


/- Strongly MeromorphicAt is Meromorphic -/
theorem StronglyMeromorphicAt.meromorphicAt
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : StronglyMeromorphicAt f z₀) :
  MeromorphicAt f z₀ := by
  rcases hf with h|h
  · use 0; simp
    rw [analyticAt_congr h]
    exact analyticAt_const
  · obtain ⟨n, g, h₁g, _, h₃g⟩ := h
    rw [meromorphicAt_congr' h₃g]
    fun_prop


/- Strongly MeromorphicAt of non-negative order is analytic -/
theorem StronglyMeromorphicAt.analytic
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (h₁f : StronglyMeromorphicAt f z₀)
  (h₂f : 0 ≤ h₁f.meromorphicAt.order):
  AnalyticAt ℂ f z₀ := by
  let h₁f' := h₁f
  rcases h₁f' with h|h
  · rw [analyticAt_congr h]
    exact analyticAt_const
  · obtain ⟨n, g, h₁g, h₂g, h₃g⟩ := h
    rw [analyticAt_congr h₃g]

    have : h₁f.meromorphicAt.order = n := by
      rw [MeromorphicAt.order_eq_int_iff]
      use g
      constructor
      · exact h₁g
      · constructor
        · exact h₂g
        · exact Filter.EventuallyEq.filter_mono h₃g nhdsWithin_le_nhds
    rw [this] at h₂f
    apply AnalyticAt.smul'
    nth_rw 1 [← Int.toNat_of_nonneg (WithTop.coe_nonneg.mp h₂f)]
    fun_prop
    exact h₁g


/- Analytic functions are strongly meromorphic -/
theorem AnalyticAt.stronglyMeromorphicAt
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (h₁f : AnalyticAt ℂ f z₀) :
  StronglyMeromorphicAt f z₀ := by
  by_cases h₂f : h₁f.order = ⊤
  · rw [AnalyticAt.order_eq_top_iff] at h₂f
    tauto
  · have : h₁f.order ≠ ⊤ := h₂f
    rw [← ENat.coe_toNat_eq_self] at this
    rw [eq_comm, AnalyticAt.order_eq_nat_iff] at this
    right
    use h₁f.order.toNat
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := this
    use g
    tauto


/- Strong meromorphic depends only on germ -/
theorem stronglyMeromorphicAt_congr
  {f g : ℂ → ℂ}
  {z₀ : ℂ}
  (hfg : f =ᶠ[𝓝 z₀] g) :
  StronglyMeromorphicAt f z₀ ↔ StronglyMeromorphicAt g z₀ := by
  unfold StronglyMeromorphicAt
  constructor
  · intro h
    rcases h with h|h
    · left
      exact Filter.EventuallyEq.rw h (fun x => Eq (g x)) (id (Filter.EventuallyEq.symm hfg))
    · obtain ⟨n, h, h₁h, h₂h, h₃h⟩ := h
      right
      use n
      use h
      constructor
      · assumption
      · constructor
        · assumption
        · apply Filter.EventuallyEq.trans hfg.symm
          assumption
  · intro h
    rcases h with h|h
    · left
      exact Filter.EventuallyEq.rw h (fun x => Eq (f x)) hfg
    · obtain ⟨n, h, h₁h, h₂h, h₃h⟩ := h
      right
      use n
      use h
      constructor
      · assumption
      · constructor
        · assumption
        · apply Filter.EventuallyEq.trans hfg
          assumption

/- A function is strongly meromorphic at a point iff it is strongly meromorphic
   after multiplication with a non-vanishing analytic function
-/
theorem stronglyMeromorphicAt_of_mul_analytic
  {f g : ℂ → ℂ}
  {z₀ : ℂ}
  (h₁g : AnalyticAt ℂ g z₀)
  (h₂g : g z₀ ≠ 0) :
  StronglyMeromorphicAt f z₀ ↔ StronglyMeromorphicAt (f * g) z₀ := by
  constructor
  · apply stronglyMeromorphicAt_of_mul_analytic' h₁g h₂g
  · intro hprod
    let g' := fun z ↦ (g z)⁻¹
    have h₁g' := h₁g.inv h₂g
    have h₂g' : g' z₀ ≠ 0 := by
      exact inv_ne_zero h₂g

    let B := stronglyMeromorphicAt_of_mul_analytic' h₁g' h₂g' (f := f * g) hprod
    have : f =ᶠ[𝓝 z₀] f * g * fun x => (g x)⁻¹ := by
      unfold Filter.EventuallyEq
      apply Filter.eventually_iff_exists_mem.mpr
      use g⁻¹' {0}ᶜ
      constructor
      · apply ContinuousAt.preimage_mem_nhds
        exact AnalyticAt.continuousAt h₁g
        exact compl_singleton_mem_nhds_iff.mpr h₂g
      · intro y hy
        simp at hy
        simp [hy]
    rwa [stronglyMeromorphicAt_congr this]


theorem StronglyMeromorphicAt.order_eq_zero_iff
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : StronglyMeromorphicAt f z₀) :
  hf.meromorphicAt.order = 0 ↔ f z₀ ≠ 0 := by
  constructor
  · intro h₁f
    let A := hf.analytic (le_of_eq (id (Eq.symm h₁f)))
    apply A.order_eq_zero_iff.1
    let B := A.meromorphicAt_order
    rw [h₁f] at B
    apply WithTopCoe
    rw [eq_comm]
    exact B
  · intro h
    have hf' := hf
    rcases hf with h₁|h₁
    · have : f z₀ = 0 := by
        apply Filter.EventuallyEq.eq_of_nhds h₁
      tauto
    · obtain ⟨n, g, h₁g, h₂g, h₃g⟩ := h₁
      have : n = 0 := by
        by_contra hContra
        let A := Filter.EventuallyEq.eq_of_nhds h₃g
        have : (0 : ℂ) ^ n = 0 := by
          exact zero_zpow n hContra
        simp at A
        simp_rw [this] at A
        simp at A
        tauto
      rw [this] at h₃g
      simp at h₃g

      have : hf'.meromorphicAt.order = 0 := by
        apply (hf'.meromorphicAt.order_eq_int_iff 0).2
        use g
        constructor
        · assumption
        · constructor
          · assumption
          · simp
            apply Filter.EventuallyEq.filter_mono h₃g
            exact nhdsWithin_le_nhds
      exact this


theorem StronglyMeromorphicAt.localIdentity
  {f g : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : StronglyMeromorphicAt f z₀)
  (hg : StronglyMeromorphicAt g z₀) :
  f =ᶠ[𝓝[≠] z₀] g → f =ᶠ[𝓝 z₀] g := by

  intro h

  have t₀ : hf.meromorphicAt.order = hg.meromorphicAt.order := by
    exact hf.meromorphicAt.order_congr h

  by_cases cs : hf.meromorphicAt.order = 0
  · rw [cs] at t₀
    have h₁f := hf.analytic (le_of_eq (id (Eq.symm cs)))
    have h₁g := hg.analytic (le_of_eq t₀)
    exact h₁f.localIdentity h₁g h
  · apply Mnhds h
    let A := cs
    rw [hf.order_eq_zero_iff] at A
    simp at A
    let B := cs
    rw [t₀] at B
    rw [hg.order_eq_zero_iff] at B
    simp at B
    rw [A, B]



/- Make strongly MeromorphicAt -/
noncomputable def MeromorphicAt.makeStronglyMeromorphicAt
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : MeromorphicAt f z₀) :
  ℂ → ℂ := by
  intro z
  by_cases z = z₀
  · by_cases h₁f : hf.order = (0 : ℤ)
    · rw [hf.order_eq_int_iff] at h₁f
      exact (Classical.choose h₁f) z₀
    · exact 0
  · exact f z


lemma m₁
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : MeromorphicAt f z₀) :
  ∀ z ≠ z₀, f z = hf.makeStronglyMeromorphicAt z := by
  intro z hz
  unfold MeromorphicAt.makeStronglyMeromorphicAt
  simp [hz]


lemma m₂
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : MeromorphicAt f z₀) :
  f =ᶠ[𝓝[≠] z₀] hf.makeStronglyMeromorphicAt := by
  apply eventually_nhdsWithin_of_forall
  exact fun x a => m₁ hf x a


theorem StronglyMeromorphicAt_of_makeStronglyMeromorphic
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : MeromorphicAt f z₀) :
  StronglyMeromorphicAt hf.makeStronglyMeromorphicAt z₀ := by

  by_cases h₂f : hf.order = ⊤
  · have : hf.makeStronglyMeromorphicAt =ᶠ[𝓝 z₀] 0 := by
      apply Mnhds
      · apply Filter.EventuallyEq.trans (Filter.EventuallyEq.symm (m₂ hf))
        exact (MeromorphicAt.order_eq_top_iff hf).1 h₂f
      · unfold MeromorphicAt.makeStronglyMeromorphicAt
        simp [h₂f]

    apply AnalyticAt.stronglyMeromorphicAt
    rw [analyticAt_congr this]
    apply analyticAt_const
  · let n := hf.order.untop h₂f
    have : hf.order = n := by
      exact Eq.symm (WithTop.coe_untop hf.order h₂f)
    rw [hf.order_eq_int_iff] at this
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := this
    right
    use n
    use g
    constructor
    · assumption
    · constructor
      · assumption
      · apply Mnhds
        · apply Filter.EventuallyEq.trans (Filter.EventuallyEq.symm (m₂ hf))
          exact h₃g
        · unfold MeromorphicAt.makeStronglyMeromorphicAt
          simp
          by_cases h₃f : hf.order = (0 : ℤ)
          · let h₄f := (hf.order_eq_int_iff 0).1 h₃f
            simp [h₃f]
            obtain ⟨h₁G, h₂G, h₃G⟩  := Classical.choose_spec h₄f
            simp at h₃G
            have hn : n = 0 := Eq.symm ((fun {α} {a} {b} h => (WithTop.eq_untop_iff h).mpr) h₂f (id (Eq.symm h₃f)))
            rw [hn]
            rw [hn] at h₃g; simp at h₃g
            simp
            have : g =ᶠ[𝓝 z₀] (Classical.choose h₄f) := by
              apply h₁g.localIdentity h₁G
              exact Filter.EventuallyEq.trans (Filter.EventuallyEq.symm h₃g) h₃G
            rw [Filter.EventuallyEq.eq_of_nhds this]
          · have : hf.order ≠ 0 := h₃f
            simp [this]
            left
            apply zero_zpow n
            dsimp [n]
            rwa [WithTop.untop_eq_iff h₂f]


theorem StronglyMeromorphicAt.makeStronglyMeromorphic_id
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : StronglyMeromorphicAt f z₀) :
  f = hf.meromorphicAt.makeStronglyMeromorphicAt := by

  funext z
  by_cases hz : z = z₀
  · rw [hz]
    unfold MeromorphicAt.makeStronglyMeromorphicAt
    simp
    have h₀f := hf
    rcases hf with h₁f|h₁f
    · have A : f =ᶠ[𝓝[≠] z₀] 0 := by
        apply Filter.EventuallyEq.filter_mono h₁f
        exact nhdsWithin_le_nhds
      let B := (MeromorphicAt.order_eq_top_iff h₀f.meromorphicAt).2 A
      simp [B]
      exact Filter.EventuallyEq.eq_of_nhds h₁f
    · obtain ⟨n, g, h₁g, h₂g, h₃g⟩ := h₁f
      rw [Filter.EventuallyEq.eq_of_nhds h₃g]
      have : h₀f.meromorphicAt.order = n := by
        rw [MeromorphicAt.order_eq_int_iff (StronglyMeromorphicAt.meromorphicAt h₀f) n]
        use g
        constructor
        · assumption
        · constructor
          · assumption
          · exact eventually_nhdsWithin_of_eventually_nhds h₃g
      by_cases h₃f : h₀f.meromorphicAt.order = 0
      · simp [h₃f]
        have hn : n = (0 : ℤ) := by
          rw [h₃f] at this
          exact WithTop.coe_eq_zero.mp (id (Eq.symm this))
        simp_rw [hn]
        simp
        let t₀ : h₀f.meromorphicAt.order = (0 : ℤ) := by
          exact h₃f
        let A := (h₀f.meromorphicAt.order_eq_int_iff 0).1 t₀
        have : g =ᶠ[𝓝 z₀] (Classical.choose A) := by
          obtain ⟨h₀, h₁, h₂⟩  := Classical.choose_spec A
          apply h₁g.localIdentity h₀
          rw [hn] at h₃g
          simp at h₃g
          simp at h₂
          have h₄g : f =ᶠ[𝓝[≠] z₀] g := by
            apply Filter.EventuallyEq.filter_mono h₃g
            exact nhdsWithin_le_nhds
          exact Filter.EventuallyEq.trans (Filter.EventuallyEq.symm h₄g) h₂
        exact Filter.EventuallyEq.eq_of_nhds this
      · simp [h₃f]
        left
        apply zero_zpow n
        by_contra hn
        rw [hn] at this
        tauto
  · exact m₁ (StronglyMeromorphicAt.meromorphicAt hf) z hz


theorem StronglyMeromorphicAt.eliminate
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (h₁f : StronglyMeromorphicAt f z₀)
  (h₂f : h₁f.meromorphicAt.order ≠ ⊤) :
  ∃ g : ℂ → ℂ, (AnalyticAt ℂ g z₀)
    ∧ (g z₀ ≠ 0)
    ∧ (f = (fun z ↦ (z-z₀) ^ (h₁f.meromorphicAt.order.untop h₂f)) * g) := by

  let g₁ := (fun z ↦ (z-z₀) ^ (-h₁f.meromorphicAt.order.untop h₂f)) * f
  let g₁₁ := fun z ↦ (z-z₀) ^ (-h₁f.meromorphicAt.order.untop h₂f)
  have h₁g₁₁ : MeromorphicAt g₁₁ z₀ := by fun_prop
  have h₂g₁₁ : h₁g₁₁.order = - h₁f.meromorphicAt.order.untop h₂f := by
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
    rw [h₁g₁₁.order_eq_int_iff]
    use 1
    constructor
    · exact analyticAt_const
    · constructor
      · simp
      · apply eventually_nhdsWithin_of_forall
        simp [g₁₁]
  have h₁g₁ : MeromorphicAt g₁ z₀ := h₁g₁₁.mul h₁f.meromorphicAt
  have h₂g₁ : h₁g₁.order = 0 := by
    rw [h₁g₁₁.order_mul h₁f.meromorphicAt]
    rw [h₂g₁₁]
    simp
    rw [add_comm]
    rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top h₂f]
  let g := h₁g₁.makeStronglyMeromorphicAt
  use g
  have h₁g : StronglyMeromorphicAt g z₀ := by
    exact StronglyMeromorphicAt_of_makeStronglyMeromorphic h₁g₁
  have h₂g : h₁g.meromorphicAt.order = 0 := by
    rw [← h₁g₁.order_congr (m₂ h₁g₁)]
    exact h₂g₁
  constructor
  · apply analytic
    · rw [h₂g]
    · exact h₁g
  · constructor
    · rwa [← h₁g.order_eq_zero_iff]
    · funext z
      by_cases hz : z = z₀
      · by_cases hOrd : h₁f.meromorphicAt.order.untop h₂f = 0
        · simp [hOrd]
          have : StronglyMeromorphicAt g₁ z₀ := by
            unfold g₁
            simp [hOrd]
            have : (fun z => 1) * f = f := by
              funext z
              simp
            rwa [this]
          rw [hz]
          unfold g
          let A := makeStronglyMeromorphic_id this
          rw [← A]
          unfold g₁
          rw [hOrd]
          simp
        · have : h₁f.meromorphicAt.order ≠ 0 := by
            by_contra hC
            simp_rw [hC] at hOrd
            tauto
          let A := h₁f.order_eq_zero_iff.not.1 this
          simp at A
          rw [hz, A]
          simp
          left
          rw [zpow_eq_zero_iff]
          assumption
      · simp
        have : g z = g₁ z := by
          exact Eq.symm (m₁ h₁g₁ z hz)
        rw [this]
        unfold g₁
        simp [hz]
        rw [← mul_assoc]
        rw [mul_inv_cancel₀]
        simp
        apply zpow_ne_zero
        exact sub_ne_zero_of_ne hz
