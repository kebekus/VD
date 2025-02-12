import Mathlib.Analysis.Meromorphic.Basic
import VD.meromorphicAt
import VD.ToMathlib.analyticAt

open Topology

variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def MeromorphicNFAt (f : 𝕜 → E) (x : 𝕜) :=
  (f =ᶠ[𝓝 x] 0) ∨ (∃ (n : ℤ), ∃ g : 𝕜 → E, (AnalyticAt 𝕜 g x) ∧ (g x ≠ 0) ∧ (f =ᶠ[𝓝 x] (· - x) ^ n • g ))

theorem meromorphicNFAt_def {f : 𝕜 → E} {x : 𝕜} :
    MeromorphicNFAt f x ↔  (f =ᶠ[𝓝 x] 0) ∨
    (∃ (n : ℤ), ∃ g : 𝕜 → E, (AnalyticAt 𝕜 g x) ∧ (g x ≠ 0) ∧ (f =ᶠ[𝓝 x] (· - x) ^ n • g )) := by
  rfl

theorem MeromorphicAt.meromorphicNFAt_iff {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) :
    MeromorphicNFAt f x ↔ (AnalyticAt 𝕜 f x) ∨ (hf.order < 0 ∧ f x = 0) := by
  constructor
  · intro h₁f
    rcases h₁f with h | h
    · simp [(analyticAt_congr h).2 analyticAt_const]
    · obtain ⟨n, g, h₁g, h₂g, h₃g⟩ := h
      have : hf.order = n := by
        rw [hf.order_eq_int_iff]
        use g, h₁g, h₂g
        exact eventually_nhdsWithin_of_eventually_nhds h₃g
      by_cases hn : 0 ≤ n
      · left
        rw [analyticAt_congr h₃g]
        apply (AnalyticAt.zpow_nonneg (by fun_prop) hn).smul h₁g
      · simp [this, WithTop.coe_lt_zero.2 (not_le.1 hn), h₃g.eq_of_nhds,
          zero_zpow n (ne_of_not_le hn).symm]
  · intro h₁f
    rcases h₁f with h | ⟨h₁, h₂⟩
    · by_cases h₂f : h.order = ⊤
      · rw [AnalyticAt.order_eq_top_iff] at h₂f
        tauto
      · right
        use h.order.toNat
        have : h.order ≠ ⊤ := h₂f
        rw [← ENat.coe_toNat_eq_self, eq_comm, AnalyticAt.order_eq_nat_iff] at this
        obtain ⟨g, h₁g, h₂g, h₃g⟩ := this
        use g, h₁g, h₂g
        simpa [ne_eq, not_false_eq_true, zpow_natCast, true_and]
    · right
      obtain ⟨g, h₁g, h₂g, h₃g⟩ := (hf.order_eq_int_iff (hf.order.untop' 0)).1
        (untop'_of_ne_top (LT.lt.ne_top h₁)).symm
      use (hf.order.untop' 0), g, h₁g, h₂g
      filter_upwards [eventually_nhdsWithin_iff.1 h₃g]
      intro z hz
      by_cases h₁z : z = x
      · simp [h₁z, h₂]
        apply (smul_eq_zero_of_left (zero_zpow (WithTop.untop' 0 hf.order) _) (g x)).symm
        by_contra hCon
        rw [WithTop.untop'_eq_self_iff, WithTop.coe_zero] at hCon
        rcases hCon with h | h
        <;> simp [h] at h₁
      · exact hz h₁z


theorem MeromorphicNFAt.meromorphicAt {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicNFAt f x) :
    MeromorphicAt f x := by
  rcases hf with h | h
  · exact (meromorphicAt_congr' h).2 analyticAt_const.meromorphicAt
  · obtain ⟨n, g, h₁g, _, h₃g⟩ := h
    rw [meromorphicAt_congr' h₃g]
    fun_prop

theorem meromorphicNFAt_congr {f g : 𝕜 → E} {x : 𝕜} (hfg : f =ᶠ[𝓝 x] g) :
    MeromorphicNFAt f x ↔ MeromorphicNFAt g x := by
  unfold MeromorphicNFAt
  constructor
  · intro h
    rcases h with h | h
    · left
      exact hfg.symm.trans h
    · obtain ⟨n, h, h₁h, h₂h, h₃h⟩ := h
      right
      use n, h, h₁h, h₂h, hfg.symm.trans h₃h
  · intro h
    rcases h with h | h
    · left
      exact hfg.trans h
    · obtain ⟨n, h, h₁h, h₂h, h₃h⟩ := h
      right
      use n, h, h₁h, h₂h, hfg.trans h₃h

theorem AnalyticAt.MeromorphicNFAt {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
  MeromorphicNFAt f x := by
  simp [hf.meromorphicAt.meromorphicNFAt_iff, hf]


/- Strongly MeromorphicAt of non-negative order is analytic -/
theorem MeromorphicNFAt.analyticAt {f : 𝕜 → E} {x : 𝕜} (h₁f : MeromorphicNFAt f x)
    (h₂f : 0 ≤ h₁f.meromorphicAt.order) :
    AnalyticAt 𝕜 f x := by
  have h₃f := h₁f.meromorphicAt
  rw [h₃f.meromorphicNFAt_iff] at h₁f
  rcases h₁f with h | h
  · exact h
  · have : h₃f.order < 0 := by tauto

    sorry


  let h₁f' := h₁f
  rcases h₁f' with h | h
  · rw [analyticAt_congr h]
    exact analyticAt_const
  · obtain ⟨n, g, h₁g, h₂g, h₃g⟩ := h
    rw [analyticAt_congr h₃g]
    have : h₁f.meromorphicAt.order = n := by
      rw [MeromorphicAt.order_eq_int_iff]
      use g, h₁g
      exact ⟨h₂g, Filter.EventuallyEq.filter_mono h₃g nhdsWithin_le_nhds⟩
    rw [this] at h₂f
    apply AnalyticAt.smul _ h₁g
    nth_rw 1 [← Int.toNat_of_nonneg (WithTop.coe_nonneg.mp h₂f)]
    exact AnalyticAt.zpow_nonneg (by fun_prop) (Int.ofNat_zero_le n.toNat)


lemma MeromorphicNFAt_of_mul_analytic'
  {f : 𝕜 → 𝕜}
  {g : 𝕜 → 𝕜}
  {z₀ : 𝕜}
  (h₁g : AnalyticAt 𝕜 g z₀)
  (h₂g : g z₀ ≠ 0) :
  MeromorphicNFAt f z₀ → MeromorphicNFAt (f • g) z₀ := by

  intro hf
  --unfold MeromorphicNFAt at hf
  rcases hf with h₁f|h₁f
  · left
    rw [Filter.EventuallyEq, eventually_nhds_iff] at h₁f
    obtain ⟨t, ht⟩ := h₁f
    rw [Filter.EventuallyEq, eventually_nhds_iff]
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
      · rw [Filter.EventuallyEq, eventually_nhds_iff] at h₃g_f
        obtain ⟨t, ht⟩ := h₃g_f
        rw [Filter.EventuallyEq, eventually_nhds_iff]
        use t
        constructor
        · intro y hy
          simp
          rw [ht.1]
          simp
          ring
          exact hy
        · exact ht.2





/- A function is strongly meromorphic at a point iff it is strongly meromorphic
   after multiplication with a non-vanishing analytic function
-/
theorem MeromorphicNFAt_of_mul_analytic
  {f g : ℂ → ℂ}
  {z₀ : ℂ}
  (h₁g : AnalyticAt ℂ g z₀)
  (h₂g : g z₀ ≠ 0) :
  MeromorphicNFAt f z₀ ↔ MeromorphicNFAt (f * g) z₀ := by
  constructor
  · apply MeromorphicNFAt_of_mul_analytic' h₁g h₂g
  · intro hprod
    have : f =ᶠ[𝓝 z₀] f * g * g⁻¹ := by
      filter_upwards [h₁g.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr h₂g)]
      intro y hy
      rw [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_singleton_iff] at hy
      simp [hy]
    rw [meromorphicNFAt_congr this]
    exact MeromorphicNFAt_of_mul_analytic' (h₁g.inv h₂g) (inv_ne_zero h₂g) (f := f * g) hprod

theorem MeromorphicNFAt.order_eq_zero_iff
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : MeromorphicNFAt f z₀) :
  hf.meromorphicAt.order = 0 ↔ f z₀ ≠ 0 := by
  constructor
  · intro h₁f
    let A := hf.analyticAt (le_of_eq (id (Eq.symm h₁f)))
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


theorem MeromorphicNFAt.localIdentity
  {f g : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : MeromorphicNFAt f z₀)
  (hg : MeromorphicNFAt g z₀) :
  f =ᶠ[𝓝[≠] z₀] g → f =ᶠ[𝓝 z₀] g := by

  intro h

  have t₀ : hf.meromorphicAt.order = hg.meromorphicAt.order := by
    exact hf.meromorphicAt.order_congr h

  by_cases cs : hf.meromorphicAt.order = 0
  · rw [cs] at t₀
    have h₁f := hf.analyticAt (le_of_eq (id (Eq.symm cs)))
    have h₁g := hg.analyticAt (le_of_eq t₀)
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
noncomputable def MeromorphicAt.makeMeromorphicNFAt
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
  ∀ z ≠ z₀, f z = hf.makeMeromorphicNFAt z := by
  intro z hz
  unfold MeromorphicAt.makeMeromorphicNFAt
  simp [hz]


lemma m₂
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : MeromorphicAt f z₀) :
  f =ᶠ[𝓝[≠] z₀] hf.makeMeromorphicNFAt := by
  apply eventually_nhdsWithin_of_forall
  exact fun x a => m₁ hf x a


theorem MeromorphicNFAt_of_makeStronglyMeromorphic
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : MeromorphicAt f z₀) :
  MeromorphicNFAt hf.makeMeromorphicNFAt z₀ := by

  by_cases h₂f : hf.order = ⊤
  · have : hf.makeMeromorphicNFAt =ᶠ[𝓝 z₀] 0 := by
      apply Mnhds
      · apply Filter.EventuallyEq.trans (Filter.EventuallyEq.symm (m₂ hf))
        exact (MeromorphicAt.order_eq_top_iff hf).1 h₂f
      · unfold MeromorphicAt.makeMeromorphicNFAt
        simp [h₂f]

    apply AnalyticAt.MeromorphicNFAt
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
        · unfold MeromorphicAt.makeMeromorphicNFAt
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


theorem MeromorphicNFAt.makeStronglyMeromorphic_id
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (hf : MeromorphicNFAt f z₀) :
  f = hf.meromorphicAt.makeMeromorphicNFAt := by

  funext z
  by_cases hz : z = z₀
  · rw [hz]
    unfold MeromorphicAt.makeMeromorphicNFAt
    simp
    have h₀f := hf
    rcases hf with h₁f | h₁f
    · simp [(h₀f.meromorphicAt.order_eq_top_iff).2 (h₁f.filter_mono nhdsWithin_le_nhds)]
      exact Filter.EventuallyEq.eq_of_nhds h₁f
    · obtain ⟨n, g, h₁g, h₂g, h₃g⟩ := h₁f
      rw [Filter.EventuallyEq.eq_of_nhds h₃g]
      have : h₀f.meromorphicAt.order = n := by
        rw [MeromorphicAt.order_eq_int_iff (MeromorphicNFAt.meromorphicAt h₀f) n]
        use g, h₁g, h₂g
        exact eventually_nhdsWithin_of_eventually_nhds h₃g
      by_cases h₃f : h₀f.meromorphicAt.order = 0
      · simp [h₃f]
        have hn : n = (0 : ℤ) := by
          rw [h₃f] at this
          exact WithTop.coe_eq_zero.mp (id (Eq.symm this))
        simp_rw [hn]
        simp
        let A := (h₀f.meromorphicAt.order_eq_int_iff 0).1 h₃f
        have : g =ᶠ[𝓝 z₀] (Classical.choose A) := by
          obtain ⟨h₀, h₁, h₂⟩ := Classical.choose_spec A
          apply h₁g.localIdentity h₀
          rw [hn] at h₃g
          simp at h₃g h₂
          exact (Filter.EventuallyEq.symm (h₃g.filter_mono nhdsWithin_le_nhds)).trans h₂
        exact Filter.EventuallyEq.eq_of_nhds this
      · simp [h₃f]
        left
        apply zero_zpow n
        by_contra hn
        rw [hn] at this
        tauto
  · exact m₁ (MeromorphicNFAt.meromorphicAt hf) z hz


theorem MeromorphicNFAt.eliminate
  {f : ℂ → ℂ}
  {z₀ : ℂ}
  (h₁f : MeromorphicNFAt f z₀)
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
  let g := h₁g₁.makeMeromorphicNFAt
  use g
  have h₁g : MeromorphicNFAt g z₀ := by
    exact MeromorphicNFAt_of_makeStronglyMeromorphic h₁g₁
  have h₂g : h₁g.meromorphicAt.order = 0 := by
    rw [← h₁g₁.order_congr (m₂ h₁g₁)]
    exact h₂g₁
  constructor
  · apply analyticAt
    · rw [h₂g]
    · exact h₁g
  · constructor
    · rwa [← h₁g.order_eq_zero_iff]
    · funext z
      by_cases hz : z = z₀
      · by_cases hOrd : h₁f.meromorphicAt.order.untop h₂f = 0
        · simp [hOrd]
          have : MeromorphicNFAt g₁ z₀ := by
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
