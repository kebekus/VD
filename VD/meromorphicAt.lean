import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import VD.ToMathlib.analyticAt
import VD.divisor
import VD.mathlibAddOn

open scoped Interval Topology
open Real Filter MeasureTheory intervalIntegral

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → 𝕜} {z₀ : 𝕜}

-- TODO: AnalyticAt is a codiscrete property within MeromorphicAt
-- TODO: Preimages of discrete and countable sets

/-- The order multiplies by `n` when taking an analytic function to its `n`th power -/

theorem MeromorphicAt.order_pow (hf : MeromorphicAt f z₀) {n : ℕ} :
    (hf.pow n).order = n * hf.order := by
  induction' n with n hn
  · simp
    rw [← WithTop.coe_zero, MeromorphicAt.order_eq_int_iff]
    use 1, analyticAt_const
    simp
  · simp [add_mul, pow_add, (hf.pow n).order_mul hf, hn]
    -- Really want rdistrib here
    cases hf.order
    · simp
      rfl
    · norm_cast
      simp
      ring

-- TODO: `order_zpow`

-- TODO: `order_inv`


theorem MeromorphicAt.order_ne_top_iff {f : 𝕜 → E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    hf.order ≠ ⊤ ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ (hf.order.untopD 0) • g z :=
  ⟨fun h ↦ (hf.order_eq_int_iff (hf.order.untopD 0)).1 (untop'_of_ne_top h).symm,
    fun h ↦ Option.ne_none_iff_exists'.2 ⟨hf.order.untopD 0, (hf.order_eq_int_iff (hf.order.untopD 0)).2 h⟩⟩

/-
theorem MeromorphicAt.order_ne_top_iff' {f : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f z₀) :
    hf.order ≠ ⊤ ↔ f * f⁻¹ =ᶠ[𝓝[≠] z₀] 1 := by

  sorry
-/

theorem meromorphicAt_congr
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → E} {x : 𝕜}
  (h : f =ᶠ[𝓝[≠] x] g) : MeromorphicAt f x ↔ MeromorphicAt g x :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩


theorem meromorphicAt_congr'
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → E} {x : 𝕜}
  (h : f =ᶠ[nhds x] g) : MeromorphicAt f x ↔ MeromorphicAt g x :=
  meromorphicAt_congr (Filter.EventuallyEq.filter_mono h nhdsWithin_le_nhds)


theorem MeromorphicAt.order_congr
  {f₁ f₂ : 𝕜 → E}
  {z₀ : 𝕜}
  (hf₁ : MeromorphicAt f₁ z₀)
  (h : f₁ =ᶠ[𝓝[≠] z₀] f₂):
  hf₁.order = (hf₁.congr h).order := by
  by_cases hord : hf₁.order = ⊤
  · rw [hord, eq_comm]
    rw [hf₁.order_eq_top_iff] at hord
    rw [(hf₁.congr h).order_eq_top_iff]
    exact EventuallyEq.rw hord (fun x => Eq (f₂ x)) (_root_.id (EventuallyEq.symm h))
  · obtain ⟨n, hn : hf₁.order = n⟩ := Option.ne_none_iff_exists'.mp hord
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (hf₁.order_eq_int_iff n).1 hn
    rw [hn, eq_comm, (hf₁.congr h).order_eq_int_iff]
    use g, h₁g, h₂g
    exact EventuallyEq.rw h₃g (fun x => Eq (f₂ x)) (_root_.id (EventuallyEq.symm h))

theorem MeromorphicAt.order_inv
  {f : 𝕜 → 𝕜}
  {z₀ : 𝕜}
  (hf : MeromorphicAt f z₀) :
  hf.order = -hf.inv.order := by

  by_cases h₂f : hf.order = ⊤
  · rw [h₂f, ← LinearOrderedAddCommGroupWithTop.neg_top, neg_eq_iff_eq_neg, neg_neg, eq_comm]
    rw [MeromorphicAt.order_eq_top_iff] at *
    filter_upwards [h₂f]
    simp

  · have : hf.order = hf.order.untopD 0 := by
      simp [h₂f, untop'_of_ne_top]
    rw [this]
    rw [eq_comm]
    rw [neg_eq_iff_eq_neg]
    apply (hf.inv.order_eq_int_iff (-hf.order.untopD 0)).2
    rw [hf.order_eq_int_iff] at this
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := this
    use g⁻¹, h₁g.inv h₂g
    constructor
    · simp [h₂g]
    · rw [eventually_nhdsWithin_iff]
      rw [eventually_nhds_iff]
      rw [eventually_nhdsWithin_iff] at h₃g
      rw [eventually_nhds_iff] at h₃g
      obtain ⟨t, h₁t, h₂t, h₃t⟩ := h₃g
      use t
      constructor
      · intro y h₁y h₂y
        simp
        let A := h₁t y h₁y h₂y
        rw [A]
        simp
        rw [mul_comm]
      · exact ⟨h₂t, h₃t⟩


theorem AnalyticAt.meromorphicAt_order_nonneg
  {f : 𝕜 → E}
  {z₀ : 𝕜}
  (hf : AnalyticAt 𝕜 f z₀) :
  0 ≤ hf.meromorphicAt.order := by
  rw [hf.meromorphicAt_order]
  rw [(by rfl : (0 : WithTop ℤ) = WithTop.map Nat.cast (0 : ℕ∞))]
  erw [WithTop.map_le_iff]
  simp; simp


theorem MeromorphicAt.order_add
  {f₁ f₂ : 𝕜 → 𝕜}
  {z₀ : 𝕜}
  (hf₁ : MeromorphicAt f₁ z₀)
  (hf₂ : MeromorphicAt f₂ z₀) :
  min hf₁.order hf₂.order ≤ (hf₁.add hf₂).order := by

  -- Handle the trivial cases where one of the orders equals ⊤
  by_cases h₂f₁: hf₁.order = ⊤
  · rw [h₂f₁]; simp
    rw [hf₁.order_eq_top_iff] at h₂f₁
    have h : f₁ + f₂ =ᶠ[𝓝[≠] z₀] f₂ := by
      -- Optimize this, here an elsewhere
      rw [eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
      rw [eventually_nhdsWithin_iff, eventually_iff_exists_mem] at h₂f₁
      obtain ⟨v, hv⟩ := h₂f₁
      use v; simp; trivial
    rw [(hf₁.add hf₂).order_congr h]
  by_cases h₂f₂: hf₂.order = ⊤
  · rw [h₂f₂]; simp
    rw [hf₂.order_eq_top_iff] at h₂f₂
    have h : f₁ + f₂ =ᶠ[𝓝[≠] z₀] f₁ := by
      rw [eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
      rw [eventually_nhdsWithin_iff, eventually_iff_exists_mem] at h₂f₂
      obtain ⟨v, hv⟩ := h₂f₂
      use v; simp; trivial
    rw [(hf₁.add hf₂).order_congr h]

  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := hf₁.order_ne_top_iff.1 h₂f₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := hf₂.order_ne_top_iff.1 h₂f₂

  let n₁ := WithTop.untopD 0 hf₁.order
  let n₂ := WithTop.untopD 0 hf₂.order
  let n := min n₁ n₂
  have h₁n₁ : 0 ≤ n₁ - n := by
    rw [sub_nonneg]
    exact Int.min_le_left n₁ n₂
  have h₁n₂ : 0 ≤ n₂ - n := by
    rw [sub_nonneg]
    exact Int.min_le_right n₁ n₂

  let g := (fun z ↦ (z - z₀) ^ (n₁ - n)) * g₁ +  (fun z ↦ (z - z₀) ^ (n₂ - n)) * g₂
  have h₁g : AnalyticAt 𝕜 g z₀ := by
    apply AnalyticAt.add
    apply AnalyticAt.mul (AnalyticAt.zpow_nonneg (by fun_prop) h₁n₁) h₁g₁
    apply AnalyticAt.mul (AnalyticAt.zpow_nonneg (by fun_prop) h₁n₂) h₁g₂
  have h₂g : 0 ≤ h₁g.meromorphicAt.order := h₁g.meromorphicAt_order_nonneg

  have : f₁ + f₂ =ᶠ[𝓝[≠] z₀] (fun z ↦ (z - z₀) ^ n) * g := by
    rw [eventuallyEq_nhdsWithin_iff, eventually_nhds_iff]
    obtain ⟨t, ht⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 (h₃g₁.and h₃g₂))
    use t
    simp [ht]
    intro y h₁y h₂y
    rw [(ht.1 y h₁y h₂y).1, (ht.1 y h₁y h₂y).2]
    unfold g; simp; rw [mul_add]
    repeat rw [←mul_assoc, ← zpow_add' (by left; exact (sub_ne_zero_of_ne h₂y))]
    simp [n₁, n₂]

  rw [(hf₁.add hf₂).order_congr this]

  have t₀ : MeromorphicAt (fun z ↦ (z - z₀) ^ n) z₀ := by fun_prop
  rw [t₀.order_mul h₁g.meromorphicAt]
  have t₁ : t₀.order = n := by
    rw [t₀.order_eq_int_iff]
    use 1
    constructor
    · apply analyticAt_const
    · simp
  rw [t₁]
  unfold n n₁ n₂
  have : hf₁.order ⊓ hf₂.order = (WithTop.untopD 0 hf₁.order ⊓ WithTop.untopD 0 hf₂.order) := by
    rw [←untop'_of_ne_top (d := 0) h₂f₁, ←untop'_of_ne_top (d := 0) h₂f₂]
    simp
  rw [this]
  exact le_add_of_nonneg_right h₂g


theorem MeromorphicAt.order_add_of_ne_orders
  {f₁ f₂ : 𝕜 → 𝕜}
  {z₀ : 𝕜}
  (hf₁ : MeromorphicAt f₁ z₀)
  (hf₂ : MeromorphicAt f₂ z₀)
  (hf₁₂ : hf₁.order ≠ hf₂.order) :
  min hf₁.order hf₂.order = (hf₁.add hf₂).order := by

  -- Handle the trivial cases where one of the orders equals ⊤
  by_cases h₂f₁: hf₁.order = ⊤
  · rw [h₂f₁]; simp
    rw [hf₁.order_eq_top_iff] at h₂f₁
    have h : f₁ + f₂ =ᶠ[𝓝[≠] z₀] f₂ := by
      -- Optimize this, here and elsewhere
      rw [eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
      rw [eventually_nhdsWithin_iff, eventually_iff_exists_mem] at h₂f₁
      obtain ⟨v, hv⟩ := h₂f₁
      use v
      simpa
    rw [(hf₁.add hf₂).order_congr h]
  by_cases h₂f₂: hf₂.order = ⊤
  · rw [h₂f₂]; simp
    rw [hf₂.order_eq_top_iff] at h₂f₂
    have h : f₁ + f₂ =ᶠ[𝓝[≠] z₀] f₁ := by
      rw [eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
      rw [eventually_nhdsWithin_iff, eventually_iff_exists_mem] at h₂f₂
      obtain ⟨v, hv⟩ := h₂f₂
      use v; simp; trivial
    rw [(hf₁.add hf₂).order_congr h]

  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := hf₁.order_ne_top_iff.1 h₂f₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := hf₂.order_ne_top_iff.1 h₂f₂

  let n₁ := WithTop.untopD 0 hf₁.order
  let n₂ := WithTop.untopD 0 hf₂.order
  have hn₁₂ : n₁ ≠ n₂ := by
    unfold n₁ n₂
    simp [WithTop.untopD_eq_untopD_iff]
    tauto

  let n := min n₁ n₂
  have h₁n₁ : 0 ≤ n₁ - n := by
    rw [sub_nonneg]
    exact Int.min_le_left n₁ n₂
  have h₁n₂ : 0 ≤ n₂ - n := by
    rw [sub_nonneg]
    exact Int.min_le_right n₁ n₂

  let g := (fun z ↦ (z - z₀) ^ (n₁ - n)) * g₁ +  (fun z ↦ (z - z₀) ^ (n₂ - n)) * g₂
  have h₁g : AnalyticAt 𝕜 g z₀ := by
    apply AnalyticAt.add
    apply (AnalyticAt.zpow_nonneg (by fun_prop) h₁n₁).mul h₁g₁
    apply (AnalyticAt.zpow_nonneg (by fun_prop) h₁n₂).mul h₁g₂
  have h₂g : 0 ≤ h₁g.meromorphicAt.order := h₁g.meromorphicAt_order_nonneg
  have h₂'g : g z₀ ≠ 0 := by
    unfold g
    simp
    have : n = n₁ ∨ n = n₂ := by
      unfold n
      simp
      by_cases h : n₁ ≤ n₂
      · left; assumption
      · right
        simp at h
        exact h.le
    rcases this with h|h
    · rw [h]
      have : n₂ - n₁ ≠ 0 := by
        rw [sub_ne_zero, ne_comm]
        apply hn₁₂
      have : (0 : 𝕜) ^ (n₂ - n₁) = 0 := by
        rwa [zpow_eq_zero_iff]
      simp [this]
      exact h₂g₁
    · rw [h]
      have : n₁ - n₂ ≠ 0 := by
        rw [sub_ne_zero]
        apply hn₁₂
      have : (0 : 𝕜) ^ (n₁ - n₂) = 0 := by
        rwa [zpow_eq_zero_iff]
      simp [this]
      exact h₂g₂
  have h₃g : h₁g.meromorphicAt.order = 0 := by
    let A := h₁g.meromorphicAt_order
    let B := h₁g.order_eq_zero_iff.2 h₂'g
    rw [B] at A
    simpa

  have : f₁ + f₂ =ᶠ[𝓝[≠] z₀] (fun z ↦ (z - z₀) ^ n) * g := by
    rw [eventuallyEq_nhdsWithin_iff, eventually_nhds_iff]
    obtain ⟨t, ht⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 (h₃g₁.and h₃g₂))
    use t
    simp [ht]
    intro y h₁y h₂y
    rw [(ht.1 y h₁y h₂y).1, (ht.1 y h₁y h₂y).2]
    unfold g; simp; rw [mul_add]
    repeat rw [←mul_assoc, ← zpow_add' (by left; exact (sub_ne_zero_of_ne h₂y))]
    simp [n₁, n₂]

  rw [(hf₁.add hf₂).order_congr this]

  have t₀ : MeromorphicAt (fun z ↦ (z - z₀) ^ n) z₀ := by fun_prop
  rw [t₀.order_mul h₁g.meromorphicAt]
  have t₁ : t₀.order = n := by
    rw [t₀.order_eq_int_iff]
    use 1, analyticAt_const
    simp
  rw [t₁]
  unfold n n₁ n₂
  have : hf₁.order ⊓ hf₂.order = (WithTop.untopD 0 hf₁.order ⊓ WithTop.untopD 0 hf₂.order) := by
    rw [← untop'_of_ne_top (d := 0) h₂f₁, ← untop'_of_ne_top (d := 0) h₂f₂]
    simp
  rw [this, h₃g]
  simp

-- Might want to think about adding an analytic function instead of a constant
theorem MeromorphicAt.order_add_const
  --have {z : ℂ} : 0 < (hf z trivial).order → (hf z trivial).order = ((hf.add (MeromorphicOn.const a)) z trivial).order:= by
  {f : ℂ → ℂ}
  {z a : ℂ}
  (hf : MeromorphicAt f z) :
  hf.order < 0 → hf.order = (hf.add (MeromorphicAt.const a z)).order := by
  intro h

  by_cases ha: a = 0
  · -- might want theorem MeromorphicAt.order_const
    have : (MeromorphicAt.const a z).order = ⊤ := by
      rw [MeromorphicAt.order_eq_top_iff]
      rw [ha]
      simp
    rw [← hf.order_add_of_ne_orders (MeromorphicAt.const a z)]
    rw [this]
    simp
    rw [this]
    exact h.ne_top
  · have : (MeromorphicAt.const a z).order = (0 : ℤ) := by
      rw [MeromorphicAt.order_eq_int_iff]
      use fun _ ↦ a
      exact ⟨analyticAt_const, by simpa⟩
    rw [← hf.order_add_of_ne_orders (MeromorphicAt.const a z)]
    rw [this]
    simp [h.le]
    rw [this]
    exact h.ne


-- might want theorem MeromorphicAt.order_zpow
