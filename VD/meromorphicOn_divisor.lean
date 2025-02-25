import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.DiscreteSubset
import VD.divisor
import VD.mathlibAddOn
import VD.meromorphicOn
import VD.stronglyMeromorphicOn

open scoped Interval Topology
open Real Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

theorem MeromorphicOn.codiscrete_setOf_order_eq_zero_or_top {f : 𝕜 → E} {U : Set 𝕜} (hf : MeromorphicOn f U) :
    {u : U | (hf u u.2).order = 0 ∨ (hf u u.2).order = ⊤} ∈ Filter.codiscrete U := by
  rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with A₂ | A₂
  · filter_upwards [eventually_eventually_nhdsWithin.2 A₂]
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Subtype.exists,
      exists_and_right, exists_eq_right, not_exists, not_or, not_and, not_forall, Decidable.not_not]
    intro a h₃a h₄a
    use h₄a
    by_cases h₅a : a = x
    · rw [← (hf x hx).order_eq_top_iff] at A₂
      simp_rw [h₅a]
      tauto
    · have : (hf a h₄a).order = ⊤ := by
        rw [(hf a h₄a).order_eq_top_iff]
        rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at h₃a ⊢
        obtain ⟨t, h₁t, h₂t, h₃t⟩ := h₃a
        use t \ {x}, fun y h₁y _ ↦ h₁t y h₁y.1 h₁y.2
        exact ⟨h₂t.sdiff isClosed_singleton, Set.mem_diff_of_mem h₃t h₅a⟩
      tauto
  · filter_upwards [(hf x hx).eventually_analyticAt, A₂]
    intro a h₁a h₂a
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Subtype.exists,
      exists_and_right, exists_eq_right, not_exists, not_or, not_and, not_forall, Decidable.not_not]
    intro h₃a
    use h₃a
    rw [h₁a.meromorphicAt_order, h₁a.order_eq_zero_iff.2 h₂a]
    tauto

noncomputable def MeromorphicOn.divisor
  {f : 𝕜 → E}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  Divisor U where

  toFun := by
    intro z
    if hz : z ∈ U then
      exact ((hf z hz).order.untopD 0 : ℤ)
    else
      exact 0

  supportWithinDomain := by
    intro z hz
    simp at hz
    by_contra h₂z
    simp [h₂z] at hz

  supportDiscreteWithinDomain := by
    have A₁ := hf.eventually_codiscreteWithin_analyticAt
    let U' := { x ∈ U | AnalyticAt 𝕜 f x}
    have A₂ : U' ⊆ U := fun x hx ↦ hx.1
    have A₃ : AnalyticOnNhd 𝕜 f U' := fun x hx ↦ hx.2
    rw [Filter.EventuallyEq, Filter.Eventually]
    rw [mem_codiscreteWithin]
    intro z hz
    rw [Filter.disjoint_principal_right]
    simp
    have A := (hf z hz).eventually_analyticAt
    rcases MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero (hf z hz) with h | h
    · have C := hf.isClopen_setOf_order_eq_top
      have D := (hf z hz).order_eq_top_iff.2 h
      rw [← eventually_eventually_nhdsWithin] at h
      have h' : ∀ᶠ (y : 𝕜) in 𝓝[≠] z, ∀ᶠ (x : 𝕜) in 𝓝 y, f x = 0:= by
        simp_rw [eventually_nhdsWithin_iff] at h
        simp_rw [eventually_nhdsWithin_iff]
        filter_upwards [h]
        intro a h₁a h₂a
        have h₃a : ∀ᶠ (y : 𝕜) in 𝓝 a, y ≠ z := by
          exact ContinuousAt.eventually_ne (fun ⦃U⦄ a ↦ a) h₂a
        filter_upwards [h₁a h₂a, h₃a]
        intro b h₁b h₂b
        tauto
      filter_upwards [h, h', A]
      intro a h₁a h₂a h₃a
      simp
      intro h₄a h₅a
      rw [MeromorphicAt.order_eq_top_iff]
      exact eventually_nhdsWithin_of_eventually_nhds h₂a
    · filter_upwards [h, A]
      intro a h₁a h₂a
      simp
      intro h₃a
      let D := h₂a.order_eq_zero_iff.2 h₁a
      have : (hf a h₃a).order = 0 := by
        rw [AnalyticAt.meromorphicAt_order h₂a, D]
        simp
      tauto

theorem MeromorphicOn.divisor_def₁
  {f : 𝕜 → E}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (hz : z ∈ U) :
  hf.divisor z = ((hf z hz).order.untopD 0 : ℤ) := by
  unfold MeromorphicOn.divisor
  simp [hz]


theorem MeromorphicOn.divisor_def₂
  {f : 𝕜 → E}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (hz : z ∈ U)
  (h₂f : (hf z hz).order ≠ ⊤) :
  hf.divisor z = (hf z hz).order.untop h₂f := by
  unfold MeromorphicOn.divisor
  simp [hz]
  rw [WithTop.untopD_eq_iff]
  left
  exact Eq.symm (WithTop.coe_untop (hf z hz).order h₂f)


theorem MeromorphicOn.divisor_mul₀  [CompleteSpace 𝕜]
  {f₁ f₂ : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z : 𝕜}
  (hz : z ∈ U)
  (h₁f₁ : MeromorphicOn f₁ U)
  (h₂f₁ : (h₁f₁ z hz).order ≠ ⊤)
  (h₁f₂ : MeromorphicOn f₂ U)
  (h₂f₂ : (h₁f₂ z hz).order ≠ ⊤) :
  (h₁f₁.mul h₁f₂).divisor.toFun z = h₁f₁.divisor.toFun z + h₁f₂.divisor.toFun z := by
  by_cases h₁z : z ∈ U
  · rw [MeromorphicOn.divisor_def₂ h₁f₁ hz h₂f₁]
    rw [MeromorphicOn.divisor_def₂ h₁f₂ hz h₂f₂]
    have B : ((h₁f₁.mul h₁f₂) z hz).order ≠ ⊤ := by
      rw [MeromorphicAt.order_mul (h₁f₁ z hz) (h₁f₂ z hz)]
      simp; tauto
    rw [MeromorphicOn.divisor_def₂ (h₁f₁.mul h₁f₂) hz B]
    simp_rw [MeromorphicAt.order_mul (h₁f₁ z hz) (h₁f₂ z hz)]
    rw [untop_add]
  · unfold MeromorphicOn.divisor
    simp [h₁z]


theorem MeromorphicOn.divisor_mul [CompleteSpace 𝕜]
  {f₁ f₂ : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁f₁ : MeromorphicOn f₁ U)
  (h₂f₁ : ∀ z, (hz : z ∈ U) → (h₁f₁ z hz).order ≠ ⊤)
  (h₁f₂ : MeromorphicOn f₂ U)
  (h₂f₂ : ∀ z, (hz : z ∈ U) → (h₁f₂ z hz).order ≠ ⊤) :
  (h₁f₁.mul h₁f₂).divisor.toFun = h₁f₁.divisor.toFun + h₁f₂.divisor.toFun := by
  funext z
  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_mul₀ hz h₁f₁ (h₂f₁ z hz) h₁f₂ (h₂f₂ z hz)]
    simp
  · simp
    rw [Function.nmem_support.mp (fun a => hz (h₁f₁.divisor.supportWithinDomain a))]
    rw [Function.nmem_support.mp (fun a => hz (h₁f₂.divisor.supportWithinDomain a))]
    rw [Function.nmem_support.mp (fun a => hz ((h₁f₁.mul h₁f₂).divisor.supportWithinDomain a))]
    simp


theorem MeromorphicOn.divisor_inv [CompleteSpace 𝕜]
  {f: 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁f : MeromorphicOn f U) :
  h₁f.inv.divisor.toFun = -h₁f.divisor.toFun := by
  funext z

  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_def₁]
    simp
    rw [MeromorphicOn.divisor_def₁]
    rw [MeromorphicAt.order_inv]
    simp
    by_cases h₂f : (h₁f z hz).order = ⊤
    · simp [h₂f]
    · let A := untop'_of_ne_top (d := 0) h₂f
      rw [← A]
      exact rfl
    repeat exact hz
  · unfold MeromorphicOn.divisor
    simp [hz]


theorem MeromorphicOn.divisor_add_const₁  [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (a : 𝕜) :
  0 ≤ hf.divisor z → 0 ≤ (hf.add (MeromorphicOn.const a)).divisor z := by
  intro h

  unfold MeromorphicOn.divisor

  -- Trivial case: z ∉ U
  by_cases hz : z ∉ U
  · simp [hz]

  -- Non-trivial case: z ∈ U
  simp at hz; simp [hz]

  by_cases h₁f : (hf z hz).order = ⊤
  · have : f + (fun z ↦ a) =ᶠ[𝓝[≠] z] (fun z ↦ a) := by
      rw [MeromorphicAt.order_eq_top_iff] at h₁f
      rw [eventually_nhdsWithin_iff] at h₁f
      rw [eventually_nhds_iff] at h₁f
      obtain ⟨t, ht⟩ := h₁f
      rw [eventuallyEq_nhdsWithin_iff]
      rw [eventually_nhds_iff]
      use t
      simp [ht]
      tauto
    rw [((hf z hz).add (MeromorphicAt.const a z)).order_congr this]

    by_cases ha: (MeromorphicAt.const a z).order = ⊤
    · simp [ha]
    · rw [WithTop.le_untopD_iff]
      apply AnalyticAt.meromorphicAt_order_nonneg
      exact analyticAt_const
      tauto

  · rw [WithTop.le_untopD_iff]
    let A := (hf z hz).order_add (MeromorphicAt.const a z)
    have : 0 ≤ min (hf z hz).order (MeromorphicAt.const a z).order := by
      apply le_min
      --
      unfold MeromorphicOn.divisor at h
      simp [hz] at h
      let V := untop'_of_ne_top (d := 0) h₁f
      rw [← V]
      simp [h]
      --
      apply AnalyticAt.meromorphicAt_order_nonneg
      exact analyticAt_const
    exact le_trans this A
    tauto


theorem MeromorphicOn.divisor_add_const₂ [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (a : 𝕜) :
  hf.divisor z < 0 → (hf.add (MeromorphicOn.const a)).divisor z < 0 := by
  intro h

  by_cases hz : z ∉ U
  · have : hf.divisor z = 0 := by
      unfold MeromorphicOn.divisor
      simp [hz]
    rw [this] at h
    tauto

  simp at hz
  unfold MeromorphicOn.divisor
  simp [hz]
  unfold MeromorphicOn.divisor at h
  simp [hz] at h

  have : (hf z hz).order = (((hf.add (MeromorphicOn.const a))) z hz).order := by
    have t₀ : (hf z hz).order < (0 : ℤ) := by
        by_contra hCon
        simp only [not_lt] at hCon
        rw [←WithTop.le_untopD_iff (b := 0)] at hCon
        exact Lean.Omega.Int.le_lt_asymm hCon h
        tauto
    rw [← MeromorphicAt.order_add_of_ne_orders (hf z hz) (MeromorphicAt.const a z)]
    simp

    by_cases ha: (MeromorphicAt.const a z).order = ⊤
    · simp [ha]
    · calc (hf z hz).order
      _ ≤ 0 := t₀.le
      _ ≤ (MeromorphicAt.const a z).order := by
        apply AnalyticAt.meromorphicAt_order_nonneg
        exact analyticAt_const

    apply ne_of_lt
    calc (hf z hz).order
      _ < 0 := by exact t₀
      _ ≤ (MeromorphicAt.const a z).order := by
        apply AnalyticAt.meromorphicAt_order_nonneg
        exact analyticAt_const
  rwa [this] at h


theorem MeromorphicOn.divisor_add_const₃ [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  {z : 𝕜}
  (hf : MeromorphicOn f U)
  (a : 𝕜) :
  hf.divisor z < 0 → (hf.add (MeromorphicOn.const a)).divisor z = hf.divisor z := by
  intro h

  by_cases hz : z ∉ U
  · have : hf.divisor z = 0 := by
      unfold MeromorphicOn.divisor
      simp [hz]
    rw [this] at h
    tauto

  simp at hz
  unfold MeromorphicOn.divisor
  simp [hz]
  unfold MeromorphicOn.divisor at h
  simp [hz] at h

  have : (hf z hz).order = (((hf.add (MeromorphicOn.const a))) z hz).order := by
    have t₀ : (hf z hz).order < (0 : ℤ) := by
        by_contra hCon
        simp only [not_lt] at hCon
        rw [←WithTop.le_untopD_iff (b := 0)] at hCon
        exact Lean.Omega.Int.le_lt_asymm hCon h
        tauto
    rw [← MeromorphicAt.order_add_of_ne_orders (hf z hz) (MeromorphicAt.const a z)]
    simp

    by_cases ha: (MeromorphicAt.const a z).order = ⊤
    · simp [ha]
    · calc (hf z hz).order
      _ ≤ 0 := t₀.le
      _ ≤ (MeromorphicAt.const a z).order := by
        apply AnalyticAt.meromorphicAt_order_nonneg
        exact analyticAt_const

    apply ne_of_lt
    calc (hf z hz).order
      _ < 0 := by exact t₀
      _ ≤ (MeromorphicAt.const a z).order := by
        apply AnalyticAt.meromorphicAt_order_nonneg
        exact analyticAt_const
  rw [this]


theorem MeromorphicOn.divisor_of_makeStronglyMeromorphicOn [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (hf : MeromorphicOn f U) :
  hf.divisor = (stronglyMeromorphicOn_of_makeStronglyMeromorphicOn hf).meromorphicOn.divisor := by
  unfold MeromorphicOn.divisor
  simp
  funext z
  by_cases hz : z ∈ U
  · simp [hz]
    congr 1
    apply MeromorphicAt.order_congr
    exact EventuallyEq.symm (makeStronglyMeromorphicOn_changeDiscrete hf hz)
  · simp [hz]



-- STRONGLY MEROMORPHIC THINGS

/- Strongly MeromorphicOn of non-negative order is analytic -/
theorem StronglyMeromorphicOn.analyticOnNhd [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁f : StronglyMeromorphicOn f U)
  (h₂f : ∀ x, (hx : x ∈ U) → 0 ≤ h₁f.meromorphicOn.divisor x) :
  AnalyticOnNhd 𝕜 f U := by

  apply StronglyMeromorphicOn.analytic
  intro z hz
  let A := h₂f z hz
  unfold MeromorphicOn.divisor at A
  simp [hz] at A
  by_cases h : (h₁f z hz).meromorphicAt.order = ⊤
  · rw [h]
    simp
  · rw [WithTop.le_untopD_iff] at A
    tauto
    tauto
  assumption


theorem StronglyMeromorphicOn.support_divisor [CompleteSpace 𝕜]
  {f : 𝕜 → 𝕜}
  {U : Set 𝕜}
  (h₁f : StronglyMeromorphicOn f U)
  (h₂f : ∃ u : U, f u ≠ 0)
  (hU : IsConnected U) :
  U ∩ f⁻¹' {0} = (Function.support h₁f.meromorphicOn.divisor) := by

  ext u
  constructor
  · intro hu
    unfold MeromorphicOn.divisor
    simp [h₁f.order_ne_top hU h₂f ⟨u, hu.1⟩]
    use hu.1
    rw [(h₁f u hu.1).order_eq_zero_iff]
    simp
    exact hu.2
  · intro hu
    simp at hu
    let A := h₁f.meromorphicOn.divisor.supportWithinDomain hu
    constructor
    · exact h₁f.meromorphicOn.divisor.supportWithinDomain hu
    · simp
      let B := (h₁f u A).order_eq_zero_iff.not
      simp at B
      rw [← B]
      unfold MeromorphicOn.divisor at hu
      simp [A] at hu
      exact hu.1
