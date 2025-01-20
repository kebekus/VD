import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import VD.analyticAt
import VD.ToMathlib.analyticAt


noncomputable def AnalyticOnNhd.order
  {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) : U → ℕ∞ := fun u ↦ (hf u u.2).order


theorem AnalyticOnNhd.order_eq_nat_iff
  {f : ℂ → ℂ}
  {U : Set ℂ}
  {z₀ : U}
  (hf : AnalyticOnNhd ℂ f U)
  (n : ℕ) :
  hf.order z₀ = ↑n ↔ ∃ (g : ℂ → ℂ), AnalyticOnNhd ℂ g U ∧ g z₀ ≠ 0 ∧ ∀ z, f z = (z - z₀) ^ n • g z := by

  constructor
  -- Direction →
  intro hn
  obtain ⟨gloc, h₁gloc, h₂gloc, h₃gloc⟩ := (AnalyticAt.order_eq_nat_iff (hf z₀ z₀.2) n).1 hn

  -- Define a candidate function; this is (f z) / (z - z₀) ^ n with the
  -- removable singularity removed
  let g : ℂ → ℂ := fun z ↦ if z = z₀ then gloc z₀ else (f z) / (z - z₀) ^ n

  -- Describe g near z₀
  have g_near_z₀ : ∀ᶠ (z : ℂ) in nhds z₀, g z = gloc z := by
    rw [eventually_nhds_iff]
    obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 h₃gloc
    use t
    constructor
    · intro y h₁y
      by_cases h₂y : y = z₀
      · dsimp [g]; simp [h₂y]
      · dsimp [g]; simp [h₂y]
        rw [div_eq_iff_mul_eq, eq_comm, mul_comm]
        exact h₁t y h₁y
        norm_num
        rw [sub_eq_zero]
        tauto
    · constructor
      · assumption
      · assumption

  -- Describe g near points z₁ that are different from z₀
  have g_near_z₁ {z₁ : ℂ} : z₁ ≠ z₀ → ∀ᶠ (z : ℂ) in nhds z₁, g z = f z / (z - z₀) ^ n := by
    intro hz₁
    rw [eventually_nhds_iff]
    use {z₀.1}ᶜ
    constructor
    · intro y hy
      simp at hy
      simp [g, hy]
    · exact ⟨isOpen_compl_singleton, hz₁⟩

  -- Use g and show that it has all required properties
  use g
  constructor
  · -- AnalyticOn ℂ g U
    intro z h₁z
    by_cases h₂z : z = z₀
    · rw [h₂z]
      apply AnalyticAt.congr h₁gloc
      exact Filter.EventuallyEq.symm g_near_z₀
    · simp_rw [eq_comm] at g_near_z₁
      apply AnalyticAt.congr _ (g_near_z₁ h₂z)
      apply AnalyticAt.div
      exact hf z h₁z
      apply AnalyticAt.pow
      apply AnalyticAt.sub
      apply analyticAt_id
      apply analyticAt_const
      simp
      rw [sub_eq_zero]
      tauto
  · constructor
    · simp [g]; tauto
    · intro z
      by_cases h₂z : z = z₀
      · rw [h₂z, g_near_z₀.self_of_nhds]
        exact h₃gloc.self_of_nhds
      · rw [(g_near_z₁ h₂z).self_of_nhds]
        simp [h₂z]
        rw [div_eq_mul_inv, mul_comm, mul_assoc, inv_mul_cancel₀]
        simp; norm_num
        rw [sub_eq_zero]
        tauto

  -- direction ←
  intro h
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h
  dsimp [AnalyticOnNhd.order]
  rw [AnalyticAt.order_eq_nat_iff]
  use g
  exact ⟨h₁g z₀ z₀.2, ⟨h₂g, Filter.Eventually.of_forall h₃g⟩⟩


theorem AnalyticOnNhd.support_of_order₁
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (hf : AnalyticOnNhd ℂ f U) :
  Function.support hf.order = U.restrict f⁻¹' {0} := by
  ext u
  simp [AnalyticOnNhd.order]
  rw [not_iff_comm, (hf u u.2).order_eq_zero_iff]


theorem AnalyticOnNhd.eliminateZeros
  {f : ℂ → ℂ}
  {U : Set ℂ}
  {A : Finset U}
  (hf : AnalyticOnNhd ℂ f U)
  (n : U → ℕ) :
  (∀ a ∈ A, hf.order a = n a) → ∃ (g : ℂ → ℂ), AnalyticOnNhd ℂ g U ∧ (∀ a ∈ A, g a ≠ 0) ∧ ∀ z, f z = (∏ a ∈ A, (z - a) ^ (n a)) • g z := by

  apply Finset.induction (α := U) (p := fun A ↦ (∀ a ∈ A, (hf a.1 a.2).order = n a) → ∃ (g : ℂ → ℂ), AnalyticOnNhd ℂ g U ∧ (∀ a ∈ A, g a ≠ 0) ∧ ∀ z, f z = (∏ a ∈ A, (z - a) ^ (n a)) • g z)

  -- case empty
  simp
  use f
  simp
  exact hf

  -- case insert
  intro b₀ B hb iHyp
  intro hBinsert
  obtain ⟨g₀, h₁g₀, h₂g₀, h₃g₀⟩ := iHyp (fun a ha ↦ hBinsert a (Finset.mem_insert_of_mem ha))

  have : (h₁g₀ b₀ b₀.2).order = n b₀ := by

    rw [← hBinsert b₀ (Finset.mem_insert_self b₀ B)]

    let φ := fun z ↦ (∏ a ∈ B, (z - a.1) ^ n a)

    have : f = fun z ↦ φ z * g₀ z := by
      funext z
      rw [h₃g₀ z]
      rfl
    simp_rw [this]

    have h₁φ : AnalyticAt ℂ φ b₀ := by
      dsimp [φ]
      apply Finset.analyticAt_prod
      intro b _
      apply AnalyticAt.pow
      apply AnalyticAt.sub
      apply analyticAt_id
      exact analyticAt_const

    have h₂φ : h₁φ.order = (0 : ℕ) := by
      rw [AnalyticAt.order_eq_nat_iff h₁φ 0]
      use φ
      constructor
      · assumption
      · constructor
        · dsimp [φ]
          push_neg
          rw [Finset.prod_ne_zero_iff]
          intro a ha
          simp
          have : ¬ (b₀.1 - a.1 = 0) := by
            by_contra C
            rw [sub_eq_zero] at C
            rw [SetCoe.ext C] at hb
            tauto
          tauto
        · simp

    rw [AnalyticAt.order_mul h₁φ (h₁g₀ b₀ b₀.2)]

    rw [h₂φ]
    simp

  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (AnalyticOnNhd.order_eq_nat_iff h₁g₀ (n b₀)).1 this

  use g₁
  constructor
  · exact h₁g₁
  · constructor
    · intro a h₁a
      by_cases h₂a : a = b₀
      · rwa [h₂a]
      · let A' := Finset.mem_of_mem_insert_of_ne h₁a h₂a
        let B' := h₃g₁ a
        let C' := h₂g₀ a A'
        rw [B'] at C'
        exact right_ne_zero_of_smul C'
    · intro z
      let A' := h₃g₀ z
      rw [h₃g₁ z] at A'
      rw [A']
      rw [← smul_assoc]
      congr
      simp
      rw [Finset.prod_insert]
      ring
      exact hb


theorem XX
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (hU : IsPreconnected U)
  (h₁f : AnalyticOnNhd ℂ f U)
  (h₂f : ∃ u ∈ U, f u ≠ 0) :
  ∀ (hu : u ∈ U), (h₁f u hu).order.toNat = (h₁f u hu).order := by

  intro hu
  apply ENat.coe_toNat
  by_contra C
  rw [(h₁f u hu).order_eq_top_iff] at C
  rw [← (h₁f u hu).frequently_zero_iff_eventually_zero] at C
  obtain ⟨u₁, h₁u₁, h₂u₁⟩ := h₂f
  rw [(h₁f.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hu C) h₁u₁] at h₂u₁
  tauto


theorem discreteZeros
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (hU : IsPreconnected U)
  (h₁f : AnalyticOnNhd ℂ f U)
  (h₂f : ∃ u ∈ U, f u ≠ 0) :
  DiscreteTopology ((U.restrict f)⁻¹' {0}) := by

  simp_rw [← singletons_open_iff_discrete]
  simp_rw [Metric.isOpen_singleton_iff]

  intro z

  let A := XX hU h₁f h₂f z.1.2
  rw [eq_comm] at A
  rw [AnalyticAt.order_eq_nat_iff] at A
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := A

  rw [Metric.eventually_nhds_iff_ball] at h₃g
  have : ∃ ε > 0, ∀ y ∈ Metric.ball (↑z) ε, g y ≠ 0 := by
    have h₄g : ContinuousAt g z := AnalyticAt.continuousAt h₁g
    have : {0}ᶜ ∈ nhds (g z) := by
      exact compl_singleton_mem_nhds_iff.mpr h₂g

    let F := h₄g.preimage_mem_nhds this
    rw [Metric.mem_nhds_iff] at F
    obtain ⟨ε, h₁ε, h₂ε⟩ := F
    use ε
    constructor; exact h₁ε
    intro y hy
    let G := h₂ε hy
    simp at G
    exact G
  obtain ⟨ε₁, h₁ε₁⟩ := this

  obtain ⟨ε₂, h₁ε₂, h₂ε₂⟩ := h₃g
  use min ε₁ ε₂
  constructor
  · have : 0 < min ε₁ ε₂ := by
      rw [lt_min_iff]
      exact And.imp_right (fun _ => h₁ε₂) h₁ε₁
    exact this

  intro y
  intro h₁y

  have h₂y : ↑y ∈ Metric.ball (↑z) ε₂ := by
    simp
    calc dist y z
    _ < min ε₁ ε₂ := by assumption
    _ ≤ ε₂ := by exact min_le_right ε₁ ε₂

  have h₃y : ↑y ∈ Metric.ball (↑z) ε₁ := by
    simp
    calc dist y z
    _ < min ε₁ ε₂ := by assumption
    _ ≤ ε₁ := by exact min_le_left ε₁ ε₂

  have F := h₂ε₂ y.1 h₂y
  have : f y = 0 := by exact y.2
  rw [this] at F
  simp at F

  have : g y.1 ≠ 0 := by
    exact h₁ε₁.2 y h₃y
  simp [this] at F
  ext
  rw [sub_eq_zero] at F
  tauto


theorem finiteZeros
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁U : IsPreconnected U)
  (h₂U : IsCompact U)
  (h₁f : AnalyticOnNhd ℂ f U)
  (h₂f : ∃ u ∈ U, f u ≠ 0) :
  Set.Finite (U.restrict f⁻¹' {0}) := by

  have closedness : IsClosed (U.restrict f⁻¹' {0}) := by
    apply IsClosed.preimage
    apply continuousOn_iff_continuous_restrict.1
    exact h₁f.continuousOn
    exact isClosed_singleton

  have : CompactSpace U := by
    exact isCompact_iff_compactSpace.mp h₂U

  apply (IsClosed.isCompact closedness).finite
  exact discreteZeros h₁U h₁f h₂f


theorem AnalyticOnNhdCompact.eliminateZeros
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁U : IsPreconnected U)
  (h₂U : IsCompact U)
  (h₁f : AnalyticOnNhd ℂ f U)
  (h₂f : ∃ u ∈ U, f u ≠ 0) :
  ∃ (g : ℂ → ℂ) (A : Finset U), AnalyticOnNhd ℂ g U ∧ (∀ z ∈ U, g z ≠ 0) ∧ ∀ z, f z = (∏ a ∈ A, (z - a) ^ (h₁f.order a).toNat) • g z := by

  let A := (finiteZeros h₁U h₂U h₁f h₂f).toFinset

  let n : U → ℕ := fun z ↦ (h₁f z z.2).order.toNat

  have hn : ∀ a ∈ A, (h₁f a a.2).order = n a := by
    intro a _
    dsimp [n, AnalyticOnNhd.order]
    rw [eq_comm]
    apply XX h₁U
    exact h₂f


  obtain ⟨g, h₁g, h₂g, h₃g⟩ := AnalyticOnNhd.eliminateZeros (A := A) h₁f n hn
  use g
  use A

  have inter : ∀ (z : ℂ), f z = (∏ a ∈ A, (z - ↑a) ^ (h₁f (↑a) a.property).order.toNat) • g z := by
    intro z
    rw [h₃g z]

  constructor
  · exact h₁g
  · constructor
    · intro z h₁z
      by_cases h₂z : ⟨z, h₁z⟩  ∈ ↑A.toSet
      · exact h₂g ⟨z, h₁z⟩ h₂z
      · have : f z ≠ 0 := by
          by_contra C
          have : ⟨z, h₁z⟩ ∈ ↑A.toSet := by
            dsimp [A]
            simp
            exact C
          tauto
        rw [inter z] at this
        exact right_ne_zero_of_smul this
    · exact inter


theorem AnalyticOnNhdCompact.eliminateZeros₂
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁U : IsPreconnected U)
  (h₂U : IsCompact U)
  (h₁f : AnalyticOnNhd ℂ f U)
  (h₂f : ∃ u ∈ U, f u ≠ 0) :
  ∃ (g : ℂ → ℂ), AnalyticOnNhd ℂ g U ∧ (∀ z ∈ U, g z ≠ 0) ∧ ∀ z, f z = (∏ a ∈ (finiteZeros h₁U h₂U h₁f h₂f).toFinset, (z - a) ^ (h₁f.order a).toNat) • g z := by

  let A := (finiteZeros h₁U h₂U h₁f h₂f).toFinset

  let n : U → ℕ := fun z ↦ (h₁f z z.2).order.toNat

  have hn : ∀ a ∈ A, (h₁f a a.2).order = n a := by
    intro a _
    dsimp [n, AnalyticOnNhd.order]
    rw [eq_comm]
    apply XX h₁U
    exact h₂f

  obtain ⟨g, h₁g, h₂g, h₃g⟩ := AnalyticOnNhd.eliminateZeros (A := A) h₁f n hn
  use g

  have inter : ∀ (z : ℂ), f z = (∏ a ∈ A, (z - ↑a) ^ (h₁f (↑a) a.property).order.toNat) • g z := by
    intro z
    rw [h₃g z]

  constructor
  · exact h₁g
  · constructor
    · intro z h₁z
      by_cases h₂z : ⟨z, h₁z⟩  ∈ ↑A.toSet
      · exact h₂g ⟨z, h₁z⟩ h₂z
      · have : f z ≠ 0 := by
          by_contra C
          have : ⟨z, h₁z⟩ ∈ ↑A.toSet := by
            dsimp [A]
            simp
            exact C
          tauto
        rw [inter z] at this
        exact right_ne_zero_of_smul this
    · exact h₃g


theorem AnalyticOnNhdCompact.eliminateZeros₁
  {f : ℂ → ℂ}
  {U : Set ℂ}
  (h₁U : IsPreconnected U)
  (h₂U : IsCompact U)
  (h₁f : AnalyticOnNhd ℂ f U)
  (h₂f : ∃ u ∈ U, f u ≠ 0) :
  ∃ (g : ℂ → ℂ), AnalyticOnNhd ℂ g U ∧ (∀ z ∈ U, g z ≠ 0) ∧ ∀ z, f z = (∏ᶠ a, (z - a) ^ (h₁f.order a).toNat) • g z := by

  let A := (finiteZeros h₁U h₂U h₁f h₂f).toFinset

  let n : U → ℕ := fun z ↦ (h₁f z z.2).order.toNat

  have hn : ∀ a ∈ A, (h₁f a a.2).order = n a := by
    intro a _
    dsimp [n, AnalyticOnNhd.order]
    rw [eq_comm]
    apply XX h₁U
    exact h₂f

  obtain ⟨g, h₁g, h₂g, h₃g⟩ := AnalyticOnNhd.eliminateZeros (A := A) h₁f n hn
  use g

  have inter : ∀ (z : ℂ), f z = (∏ a ∈ A, (z - ↑a) ^ (h₁f (↑a) a.property).order.toNat) • g z := by
    intro z
    rw [h₃g z]

  constructor
  · exact h₁g
  · constructor
    · intro z h₁z
      by_cases h₂z : ⟨z, h₁z⟩  ∈ ↑A.toSet
      · exact h₂g ⟨z, h₁z⟩ h₂z
      · have : f z ≠ 0 := by
          by_contra C
          have : ⟨z, h₁z⟩ ∈ ↑A.toSet := by
            dsimp [A]
            simp
            exact C
          tauto
        rw [inter z] at this
        exact right_ne_zero_of_smul this
    · intro z

      let φ : U → ℂ := fun a ↦ (z - ↑a) ^ (h₁f.order a).toNat
      have hφ : Function.mulSupport φ ⊆ A := by
        intro x hx
        simp [φ] at hx
        have : (h₁f.order x).toNat ≠ 0 := by
          by_contra C
          rw [C] at hx
          simp at hx
        simp [A]
        exact (h₁f x x.2).apply_eq_zero_of_order_toNat_ne_zero this
      rw [finprod_eq_prod_of_mulSupport_subset φ hφ]
      rw [inter z]
      rfl
