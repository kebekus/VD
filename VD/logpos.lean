import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real


noncomputable def logpos : ℝ → ℝ := fun r ↦ max 0 (log r)

notation "log⁺" => logpos


theorem loglogpos {r : ℝ} : log r = log⁺ r - log⁺ r⁻¹ := by
  unfold logpos
  rw [log_inv]
  by_cases h : 0 ≤ log r
  · simp [h]
  · simp at h
    have : 0 ≤ -log r := Left.nonneg_neg_iff.2 (le_of_lt h)
    simp [h, this]
    exact neg_nonneg.mp this


theorem logpos_norm {r : ℝ} : log⁺ r = 2⁻¹ * (log r + ‖log r‖) := by
  by_cases hr : 0 ≤ log r
  · rw [norm_of_nonneg hr]
    have : logpos r = log r := by
      unfold logpos
      simp [hr]
    rw [this]
    ring
  · rw [norm_of_nonpos (le_of_not_ge hr)]
    have : logpos r = 0 := by
      unfold logpos
      simp
      exact le_of_not_ge hr
    rw [this]
    ring


theorem logpos_nonneg
  {x : ℝ} :
  0 ≤ log⁺ x := by
  unfold logpos
  simp


theorem logpos_abs
  {x : ℝ} :
  log⁺ x = log⁺ |x| := by
  unfold logpos
  simp

-- Warning: This should be fixed in Mathlib

theorem log_pos_iff' (hx : 0 ≤ x) : 0 < log x ↔ 1 < x := by
  by_cases h₁x : x = 0
  · rw [h₁x]; simp
  · exact log_pos_iff (lt_of_le_of_ne hx (Ne.symm h₁x))


theorem Real.monotoneOn_logpos :
  MonotoneOn logpos (Set.Ici 0) := by

  intro x hx y hy hxy
  unfold logpos
  simp

  by_cases h : log x ≤ 0
  · tauto
  · simp [h]
    simp at h

    have : log x ≤ log y := by
      apply log_le_log
      --
      rw [log_pos_iff' hx] at h
      have : (0 : ℝ) < 1 := by exact Real.zero_lt_one
      exact lt_trans this h
      assumption

    constructor
    · linarith
    · linarith


theorem logpos_add_le_add_logpos_add_log2₀
  {a b : ℝ}
  (h : |a| ≤ |b|) :
  log⁺ (a + b) ≤ log⁺ a + log⁺ b + log 2 := by

  nth_rw 1 [logpos_abs]
  nth_rw 2 [logpos_abs]
  nth_rw 3 [logpos_abs]

  calc log⁺ |a + b|
  _ ≤ log⁺ (|a| + |b|) := by
    apply Real.monotoneOn_logpos
    simp [abs_nonneg]; simp [abs_nonneg]
    apply add_nonneg
    simp [abs_nonneg]; simp [abs_nonneg]
    exact abs_add_le a b
  _ ≤ log⁺ (|b| + |b|) := by
    apply Real.monotoneOn_logpos
    simp [abs_nonneg]
    apply add_nonneg
    simp [abs_nonneg]; simp [abs_nonneg]
    simp [h]
    linarith
  _ = log⁺ (2 * |b|) := by
    congr; ring
  _ ≤ log⁺ |b| + log 2 := by
    unfold logpos; simp
    constructor
    · apply add_nonneg
      simp
      exact log_nonneg one_le_two
    · by_cases hb: b = 0
      · rw [hb]; simp
        exact log_nonneg one_le_two
      · rw [log_mul, log_abs, add_comm]
        simp
        exact Ne.symm (NeZero.ne' 2)
        exact abs_ne_zero.mpr hb
  _ ≤ log⁺ |a| + log⁺ |b| + log 2 := by
    unfold logpos; simp


theorem logpos_add_le_add_logpos_add_log2
  {a b : ℝ} :
  log⁺ (a + b) ≤ log⁺ a + log⁺ b + log 2 := by

  by_cases h : |a| ≤ |b|
  · exact logpos_add_le_add_logpos_add_log2₀ h
  · rw [add_comm a b, add_comm (log⁺ a) (log⁺ b)]
    apply logpos_add_le_add_logpos_add_log2₀
    exact le_of_not_ge h

theorem monoOn_logpos :
  MonotoneOn log⁺ (Set.Ici 0) := by
  intro x hx y hy hxy
  by_cases h₁x : x = 0
  · rw [h₁x]
    unfold logpos
    simp

  simp at hx hy
  unfold logpos
  simp
  by_cases h₂x : log x ≤ 0
  · tauto
  · simp [h₂x]
    simp at h₂x
    have : log x ≤ log y := by
      apply log_le_log
      exact lt_of_le_of_ne hx fun a => h₁x (id (Eq.symm a))
      assumption
    simp [this]
    calc 0
    _ ≤ log x := by exact le_of_lt h₂x
    _ ≤ log y := this
