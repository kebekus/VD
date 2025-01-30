/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Positive Part of the Logarithm

This file defines the function `log⁺ = r ↦ max 0 (log r)`, and establishes
standard estimates.
-/

open Real


/-!
## Definition, Notation and Reformulations
-/
noncomputable def Real.logpos : ℝ → ℝ := fun r ↦ max 0 (log r)

notation "log⁺" => logpos

theorem Real.logpos_def {r : ℝ} : log⁺ r = max 0 (log r) := rfl

theorem Real.log_eq_logpos_sub_logpos_inv {r : ℝ} : log r = log⁺ r - log⁺ r⁻¹ := by
  rw [logpos_def, logpos_def, log_inv]
  by_cases h : 0 ≤ log r
  · simp [h]
  · rw [not_le] at h
    simp [h, neg_nonneg.mp (Left.nonneg_neg_iff.2 h.le)]

theorem Real.logpos_eq_half_mul_log_add_log_abs {r : ℝ} : log⁺ r = 2⁻¹ * (log r + |log r|) := by
  by_cases hr : 0 ≤ log r
  · simp [logpos, hr, abs_of_nonneg hr]
    ring
  · simp [logpos, le_of_not_ge hr, abs_of_nonpos (le_of_not_ge hr)]


/-!
## Elementary Properties
-/
theorem Real.logpos_nonneg {x : ℝ} : 0 ≤ log⁺ x := by simp [logpos]

theorem Real.logpos_neg (x : ℝ) : log⁺ x = log⁺ (-x) := by simp [logpos]

theorem Real.logpos_abs (x : ℝ) : log⁺ |x| = log⁺ x := by simp [logpos]

theorem Real.logpos_eq_zero_iff (x : ℝ) :
    log⁺ x = 0 ↔ |x| ≤ 1 := by
  rw [← logpos_abs, ← log_nonpos_iff (abs_nonneg x)]
  simp [logpos]

theorem Real.logpos_eq_log {x : ℝ} (hx : 1 ≤ |x|) :
    log⁺ x = log x := by
  simp [logpos]
  rw [← log_abs]
  apply log_nonneg hx

theorem Real.logpos_eq_log_of_nat {n : ℕ} : log n = log⁺ n := by
  by_cases hn : n = 0
  · simp [hn, logpos]
  · simp [logpos_eq_log, abs_of_nonneg, Nat.one_le_iff_ne_zero.mpr hn, Nat.cast_nonneg']

theorem Real.monotoneOn_logpos : MonotoneOn log⁺ (Set.Ici 0) := by
  intro x hx y hy hxy
  simp [logpos]
  by_cases h : log x ≤ 0
  · tauto
  · right
    have := log_le_log (lt_trans Real.zero_lt_one ((log_pos_iff hx).1 (not_le.1 h))) hxy
    simp [this]
    linarith

/-!
## Estimates for Sums and Products
-/
theorem Real.logpos_mul {a b : ℝ} :
    log⁺ (a * b) ≤ log⁺ a + log⁺ b := by
  by_cases ha : a = 0
  · simp [ha, logpos]
  by_cases hb : b = 0
  · simp [hb, logpos]
  unfold logpos
  nth_rw 1 [← add_zero 0, log_mul ha hb]
  exact max_add_add_le_max_add_max

theorem Real.logpos_mul_nat {n : ℕ} {a : ℝ} :
    log⁺ (n * a) ≤ log n + log⁺ a := by
  rw [logpos_eq_log_of_nat]
  exact logpos_mul

theorem logpos_add_le_add_logpos_add_log2₀
  {a b : ℝ}
  (h : |a| ≤ |b|) :
  log⁺ (a + b) ≤ log⁺ a + log⁺ b + log 2 := by

  nth_rw 1 [← logpos_abs]
  nth_rw 2 [← logpos_abs]
  nth_rw 3 [← logpos_abs]

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

theorem logpos_add_le_add_logpos_add_log2 {a b : ℝ} :
    log⁺ (a + b) ≤ log⁺ a + log⁺ b + log 2 := by
  by_cases h : |a| ≤ |b|
  · exact logpos_add_le_add_logpos_add_log2₀ h
  · rw [add_comm a b, add_comm (log⁺ a) (log⁺ b)]
    apply logpos_add_le_add_logpos_add_log2₀
    exact le_of_not_ge h

theorem Real.logpos_sum {n : ℕ} (f : Fin n → ℝ) :
    log⁺ (∑ t, f t) ≤ log n + ∑ t, log⁺ (f t) := by
  -- Trivial case: empty sum
  by_cases hs : n = 0
  · simp [hs, Fin.isEmpty', logpos]
  -- Nontrivial case:
  -- Obtain maximal element…
  have nonEmpty := Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_ne_zero hs)
  obtain ⟨t_max, ht_max⟩ := Finite.exists_max (fun t ↦ |f t|)
  -- …then calculate
  calc log⁺ (∑ t, f t)
  _ = log⁺ |∑ t, f t| := by
    rw [Real.logpos_abs]
  _ ≤ log⁺ (∑ t, |f t|) := by
    apply monotoneOn_logpos (by simp) (by simp [Finset.sum_nonneg])
    simp [Finset.abs_sum_le_sum_abs]
  _ ≤ log⁺ (∑ t : Fin n, |f t_max|) := by
    apply monotoneOn_logpos (by simp [Finset.sum_nonneg]) (by simp [Finset.sum_nonneg]; positivity)
    exact Finset.sum_le_sum fun i a ↦ ht_max i
  _ = log⁺ (n * |f t_max|) := by
    simp [Finset.sum_const]
  _ ≤ log n + log⁺ |f t_max| := Real.logpos_mul_nat
  _ ≤ log n + ∑ t, log⁺ (f t) := by
    --Finset.single_le_sum
    sorry

/-
For any positive real numbers a₁,...,aₙ: log⁺(a₁ + ... + aₙ) ≤ log⁺ a₁ + ... +
log⁺ aₙ + log n Proof:

First, a₁ + ... + aₙ ≤ n max(a₁,...,aₙ)

Taking logarithms: log(a₁ + ... + aₙ) ≤ log n + log(max(a₁,...,aₙ))

Note that log(max(a₁,...,aₙ)) ≤ max(log a₁,...,log aₙ) ≤ log⁺ a₁ + ... + log⁺ aₙ

Therefore log(a₁ + ... + aₙ) ≤ log n + log⁺ a₁ + ... + log⁺ aₙ

Taking positive parts of both sides gives the desired inequality.
-/
