import Mathlib.MeasureTheory.Integral.Periodic


theorem periodic_integrability₁
  {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E}
  {t T : ℝ}
  {n : ℕ}
  (h₁f : Function.Periodic f T)
  (h₂f : IntervalIntegrable f MeasureTheory.volume t (t + T)) :
  IntervalIntegrable f MeasureTheory.volume t (t + n * T) := by
  induction' n with n hn
  simp
  apply IntervalIntegrable.trans (b := t + n * T)
  exact hn

  let A := IntervalIntegrable.comp_sub_right h₂f (n * T)
  have : f = fun x ↦ f (x - n * T) := by simp [Function.Periodic.sub_nat_mul_eq h₁f n]
  simp_rw [← this] at A
  have : (t + T + ↑n * T) = (t + ↑(n + 1) * T) := by simp; ring
  simp_rw [this] at A
  exact A

theorem periodic_integrability₂
  {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E}
  {t T : ℝ}
  {n : ℕ}
  (h₁f : Function.Periodic f T)
  (h₂f : IntervalIntegrable f MeasureTheory.volume t (t + T)) :
  IntervalIntegrable f MeasureTheory.volume (t - n * T) t := by
  induction' n with n hn
  simp
  --
  apply IntervalIntegrable.trans (b := t - n * T)
  --
  have A := IntervalIntegrable.comp_add_right h₂f (((n + 1): ℕ) * T)

  have : f = fun x ↦ f (x + ((n + 1) : ℕ) * T) := by
    funext x
    have : x = x + ↑(n + 1) * T - ↑(n + 1) * T := by ring
    nth_rw 1 [this]
    rw [Function.Periodic.sub_nat_mul_eq h₁f]
  simp_rw [← this] at A
  have : (t + T - ↑(n + 1) * T) = (t - ↑n * T) := by simp; ring
  simp_rw [this] at A
  exact A
  --
  exact hn


theorem periodic_integrability₃
  {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E}
  {t T : ℝ}
  {n₁ n₂ : ℕ}
  (h₁f : Function.Periodic f T)
  (h₂f : IntervalIntegrable f MeasureTheory.volume t (t + T)) :
  IntervalIntegrable f MeasureTheory.volume (t - n₁ * T) (t + n₂ * T) := by
  apply IntervalIntegrable.trans (b := t)
  exact periodic_integrability₂ h₁f h₂f
  exact periodic_integrability₁ h₁f h₂f

/-- A periodic function is interval integrable over every interval if it is
  interval integrable over one period. -/
theorem periodic_integrability4
  {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E}
  {t T : ℝ}
  {a₁ a₂ : ℝ}
  (h₁f : Function.Periodic f T)
  (hT : 0 < T)
  (h₂f : IntervalIntegrable f MeasureTheory.volume t (t + T)) :
  IntervalIntegrable f MeasureTheory.volume a₁ a₂ := by

  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, t - n₁ * T ≤ min a₁ a₂ := by
    obtain ⟨n₁, hn₁⟩ := exists_nat_ge ((t -min a₁ a₂) / T)
    use n₁
    rw [div_le_iff₀ hT] at hn₁
    linarith
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, max a₁ a₂ ≤ t + n₂ * T := by
    obtain ⟨n₂, hn₂⟩ := exists_nat_ge ((max a₁ a₂ - t) / T)
    use n₂
    rw [div_le_iff₀ hT] at hn₂
    linarith

  have : Set.uIcc a₁ a₂ ⊆ Set.uIcc (t - n₁ * T) (t + n₂ * T) := by
    apply Set.uIcc_subset_uIcc_iff_le.mpr
    constructor
    · calc min (t - ↑n₁ * T) (t + ↑n₂ * T)
      _ ≤ (t - ↑n₁ * T) := by apply min_le_left
      _ ≤ min a₁ a₂ := hn₁
    · calc max a₁ a₂
      _ ≤ t + n₂ * T := hn₂
      _ ≤ max (t - ↑n₁ * T) (t + ↑n₂ * T) := by apply le_max_right

  apply IntervalIntegrable.mono_set _ this
  let a : ℕ → ℝ := fun n ↦ t + (n - n₁) * T
  have a₀ : a 0 = t - n₁ * T := by sorry
  rw [← a₀]; clear a₀
  have a₁ : a (n₁ + n₂) = t + n₂ * T := by sorry
  rw [← a₁]; clear a₁
  apply IntervalIntegrable.trans_iterate
  intro k hk
  simp [a]
  clear a

  have A := IntervalIntegrable.comp_sub_right h₂f ((k - ↑n₁) * T)
  have : (fun x ↦ f (x - (k - n₁) * T)) = f := by
    /-
    let N : ℕ := k - n₁
    rw [← N]
    funext x
    have : (k : ℝ ) - (n₁ : ℝ) = ((k - n₁) : ℝ) := by sorry
    rw [this]
    rw [h₁f.sub_int_mul_eq]
    apply h₁f.sub_int_mul_eq --sub_zsmul_eq
    refine h₁fFunction.Periodic.funext ?_
    -/
    sorry
  simp_rw [this] at A
  have : t + T + (k - ↑n₁) * T = t + (k + 1 - ↑n₁) * T := by ring
  rw [this] at A
  tauto
