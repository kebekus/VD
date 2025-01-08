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
    rw [sub_le_iff_le_add]
    rw [div_le_iff₀ hT] at hn₁
    rw [sub_le_iff_le_add] at hn₁
    rw [add_comm]
    exact hn₁
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, max a₁ a₂ ≤ t + n₂ * T := by
    obtain ⟨n₂, hn₂⟩ := exists_nat_ge ((max a₁ a₂ - t) / T)
    use n₂
    rw [← sub_le_iff_le_add]
    rw [div_le_iff₀ hT] at hn₂
    linarith

  have : Set.uIcc a₁ a₂ ⊆ Set.uIcc (t - n₁ * T) (t + n₂ * T) := by
    apply Set.uIcc_subset_uIcc_iff_le.mpr
    constructor
    · calc min (t - ↑n₁ * T) (t + ↑n₂ * T)
      _ ≤ (t - ↑n₁ * T) := by exact min_le_left (t - ↑n₁ * T) (t + ↑n₂ * T)
      _ ≤ min a₁ a₂ := by exact hn₁
    · calc max a₁ a₂
      _ ≤ t + n₂ * T := by exact hn₂
      _ ≤ max (t - ↑n₁ * T) (t + ↑n₂ * T) := by exact le_max_right (t - ↑n₁ * T) (t + ↑n₂ * T)

  apply IntervalIntegrable.mono_set _ this
  exact periodic_integrability₃ h₁f h₂f
