import Mathlib.MeasureTheory.Integral.Periodic

/-- A periodic function is interval integrable over every interval if it is interval integrable
  over one period. -/
theorem Function.Periodic.intervalperiodic_integrability
  {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E}
  {a₁ a₂ t T : ℝ}
  (h₁f : Function.Periodic f T)
  (hT : 0 < T)
  (h₂f : IntervalIntegrable f MeasureTheory.volume t (t + T)) :
  IntervalIntegrable f MeasureTheory.volume a₁ a₂ := by

  -- Replace [a₁, a₂] by [t - n₁ * T, t + n₂ * T], where n₁ and n₂ are integers
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge ((t -min a₁ a₂) / T)
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge ((max a₁ a₂ - t) / T)
  have : Set.uIcc a₁ a₂ ⊆ Set.uIcc (t - n₁ * T) (t + n₂ * T) := by
    apply Set.uIcc_subset_uIcc_iff_le.mpr
    constructor
    · calc min (t - ↑n₁ * T) (t + ↑n₂ * T)
      _ ≤ (t - ↑n₁ * T) := by apply min_le_left
      _ ≤ min a₁ a₂ := by linarith [(div_le_iff₀ hT).1 hn₁]
    · calc max a₁ a₂
      _ ≤ t + n₂ * T := by linarith [(div_le_iff₀ hT).1 hn₂]
      _ ≤ max (t - ↑n₁ * T) (t + ↑n₂ * T) := by apply le_max_right
  apply IntervalIntegrable.mono_set _ this
  clear this

  -- Suffices to show integrability over one shifted period
  let a : ℕ → ℝ := fun n ↦ t + (n - n₁) * T
  rw [(by ring : t - n₁ * T = a 0), (by simp [a] : t + n₂ * T = a (n₁ + n₂))]
  apply IntervalIntegrable.trans_iterate (a := fun n ↦ t + (n - n₁) * T)
  clear a

  -- Show integrability over one shifted period
  intro k hk
  convert (IntervalIntegrable.comp_sub_right h₂f ((k - ↑n₁) * T)) using 1
  · funext x
    rw [← h₁f.sub_int_mul_eq (k - n₁)]
    simp
  · rw [Nat.cast_add]
    ring
