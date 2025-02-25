import Mathlib.Analysis.Meromorphic.Order

open Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem AnalyticOnNhd.codiscrete_setOf_order_eq_zero_or_top {f : 𝕜 → E} {U : Set 𝕜}
    (hf : AnalyticOnNhd 𝕜 f U) :
    {u : U | (hf u u.2).order = 0 ∨ (hf u u.2).order = ⊤} ∈ Filter.codiscrete U := by
  rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Filter.Eventually.eventually_nhds h₁f)]
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Subtype.exists,
      exists_and_right, exists_eq_right, not_exists, not_or, not_and, not_forall, Decidable.not_not]
    intro a _ h₁a
    use h₁a
    by_cases h₂a : a = x
    · rw [← (hf x hx).order_eq_top_iff] at h₁f
      simp_rw [h₂a]
      tauto
    · have : (hf a h₁a).order = ⊤ := by rwa [(hf a h₁a).order_eq_top_iff]
      tauto
  · filter_upwards [h₁f]
    intro a h₁a
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Subtype.exists,
      exists_and_right, exists_eq_right, not_exists, not_or, not_and, not_forall, Decidable.not_not]
    intro h₂a
    use h₂a
    rw [(hf a h₂a).order_eq_zero_iff.2 h₁a]
    tauto

theorem MeromorphicOn.codiscrete_setOf_order_eq_zero_or_top [CompleteSpace E] {f : 𝕜 → E} {U : Set 𝕜}
    (hf : MeromorphicOn f U) :
    {u : U | (hf u u.2).order = 0 ∨ (hf u u.2).order = ⊤} ∈ Filter.codiscrete U := by
  rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_eventually_nhdsWithin.2 h₁f]
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Subtype.exists,
      exists_and_right, exists_eq_right, not_exists, not_or, not_and, not_forall, Decidable.not_not]
    intro a h₁a h₂a
    use h₂a
    by_cases h₃a : a = x
    · rw [← (hf x hx).order_eq_top_iff] at h₁f
      simp_rw [h₃a]
      tauto
    · have : (hf a h₂a).order = ⊤ := by
        rw [(hf a h₂a).order_eq_top_iff]
        rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at h₁a ⊢
        obtain ⟨t, h₁t, h₂t, h₃t⟩ := h₁a
        use t \ {x}, fun y h₁y _ ↦ h₁t y h₁y.1 h₁y.2
        exact ⟨h₂t.sdiff isClosed_singleton, Set.mem_diff_of_mem h₃t h₃a⟩
      tauto
  · filter_upwards [(hf x hx).eventually_analyticAt, h₁f]
    intro a h₁a h₂a
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Subtype.exists,
      exists_and_right, exists_eq_right, not_exists, not_or, not_and, not_forall, Decidable.not_not]
    intro h₃a
    use h₃a
    rw [h₁a.meromorphicAt_order, h₁a.order_eq_zero_iff.2 h₂a]
    tauto
