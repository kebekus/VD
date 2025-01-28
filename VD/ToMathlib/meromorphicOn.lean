import Mathlib.Analysis.Analytic.Meromorphic
import VD.ToMathlib.meromorphicAt

--open scoped Topology
--open Real Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {f : 𝕜 → E}

/-- The set where a meromorphic function has infinite order is clopen in its domain of meromorphy. -/
theorem MeromorphicOn.clopen_of_order_eq_top {U : Set 𝕜} (h₁f : MeromorphicOn f U) :
    IsClopen { u : U | (h₁f u.1 u.2).order = ⊤ } := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (h₁f z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← (h₁f z.1 z.2).order_eq_top_iff] at h
      tauto
    · -- Case: f is locally nonzero in a punctured neighborhood of z
      obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1
        (h.and (h₁f z.1 z.2).eventually_analyticAt))
      use Subtype.val ⁻¹' t'
      constructor
      · intro w hw
        simp
        by_cases h₁w : w = z
        · rwa [h₁w]
        · have h₂f := (h₁t' w hw) (Subtype.coe_ne_coe.mpr h₁w)
          simp [h₂f.2.meromorphicAt_order, h₂f.2.order_eq_zero_iff.2 h₂f.1]
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    simp_rw [MeromorphicAt.order_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at *
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := hz
    use Subtype.val ⁻¹' t'
    simp [isOpen_induced h₂t', h₃t']
    intro w hw
    simp
    -- Trivial case: w = z
    by_cases h₁w : w = z
    · rw [h₁w]
      tauto
    -- Nontrivial case: w ≠ z
    use t' \ {z.1}, fun y hy _ ↦ h₁t' y (Set.mem_of_mem_diff hy) (Set.mem_of_mem_inter_right hy)
    constructor
    · exact h₂t'.sdiff isClosed_singleton
    · apply (Set.mem_diff w).1
      exact ⟨hw, Set.mem_singleton_iff.not.1 (Subtype.coe_ne_coe.2 h₁w)⟩
