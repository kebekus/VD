import VD.laplace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]


def Harmonic (f : ℂ → F) : Prop :=
  (ContDiff ℝ 2 f) ∧ (∀ z, Δ f z = 0)

def HarmonicAt (f : ℂ → F) (x : ℂ) : Prop :=
  (ContDiffAt ℝ 2 f x) ∧ (Δ f =ᶠ[nhds x] 0)

def HarmonicOn (f : ℂ → F) (s : Set ℂ) : Prop :=
  (ContDiffOn ℝ 2 f s) ∧ (∀ z ∈ s, Δ f z = 0)


theorem HarmonicAt_iff
  {f : ℂ → F}
  {x : ℂ} :
  HarmonicAt f x ↔ ∃ s : Set ℂ, IsOpen s ∧ x ∈ s ∧ (ContDiffOn ℝ 2 f s) ∧ (∀ z ∈ s, Δ f z = 0) := by
  constructor
  · intro hf
    obtain ⟨s₁, h₁s₁, h₂s₁, h₃s₁⟩ := hf.1.contDiffOn' le_rfl (by trivial)
    simp at h₃s₁
    obtain ⟨t₂, h₁t₂, h₂t₂⟩ := (Filter.eventuallyEq_iff_exists_mem.1 hf.2)
    obtain ⟨s₂, h₁s₂, h₂s₂, h₃s₂⟩ := mem_nhds_iff.1 h₁t₂
    let s := s₁ ∩ s₂
    use s
    constructor
    · exact IsOpen.inter h₁s₁ h₂s₂
    · constructor
      · exact Set.mem_inter h₂s₁ h₃s₂
      · constructor
        · exact h₃s₁.mono Set.inter_subset_left
        · intro z hz
          exact h₂t₂ (h₁s₂ hz.2)
  · intro hyp
    obtain ⟨s, h₁s, h₂s, h₁f, h₂f⟩ := hyp
    constructor
    · apply h₁f.contDiffAt
      apply (IsOpen.mem_nhds_iff h₁s).2 h₂s
    · apply Filter.eventuallyEq_iff_exists_mem.2
      use s
      constructor
      · apply (IsOpen.mem_nhds_iff h₁s).2 h₂s
      · exact h₂f

theorem HarmonicAt_isOpen
  (f : ℂ → F) :
  IsOpen { x : ℂ | HarmonicAt f x } := by

  rw [← subset_interior_iff_isOpen]
  intro x hx
  simp at hx
  obtain ⟨s, h₁s, h₂s, h₃s⟩ := HarmonicAt_iff.1 hx
  use s
  constructor
  · simp
    constructor
    · exact h₁s
    · intro x hx
      simp
      rw [HarmonicAt_iff]
      use s
  · exact h₂s

theorem HarmonicAt_eventuallyEq {f₁ f₂ : ℂ → F} {x : ℂ} (h : f₁ =ᶠ[nhds x] f₂) : HarmonicAt f₁ x ↔ HarmonicAt f₂ x := by
  constructor
  · intro h₁
    constructor
    · exact ContDiffAt.congr_of_eventuallyEq h₁.1 (Filter.EventuallyEq.symm h)
    · exact Filter.EventuallyEq.trans (laplace_eventuallyEq' (Filter.EventuallyEq.symm h)) h₁.2
  · intro h₁
    constructor
    · exact ContDiffAt.congr_of_eventuallyEq h₁.1 h
    · exact Filter.EventuallyEq.trans (laplace_eventuallyEq' h) h₁.2


theorem HarmonicOn_of_locally_HarmonicOn {f : ℂ → F} {s : Set ℂ} (h : ∀ x ∈ s, ∃ (u : Set ℂ), IsOpen u ∧ x ∈ u ∧ HarmonicOn f (s ∩ u)) :
  HarmonicOn f s := by
  constructor
  · apply contDiffOn_of_locally_contDiffOn
    intro x xHyp
    obtain ⟨u, uHyp⟩ := h x xHyp
    use u
    exact ⟨ uHyp.1, ⟨uHyp.2.1, uHyp.2.2.1⟩⟩
  · intro x xHyp
    obtain ⟨u, uHyp⟩ := h x xHyp
    exact (uHyp.2.2.2) x ⟨xHyp, uHyp.2.1⟩


theorem HarmonicOn_congr {f₁ f₂ : ℂ → F} {s : Set ℂ} (hs : IsOpen s) (hf₁₂ : ∀ x ∈ s, f₁ x = f₂ x) :
  HarmonicOn f₁ s ↔ HarmonicOn f₂ s := by
  constructor
  · intro h₁
    constructor
    · apply ContDiffOn.congr h₁.1
      intro x hx
      rw [eq_comm]
      exact hf₁₂ x hx
    · intro z hz
      have : f₁ =ᶠ[nhds z] f₂ := by
        unfold Filter.EventuallyEq
        unfold Filter.Eventually
        simp
        refine mem_nhds_iff.mpr ?_
        use s
        constructor
        · exact hf₁₂
        · constructor
          · exact hs
          · exact hz
      rw [← laplace_eventuallyEq this]
      exact h₁.2 z hz
  · intro h₁
    constructor
    · apply ContDiffOn.congr h₁.1
      intro x hx
      exact hf₁₂ x hx
    · intro z hz
      have : f₁ =ᶠ[nhds z] f₂ := by
        unfold Filter.EventuallyEq
        unfold Filter.Eventually
        simp
        refine mem_nhds_iff.mpr ?_
        use s
        constructor
        · exact hf₁₂
        · constructor
          · exact hs
          · exact hz
      rw [laplace_eventuallyEq this]
      exact h₁.2 z hz


theorem harmonic_add_harmonic_is_harmonic {f₁ f₂ : ℂ → F} (h₁ : Harmonic f₁) (h₂ : Harmonic f₂) :
  Harmonic (f₁ + f₂) := by
  constructor
  · exact ContDiff.add h₁.1 h₂.1
  · rw [laplace_add h₁.1 h₂.1]
    simp
    intro z
    rw [h₁.2 z, h₂.2 z]
    simp


theorem harmonicOn_add_harmonicOn_is_harmonicOn {f₁ f₂ : ℂ → F} {s : Set ℂ} (hs : IsOpen s) (h₁ : HarmonicOn f₁ s) (h₂ : HarmonicOn f₂ s) :
  HarmonicOn (f₁ + f₂) s := by
  constructor
  · exact ContDiffOn.add h₁.1 h₂.1
  · intro z hz
    rw [laplace_add_ContDiffOn hs h₁.1 h₂.1 z hz]
    rw [h₁.2 z hz, h₂.2 z hz]
    simp


theorem harmonicAt_add_harmonicAt_is_harmonicAt
  {f₁ f₂ : ℂ → F}
  {x : ℂ}
  (h₁ : HarmonicAt f₁ x)
  (h₂ : HarmonicAt f₂ x) :
  HarmonicAt (f₁ + f₂) x := by
  constructor
  · exact ContDiffAt.add h₁.1 h₂.1
  · apply Filter.EventuallyEq.trans (laplace_add_ContDiffAt' h₁.1 h₂.1)
    apply Filter.EventuallyEq.trans (Filter.EventuallyEq.add h₁.2 h₂.2)
    simp
    rfl


theorem harmonic_smul_const_is_harmonic {f : ℂ → F} {c : ℝ} (h : Harmonic f) :
  Harmonic (c • f) := by
  constructor
  · exact ContDiff.const_smul c h.1
  · rw [laplace_smul]
    dsimp
    intro z
    rw [h.2 z]
    simp


theorem harmonicAt_smul_const_is_harmonicAt
  {f : ℂ → F}
  {x : ℂ}
  {c : ℝ}
  (h : HarmonicAt f x) :
  HarmonicAt (c • f) x := by
  constructor
  · exact ContDiffAt.const_smul c h.1
  · rw [laplace_smul]
    have A := Filter.EventuallyEq.const_smul h.2 c
    simp at A
    assumption


theorem harmonic_iff_smul_const_is_harmonic {f : ℂ → F} {c : ℝ} (hc : c ≠ 0) :
  Harmonic f ↔ Harmonic (c • f) := by
  constructor
  · exact harmonic_smul_const_is_harmonic
  · nth_rewrite 2 [((eq_inv_smul_iff₀ hc).mpr rfl : f = c⁻¹ • c • f)]
    exact fun a => harmonic_smul_const_is_harmonic a


theorem harmonicAt_iff_smul_const_is_harmonicAt
  {f : ℂ → F}
  {x : ℂ}
  {c : ℝ}
  (hc : c ≠ 0) :
  HarmonicAt f x ↔ HarmonicAt (c • f) x := by
  constructor
  · exact harmonicAt_smul_const_is_harmonicAt
  · nth_rewrite 2 [((eq_inv_smul_iff₀ hc).mpr rfl : f = c⁻¹ • c • f)]
    exact fun a => harmonicAt_smul_const_is_harmonicAt a


theorem harmonic_comp_CLM_is_harmonic {f : ℂ → F₁} {l : F₁ →L[ℝ] G} (h : Harmonic f) :
  Harmonic (l ∘ f) := by

  constructor
  · -- Continuous differentiability
    apply ContDiff.comp
    exact ContinuousLinearMap.contDiff l
    exact h.1
  · rw [laplace_compCLM]
    simp
    intro z
    rw [h.2 z]
    simp
    exact ContDiff.restrict_scalars ℝ h.1


theorem harmonicOn_comp_CLM_is_harmonicOn {f : ℂ → F₁} {s : Set ℂ} {l : F₁ →L[ℝ] G} (hs : IsOpen s) (h : HarmonicOn f s) :
  HarmonicOn (l ∘ f) s := by

  constructor
  · -- Continuous differentiability
    apply ContDiffOn.continuousLinearMap_comp
    exact h.1
  · -- Vanishing of Laplace
    intro z zHyp
    rw [laplace_compCLMAt]
    simp
    rw [h.2 z]
    simp
    assumption
    apply ContDiffOn.contDiffAt h.1
    exact IsOpen.mem_nhds hs zHyp


theorem harmonicAt_comp_CLM_is_harmonicAt
  {f : ℂ → F₁}
  {z : ℂ}
  {l : F₁ →L[ℝ] G}
  (h : HarmonicAt f z) :
  HarmonicAt (l ∘ f) z := by

  constructor
  · -- ContDiffAt ℝ 2 (⇑l ∘ f) z
    apply ContDiffAt.continuousLinearMap_comp
    exact h.1
  · -- Δ (⇑l ∘ f) =ᶠ[nhds z] 0
    obtain ⟨r, h₁r, h₂r⟩ := h.1.contDiffOn le_rfl (by trivial)
    obtain ⟨s, h₁s, h₂s, h₃s⟩ := mem_nhds_iff.1 h₁r
    obtain ⟨t, h₁t, h₂t⟩ := Filter.eventuallyEq_iff_exists_mem.1 h.2
    obtain ⟨u, h₁u, h₂u, h₃u⟩ := mem_nhds_iff.1 h₁t
    apply Filter.eventuallyEq_iff_exists_mem.2
    use s ∩ u
    constructor
    · apply IsOpen.mem_nhds
      exact IsOpen.inter h₂s h₂u
      constructor
      · exact h₃s
      · exact h₃u
    · intro x xHyp
      rw [laplace_compCLMAt]
      simp
      rw [h₂t]
      simp
      exact h₁u xHyp.2
      apply (h₂r.mono h₁s).contDiffAt (IsOpen.mem_nhds h₂s xHyp.1)


theorem harmonic_iff_comp_CLE_is_harmonic {f : ℂ → F₁} {l : F₁ ≃L[ℝ] G₁} :
  Harmonic f ↔ Harmonic (l ∘ f) := by

  constructor
  · have : l ∘ f = (l : F₁ →L[ℝ] G₁) ∘ f := by rfl
    rw [this]
    exact harmonic_comp_CLM_is_harmonic
  · have : f = (l.symm : G₁ →L[ℝ] F₁) ∘ l ∘ f := by
      funext z
      unfold Function.comp
      simp
    nth_rewrite 2 [this]
    exact harmonic_comp_CLM_is_harmonic


theorem harmonicAt_iff_comp_CLE_is_harmonicAt
  {f : ℂ → F₁}
  {z : ℂ}
  {l : F₁ ≃L[ℝ] G₁} :
  HarmonicAt f z ↔ HarmonicAt (l ∘ f) z := by

  constructor
  · have : l ∘ f = (l : F₁ →L[ℝ] G₁) ∘ f := by rfl
    rw [this]
    exact harmonicAt_comp_CLM_is_harmonicAt
  · have : f = (l.symm : G₁ →L[ℝ] F₁) ∘ l ∘ f := by
      funext z
      unfold Function.comp
      simp
    nth_rewrite 2 [this]
    exact harmonicAt_comp_CLM_is_harmonicAt


theorem harmonicOn_iff_comp_CLE_is_harmonicOn {f : ℂ → F₁} {s : Set ℂ} {l : F₁ ≃L[ℝ] G₁} (hs : IsOpen s) :
  HarmonicOn f s ↔ HarmonicOn (l ∘ f) s := by

  constructor
  · have : l ∘ f = (l : F₁ →L[ℝ] G₁) ∘ f := by rfl
    rw [this]
    exact harmonicOn_comp_CLM_is_harmonicOn hs
  · have : f = (l.symm : G₁ →L[ℝ] F₁) ∘ l ∘ f := by
      funext z
      unfold Function.comp
      simp
    nth_rewrite 2 [this]
    exact harmonicOn_comp_CLM_is_harmonicOn hs