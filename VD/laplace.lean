import Mathlib.Analysis.Complex.Basic
import VD.partialDeriv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]


noncomputable def Complex.laplace (f : ℂ → F) : ℂ → F :=
  partialDeriv ℝ 1 (partialDeriv ℝ 1 f) + partialDeriv ℝ Complex.I (partialDeriv ℝ Complex.I f)

notation "Δ" => Complex.laplace


theorem laplace_eventuallyEq {f₁ f₂ : ℂ → F} {x : ℂ} (h : f₁ =ᶠ[nhds x] f₂) : Δ f₁ x = Δ f₂ x := by
  unfold Complex.laplace
  simp
  rw [partialDeriv_eventuallyEq ℝ (partialDeriv_eventuallyEq' ℝ h 1) 1]
  rw [partialDeriv_eventuallyEq ℝ (partialDeriv_eventuallyEq' ℝ h Complex.I) Complex.I]


theorem laplace_eventuallyEq' {f₁ f₂ : ℂ → F} {x : ℂ} (h : f₁ =ᶠ[nhds x] f₂) : Δ f₁ =ᶠ[nhds x] Δ f₂ := by
  unfold Complex.laplace
  apply Filter.EventuallyEq.add
  exact partialDeriv_eventuallyEq' ℝ (partialDeriv_eventuallyEq' ℝ h 1) 1
  exact partialDeriv_eventuallyEq' ℝ (partialDeriv_eventuallyEq' ℝ h Complex.I) Complex.I


theorem laplace_add
  {f₁ f₂ : ℂ → F}
  (h₁ : ContDiff ℝ 2 f₁)
  (h₂ : ContDiff ℝ 2 f₂) :
  Δ (f₁ + f₂) = (Δ f₁) + (Δ f₂) := by

  unfold Complex.laplace
  rw [partialDeriv_add₂]
  rw [partialDeriv_add₂]
  rw [partialDeriv_add₂]
  rw [partialDeriv_add₂]
  exact
    add_add_add_comm (partialDeriv ℝ 1 (partialDeriv ℝ 1 f₁))
      (partialDeriv ℝ 1 (partialDeriv ℝ 1 f₂))
      (partialDeriv ℝ Complex.I (partialDeriv ℝ Complex.I f₁))
      (partialDeriv ℝ Complex.I (partialDeriv ℝ Complex.I f₂))

  exact (partialDeriv_contDiff ℝ h₁ Complex.I).differentiable le_rfl
  exact (partialDeriv_contDiff ℝ h₂ Complex.I).differentiable le_rfl
  exact h₁.differentiable one_le_two
  exact h₂.differentiable one_le_two
  exact (partialDeriv_contDiff ℝ h₁ 1).differentiable le_rfl
  exact (partialDeriv_contDiff ℝ h₂ 1).differentiable le_rfl
  exact h₁.differentiable one_le_two
  exact h₂.differentiable one_le_two


theorem laplace_add_ContDiffOn
  {f₁ f₂ : ℂ → F}
  {s : Set ℂ}
  (hs : IsOpen s)
  (h₁ : ContDiffOn ℝ 2 f₁ s)
  (h₂ : ContDiffOn ℝ 2 f₂ s) :
  ∀ x ∈ s, Δ (f₁ + f₂) x = (Δ f₁) x + (Δ f₂) x := by

  unfold Complex.laplace
  simp
  intro x hx

  have hf₁ : ∀ z ∈ s, DifferentiableAt ℝ f₁ z := by
    intro z hz
    exact (h₁.differentiableOn one_le_two).differentiableAt (hs.mem_nhds hz)
  have hf₂ : ∀ z ∈ s, DifferentiableAt ℝ f₂ z := by
    intro z hz
    exact (h₂.differentiableOn one_le_two).differentiableAt (hs.mem_nhds hz)
  have : partialDeriv ℝ 1 (f₁ + f₂) =ᶠ[nhds x] (partialDeriv ℝ 1 f₁) + (partialDeriv ℝ 1 f₂) := by
    apply Filter.eventuallyEq_iff_exists_mem.2
    use s, hs.mem_nhds hx
    intro z hz
    apply partialDeriv_add₂_differentiableAt
    exact hf₁ z hz
    exact hf₂ z hz
  rw [partialDeriv_eventuallyEq ℝ this]
  have t₁ : DifferentiableAt ℝ (partialDeriv ℝ 1 f₁) x := by
    let B₀ := (h₁ x hx).contDiffAt (IsOpen.mem_nhds hs hx)
    let A₀ := partialDeriv_contDiffAt ℝ B₀ 1
    apply A₀.differentiableAt (Preorder.le_refl 1)
  have t₂ : DifferentiableAt ℝ (partialDeriv ℝ 1 f₂) x := by
    let B₀ := (h₂ x hx).contDiffAt (IsOpen.mem_nhds hs hx)
    let A₀ := partialDeriv_contDiffAt ℝ B₀ 1
    exact A₀.differentiableAt (Preorder.le_refl 1)
  rw [partialDeriv_add₂_differentiableAt ℝ t₁ t₂]

  have : partialDeriv ℝ Complex.I (f₁ + f₂) =ᶠ[nhds x] (partialDeriv ℝ Complex.I f₁) + (partialDeriv ℝ Complex.I f₂) := by
    apply Filter.eventuallyEq_iff_exists_mem.2
    use s, hs.mem_nhds hx
    intro z hz
    apply partialDeriv_add₂_differentiableAt
    exact hf₁ z hz
    exact hf₂ z hz
  rw [partialDeriv_eventuallyEq ℝ this]
  have t₃ : DifferentiableAt ℝ (partialDeriv ℝ Complex.I f₁) x := by
    let B₀ := (h₁ x hx).contDiffAt (hs.mem_nhds hx)
    let A₀ := partialDeriv_contDiffAt ℝ B₀ Complex.I
    exact A₀.differentiableAt (le_refl 1)
  have t₄ : DifferentiableAt ℝ (partialDeriv ℝ Complex.I f₂) x := by
    let B₀ := (h₂ x hx).contDiffAt (hs.mem_nhds hx)
    let A₀ := partialDeriv_contDiffAt ℝ B₀ Complex.I
    exact A₀.differentiableAt (le_refl 1)
  rw [partialDeriv_add₂_differentiableAt ℝ t₃ t₄]

  -- I am super confused at this point because the tactic 'ring' does not work.
  -- I do not understand why. So, I need to do things by hand.
  rw [add_assoc]
  rw [add_assoc]
  rw [add_right_inj (partialDeriv ℝ 1 (partialDeriv ℝ 1 f₁) x)]
  rw [add_comm]
  rw [add_assoc]
  rw [add_right_inj (partialDeriv ℝ Complex.I (partialDeriv ℝ Complex.I f₁) x)]
  rw [add_comm]


theorem laplace_add_ContDiffAt
  {f₁ f₂ : ℂ → F}
  {x : ℂ}
  (h₁ : ContDiffAt ℝ 2 f₁ x)
  (h₂ : ContDiffAt ℝ 2 f₂ x) :
  Δ (f₁ + f₂) x = (Δ f₁) x + (Δ f₂) x := by

  unfold Complex.laplace
  simp

  have h₁₁ : ContDiffAt ℝ 1 f₁ x := h₁.of_le one_le_two
  have h₂₁ : ContDiffAt ℝ 1 f₂ x := h₂.of_le one_le_two
  repeat
    rw [partialDeriv_eventuallyEq ℝ (partialDeriv_add₂_contDiffAt ℝ h₁₁ h₂₁)]
    rw [partialDeriv_add₂_differentiableAt]

  -- I am super confused at this point because the tactic 'ring' does not work.
  -- I do not understand why. So, I need to do things by hand.
  rw [add_assoc]
  rw [add_assoc]
  rw [add_right_inj (partialDeriv ℝ 1 (partialDeriv ℝ 1 f₁) x)]
  rw [add_comm]
  rw [add_assoc]
  rw [add_right_inj (partialDeriv ℝ Complex.I (partialDeriv ℝ Complex.I f₁) x)]
  rw [add_comm]

  repeat
    apply fun v ↦ (partialDeriv_contDiffAt ℝ h₁ v).differentiableAt le_rfl
    apply fun v ↦ (partialDeriv_contDiffAt ℝ h₂ v).differentiableAt le_rfl


theorem laplace_add_ContDiffAt'
  {f₁ f₂ : ℂ → F}
  {x : ℂ}
  (h₁ : ContDiffAt ℝ 2 f₁ x)
  (h₂ : ContDiffAt ℝ 2 f₂ x) :
  Δ (f₁ + f₂) =ᶠ[nhds x] (Δ f₁) + (Δ f₂):= by

  unfold Complex.laplace

  rw [add_assoc]
  nth_rw 5 [add_comm]
  rw [add_assoc]
  rw [← add_assoc]

  have dualPDeriv : ∀ v : ℂ, partialDeriv ℝ v (partialDeriv ℝ v (f₁ + f₂)) =ᶠ[nhds x]
    partialDeriv ℝ v (partialDeriv ℝ v f₁) + partialDeriv ℝ v (partialDeriv ℝ v f₂) := by

    intro v
    have h₁₁ : ContDiffAt ℝ 1 f₁ x := h₁.of_le one_le_two
    have h₂₁ : ContDiffAt ℝ 1 f₂ x := h₂.of_le one_le_two

    have t₁ : partialDeriv ℝ v (partialDeriv ℝ v (f₁ + f₂)) =ᶠ[nhds x] partialDeriv ℝ v (partialDeriv ℝ v f₁ + partialDeriv ℝ v f₂) := by
      exact partialDeriv_eventuallyEq' ℝ (partialDeriv_add₂_contDiffAt ℝ h₁₁ h₂₁) v

    have t₂ : partialDeriv ℝ v (partialDeriv ℝ v f₁ + partialDeriv ℝ v f₂) =ᶠ[nhds x] (partialDeriv ℝ v (partialDeriv ℝ v f₁)) + (partialDeriv ℝ v (partialDeriv ℝ v f₂)) := by
      apply partialDeriv_add₂_contDiffAt ℝ
      apply partialDeriv_contDiffAt
      exact h₁
      apply partialDeriv_contDiffAt
      exact h₂

    apply Filter.EventuallyEq.trans t₁ t₂

  have eventuallyEq_add
    {a₁ a₂ b₁ b₂ : ℂ → F}
    (h : a₁ =ᶠ[nhds x] b₁)
    (h' : a₂ =ᶠ[nhds x] b₂) : (a₁ + a₂) =ᶠ[nhds x] (b₁ + b₂) := by
    have {c₁ c₂ : ℂ → F} : (fun x => c₁ x + c₂ x) = c₁ + c₂ := by rfl
    rw [← this, ← this]
    exact Filter.EventuallyEq.add h h'
  apply eventuallyEq_add
  · exact dualPDeriv 1
  · nth_rw 2 [add_comm]
    exact dualPDeriv Complex.I


theorem laplace_smul {f : ℂ → F} : ∀ v : ℝ, Δ (v • f) = v • (Δ f) := by
  intro v
  unfold Complex.laplace
  repeat
    rw [partialDeriv_smul₂]
  simp


theorem laplace_compCLMAt
  {f : ℂ → F}
  {l : F →L[ℝ] G}
  {x : ℂ}
  (h : ContDiffAt ℝ 2 f x) :
  Δ (l ∘ f) x = (l ∘ (Δ f)) x := by

  obtain ⟨v, hv₁, hv₂, hv₃, hv₄⟩ : ∃ v ∈ nhds x, (IsOpen v) ∧ (x ∈ v) ∧ (ContDiffOn ℝ 2 f v) := by
    obtain ⟨u, hu₁, hu₂⟩ : ∃ u ∈ nhds x, ContDiffOn ℝ 2 f u := by
      apply ContDiffAt.contDiffOn h
      rfl
      simp
    obtain ⟨v, hv₁, hv₂, hv₃⟩ := mem_nhds_iff.1 hu₁
    use v, hv₂.mem_nhds hv₃, hv₂, hv₃
    exact hu₂.congr_mono (fun x => congrFun rfl) hv₁

  have D (w : ℂ) : partialDeriv ℝ w (l ∘ f) =ᶠ[nhds x] l ∘ partialDeriv ℝ w (f) := by
    apply Filter.eventuallyEq_iff_exists_mem.2
    use v, hv₂.mem_nhds hv₃
    intro y hy
    apply partialDeriv_compContLinAt
    apply (hv₄.differentiableOn one_le_two).differentiableAt (hv₂.mem_nhds hy)

  unfold Complex.laplace
  simp

  rw [partialDeriv_eventuallyEq ℝ (D 1) 1]
  rw [partialDeriv_compContLinAt]
  rw [partialDeriv_eventuallyEq ℝ (D Complex.I) Complex.I]
  rw [partialDeriv_compContLinAt]
  simp

  -- DifferentiableAt ℝ (partialDeriv ℝ Complex.I f) x
  apply ContDiffAt.differentiableAt (partialDeriv_contDiffAt ℝ (ContDiffOn.contDiffAt hv₄ hv₁) Complex.I) le_rfl

  -- DifferentiableAt ℝ (partialDeriv ℝ 1 f) x
  apply ContDiffAt.differentiableAt (partialDeriv_contDiffAt ℝ (ContDiffOn.contDiffAt hv₄ hv₁) 1) le_rfl


theorem laplace_compCLM
  {f : ℂ → F}
  {l : F →L[ℝ] G}
  (h : ContDiff ℝ 2 f) :
  Δ (l ∘ f) = l ∘ (Δ f) := by
  funext z
  exact laplace_compCLMAt h.contDiffAt


theorem laplace_compCLE {f : ℂ → F} {l : F ≃L[ℝ] G} :
  Δ (l ∘ f) = l ∘ (Δ f) := by
  unfold Complex.laplace
  repeat
    rw [partialDeriv_compCLE]
  simp
