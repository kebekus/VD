import Mathlib.Analysis.Complex.Basic
import VD.partialDeriv

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

noncomputable def Complex.laplace (f : ℂ → F) : ℂ → F :=
  partialDeriv ℝ 1 (partialDeriv ℝ 1 f) + partialDeriv ℝ Complex.I (partialDeriv ℝ Complex.I f)

notation "Δ" => Complex.laplace

variable {f₁ f₂ : ℂ → F} {x : ℂ}

theorem laplace_eventuallyEq (h : f₁ =ᶠ[nhds x] f₂) : Δ f₁ x = Δ f₂ x := by
  unfold Complex.laplace
  simp
  rw [partialDeriv_eventuallyEq ℝ (partialDeriv_eventuallyEq' ℝ h 1) 1]
  rw [partialDeriv_eventuallyEq ℝ (partialDeriv_eventuallyEq' ℝ h Complex.I) Complex.I]

theorem laplace_eventuallyEq' (h : f₁ =ᶠ[nhds x] f₂) : Δ f₁ =ᶠ[nhds x] Δ f₂ := by
  unfold Complex.laplace
  apply Filter.EventuallyEq.add
  exact partialDeriv_eventuallyEq' ℝ (partialDeriv_eventuallyEq' ℝ h 1) 1
  exact partialDeriv_eventuallyEq' ℝ (partialDeriv_eventuallyEq' ℝ h Complex.I) Complex.I

lemma ht {s : Set ℂ} (hs : IsOpen s) {x y : ℂ} (hy : y ∈ s) (f : ℂ → F) (hf: ContDiffOn ℝ 2 f s) :
      DifferentiableAt ℝ (partialDeriv ℝ x f) y := by
  apply ContDiffAt.differentiableAt
  · exact (partialDeriv_contDiffAt _ ((hf _ hy).contDiffAt (hs.mem_nhds hy)) x)
  · apply le_refl

lemma contdiffon_contdiffat {s : Set ℂ} (hs : IsOpen s) (f : ℂ → F)
    (h : ContDiffOn ℝ 2 f s) (hx : x ∈ s) : DifferentiableAt ℝ f x :=
  (h.differentiableOn one_le_two).differentiableAt (hs.mem_nhds hx)

lemma partialDeriv_add_eventually_equal (y : ℂ) {s : Set ℂ} (hs : IsOpen s) (hx : x ∈ s)
    (h₁ : ContDiffOn ℝ 2 f₁ s) (h₂ : ContDiffOn ℝ 2 f₂ s)  :
    partialDeriv ℝ y (f₁ + f₂) =ᶠ[nhds x] (partialDeriv ℝ y f₁) + (partialDeriv ℝ y f₂) := by
  apply Filter.eventuallyEq_iff_exists_mem.2
  use s, hs.mem_nhds hx
  intro z hz
  apply partialDeriv_add₂_differentiableAt
  apply contdiffon_contdiffat hs _ h₁ hz
  exact contdiffon_contdiffat hs _ h₂ hz

theorem laplace_add_ContDiffOn {s : Set ℂ} (hs : IsOpen s)
    (h₁ : ContDiffOn ℝ 2 f₁ s) (h₂ : ContDiffOn ℝ 2 f₂ s) (hx : x ∈ s) :
  Δ (f₁ + f₂) x = (Δ f₁) x + (Δ f₂) x := by
  have hf₃ : partialDeriv ℝ 1 (f₁ + f₂) =ᶠ[nhds x] (partialDeriv ℝ 1 f₁) + (partialDeriv ℝ 1 f₂) := by
    apply partialDeriv_add_eventually_equal 1 hs hx h₁ h₂
  have hf₄ : partialDeriv ℝ Complex.I (f₁ + f₂) =ᶠ[nhds x] (partialDeriv ℝ Complex.I f₁) + (partialDeriv ℝ Complex.I f₂) := by
    apply partialDeriv_add_eventually_equal Complex.I hs hx h₁ h₂
  unfold Complex.laplace
  simp
  rw [partialDeriv_eventuallyEq ℝ hf₃]
  rw [partialDeriv_add₂_differentiableAt ℝ (ht hs hx f₁ h₁) (ht hs hx f₂ h₂)]
  rw [partialDeriv_eventuallyEq ℝ hf₄]
  rw [partialDeriv_add₂_differentiableAt ℝ (ht hs hx f₁ h₁) (ht hs hx f₂ h₂)]
  abel
  -- I am super confused at this point because the tactic 'ring' does not work.
  -- I do not understand why. So, I need to do things by hand.

lemma contdiff_all {f : ℂ → F} (h : ContDiff ℝ 2 f) : ContDiffOn ℝ (E := ℂ) 2 f Set.univ :=
  h.contDiffOn

theorem laplace_add (h₁ : ContDiff ℝ 2 f₁) (h₂ : ContDiff ℝ 2 f₂) :
    Δ (f₁ + f₂) = (Δ f₁) + (Δ f₂) := by
  ext x
  apply laplace_add_ContDiffOn (s := Set.univ) _ (h₁.contDiffOn) (h₂.contDiffOn) _ <;> simp

example {f : ℂ → F} {x : ℂ} (h : ContDiffAt ℝ 2 f x) : ∃ u ∈ nhds x, ContDiffOn ℝ 2 f u := by
  apply ContDiffAt.contDiffOn h (le_refl 2)
  simp

theorem laplace_add_ContDiffAt (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) x = (Δ f₁) x + (Δ f₂) x := by
  unfold Complex.laplace
  simp
  have h₁₁ : ContDiffAt ℝ 1 f₁ x := h₁.of_le one_le_two
  have h₂₁ : ContDiffAt ℝ 1 f₂ x := h₂.of_le one_le_two
  repeat
    rw [partialDeriv_eventuallyEq ℝ (partialDeriv_add₂_contDiffAt ℝ h₁₁ h₂₁)]
    rw [partialDeriv_add₂_differentiableAt]
  abel
  -- I am super confused at this point because the tactic 'ring' does not work.
  -- I do not understand why. So, I need to do things by hand.
  repeat
    apply fun v ↦ (partialDeriv_contDiffAt ℝ h₁ v).differentiableAt le_rfl
    apply fun v ↦ (partialDeriv_contDiffAt ℝ h₂ v).differentiableAt le_rfl

theorem laplace_add_ContDiffAt' (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
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
  simp [partialDeriv_smul₂]

theorem laplace_compCLMAt {f : ℂ → F} {l : F →L[ℝ] G} {x : ℂ} (h : ContDiffAt ℝ 2 f x) :
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

theorem laplace_compCLM {f : ℂ → F} {l : F →L[ℝ] G} (h : ContDiff ℝ 2 f) :
    Δ (l ∘ f) = l ∘ (Δ f) := by
  funext z
  exact laplace_compCLMAt h.contDiffAt

theorem laplace_compCLE {f : ℂ → F} {l : F ≃L[ℝ] G} :
  Δ (l ∘ f) = l ∘ (Δ f) := by
  unfold Complex.laplace
  simp [partialDeriv_compCLE]
