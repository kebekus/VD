import VD.divisor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Metric Real

variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {U : Set 𝕜}

noncomputable def Divisor.counting (D : Divisor (⊤ : Set 𝕜)) :
    ℝ → ℝ :=
  fun r ↦ ∑ᶠ z, D.restrict (by tauto : closedBall (0 : 𝕜) |r| ⊆ ⊤) z

noncomputable def Divisor.logCounting (D : Divisor (⊤ : Set 𝕜)) :
    ℝ → ℝ :=
  fun r ↦ ∑ᶠ z, D.restrict (by tauto : closedBall (0 : 𝕜) |r| ⊆ ⊤) z * (log r - log ‖z‖)
