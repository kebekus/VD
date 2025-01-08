/-
Copyright (c) 2024 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!

# Canoncial Elements in Tensor Powers of Real Inner Product Spaces

Given an `InnerProductSpace ℝ E`, this file defines two canonical tensors, which
are relevant when for a coordinate-free definition of differential operators
such as the Laplacian.

* `InnerProductSpace.canonicalContravariantTensor E : E ⊗[ℝ] E →ₗ[ℝ] ℝ`. This is
  the element corresponding to the inner product.

* If `E` is finite-dimensional, then `E ⊗[ℝ] E` is canonically isomorphic to its
  dual. Accordingly, there exists an element
  `InnerProductSpace.canonicalCovariantTensor E : E ⊗[ℝ] E` that corresponds to
  `InnerProductSpace.canonicalContravariantTensor E` under this identification.

The theorem `InnerProductSpace.canonicalCovariantTensorRepresentation` shows
that `InnerProductSpace.canonicalCovariantTensor E` can be computed from any
orthonormal basis `v` as `∑ i, (v i) ⊗ₜ[ℝ] (v i)`.

-/

open InnerProductSpace
open TensorProduct


noncomputable def InnerProductSpace.canonicalContravariantTensor
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  : E ⊗[ℝ] E →ₗ[ℝ] ℝ := TensorProduct.lift bilinFormOfRealInner


noncomputable def InnerProductSpace.canonicalCovariantTensor
  (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  : E ⊗[ℝ] E := ∑ i, ((stdOrthonormalBasis ℝ E) i) ⊗ₜ[ℝ] ((stdOrthonormalBasis ℝ E) i)

theorem InnerProductSpace.canonicalCovariantTensorRepresentation
  (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]
  (v : OrthonormalBasis ι ℝ E) :
  InnerProductSpace.canonicalCovariantTensor E = ∑ i, (v i) ⊗ₜ[ℝ] (v i) := by

  let w := stdOrthonormalBasis ℝ E
  conv =>
    right
    arg 2
    intro i
    rw [← w.sum_repr' (v i)]
  simp_rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul_smul]

  conv =>
    right
    rw [Finset.sum_comm]
    arg 2
    intro y
    rw [Finset.sum_comm]
    arg 2
    intro x
    rw [← Finset.sum_smul]
    arg 1
    arg 2
    intro i
    rw [← real_inner_comm (w x)]
  simp_rw [OrthonormalBasis.sum_inner_mul_inner v]

  have {i} : ∑ j, ⟪w i, w j⟫_ℝ • w i ⊗ₜ[ℝ] w j = w i ⊗ₜ[ℝ] w i := by
    rw [Fintype.sum_eq_single i, orthonormal_iff_ite.1 w.orthonormal]; simp
    intro _ _; rw [orthonormal_iff_ite.1 w.orthonormal]; simp; tauto
  simp_rw [this]
  rfl
