/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# A rank-two noncommuting example
Three levels demonstrate internal dynamics after projection.

## i. Overview
This module contains exact matrix identities only. It does not use a matrix default norm to
stand in for the Hilbert operator norm.

## ii. Key results
noncommuting, compressed_matrix, projected_square_not_compressed_square.

## iii. Table of contents
- A. Definitions and results

## iv. References
* None.
-/
/-! ## A. Definitions and results -/

@[expose] public section

noncomputable section
namespace QuantumZenoDynamics.Witness
open Matrix

/-- A self-adjoint three-level Hamiltonian coupling kept and discarded levels. -/
def H : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0,1,1; 1,0,0; 1,0,2]
/-- The rank-two orthogonal projection onto the first two coordinate levels. -/
def P : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,0,0; 0,1,0; 0,0,0]
/-- The compressed Hamiltonian, with nontrivial dynamics in the retained plane. -/
def K : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0,1,0; 1,0,0; 0,0,0]

lemma projection_idempotent : P*P=P := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P, Matrix.mul_apply, Fin.sum_univ_succ]

lemma projection_selfAdjoint : P.conjTranspose=P := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P, Matrix.conjTranspose_apply]

lemma hamiltonian_selfAdjoint : H.conjTranspose=H := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [H, Matrix.conjTranspose_apply]

lemma compressed_matrix : P*H*P=K := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P,H,K,Matrix.mul_apply,Fin.sum_univ_succ]

lemma noncommuting : P*H ≠ H*P := by
  intro heq
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 2) heq
  norm_num [P,H,Matrix.mul_apply,Fin.sum_univ_succ] at h

lemma compression_nonzero : P*H*P ≠ 0 := by
  rw [compressed_matrix]
  intro heq
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 1) heq
  norm_num [K] at h

/-- Projection and squaring cannot be interchanged: the missing term is the
coupling through the discarded level. This guards against a false proof. -/
lemma projected_square_not_compressed_square : P*(H*H)*P ≠ (P*H*P)*(P*H*P) := by
  intro heq
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) heq
  norm_num [P,H,Matrix.mul_apply,Fin.sum_univ_succ] at h

end QuantumZenoDynamics.Witness
