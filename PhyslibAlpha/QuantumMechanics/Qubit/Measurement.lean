/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.Qubit.Basic
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.OrthonormalMeasurement

/-!
# Computational-basis measurement of a qubit

A measurement on a qubit with outcomes indexed by its computational basis.

## i. Overview

The outcomes index the standard orthonormal basis `QuantumMechanics.Qubit.basis` of the
qubit's Hilbert space. On a normalized state vector, each outcome has probability equal to
the squared norm of the corresponding coordinate. The basis spans the whole space, so the
remainder in the orthonormal-family measurement vanishes.

## ii. Key results

- `computationalBasisMeasurement` measures a qubit in the standard basis.
- `expectation_computationalBasisMeasurement_singleton` gives each outcome probability.

## iii. Table of contents

- A. Computational-basis measurement

## iv. References

- See the qubit API map in `Physlib/QuantumMechanics/Qubit/API-map.md`.

## A. Computational-basis measurement
-/

@[expose] public noncomputable section

namespace PhyslibAlpha.Qubit

open PhyslibAlpha.ProbabilisticTheory UnitalPositiveLinearMap
open scoped InnerProductSpace

/-- The computational-basis measurement with outcomes `0` and `1`. -/
def computationalBasisMeasurement :
    Measurement (Fin 2) (Observable (QuantumMechanics.Qubit →L[ℂ] QuantumMechanics.Qubit)) :=
  Measurement.ofOrthonormal QuantumMechanics.Qubit.basis.orthonormal 0

private lemma inner_basis_eq_coordinate (ψ : QuantumMechanics.Qubit) (i : Fin 2) :
    ⟪QuantumMechanics.Qubit.basis i, ψ⟫_ℂ = ψ.val i := by
  rw [QuantumMechanics.Qubit.basis_apply, QuantumMechanics.FiniteHilbertSpace.inner_eq_val,
    ← EuclideanSpace.basisFun_apply]
  simp only [EuclideanSpace.basisFun_inner]

/-- In a pure state, the probability of outcome `i` is the squared norm of its amplitude. -/
lemma expectation_computationalBasisMeasurement_singleton (ψ : QuantumMechanics.Qubit)
    (hψ : ‖ψ‖ = 1) (i : Fin 2) :
    (ofVec hψ)⟨computationalBasisMeasurement {i}
      (measurableSet_singleton i)⟩ = ‖ψ.val i‖ ^ 2 := by
  rw [computationalBasisMeasurement, Measurement.expectation_ofOrthonormal_singleton]
  rw [QuantumMechanics.Qubit.basis.sum_sq_norm_inner_right, hψ, inner_basis_eq_coordinate]
  simp

end PhyslibAlpha.Qubit
