/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Quantum Zeno model
Bounded Hamiltonians, projections and repeated selective measurements.

## i. Overview
The input consists only of a Hamiltonian, an orthogonal projection and physical parameters. The
actual Banach-algebra exponential defines the dynamics.

## ii. Key results
compress, flow, pulse, product, effective, generator, rateConstant, errorBudget.

## iii. Table of contents
- A. Definitions and results

## iv. References
* None.
-/
/-! ## A. Definitions and results -/

@[expose] public section

noncomputable section
open scoped Topology
namespace QuantumZenoDynamics

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Algebraic compression, without assuming P and a commute. -/
def compress (P a : A) : A := P * a * P

/-- Actual exponential flow of a bounded generator. -/
def flow (a : A) (t : ℝ) : A := NormedSpace.exp ((t : ℂ) • a)

/-- One ideal selective-measurement step, retaining its unnormalized amplitude. -/
def pulse (P a : A) (t : ℝ) : A := P * flow a t * P

/-- n pulses over total time t; n=0 is the algebraic empty product 1.
All finite-n physics bounds below require n>0. -/
def product (P a : A) (t : ℝ) (n : ℕ) : A := (pulse P a (t / n)) ^ n

/-- Effective evolution is zero on the complement of the measured subspace.
The final P is essential: the ambient exponential alone is not the limit. -/
def effective (P a : A) (t : ℝ) : A := flow (compress P a) t * P

/-- Physical generator -i H / hbar. -/
def generator (H : A) (hbar : ℝ) : A := (-Complex.I / (hbar : ℂ)) • H

/-- A dimension-independent but deliberately non-sharp convergence constant. -/
def rateConstant (R M : ℝ) : ℝ := 2 * (R * M)^2 * Real.exp (R * M)

/-- Finite-step operator-norm error budget; physical estimates use a positive step count. -/
def errorBudget (R M : ℝ) (n : ℕ) : ℝ := rateConstant R M / n

lemma rateConstant_nonneg (R M : ℝ) : 0 ≤ rateConstant R M := by
  unfold rateConstant
  positivity

lemma errorBudget_nonneg (R M : ℝ) (n : ℕ) : 0 ≤ errorBudget R M n := by
  exact div_nonneg (rateConstant_nonneg R M) (Nat.cast_nonneg n)

omit [CompleteSpace A] in
@[simp] lemma flow_zero (a : A) : flow a 0 = 1 := by
  simp [flow]

omit [CompleteSpace A] in
@[simp] lemma generator_zero (hbar : ℝ) : generator (0 : A) hbar = 0 := by
  simp [generator]

omit [CompleteSpace A] in
lemma norm_generator (H : A) {hbar : ℝ} (hh : 0 < hbar) :
    ‖generator H hbar‖ = ‖H‖ / hbar := by
  simp only [generator, norm_smul, norm_div, norm_neg, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  ring

omit [CompleteSpace A] in
lemma norm_time_smul (a : A) (t : ℝ) : ‖(t : ℂ) • a‖ = |t| * ‖a‖ := by
  simp [norm_smul]

omit [CompleteSpace A] in
lemma time_smul_compress (P a : A) (t : ℝ) :
    (t : ℂ) • compress P a = P * ((t : ℂ) • a) * P := by
  simp [compress]

end QuantumZenoDynamics
