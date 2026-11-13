/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.QuantumZeno.Unitary
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Effective projected dynamics
Schrodinger evolution within the measured subspace.

## i. Overview
The effective operator is a partial unitary on the ambient space. Its derivative is a genuine
derivative of the Banach-algebra exponential.

## ii. Key results
effective_derivative, effective_schrodinger, effective_star_mul, effective_mul_star.

## iii. Table of contents
- A. Definitions and results

## iv. References
* None.
-/
/-! ## A. Definitions and results -/

@[expose] public section

noncomputable section
namespace QuantumZenoDynamics
variable {A : Type*} [CStarAlgebra A]

lemma generator_compress (P H : A) (hbar : ℝ) :
    compress P (generator H hbar) = generator (compress P H) hbar := by
  simp [compress, generator]

lemma flow_derivative (a : A) (t : ℝ) :
    HasDerivAt (flow a) (a * flow a t) t := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℂ) a (t : ℂ)).hasFDerivAt
  have hr := (h.restrictScalars ℝ).comp t Complex.ofRealCLM.hasFDerivAt
  have hd := hr.hasDerivAt
  change HasDerivAt (flow a) ((1 : ℂ) • (a * flow a t)) t at hd
  rw [one_smul] at hd
  exact hd

lemma effective_derivative (P a : A) (t : ℝ) :
    HasDerivAt (effective P a) (compress P a * effective P a t) t := by
  let rightMul := (ContinuousLinearMap.mul ℂ A).flip P
  have h := ((rightMul.restrictScalars ℝ).hasFDerivAt).comp t
    (flow_derivative (compress P a) t).hasFDerivAt
  change HasDerivAt (fun s => flow (compress P a) s * P)
    (compress P a * (flow (compress P a) t * P)) t
  simpa [rightMul, Function.comp_def, mul_assoc] using h.hasDerivAt

lemma effective_deriv_eq (P a : A) (t : ℝ) :
    deriv (effective P a) t = compress P a * effective P a t :=
  (effective_derivative P a t).deriv

lemma effective_schrodinger (P H : A) (hbar : ℝ) (t : ℝ) :
    HasDerivAt (effective P (generator H hbar))
      ((-Complex.I / (hbar : ℂ)) •
        (compress P H * effective P (generator H hbar) t)) t := by
  have h := effective_derivative P (generator H hbar) t
  rw [generator_compress] at h
  simpa only [generator, smul_mul_assoc] using h

lemma effective_star (P a : A) (hP : P*P=P) (hs : star P=P)
    (ha : star a = -a) (t : ℝ) :
    star (effective P a t) = effective P a (-t) := by
  unfold effective
  rw [star_mul, hs, star_flow _ (compress_skew P a hs ha) t]
  exact (commute_flow_compress P a hP (-t)).eq

lemma effective_star_mul (P a : A) (hP : P*P=P) (hs : star P=P)
    (ha : star a = -a) (t : ℝ) :
    star (effective P a t) * effective P a t = P := by
  rw [effective_star P a hP hs ha t, ← effective_add P a hP]
  simp

lemma effective_mul_star (P a : A) (hP : P*P=P) (hs : star P=P)
    (ha : star a = -a) (t : ℝ) :
    effective P a t * star (effective P a t) = P := by
  rw [effective_star P a hP hs ha t, ← effective_add P a hP]
  simp

lemma flow_physical_formula (H : A) (hbar t : ℝ) :
    flow (generator H hbar) t =
      NormedSpace.exp ((-Complex.I * (t : ℂ) / (hbar : ℂ)) • H) := by
  unfold flow generator
  rw [smul_smul]
  congr 2
  ring

lemma effective_physical_formula (P H : A) (hbar t : ℝ) :
    effective P (generator H hbar) t =
      NormedSpace.exp ((-Complex.I * (t : ℂ) / (hbar : ℂ)) • (P*H*P)) * P := by
  unfold effective
  rw [generator_compress, flow_physical_formula]
  rfl

end QuantumZenoDynamics
