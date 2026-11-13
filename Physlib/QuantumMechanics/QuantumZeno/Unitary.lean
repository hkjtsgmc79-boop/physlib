/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.QuantumZeno.CornerAlgebra

/-!
# Contractions from self-adjoint dynamics
Orthogonal projections and unitary propagators control operator norms.

## i. Overview
These bounds follow from the C-star norm identity, self-adjointness and the exponential of a
skew-adjoint generator.

## ii. Key results
projection_norm_le, flow_mem_unitary, norm_pulse_le_one, norm_effective_le_one.

## iii. Table of contents
- A. Definitions and results

## iv. References
* None.
-/
/-! ## A. Definitions and results -/

@[expose] public section

noncomputable section
namespace QuantumZenoDynamics
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
lemma projection_norm_le (P : A) (hP : P*P=P) (hs : star P=P) : ‖P‖ ≤ 1 := by
  have hc : ‖P‖ * ‖P‖ = ‖P‖ := by
    rw [← CStarRing.norm_star_mul_self, hs, hP]
  nlinarith [norm_nonneg P]

omit [Nontrivial A] in
lemma norm_mul_projection_le (x P : A) (hP : P*P=P) (hs : star P=P) :
    ‖x*P‖ ≤ ‖x‖ := by
  calc
    ‖x*P‖ ≤ ‖x‖*‖P‖ := norm_mul_le _ _
    _ ≤ ‖x‖*1 := mul_le_mul_of_nonneg_left (projection_norm_le P hP hs) (norm_nonneg x)
    _ = ‖x‖ := mul_one _

omit [Nontrivial A] in
lemma norm_projection_mul_le (P x : A) (hP : P*P=P) (hs : star P=P) :
    ‖P*x‖ ≤ ‖x‖ := by
  calc
    ‖P*x‖ ≤ ‖P‖*‖x‖ := norm_mul_le _ _
    _ ≤ 1*‖x‖ := mul_le_mul_of_nonneg_right (projection_norm_le P hP hs) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

omit [Nontrivial A] in
lemma norm_compress_le (P a : A) (hP : P*P=P) (hs : star P=P) :
    ‖compress P a‖ ≤ ‖a‖ :=
  (norm_mul_projection_le (P*a) P hP hs).trans (norm_projection_mul_le P a hP hs)

omit [Nontrivial A] in
lemma compress_skew (P a : A) (hs : star P=P) (ha : star a = -a) :
    star (compress P a) = -compress P a := by
  simp only [compress, star_mul, hs, ha]
  noncomm_ring

omit [Nontrivial A] in
lemma compress_selfAdjoint (P H : A) (hs : star P=P) (hH : star H=H) :
    star (compress P H) = compress P H := by
  simp [compress, star_mul, hs, hH, mul_assoc]

omit [Nontrivial A] in
lemma generator_skew (H : A) (hH : star H=H) (hbar : ℝ) :
    star (generator H hbar) = -generator H hbar := by
  simp [generator, star_smul, hH, neg_smul, neg_div]

omit [Nontrivial A] in
lemma flow_mem_unitary (a : A) (ha : star a = -a) (t : ℝ) :
    flow a t ∈ unitary A := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star ((t : ℂ) • a) = -((t : ℂ) • a)
  simp [star_smul, ha, smul_neg]

lemma norm_flow_eq_one (a : A) (ha : star a = -a) (t : ℝ) :
    ‖flow a t‖ = 1 :=
  CStarRing.norm_of_mem_unitary (flow_mem_unitary a ha t)

lemma norm_pulse_le_one (P a : A) (hP : P*P=P) (hs : star P=P)
    (ha : star a = -a) (t : ℝ) : ‖pulse P a t‖ ≤ 1 := by
  calc
    ‖pulse P a t‖ ≤ ‖flow a t‖ := norm_compress_le P (flow a t) hP hs
    _ = 1 := norm_flow_eq_one a ha t

lemma norm_effective_le_one (P a : A) (hP : P*P=P) (hs : star P=P)
    (ha : star a = -a) (t : ℝ) : ‖effective P a t‖ ≤ 1 := by
  calc
    ‖effective P a t‖ ≤ ‖flow (compress P a) t‖ :=
      norm_mul_projection_le _ P hP hs
    _ = 1 := norm_flow_eq_one _ (compress_skew P a hs ha) t

lemma norm_product_le_one (P a : A) (hP : P*P=P) (hs : star P=P)
    (ha : star a = -a) (t : ℝ) (n : ℕ) : ‖product P a t n‖ ≤ 1 := by
  calc
    ‖product P a t n‖ ≤ ‖pulse P a (t/n)‖^n := norm_pow_le _ _
    _ ≤ (1 : ℝ)^n := pow_le_pow_left₀ (norm_nonneg _) (norm_pulse_le_one P a hP hs ha _) n
    _ = 1 := one_pow _

omit [Nontrivial A] in
lemma star_flow (a : A) (ha : star a = -a) (t : ℝ) :
    star (flow a t) = flow a (-t) := by
  simp [flow, NormedSpace.star_exp, star_smul, ha, smul_neg, neg_smul]

end QuantumZenoDynamics
