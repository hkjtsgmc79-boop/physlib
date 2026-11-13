/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.QuantumZeno.Basic

/-!
# Products of contractions
A telescoping estimate accumulates noncommutative step errors.

## i. Overview
The bound does not assume the two operators commute.

## ii. Key results
The power-difference estimate.

## iii. Table of contents
- A. Definitions and results

## iv. References
* None.
-/
/-! ## A. Definitions and results -/

@[expose] public section

noncomputable section
namespace QuantumZenoDynamics
variable {A : Type*} [NormedRing A] [NormOneClass A]

lemma power_norm_le_one (x : A) (hx : ‖x‖ ≤ 1) (n : ℕ) : ‖x^n‖ ≤ 1 := by
  calc
    ‖x^n‖ ≤ ‖x‖^n := norm_pow_le _ _
    _ ≤ (1 : ℝ)^n := pow_le_pow_left₀ (norm_nonneg x) hx n
    _ = 1 := one_pow _

omit [NormOneClass A] in
lemma product_difference (x y z w : A) :
    x*z-y*w = x*(z-w)+(x-y)*w := by noncomm_ring

omit [NormOneClass A] in
lemma contraction_product_difference (x y z w : A)
    (hx : ‖x‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖x*z-y*w‖ ≤ ‖z-w‖ + ‖x-y‖ := by
  rw [product_difference]
  calc
    ‖x*(z-w)+(x-y)*w‖ ≤ ‖x*(z-w)‖ + ‖(x-y)*w‖ := norm_add_le _ _
    _ ≤ ‖x‖*‖z-w‖ + ‖x-y‖*‖w‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 1*‖z-w‖ + ‖x-y‖*1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
    _ = ‖z-w‖ + ‖x-y‖ := by ring

lemma contraction_power_difference (x y : A) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) :
    ‖x^n-y^n‖ ≤ (n : ℝ)*‖x-y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ']
    calc
      ‖x*x^n-y*y^n‖ ≤ ‖x^n-y^n‖ + ‖x-y‖ :=
        contraction_product_difference x y (x^n) (y^n) hx (power_norm_le_one y hy n)
      _ ≤ (n : ℝ)*‖x-y‖ + ‖x-y‖ := add_le_add_left ih _
      _ = ((n+1 : ℕ) : ℝ)*‖x-y‖ := by push_cast; ring

end QuantumZenoDynamics
