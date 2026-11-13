/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.QuantumZeno.Unitary
public import Physlib.QuantumMechanics.QuantumZeno.Taylor

/-!
# One-step Zeno approximation
The compressed true propagator and effective propagator agree to first order.

## i. Overview
The remainder identity and quadratic estimates control one measurement step without a
commutation hypothesis.

## ii. Key results
The local error estimate.

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

lemma quadratic_exp_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x^2 * Real.exp x ≤ y^2 * Real.exp y := by
  apply mul_le_mul
  · nlinarith
  · exact Real.exp_le_exp.mpr hxy
  · exact Real.exp_pos x |>.le
  · positivity

lemma compressed_remainder_bound (P a : A) (hP : P*P=P) (hs : star P=P) (t : ℝ) :
    ‖flow (compress P a) t - 1 - (t : ℂ) • compress P a‖ ≤
      (|t| * ‖a‖)^2 * Real.exp (|t| * ‖a‖) := by
  refine (flow_remainder_bound (compress P a) t).trans ?_
  apply quadratic_exp_mono
  · positivity
  · exact mul_le_mul_of_nonneg_left (norm_compress_le P a hP hs) (abs_nonneg t)

lemma one_step_error (P a : A) (hP : P*P=P) (hs : star P=P) (t : ℝ) :
    ‖pulse P a t - effective P a t‖ ≤
      2 * (|t| * ‖a‖)^2 * Real.exp (|t| * ‖a‖) := by
  rw [local_remainder_identity P a hP t]
  calc
    ‖P * (flow a t - 1 - (t : ℂ) • a) * P -
        (flow (compress P a) t - 1 - (t : ℂ) • compress P a) * P‖ ≤
        ‖P * (flow a t - 1 - (t : ℂ) • a) * P‖ +
        ‖(flow (compress P a) t - 1 - (t : ℂ) • compress P a) * P‖ :=
      norm_sub_le _ _
    _ ≤ ‖flow a t - 1 - (t : ℂ) • a‖ +
        ‖flow (compress P a) t - 1 - (t : ℂ) • compress P a‖ := by
      exact add_le_add (norm_compress_le P _ hP hs) (norm_mul_projection_le _ P hP hs)
    _ ≤ (|t| * ‖a‖)^2 * Real.exp (|t| * ‖a‖) +
        (|t| * ‖a‖)^2 * Real.exp (|t| * ‖a‖) :=
      add_le_add (flow_remainder_bound a t) (compressed_remainder_bound P a hP hs t)
    _ = 2 * (|t| * ‖a‖)^2 * Real.exp (|t| * ‖a‖) := by ring

end QuantumZenoDynamics
