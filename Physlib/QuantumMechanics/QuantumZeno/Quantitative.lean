/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.QuantumZeno.LocalError
public import Physlib.QuantumMechanics.QuantumZeno.Products

/-!
# Finite-measurement error
A dimension-independent non-sharp operator-norm error budget.

## i. Overview
Repeated compressed propagators are compared to the effective dynamics with an explicit
inverse-step-count bound.

## ii. Key results
zeno_error_uniform.

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

lemma error_before_simplification (P a : A) (hP : P*P=P) (hs : star P=P)
    (ha : star a = -a) (t : ℝ) (n : ℕ) (hn : 0<n) :
    ‖product P a t n-effective P a t‖ ≤
      (n : ℝ)*(2*(|t/n| * ‖a‖)^2*Real.exp (|t/n| * ‖a‖)) := by
  rw [← reference_power P a hP t n hn]
  exact (contraction_power_difference _ _
    (norm_pulse_le_one P a hP hs ha _) (norm_effective_le_one P a hP hs ha _) n).trans
      (mul_le_mul_of_nonneg_left (one_step_error P a hP hs (t/n)) (Nat.cast_nonneg n))

lemma scalar_rate_bound {M R t : ℝ} (hM : 0≤M) (hR : 0≤R)
    (ht : |t|≤R) (n : ℕ) (hn : 0<n) :
    (n : ℝ)*(2*(|t/n| * M)^2*Real.exp (|t/n| * M)) ≤ errorBudget R M n := by
  have hnpos : (0 : ℝ)<n := by exact_mod_cast hn
  have hnone : (1 : ℝ)≤n := by exact_mod_cast hn
  have hratio : |t/n| * M ≤ R*M := by
    rw [abs_div, abs_of_pos hnpos]
    have hdiv : |t| / (n : ℝ) ≤ R := by
      apply (div_le_iff₀ hnpos).2
      nlinarith [mul_nonneg hR (sub_nonneg.mpr hnone)]
    exact mul_le_mul_of_nonneg_right hdiv hM
  have hexp := Real.exp_le_exp.mpr hratio
  have hsq : (|t| * M)^2 ≤ (R*M)^2 :=
    pow_le_pow_left₀ (mul_nonneg (abs_nonneg t) hM)
      (mul_le_mul_of_nonneg_right ht hM) 2
  calc
    (n : ℝ)*(2*(|t/n| * M)^2*Real.exp (|t/n| * M)) =
        2*(|t| * M)^2*Real.exp (|t/n| * M)/n := by
      rw [abs_div, abs_of_pos hnpos]
      field_simp [ne_of_gt hnpos]
    _ ≤ 2*(R*M)^2*Real.exp (R*M)/n := by
      apply div_le_div_of_nonneg_right _ hnpos.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num)) hexp
        (Real.exp_pos _).le (by positivity)
    _ = errorBudget R M n := rfl

/-- All positive n, every real t in a compact interval; no asymptotic threshold. -/
lemma zeno_error_uniform (P a : A) (hP : P*P=P) (hs : star P=P)
    (ha : star a = -a) (R : ℝ) (hR : 0≤R) (t : ℝ) (ht : |t|≤R)
    (n : ℕ) (hn : 0<n) :
    ‖product P a t n-effective P a t‖ ≤ errorBudget R ‖a‖ n :=
  (error_before_simplification P a hP hs ha t n hn).trans
    (scalar_rate_bound (norm_nonneg a) hR ht n hn)

/-- Fixed-time specialization of the finite-measurement operator-norm error estimate. -/
lemma zeno_error_at_time (P a : A) (hP : P*P=P) (hs : star P=P)
    (ha : star a = -a) (t : ℝ) (n : ℕ) (hn : 0<n) :
    ‖product P a t n-effective P a t‖ ≤
      2*(|t| * ‖a‖)^2*Real.exp (|t| * ‖a‖)/n :=
  zeno_error_uniform P a hP hs ha |t| (abs_nonneg t) t le_rfl n hn

end QuantumZenoDynamics
