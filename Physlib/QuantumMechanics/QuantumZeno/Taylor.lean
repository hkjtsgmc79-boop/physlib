/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.QuantumZeno.Basic

/-!
# Exponential remainder estimate
A quadratic short-time remainder bound for bounded generators.

## i. Overview
The analytic estimate is derived from the exponential series, not supplied as a physical
assumption.

## ii. Key results
exponential_remainder_bound, flow_remainder_bound.

## iii. Table of contents
- A. Definitions and results

## iv. References
* None.
-/
/-! ## A. Definitions and results -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace QuantumZenoDynamics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [CompleteSpace A] [NormOneClass A]

/-- The factorial-weighted power appearing in the Banach-algebra exponential series. -/
private def term (x : A) (k : ℕ) : A := ((k.factorial : ℂ)⁻¹) • x^k

omit [NormOneClass A] in
private lemma term_summable (x : A) : Summable (term x) := by
  exact NormedSpace.expSeries_summable' (𝕂 := ℂ) x

omit [CompleteSpace A] [NormOneClass A] in
private lemma norm_term_summable (x : A) : Summable (fun k => ‖term x k‖) := by
  simpa [term] using (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) x)

omit [CompleteSpace A] [NormOneClass A] in
private lemma exp_series (x : A) : NormedSpace.exp x = ∑' k, term x k := by
  simpa [term] using (congrFun (NormedSpace.exp_eq_tsum ℂ) x)

omit [NormOneClass A] in
private lemma remainder_tail (x : A) :
    NormedSpace.exp x - 1 - x = ∑' k, term x (k+2) := by
  have h := (term_summable x).sum_add_tsum_nat_add 2
  have hsum : (∑ k ∈ Finset.range 2, term x k) = 1 + x := by
    simp [Finset.sum_range_succ, term]
  rw [hsum, ← exp_series x] at h
  calc
    NormedSpace.exp x - 1 - x =
        ((1 + x) + (∑' k, term x (k+2))) - 1 - x := by rw [h]
    _ = ∑' k, term x (k+2) := by abel

omit [CompleteSpace A] in
private lemma shifted_term_bound (x : A) (k : ℕ) :
    ‖term x (k+2)‖ ≤ ‖x‖^2 * (‖x‖^k / k.factorial) := by
  have hfac : (k.factorial : ℝ) ≤ ((k+2).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_le (by omega : k ≤ k+2))
  have hfacpos : 0 < (k.factorial : ℝ) := by positivity
  have hfac2pos : 0 < ((k+2).factorial : ℝ) := by positivity
  calc
    ‖term x (k+2)‖ ≤ ‖x‖^(k+2) / (k+2).factorial := by
      simp only [term, norm_smul, norm_inv, Complex.norm_natCast]
      simpa [div_eq_inv_mul] using
        (mul_le_mul_of_nonneg_left (norm_pow_le x (k+2)) (inv_nonneg.mpr hfac2pos.le))
    _ ≤ ‖x‖^(k+2) / k.factorial := by
      exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg x) _) hfacpos hfac
    _ = ‖x‖^2 * (‖x‖^k / k.factorial) := by rw [pow_add]; ring

lemma exponential_remainder_bound (x : A) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖^2 * Real.exp ‖x‖ := by
  let f : ℕ → ℝ := fun k => ‖x‖^k / (k.factorial : ℝ)
  have hf : Summable f := by
    simpa [f, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_summable ‖x‖)
  have hfsum : (∑' k, f k) = Real.exp ‖x‖ := by
    simpa [f, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ‖x‖).tsum_eq
  have hnorm : Summable (fun k => ‖term x (k+2)‖) :=
    (summable_nat_add_iff 2).2 (norm_term_summable x)
  rw [remainder_tail]
  calc
    ‖∑' k, term x (k+2)‖ ≤ ∑' k, ‖term x (k+2)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k, ‖x‖^2 * f k := by
      exact Summable.tsum_le_tsum (fun k => shifted_term_bound x k)
        hnorm (hf.mul_left _)
    _ = ‖x‖^2 * Real.exp ‖x‖ := by rw [tsum_mul_left, hfsum]

lemma flow_remainder_bound (a : A) (t : ℝ) :
    ‖flow a t - 1 - (t : ℂ) • a‖ ≤
      (|t| * ‖a‖)^2 * Real.exp (|t| * ‖a‖) := by
  simpa only [flow, norm_time_smul] using exponential_remainder_bound ((t : ℂ) • a)

end QuantumZenoDynamics
