/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.QuantumZeno.Limit
public import Physlib.QuantumMechanics.QuantumZeno.Dynamics

/-!
# Hilbert-space survival probability
Unnormalized selected measurement histories and their Born weights.

## i. Overview
The operator norm is the continuous-linear-map norm on a complex Hilbert space, and histories
retain their amplitudes rather than renormalizing after each step.

## ii. Key results
survival_probability_bound, survival_probability_limit.

## iii. Table of contents
- A. Definitions and results

## iv. References
* None.
-/
/-! ## A. Definitions and results -/

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace QuantumZenoDynamics
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]

/-- Bounded complex-linear operators, equipped with the Hilbert operator norm. -/
abbrev Operator := E →L[ℂ] E

/-- Recursively execute all successful measurements. A leading P prepares/checks
ran(P); for Pψ=ψ this changes neither the vector nor its probability. -/
def selectedBranch (P a : Operator (E := E)) (δ : ℝ) : ℕ → E → E
  | 0, ψ => P ψ
  | n+1, ψ => pulse P a δ (selectedBranch P a δ n ψ)

omit [Nontrivial E] in
lemma branch_eq_power (P a : Operator (E := E)) (δ : ℝ) (n : ℕ) (ψ : E) :
    selectedBranch P a δ n ψ = ((pulse P a δ)^n * P) ψ := by
  induction n with
  | zero => simp [selectedBranch]
  | succ n ih =>
    simp only [selectedBranch, pow_succ', mul_apply_eq_comp, ih]

omit [Nontrivial E] in
lemma branch_eq_product (P a : Operator (E := E)) (t : ℝ) (n : ℕ)
    (ψ : E) (hψ : P ψ=ψ) :
    selectedBranch P a (t/n) n ψ = product P a t n ψ := by
  rw [branch_eq_power]
  simp [product, hψ]

/-- Born probability of all n selected outcomes, including their amplitudes. -/
def survivalProbability (P a : Operator (E := E)) (t : ℝ) (n : ℕ) (ψ : E) : ℝ :=
  ‖selectedBranch P a (t/n) n ψ‖^2

omit [Nontrivial E] in
lemma effective_norm_on_range (P a : Operator (E := E))
    (hs : star P=P) (ha : star a = -a) (t : ℝ) (ψ : E) (hψ : P ψ=ψ) :
    ‖effective P a t ψ‖ = ‖ψ‖ := by
  change ‖flow (compress P a) t (P ψ)‖ = ‖ψ‖
  rw [hψ]
  exact ContinuousLinearMap.norm_map_of_mem_unitary
    (flow_mem_unitary _ (compress_skew P a hs ha) t) ψ

lemma state_error (P a : Operator (E := E)) (hP : P*P=P)
    (hs : star P=P) (ha : star a = -a) (t : ℝ) (n : ℕ) (hn : 0<n) (ψ : E) :
    ‖product P a t n ψ-effective P a t ψ‖ ≤ errorBudget |t| ‖a‖ n * ‖ψ‖ := by
  calc
    ‖product P a t n ψ-effective P a t ψ‖ ≤
        ‖product P a t n-effective P a t‖ * ‖ψ‖ :=
      (product P a t n-effective P a t).le_opNorm ψ
    _ ≤ errorBudget |t| ‖a‖ n * ‖ψ‖ :=
      mul_le_mul_of_nonneg_right (zeno_error_at_time P a hP hs ha t n hn) (norm_nonneg ψ)

lemma survival_probability_bound (P a : Operator (E := E)) (hP : P*P=P)
    (hs : star P=P) (ha : star a = -a) (t : ℝ) (n : ℕ) (hn : 0<n)
    (ψ : E) (hψ : P ψ=ψ) (hunit : ‖ψ‖=1) :
    0 ≤ 1-survivalProbability P a t n ψ ∧
    1-survivalProbability P a t n ψ ≤ 2*errorBudget |t| ‖a‖ n := by
  have hx0 : 0≤‖product P a t n ψ‖ := norm_nonneg _
  have hx1 : ‖product P a t n ψ‖ ≤ 1 := by
    calc
      ‖product P a t n ψ‖ ≤ ‖product P a t n‖*‖ψ‖ := (product P a t n).le_opNorm ψ
      _ ≤ 1 := by simpa [hunit] using norm_product_le_one P a hP hs ha t n
  have hy : ‖effective P a t ψ‖=1 :=
    (effective_norm_on_range P a hs ha t ψ hψ).trans hunit
  have hd := state_error P a hP hs ha t n hn ψ
  have htriangle := norm_sub_norm_le (effective P a t ψ) (product P a t n ψ)
  rw [hy, norm_sub_rev] at htriangle
  simp only [hunit, mul_one] at hd
  have hdef : survivalProbability P a t n ψ = ‖product P a t n ψ‖^2 := by
    rw [survivalProbability, branch_eq_product P a t n ψ hψ]
  rw [hdef]
  constructor
  · nlinarith
  · have hnonneg := errorBudget_nonneg |t| ‖a‖ n
    nlinarith [sq_nonneg (1-‖product P a t n ψ‖)]

lemma survival_probability_limit (P a : Operator (E := E)) (hP : P*P=P)
    (hs : star P=P) (ha : star a = -a) (t : ℝ)
    (ψ : E) (hψ : P ψ=ψ) (hunit : ‖ψ‖=1) :
    Tendsto (fun n : ℕ => survivalProbability P a t n ψ) atTop (𝓝 1) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N,hN,hbound⟩ := errorBudget_small |t| ‖a‖ (half_pos hε)
  refine ⟨N,?_⟩
  intro n hn
  have h := survival_probability_bound P a hP hs ha t n (by omega) ψ hψ hunit
  have he := hbound n hn
  rw [Real.dist_eq, abs_of_nonpos (by linarith : survivalProbability P a t n ψ-1≤0)]
  linarith

omit [Nontrivial E] in
lemma effective_state_derivative (P a : Operator (E := E)) (t : ℝ) (ψ : E) :
    HasDerivAt (fun s : ℝ => effective P a s ψ)
      (compress P a (effective P a t ψ)) t := by
  let evaluate := (ContinuousLinearMap.apply ℂ E ψ).restrictScalars ℝ
  have h := evaluate.hasFDerivAt.comp t (effective_derivative P a t).hasFDerivAt
  have hDerivative := h.hasDerivAt
  change HasDerivAt (fun s => effective P a s ψ)
    ((1 : ℝ) • (compress P a (effective P a t ψ))) t at hDerivative
  rw [one_smul] at hDerivative
  exact hDerivative

end QuantumZenoDynamics
