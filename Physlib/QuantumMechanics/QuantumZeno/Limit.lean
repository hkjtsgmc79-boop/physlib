/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.QuantumZeno.Quantitative

/-!
# Zeno operator limit
Convergence of repeated projections on bounded time intervals.

## i. Overview
The fixed-time limit and explicit uniform quantifiers are obtained from the finite-measurement
error budget.

## ii. Key results
zeno_operator_limit, errorBudget_small.

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

lemma errorBudget_small (R M : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ, 1≤N ∧ ∀ n : ℕ, N≤n → errorBudget R M n < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (rateConstant R M / ε)
  refine ⟨k+1, by omega, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hk_le : (k : ℝ) < n := by exact_mod_cast (show k<n by omega)
  have hratio : rateConstant R M / ε < (n : ℝ) := lt_trans hk hk_le
  unfold errorBudget
  apply (div_lt_iff₀ hnpos).2
  have h := (div_lt_iff₀ hε).1 hratio
  simpa [mul_comm] using h

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- Explicit epsilon formulation of compact-uniform operator-norm convergence. -/
lemma zeno_compact_uniform (P a : A) (hP : P*P=P) (hs : star P=P)
    (ha : star a = -a) (R : ℝ) (hR : 0≤R) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, 1≤N ∧ ∀ n : ℕ, N≤n →
      ∀ t : ℝ, |t|≤R → ‖product P a t n-effective P a t‖ < ε := by
  intro ε hε
  obtain ⟨N,hN,hbound⟩ := errorBudget_small R ‖a‖ hε
  refine ⟨N,hN,?_⟩
  intro n hn t ht
  exact lt_of_le_of_lt
    (zeno_error_uniform P a hP hs ha R hR t ht n (by omega)) (hbound n hn)

/-- This Tendsto is in the norm topology on the operator algebra, not merely
pointwise convergence of entries or strong convergence of selected states. -/
lemma zeno_operator_limit (P a : A) (hP : P*P=P) (hs : star P=P)
    (ha : star a = -a) (t : ℝ) :
    Tendsto (fun n : ℕ => product P a t n) atTop (𝓝 (effective P a t)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N,hN,hclose⟩ := zeno_compact_uniform P a hP hs ha |t| (abs_nonneg t) ε hε
  exact ⟨N,fun n hn => by simpa [dist_eq_norm] using hclose n hn t le_rfl⟩

end QuantumZenoDynamics
