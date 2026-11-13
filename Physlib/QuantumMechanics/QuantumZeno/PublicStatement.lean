/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.QuantumZeno.Hilbert

/-!
# Finite-dimensional quantum Zeno dynamics
Public results for arbitrary finite dimension and orthogonal projection.

## i. Overview
No rank, eigenbasis, spectral-gap or Hamiltonian-projection commutation assumption is used. The
operator limit includes the terminal projection.

## ii. Key results
finite_dimensional_zeno_limit, finite_dimensional_zeno_error, finite_dimensional_zeno_uniform,
finite_dimensional_effective_dynamics, finite_dimensional_zeno_survival.

## iii. Table of contents
- A. Definitions and results

## iv. References
* Burgarth et al., *Quantum Zeno Dynamics from General Quantum Operations*,
  Quantum 4, 289 (2020). Section 2(i) and Corollary 2 give background on Zeno dynamics
  under frequent projective measurements. [ref: Burgarth2020quantumzenodynamics]
-/
/-! ## A. Definitions and results -/

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace QuantumZenoDynamics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance finiteDimensionalCompleteSpace : CompleteSpace E := FiniteDimensional.complete ℂ E

set_option linter.unusedVariables false in
/-- Fully expanded operator-norm limit in the physical variables.
The positive Planck parameter is part of the physical interface. -/
@[nolint unusedArguments]
theorem finite_dimensional_zeno_limit
    (H P : E →L[ℂ] E) (hH : star H=H) (hPs : star P=P) (hP : P*P=P)
    (hbar : ℝ) (hh : 0<hbar) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (P * NormedSpace.exp
          ((-Complex.I * ((t/(n : ℝ)) : ℂ) / (hbar : ℂ)) • H) * P)^n)
      atTop
      (𝓝 (NormedSpace.exp
        ((-Complex.I * (t : ℂ) / (hbar : ℂ)) • (P*H*P)) * P)) := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    let := h
    have hf : (fun n : ℕ =>
        (P * NormedSpace.exp
          ((-Complex.I * ((t/(n : ℝ)) : ℂ) / (hbar : ℂ)) • H) * P)^n) =
        fun _ => NormedSpace.exp
          ((-Complex.I * (t : ℂ) / (hbar : ℂ)) • (P*H*P)) * P := by
      funext n
      exact Subsingleton.elim _ _
    rw [hf]
    exact tendsto_const_nhds
  | inr h =>
    let := h
    simpa [product, pulse, flow_physical_formula, effective_physical_formula] using
      zeno_operator_limit P (generator H hbar) hP hPs (generator_skew H hH hbar) t

/-- A dimension-independent finite-n estimate, uniform for |t|≤R. -/
lemma finite_dimensional_zeno_error
    (H P : E →L[ℂ] E) (hH : star H=H) (hPs : star P=P) (hP : P*P=P)
    (hbar : ℝ) (hh : 0<hbar) (R : ℝ) (hR : 0≤R)
    (t : ℝ) (ht : |t|≤R) (n : ℕ) (hn : 0<n) :
    ‖product P (generator H hbar) t n-effective P (generator H hbar) t‖ ≤
      2*(R*‖H‖/hbar)^2*Real.exp (R*‖H‖/hbar)/(n : ℝ) := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    let := h
    have hz : product P (generator H hbar) t n-effective P (generator H hbar) t=0 :=
      Subsingleton.elim _ _
    rw [hz, norm_zero]
    positivity
  | inr h =>
    let := h
    simpa [errorBudget, rateConstant, norm_generator H hh, mul_div_assoc] using
      zeno_error_uniform P (generator H hbar) hP hPs
        (generator_skew H hH hbar) R hR t ht n hn

/-- An explicit compact-uniform form of the same finite-dimensional theorem. -/
lemma finite_dimensional_zeno_uniform
    (H P : E →L[ℂ] E) (hH : star H=H) (hPs : star P=P) (hP : P*P=P)
    (hbar : ℝ) (hh : 0<hbar) (R : ℝ) (hR : 0≤R) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, 1≤N ∧ ∀ n : ℕ, N≤n →
      ∀ t : ℝ, |t|≤R →
        ‖product P (generator H hbar) t n-effective P (generator H hbar) t‖ < ε := by
  intro ε hε
  obtain ⟨N,hN,hsmall⟩ := errorBudget_small R (‖H‖/hbar) hε
  refine ⟨N,hN,?_⟩
  intro n hn t ht
  have hb := finite_dimensional_zeno_error H P hH hPs hP hbar hh R hR t ht n (by omega)
  apply lt_of_le_of_lt hb
  simpa [errorBudget, rateConstant, mul_div_assoc] using hsmall n hn

set_option linter.unusedVariables false in
/-- Effective dynamics has initial operator P, remains in its range, is unitary
on that range, and satisfies the actual compressed Schrödinger equation.
The positive Planck parameter is part of the physical interface. -/
@[nolint unusedArguments]
lemma finite_dimensional_effective_dynamics
    (H P : E →L[ℂ] E) (hH : star H=H) (hPs : star P=P) (hP : P*P=P)
    (hbar : ℝ) (hh : 0<hbar) :
    effective P (generator H hbar) 0=P ∧
    (∀ t : ℝ, P*effective P (generator H hbar) t=effective P (generator H hbar) t) ∧
    (∀ s t : ℝ, effective P (generator H hbar) (s+t)=
      effective P (generator H hbar) s*effective P (generator H hbar) t) ∧
    (∀ t : ℝ, star (effective P (generator H hbar) t)*
      effective P (generator H hbar) t=P) ∧
    (∀ t : ℝ, effective P (generator H hbar) t*
      star (effective P (generator H hbar) t)=P) ∧
    (∀ t : ℝ, HasDerivAt (effective P (generator H hbar))
      ((-Complex.I/(hbar : ℂ)) •
        ((P*H*P)*effective P (generator H hbar) t)) t) := by
  refine ⟨effective_zero _ _, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun t => effective_left P _ hP t
  · exact fun s t => effective_add P _ hP s t
  · exact fun t => effective_star_mul P _ hP hPs (generator_skew H hH hbar) t
  · exact fun t => effective_mul_star P _ hP hPs (generator_skew H hH hbar) t
  · exact fun t => effective_schrodinger P H hbar t

set_option linter.unusedVariables false in
/-- State-level survival: the selected-history probability, not a probability
artificially set to one by renormalization after each successful outcome.
The positive Planck parameter is part of the physical interface. -/
@[nolint unusedArguments]
lemma finite_dimensional_zeno_survival [Nontrivial E]
    (H P : E →L[ℂ] E) (hH : star H=H) (hPs : star P=P) (hP : P*P=P)
    (hbar : ℝ) (hh : 0<hbar) (t : ℝ) (ψ : E) (hψ : P ψ=ψ) (hunit : ‖ψ‖=1) :
    Tendsto (fun n : ℕ => survivalProbability P (generator H hbar) t n ψ)
      atTop (𝓝 1) := by
  exact survival_probability_limit P _ hP hPs (generator_skew H hH hbar) t ψ hψ hunit

end QuantumZenoDynamics
