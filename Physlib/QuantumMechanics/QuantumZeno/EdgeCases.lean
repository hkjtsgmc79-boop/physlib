/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.QuantumZeno.CornerAlgebra

/-!
# Degenerate projection cases
Zero and identity projections, zero time and zero generator.

## i. Overview
Finite-step physical statements explicitly require a positive measurement count.

## ii. Key results
product_zero_projection, product_identity_projection, product_time_zero.

## iii. Table of contents
- A. Definitions and results

## iv. References
* None.
-/
/-! ## A. Definitions and results -/

@[expose] public section

noncomputable section
namespace QuantumZenoDynamics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [CompleteSpace A] in
@[simp] lemma pulse_zero_projection (a : A) (t : ℝ) : pulse 0 a t=0 := by
  simp [pulse]
omit [CompleteSpace A] in
@[simp] lemma effective_zero_projection (a : A) (t : ℝ) : effective 0 a t=0 := by
  simp [effective, compress]
omit [CompleteSpace A] in
lemma product_zero_projection (a : A) (t : ℝ) (n : ℕ) (hn : 0<n) :
    product 0 a t n=0 := by
  simp [product, Nat.ne_of_gt hn]
omit [CompleteSpace A] in
@[simp] lemma effective_identity_projection (a : A) (t : ℝ) :
    effective 1 a t=flow a t := by simp [effective, compress]
lemma product_identity_projection (a : A) (t : ℝ) (n : ℕ) (hn : 0<n) :
    product 1 a t n=flow a t := by
  simpa [product, pulse, effective, compress] using
    reference_power (1 : A) a (by simp) t n hn
lemma product_time_zero (P a : A) (hP : P*P=P) (n : ℕ) (hn : 0<n) :
    product P a 0 n=P := by
  have he : pulse P a 0=effective P a 0 := by simp [pulse, hP]
  simpa [product, he] using reference_power P a hP 0 n hn
lemma product_zero_generator (P : A) (hP : P*P=P) (t : ℝ) (n : ℕ) (hn : 0<n) :
    product P 0 t n=P := by
  have he : pulse P 0 (t/n)=effective P 0 (t/n) := by
    simp [pulse, effective, flow, compress, hP]
  calc
    product P 0 t n=(effective P 0 (t/n))^n := by rw [product, he]
    _ = effective P 0 t := reference_power P 0 hP t n hn
    _ = P := by simp [effective, flow, compress]

end QuantumZenoDynamics
