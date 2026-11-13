/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.QuantumZeno.Basic

/-!
# Compression identities
Noncommutative algebra in the projection corner.

## i. Overview
Only idempotence of the projection is used; no commutation with the Hamiltonian is assumed.

## ii. Key results
commute_flow_compress, effective_add, reference_power, local_remainder_identity.

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

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
lemma compress_left (P a : A) (hP : P * P = P) :
    P * compress P a = compress P a := by
  simp only [compress, ← mul_assoc, hP]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
lemma compress_right (P a : A) (hP : P * P = P) :
    compress P a * P = compress P a := by
  simp only [compress, mul_assoc, hP]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
lemma commute_compress (P a : A) (hP : P * P = P) :
    Commute P (compress P a) := by
  show P * compress P a = compress P a * P
  rw [compress_left P a hP, compress_right P a hP]

omit [CompleteSpace A] in
lemma commute_flow_compress (P a : A) (hP : P * P = P) (t : ℝ) :
    Commute P (flow (compress P a) t) := by
  have h : Commute P ((t : ℂ) • compress P a) := by
    show P * ((t : ℂ) • compress P a) = ((t : ℂ) • compress P a) * P
    simp only [mul_smul_comm, smul_mul_assoc,
      compress_left P a hP, compress_right P a hP]
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  exact h.exp_right

omit [CompleteSpace A] in
lemma pulse_left (P a : A) (hP : P * P = P) (t : ℝ) :
    P * pulse P a t = pulse P a t := by
  simp only [pulse, ← mul_assoc, hP]

omit [CompleteSpace A] in
lemma pulse_right (P a : A) (hP : P * P = P) (t : ℝ) :
    pulse P a t * P = pulse P a t := by
  simp only [pulse, mul_assoc, hP]

omit [CompleteSpace A] in
lemma effective_left (P a : A) (hP : P * P = P) (t : ℝ) :
    P * effective P a t = effective P a t := by
  unfold effective
  rw [← mul_assoc, (commute_flow_compress P a hP t).eq, mul_assoc, hP]

omit [CompleteSpace A] in
lemma effective_right (P a : A) (hP : P * P = P) (t : ℝ) :
    effective P a t * P = effective P a t := by
  simp only [effective, mul_assoc, hP]

omit [CompleteSpace A] in
@[simp] lemma effective_zero (P a : A) : effective P a 0 = P := by
  simp [effective]

lemma flow_add (a : A) (s t : ℝ) : flow a (s+t) = flow a s * flow a t := by
  have hc : Commute ((s : ℂ) • a) ((t : ℂ) • a) := by
    show ((s : ℂ) • a) * ((t : ℂ) • a) = ((t : ℂ) • a) * ((s : ℂ) • a)
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm (s : ℂ) (t : ℂ)]
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  simpa [flow, Complex.ofReal_add, add_smul] using
    (NormedSpace.exp_add_of_commute hc)

lemma effective_add (P a : A) (hP : P * P = P) (s t : ℝ) :
    effective P a (s+t) = effective P a s * effective P a t := by
  change flow (compress P a) (s+t) * P = flow (compress P a) s * P * effective P a t
  rw [flow_add, mul_assoc, mul_assoc, effective_left P a hP t]
  rfl

lemma effective_nat_mul (P a : A) (hP : P * P = P) (t : ℝ) (n : ℕ) :
    effective P a ((n : ℝ)*t) = (effective P a t)^n * P := by
  induction n with
  | zero => simp [effective]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, effective_add P a hP, ih]
    rw [pow_succ]
    simp only [mul_assoc, effective_left P a hP t, effective_right P a hP t]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
lemma corner_pow_right {x P : A} (hx : x * P = x) (n : ℕ) (hn : 0 < n) :
    x^n * P = x^n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ, mul_assoc, hx]

lemma reference_power (P a : A) (hP : P * P = P) (t : ℝ) (n : ℕ) (hn : 0 < n) :
    (effective P a (t/n))^n = effective P a t := by
  have h := effective_nat_mul P a hP (t/n) n
  rw [corner_pow_right (effective_right P a hP (t/n)) n hn] at h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have heq : (n : ℝ) * (t / n) = t := by field_simp [hn0]
  simpa [heq] using h.symm

omit [CompleteSpace A] in
/-- The first-order terms agree even when the projection and generator do not commute. -/
lemma local_remainder_identity (P a : A) (hP : P * P = P) (t : ℝ) :
    pulse P a t - effective P a t =
      P * (flow a t - 1 - (t : ℂ) • a) * P -
      (flow (compress P a) t - 1 - (t : ℂ) • compress P a) * P := by
  rw [time_smul_compress]
  simp only [pulse, effective, mul_sub, sub_mul, mul_one, one_mul]
  simp only [mul_assoc, hP]
  noncomm_ring

end QuantumZenoDynamics
