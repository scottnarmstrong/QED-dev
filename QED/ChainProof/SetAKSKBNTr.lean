/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBTrace

/-!
# Set (a), stage B3: the `(2, 3)` entries of the self-energy classes as scalars

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3 (the nested
form). The inner self-energy numerator sandwiched between two equal electron numerators reduces,
by `a̸ a̸ = -a·a` and `{a̸, q̸} = -2 a·q`, to at most one slash:

* `ksN_sandwich`: `S(a) (2q̸ + 4m) S(a) = c₀ + c_a a̸ + c_q q̸`, with
  `c₀ = 4m(a·q + m² - a·a)`, `c_a = -4(a·q) - 8m²`, `c_q = 2(m² + a·a)`.

The `(2, 3)` entries of the classes `VA` and `VC` are then traces of at most four slashes, with
the two photon indices on `γ²`, `γ³` (`η²³ = 0`):

* **`ksN_vNum_VA`**: `vNum(VA)₂₃(ℓ) = K · ksNTA m (ℓ 0) (ℓ 1) k`,
  `ksNTA = -16(2m² + P·Q)(P²R³ + R²P³) + 8(m² + P·P)(Q²R³ + R²Q³)`, `R = k + P`;
* **`ksN_vNum_VC`**: `vNum(VC)₂₃(ℓ) = K · ksNTC m (ℓ 0) (ℓ 1) k`,
  `ksNTC = -16(2m² + R·Q)(P²R³ + R²P³) + 8(m² + R·R)(P²Q³ + Q²P³)`,

`K = faceIdKV e 0 1`. (Checked against the sympy fits of `vNum`, `setAKS4/fit23.py`.)
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.TwoLoop.Bridge QED.GradedProof.VP2 QED.GradedProof.RPi4
open QED.Dirac
open QED.TwoLoop.Insertion (fermionCtMatrix)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- The scalar `(2, 3)` entry of the class `VA` (photon factor `K` removed). -/
noncomputable def ksNTA (m : ℝ) (P Q k : Fin 4 → ℝ) : ℝ :=
  -16 * (2 * m ^ 2 + Minkowski.dot P Q) * (P 2 * (k + P) 3 + (k + P) 2 * P 3) +
    8 * (m ^ 2 + Minkowski.dot P P) * (Q 2 * (k + P) 3 + (k + P) 2 * Q 3)

/-- The scalar `(2, 3)` entry of the class `VC` (photon factor `K` removed). -/
noncomputable def ksNTC (m : ℝ) (P Q k : Fin 4 → ℝ) : ℝ :=
  -16 * (2 * m ^ 2 + Minkowski.dot (k + P) Q) * (P 2 * (k + P) 3 + (k + P) 2 * P 3) +
    8 * (m ^ 2 + Minkowski.dot (k + P) (k + P)) * (P 2 * Q 3 + Q 2 * P 3)

theorem ksN_slash_sq (a : Fin 4 → ℝ) :
    slash a * slash a = ((-Minkowski.dot a a : ℝ) : ℂ) • (1 : Mat) := by
  have h := slash_anticomm a a
  have h2 : (2 : ℂ) • (slash a * slash a) = (2 : ℂ) • (((-Minkowski.dot a a : ℝ) : ℂ) • 1) := by
    rw [two_smul, h, smul_smul]
    push_cast
    ring_nf
  exact smul_right_injective _ two_ne_zero h2

theorem ksN_slash_comm (a q : Fin 4 → ℝ) :
    slash q * slash a = ((-2 * Minkowski.dot a q : ℝ) : ℂ) • (1 : Mat) - slash a * slash q := by
  rw [← slash_anticomm a q]
  abel

theorem ksN_dot_comm (a q : Fin 4 → ℝ) : Minkowski.dot q a = Minkowski.dot a q := by
  simp only [Minkowski.dot]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  fin_cases μ <;> fin_cases ν <;> simp [Minkowski.metric] <;> ring

/-- **The self-energy numerator between two equal electron numerators.** -/
theorem ksN_sandwich (m : ℝ) (a q : Fin 4 → ℝ) :
    electronNumerator m a * fermionCtMatrix 2 4 m q * electronNumerator m a =
      ((4 * m * (Minkowski.dot a q + m ^ 2 - Minkowski.dot a a) : ℝ) : ℂ) • (1 : Mat) +
        ((-4 * Minkowski.dot a q - 8 * m ^ 2 : ℝ) : ℂ) • slash a +
        ((2 * (m ^ 2 + Minkowski.dot a a) : ℝ) : ℂ) • slash q := by
  have hpp := ksN_slash_sq a
  have hqp := ksN_slash_comm a q
  have hpqp : slash a * (slash q * slash a) =
      ((-2 * Minkowski.dot a q : ℝ) : ℂ) • slash a - ((-Minkowski.dot a a : ℝ) : ℂ) • slash q := by
    rw [hqp, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hpp,
      Matrix.smul_mul, Matrix.one_mul]
  simp only [electronNumerator, fermionCtMatrix, sub_mul, mul_sub, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [hpqp, hpp, hqp]
  push_cast
  module

theorem ksN_trace_four (a b : Fin 4 → ℝ) :
    (gamma 2 * slash a * gamma 3 * slash b).trace = ((4 * (a 2 * b 3 + b 2 * a 3) : ℝ) : ℂ) := by
  rw [ksB_gamma_eq_slash 2, ksB_gamma_eq_slash 3, trace_slash_mul_slash_mul_slash_mul_slash]
  simp only [ksB_single_dot, ksB_dot_single]
  simp

theorem ksN_trace_two : (gamma 2 * gamma 3).trace = 0 := by
  rw [ksB_gamma_eq_slash 2, ksB_gamma_eq_slash 3, trace_slash_mul_slash, ksB_dot_single]
  simp

theorem ksN_trace_three (a : Fin 4 → ℝ) :
    (gamma 2 * slash a * gamma 3).trace = 0 ∧ (gamma 2 * gamma 3 * slash a).trace = 0 := by
  rw [ksB_gamma_eq_slash 2, ksB_gamma_eq_slash 3]
  exact ⟨trace_slash_mul_slash_mul_slash _ _ _, trace_slash_mul_slash_mul_slash _ _ _⟩

/-- The trace of `γ² X γ³ S(r)` for `X = c₀ + c_a a̸ + c_q q̸`. -/
theorem ksN_trace_lin (m c₀ ca cq : ℝ) (a q r : Fin 4 → ℝ) :
    (gamma 2 * ((c₀ : ℂ) • (1 : Mat) + (ca : ℂ) • slash a + (cq : ℂ) • slash q) * gamma 3 *
      electronNumerator m r).trace =
      ((-4 * ca * (a 2 * r 3 + r 2 * a 3) - 4 * cq * (q 2 * r 3 + r 2 * q 3) : ℝ) : ℂ) := by
  simp only [electronNumerator, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, ksN_trace_two, (ksN_trace_three _).1,
    (ksN_trace_three _).2, ksN_trace_four, smul_eq_mul]
  push_cast
  ring

/-- The trace of `γ² S(r) γ³ X` for `X = c₀ + c_a a̸ + c_q q̸`. -/
theorem ksN_trace_lin' (m c₀ ca cq : ℝ) (a q r : Fin 4 → ℝ) :
    (gamma 2 * electronNumerator m r * gamma 3 *
      ((c₀ : ℂ) • (1 : Mat) + (ca : ℂ) • slash a + (cq : ℂ) • slash q)).trace =
      ((-4 * ca * (r 2 * a 3 + a 2 * r 3) - 4 * cq * (r 2 * q 3 + q 2 * r 3) : ℝ) : ℂ) := by
  simp only [electronNumerator, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, ksN_trace_two, (ksN_trace_three _).1,
    (ksN_trace_three _).2, ksN_trace_four, smul_eq_mul]
  push_cast
  ring

/-- **The `(2, 3)` entry of the class `VA`.** -/
theorem ksN_trace_VA (m : ℝ) (P Q k : Fin 4 → ℝ) :
    (gamma 2 * electronNumerator m P * (-fermionCtMatrix 2 4 m Q) * electronNumerator m P *
      gamma 3 * electronNumerator m (k + P)).trace = (ksNTA m P Q k : ℂ) := by
  have e : gamma 2 * electronNumerator m P * (-fermionCtMatrix 2 4 m Q) *
      electronNumerator m P * gamma 3 * electronNumerator m (k + P) =
      -(gamma 2 * (electronNumerator m P * fermionCtMatrix 2 4 m Q * electronNumerator m P) *
        gamma 3 * electronNumerator m (k + P)) := by
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [e, ksN_sandwich, Matrix.trace_neg, ksN_trace_lin, ksNTA]
  push_cast
  ring

/-- **The `(2, 3)` entry of the class `VC`.** -/
theorem ksN_trace_VC (m : ℝ) (P Q k : Fin 4 → ℝ) :
    (gamma 2 * electronNumerator m P * gamma 3 * electronNumerator m (k + P) *
      (-fermionCtMatrix 2 4 m Q) * electronNumerator m (k + P)).trace = (ksNTC m P Q k : ℂ) := by
  have e : gamma 2 * electronNumerator m P * gamma 3 * electronNumerator m (k + P) *
      (-fermionCtMatrix 2 4 m Q) * electronNumerator m (k + P) =
      -(gamma 2 * electronNumerator m P * gamma 3 * (electronNumerator m (k + P) *
        fermionCtMatrix 2 4 m Q * electronNumerator m (k + P))) := by
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [e, ksN_sandwich, Matrix.trace_neg, ksN_trace_lin', ksNTC]
  push_cast
  ring

/-- **The `(2, 3)` entry of the `VA` numerator as a scalar.** -/
theorem ksN_vNum_VA (e m : ℝ) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vNum e 0 1 aVA baseVA cVA m k ℓ 2 3 = faceIdKV e 0 1 * (ksNTA m (ℓ 0) (ℓ 1) k : ℂ) := by
  rw [ksB_vNum_VA, ksN_trace_VA]

/-- **The `(2, 3)` entry of the `VC` numerator as a scalar.** -/
theorem ksN_vNum_VC (e m : ℝ) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vNum e 0 1 aVC baseVC cVC m k ℓ 2 3 = faceIdKV e 0 1 * (ksNTC m (ℓ 0) (ℓ 1) k : ℂ) := by
  rw [ksB_vNum_VC, ksN_trace_VC]

end QED.ChainProof.SetAKS

end
