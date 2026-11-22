/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBNVBTr
public import QED.ChainProof.SetAKSKBNAlg

/-!
# Set (a), stage B3: the Gaussian moments of the `VB` entry at the shift

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3 (the nested
form). For a numerator with values `K · ksNTB m ℓ₀ ℓ₁ k` (the `(2, 3)` entry of `VB`,
`SetAKSKBNVBTr`) and a loop shift `ℓ = (-σ₀ k, σ₁ k)`:

* `ksNTBf`: `ksNTB` as a polynomial in the four momenta `P, Q, A = Q - k, R = k + P`;
* `ksN_hessForm_five`: the quadratic form of any loop quartic from five values along a line;
* `ksN_hessForm_VB`: the quadratic form of a `VB` numerator, `K ksNT2Bf` (the second-order
  coefficient of `ksNTBf` along a line);
* `ksN_ksNTB_shift` (**the moment `e`**): `ksNTB m (-σ₀k) (σ₁k) k = k²k³ · 16m²(σ₀² + 4σ₀σ₁ -
  3σ₀ + σ₁² - 3σ₁ + 1)`;
* `ksN_contractTwo_ksNTB` (**the moments `h`**): `contractTwo A (-σ₀k, σ₁k) = K k²k³ (g₀₀ h₀₀ +
  2g₀₁ h₀₁ + g₁₁ h₁₁)`, `g = A⁻¹`, `h₀₀ = 32σ₁(σ₁ - 1)`, `h₀₁ = 16(2σ₀σ₁ - σ₀ - σ₁)`,
  `h₁₁ = 32σ₀(σ₀ - 1)`.

(The moments were computed with sympy, `setAKS10/s2.py`.)
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.TwoLoop.PauliZeroExplicit.NumeratorCongr

/-- `ksNTB` as a polynomial in the four momenta `P`, `Q`, `A = Q - k`, `R = k + P`. -/
noncomputable def ksNTBf (m : ℝ) (P Q A R : Fin 4 → ℝ) : ℝ :=
  8 * m ^ 2 * (P 2 * R 3 + R 2 * P 3) -
    16 * m ^ 2 * (A 3 + Q 3) * (P 2 + R 2) +
    8 * m ^ 2 * (Q 2 * A 3 + A 2 * Q 3) +
    8 * (-P 2 * (Q 3 * Minkowski.dot A R - Minkowski.dot Q A * R 3 +
          Minkowski.dot Q R * A 3) +
      Q 2 * (P 3 * Minkowski.dot A R - Minkowski.dot P A * R 3 +
          Minkowski.dot P R * A 3) +
      A 2 * (Minkowski.dot P Q * R 3 - P 3 * Minkowski.dot Q R +
          Minkowski.dot P R * Q 3) -
      R 2 * (Minkowski.dot P Q * A 3 - P 3 * Minkowski.dot Q A +
          Minkowski.dot P A * Q 3))

theorem ksN_ksNTB_eq (m : ℝ) (P Q k : Fin 4 → ℝ) :
    ksNTB m P Q k = ksNTBf m P Q (Q - k) (k + P) := rfl

/-- The second-order coefficient of `ksNTBf` along the line `(P, Q, A, R) + t (dP, dQ, dA, dR)`. -/
noncomputable def ksNT2Bf (m : ℝ) (P Q A R dP dQ dA dR : Fin 4 → ℝ) : ℝ :=
  8 * (
    A 2 * Minkowski.dot P dQ * dR 3 + A 2 * Minkowski.dot P dR * dQ 3 -
      A 2 * Minkowski.dot Q dR * dP 3 + A 2 * Minkowski.dot dP Q * dR 3 +
      A 2 * Minkowski.dot dP R * dQ 3 + A 2 * Minkowski.dot dP dQ * R 3 +
      A 2 * Minkowski.dot dP dR * Q 3 - A 2 * Minkowski.dot dQ R * dP 3 -
      A 2 * Minkowski.dot dQ dR * P 3 - A 3 * Minkowski.dot P dQ * dR 2 +
      A 3 * Minkowski.dot P dR * dQ 2 - A 3 * Minkowski.dot Q dR * dP 2 -
      A 3 * Minkowski.dot dP Q * dR 2 + A 3 * Minkowski.dot dP R * dQ 2 -
      A 3 * Minkowski.dot dP dQ * R 2 + A 3 * Minkowski.dot dP dR * Q 2 -
      A 3 * Minkowski.dot dQ R * dP 2 - A 3 * Minkowski.dot dQ dR * P 2 -
      Minkowski.dot A R * dP 2 * dQ 3 + Minkowski.dot A R * dP 3 * dQ 2 -
      Minkowski.dot A dR * P 2 * dQ 3 + Minkowski.dot A dR * P 3 * dQ 2 +
      Minkowski.dot A dR * Q 2 * dP 3 - Minkowski.dot A dR * Q 3 * dP 2 -
      Minkowski.dot P A * dQ 2 * dR 3 - Minkowski.dot P A * dQ 3 * dR 2 +
      Minkowski.dot P Q * dA 2 * dR 3 - Minkowski.dot P Q * dA 3 * dR 2 +
      Minkowski.dot P R * dA 2 * dQ 3 + Minkowski.dot P R * dA 3 * dQ 2 -
      Minkowski.dot P dA * Q 2 * dR 3 - Minkowski.dot P dA * Q 3 * dR 2 -
      Minkowski.dot P dA * R 2 * dQ 3 - Minkowski.dot P dA * R 3 * dQ 2 -
      Minkowski.dot P dQ * R 2 * dA 3 + Minkowski.dot P dQ * R 3 * dA 2 +
      Minkowski.dot P dR * Q 2 * dA 3 + Minkowski.dot P dR * Q 3 * dA 2 +
      Minkowski.dot Q A * dP 2 * dR 3 + Minkowski.dot Q A * dP 3 * dR 2 -
      Minkowski.dot Q R * dA 2 * dP 3 - Minkowski.dot Q R * dA 3 * dP 2 +
      Minkowski.dot Q dA * P 2 * dR 3 + Minkowski.dot Q dA * P 3 * dR 2 +
      Minkowski.dot Q dA * R 2 * dP 3 + Minkowski.dot Q dA * R 3 * dP 2 -
      Minkowski.dot Q dR * P 2 * dA 3 - Minkowski.dot Q dR * P 3 * dA 2 -
      Minkowski.dot dA R * P 2 * dQ 3 + Minkowski.dot dA R * P 3 * dQ 2 +
      Minkowski.dot dA R * Q 2 * dP 3 - Minkowski.dot dA R * Q 3 * dP 2 -
      Minkowski.dot dA dR * P 2 * Q 3 + Minkowski.dot dA dR * P 3 * Q 2 -
      Minkowski.dot dP A * Q 2 * dR 3 - Minkowski.dot dP A * Q 3 * dR 2 -
      Minkowski.dot dP A * R 2 * dQ 3 - Minkowski.dot dP A * R 3 * dQ 2 -
      Minkowski.dot dP Q * R 2 * dA 3 + Minkowski.dot dP Q * R 3 * dA 2 +
      Minkowski.dot dP R * Q 2 * dA 3 + Minkowski.dot dP R * Q 3 * dA 2 -
      Minkowski.dot dP dA * Q 2 * R 3 - Minkowski.dot dP dA * Q 3 * R 2 +
      Minkowski.dot dQ A * P 2 * dR 3 + Minkowski.dot dQ A * P 3 * dR 2 +
      Minkowski.dot dQ A * R 2 * dP 3 + Minkowski.dot dQ A * R 3 * dP 2 -
      Minkowski.dot dQ R * P 2 * dA 3 - Minkowski.dot dQ R * P 3 * dA 2 +
      Minkowski.dot dQ dA * P 2 * R 3 + Minkowski.dot dQ dA * P 3 * R 2 + dA 2 * dQ 3 * m^2 -
      2 * dA 3 * dP 2 * m^2 + dA 3 * dQ 2 * m^2 - 2 * dA 3 * dR 2 * m^2 - 2 * dP 2 * dQ 3 * m^2 +
      dP 2 * dR 3 * m^2 + dP 3 * dR 2 * m^2 - 2 * dQ 3 * dR 2 * m^2)

/-- **The second-order coefficient from five values along a line.** -/
theorem ksN_ksNTBf_five (m : ℝ) (P Q A R dP dQ dA dR : Fin 4 → ℝ) :
    (16 * (ksNTBf m (P + (1 : ℝ) • dP) (Q + (1 : ℝ) • dQ) (A + (1 : ℝ) • dA) (R + (1 : ℝ) • dR) +
        ksNTBf m (P + (-1 : ℝ) • dP) (Q + (-1 : ℝ) • dQ) (A + (-1 : ℝ) • dA)
          (R + (-1 : ℝ) • dR)) -
      (ksNTBf m (P + (2 : ℝ) • dP) (Q + (2 : ℝ) • dQ) (A + (2 : ℝ) • dA) (R + (2 : ℝ) • dR) +
        ksNTBf m (P + (-2 : ℝ) • dP) (Q + (-2 : ℝ) • dQ) (A + (-2 : ℝ) • dA)
          (R + (-2 : ℝ) • dR)) -
      30 * ksNTBf m P Q A R) / 24 = ksNT2Bf m P Q A R dP dQ dA dR := by
  simp only [ksNTBf, ksNT2Bf, ksN_dot_line, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The quadratic form of a loop quartic from five values along a line.** -/
theorem ksN_hessForm_five (Q : LoopQuartic) (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    hessForm Q ℓ δ = (16 * (Q.eval (ℓ + (1 : ℝ) • δ) + Q.eval (ℓ + (-1 : ℝ) • δ)) -
      (Q.eval (ℓ + (2 : ℝ) • δ) + Q.eval (ℓ + (-2 : ℝ) • δ)) - 30 * Q.eval ℓ) / 24 := by
  have e1 : Q.eval (ℓ + δ) + Q.eval (ℓ - δ) =
      2 * (Q.eval ℓ + hessForm Q ℓ δ + Q.quartPart (loopComp δ)) := Q.eval_add_add_eval_sub ℓ δ
  have e2 : Q.eval (ℓ + (2 : ℝ) • δ) + Q.eval (ℓ - (2 : ℝ) • δ) =
      2 * (Q.eval ℓ + hessForm Q ℓ ((2 : ℝ) • δ) + Q.quartPart (loopComp ((2 : ℝ) • δ))) :=
    Q.eval_add_add_eval_sub ℓ _
  rw [hessForm_two_smul, quartPart_two_smul] at e2
  rw [one_smul, neg_smul, one_smul, ← sub_eq_add_neg, neg_smul, ← sub_eq_add_neg]
  linear_combination (e2 - 16 * e1) / 24

theorem ksN_ksNTB_line (m : ℝ) (k : Fin 4 → ℝ) (ℓ δ : Fin 2 → Fin 4 → ℝ) (t : ℝ) :
    ksNTB m ((ℓ + t • δ) 0) ((ℓ + t • δ) 1) k =
      ksNTBf m (ℓ 0 + t • δ 0) (ℓ 1 + t • δ 1) (ℓ 1 - k + t • δ 1) (k + ℓ 0 + t • δ 0) := by
  rw [ksN_ksNTB_eq]
  simp only [Pi.add_apply, Pi.smul_apply]
  congr 1 <;> abel

/-- **The quadratic form of a `VB` numerator along a direction.** -/
theorem ksN_hessForm_VB {Q : LoopQuartic} {K : ℂ} {m : ℝ} {k : Fin 4 → ℝ}
    (hQ : Q.eval = fun ℓ => K * (ksNTB m (ℓ 0) (ℓ 1) k : ℂ)) (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    hessForm Q ℓ δ =
      K * (ksNT2Bf m (ℓ 0) (ℓ 1) (ℓ 1 - k) (k + ℓ 0) (δ 0) (δ 1) (δ 1) (δ 0) : ℂ) := by
  rw [ksN_hessForm_five, hQ]
  simp only [ksN_ksNTB_line]
  rw [← ksN_ksNTBf_five, ksN_ksNTB_eq]
  push_cast
  ring

/-- **The moment `e` of the `VB` entry**: its value at the loop shift. -/
theorem ksN_ksNTB_shift (m σ₀ σ₁ : ℝ) (k : Fin 4 → ℝ) :
    ksNTB m (-σ₀ • k) (σ₁ • k) k = k 2 * k 3 *
      (16 * m ^ 2 * (σ₀ ^ 2 + 4 * σ₀ * σ₁ - 3 * σ₀ + σ₁ ^ 2 - 3 * σ₁ + 1)) := by
  have h1 : σ₁ • k - k = (σ₁ - 1) • k := by rw [sub_smul, one_smul]
  have h2 : k + -σ₀ • k = (1 - σ₀) • k := by rw [sub_smul, one_smul, sub_eq_add_neg, neg_smul]
  simp only [ksNTB, h1, h2, ksN_dot_smul_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The moments `h` of the `VB` entry**: the Gaussian contraction at the loop shift. -/
theorem ksN_contractTwo_ksNTB {Q : LoopQuartic} {K : ℂ} {m : ℝ} {k : Fin 4 → ℝ}
    (hQ : Q.eval = fun ℓ => K * (ksNTB m (ℓ 0) (ℓ 1) k : ℂ)) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.transpose = A) {g₀₀ g₀₁ g₁₁ σ₀ σ₁ : ℝ} (h00 : A⁻¹ 0 0 = g₀₀) (h01 : A⁻¹ 0 1 = g₀₁)
    (h11 : A⁻¹ 1 1 = g₁₁) :
    Q.contractTwo A (loopComp ![-σ₀ • k, σ₁ • k]) =
      K * ((k 2 * k 3 * (g₀₀ * (32 * σ₁ * (σ₁ - 1)) + 2 * g₀₁ * (16 * (2 * σ₀ * σ₁ - σ₀ - σ₁)) +
        g₁₁ * (32 * σ₀ * (σ₀ - 1))) : ℝ) : ℂ) := by
  rw [ksN_contractTwo_eq Q hA]
  simp only [ksN_hessForm_VB hQ, h00, h01, h11]
  simp only [ksNT2Bf, ksNE, Fin.sum_univ_four, Minkowski.dot, Minkowski.metric,
    Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  simp
  ring

end QED.ChainProof.SetAKS

end
