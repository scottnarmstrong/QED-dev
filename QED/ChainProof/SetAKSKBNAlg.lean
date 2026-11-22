/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBNTr
public import QED.ChainProof.SetAKSKBNHess

/-!
# Set (a), stage B3: the Gaussian moments of the `VA` entry at the shift

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3 (the nested
form). For a numerator with values `K · ksNTA m ℓ₀ ℓ₁ k` (the `(2, 3)` entry of `VA`,
`SetAKSKBNTr`) and the loop shift `ℓ = -(σ k, ξ σ k)` of the merged `VA` data:

* `ksN_ksNTA_line`: `ksNTA` along a line `ℓ + t δ` is a polynomial of degree four in `t`, with
  quadratic coefficient `ksNT2A`;
* `ksN_ksNTA_shift` (**the moment `a₀`**): `ksNTA m (-σk) (-ξσk) k = k²k³ a₀(σ)`,
  `a₀ = 16 σ(1 - σ)(4m² - ξm² + ξσ² k·k)`;
* `ksN_contractTwo_ksNTA` (**the moment `a₁`**): for `A⁻¹ = U⁻¹ [[1, ξ], [ξ, c]]`,
  `contractTwo A (-(σk, ξσk)) = 4K k²k³ a₁(σ)/U`, `a₁ = -8ξσ(4σ - 3)`.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.TwoLoop.PauliZeroExplicit.NumeratorCongr

/-- `(a + t b)·(c + t d)` expanded in `t`. -/
theorem ksN_dot_line (a b c d : Fin 4 → ℝ) (t : ℝ) :
    Minkowski.dot (a + t • b) (c + t • d) = Minkowski.dot a c +
      t * (Minkowski.dot b c + Minkowski.dot a d) + t ^ 2 * Minkowski.dot b d := by
  simp only [Minkowski.dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four,
    Minkowski.metric]
  simp
  ring

/-- The quadratic coefficient of `ksNTA` along the direction `(d₀, d₁)`. -/
noncomputable def ksNT2A (m : ℝ) (P Q k d₀ d₁ : Fin 4 → ℝ) : ℝ :=
  -16 * ((2 * m ^ 2 + Minkowski.dot P Q) * (2 * d₀ 2 * d₀ 3) +
      (Minkowski.dot d₀ Q + Minkowski.dot P d₁) *
        (d₀ 2 * (k + P) 3 + (k + P) 2 * d₀ 3 + P 2 * d₀ 3 + d₀ 2 * P 3) +
      Minkowski.dot d₀ d₁ * (P 2 * (k + P) 3 + (k + P) 2 * P 3)) +
    8 * ((m ^ 2 + Minkowski.dot P P) * (d₁ 2 * d₀ 3 + d₀ 2 * d₁ 3) +
      2 * Minkowski.dot P d₀ * (d₁ 2 * (k + P) 3 + (k + P) 2 * d₁ 3 + Q 2 * d₀ 3 + d₀ 2 * Q 3) +
      Minkowski.dot d₀ d₀ * (Q 2 * (k + P) 3 + (k + P) 2 * Q 3))

/-- **`ksNTA` along a line** is a quartic polynomial in `t`. -/
theorem ksN_ksNTA_line (m : ℝ) (P Q k d₀ d₁ : Fin 4 → ℝ) :
    ∃ c₁ c₃ c₄ : ℝ, ∀ t : ℝ, ksNTA m (P + t • d₀) (Q + t • d₁) k =
      ksNTA m P Q k + c₁ * t + ksNT2A m P Q k d₀ d₁ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4 := by
  refine ⟨-16 * ((2 * m ^ 2 + Minkowski.dot P Q) * (d₀ 2 * (k + P) 3 + (k + P) 2 * d₀ 3 + P 2
    * d₀ 3 + d₀ 2 * P 3) + (Minkowski.dot d₀ Q + Minkowski.dot P d₁) * (P 2 * (k + P) 3 + (k +
    P) 2 * P 3)) + 8 * ((m ^ 2 + Minkowski.dot P P) * (d₁ 2 * (k + P) 3 + (k + P) 2 * d₁ 3 + Q
    2 * d₀ 3 + d₀ 2 * Q 3) + (2 * Minkowski.dot P d₀) * (Q 2 * (k + P) 3 + (k + P) 2 * Q 3)),
    -16 * ((Minkowski.dot d₀ Q + Minkowski.dot P d₁) * (2 * d₀ 2 * d₀ 3) + Minkowski.dot d₀
      d₁ * (d₀ 2 * (k + P) 3 + (k + P) 2 * d₀ 3 + P 2 * d₀ 3 + d₀ 2 * P 3)) + 8 * ((2 *
      Minkowski.dot P d₀) * (d₁ 2 * d₀ 3 + d₀ 2 * d₁ 3) + Minkowski.dot d₀ d₀ * (d₁ 2 * (k +
      P) 3 + (k + P) 2 * d₁ 3 + Q 2 * d₀ 3 + d₀ 2 * Q 3)),
    -16 * Minkowski.dot d₀ d₁ * (2 * d₀ 2 * d₀ 3) + 8 * Minkowski.dot d₀ d₀ * (d₁ 2 * d₀ 3 +
      d₀ 2 * d₁ 3), fun t => ?_⟩
  have hPQ := ksN_dot_line P d₀ Q d₁ t
  have hPP := ksN_dot_line P d₀ P d₀ t
  have hd : Minkowski.dot d₀ P = Minkowski.dot P d₀ := ksN_dot_comm P d₀
  simp only [ksNTA, ksNT2A, hPQ, hPP, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hd]
  ring

/-- **The quadratic form of a `VA` numerator along a direction.** -/
theorem ksN_hessForm_VA {Q : LoopQuartic} {K : ℂ} {m : ℝ} {k : Fin 4 → ℝ}
    (hQ : Q.eval = fun ℓ => K * (ksNTA m (ℓ 0) (ℓ 1) k : ℂ)) (ℓ δ : Fin 2 → Fin 4 → ℝ) :
    hessForm Q ℓ δ = K * (ksNT2A m (ℓ 0) (ℓ 1) k (δ 0) (δ 1) : ℂ) := by
  obtain ⟨c₁, c₃, c₄, h⟩ := ksN_ksNTA_line m (ℓ 0) (ℓ 1) k (δ 0) (δ 1)
  refine ksN_hessForm_of_poly Q ℓ δ (K * (ksNTA m (ℓ 0) (ℓ 1) k : ℂ)) (K * c₁) _ (K * c₃)
    (K * c₄) fun t => ?_
  rw [hQ]
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [h t]
  push_cast
  ring

theorem ksN_dot_smul_smul (a b : ℝ) (k : Fin 4 → ℝ) :
    Minkowski.dot (a • k) (b • k) = a * b * Minkowski.dot k k := by
  simp only [Minkowski.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The moment `a₀` of the `VA` entry**: its value at the loop shift. -/
theorem ksN_ksNTA_shift (m σ ξ : ℝ) (k : Fin 4 → ℝ) :
    ksNTA m (-σ • k) (-(ξ * σ) • k) k =
      k 2 * k 3 * (16 * σ * (1 - σ) * (4 * m ^ 2 - ξ * m ^ 2 + ξ * σ ^ 2 * Minkowski.dot k k)) := by
  simp only [ksNTA, ksN_dot_smul_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The moment `a₁` of the `VA` entry**: the Gaussian contraction at the loop shift, for
`A⁻¹ = U⁻¹ [[1, ξ], [ξ, c]]`. -/
theorem ksN_contractTwo_ksNTA {Q : LoopQuartic} {K : ℂ} {m : ℝ} {k : Fin 4 → ℝ}
    (hQ : Q.eval = fun ℓ => K * (ksNTA m (ℓ 0) (ℓ 1) k : ℂ)) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.transpose = A) {U c σ ξ : ℝ} (h00 : A⁻¹ 0 0 = U⁻¹) (h01 : A⁻¹ 0 1 = ξ * U⁻¹)
    (h11 : A⁻¹ 1 1 = c * U⁻¹) :
    Q.contractTwo A (loopComp ![-σ • k, -(ξ * σ) • k]) =
      K * ((4 * k 2 * k 3 * (-8 * ξ * σ * (4 * σ - 3)) * U⁻¹ : ℝ) : ℂ) := by
  rw [ksN_contractTwo_eq Q hA]
  simp only [ksN_hessForm_VA hQ, h00, h01, h11]
  simp only [ksNT2A, ksNE, Fin.sum_univ_four, Minkowski.dot, Minkowski.metric,
    Pi.add_apply, Pi.single_apply]
  simp
  ring

end QED.ChainProof.SetAKS

end
