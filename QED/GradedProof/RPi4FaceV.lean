/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceInv
public import QED.GradedProof.RPi4SectorEl

/-!
# (R-Π₄) step L6d2: the second Symanzik function on a face, and the `v`-powers

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2. The face
integrand is `Û⁻² ρ^{p-d} ∑ⱼ Cⱼ(ρ) v^{-kⱼ}` with `v = V₀ + θσ`. This file supplies the two
remaining pieces of its `ρ`-modulus:

* **`quadForm_face`**: on a face matrix, `∑ₛₜ (A⁻¹)ₛₜ βₛ·βₜ = (c β₀·β₀ - 2ρ b β₀·b₁ + ρ a b₁·b₁)/Û`,
  regular at `ρ = 0` (so `V₀` is a rational function of the rescaled data);
* **`norm_mul_inv_pow_sub_le`**: `‖C₁ v₁⁻ᵏ - C₀ v₀⁻ᵏ‖ ≤ ρ (L_C c⁻ᵏ + B_C k L_V c^{-(k+1)})` from
  `‖C₁ - C₀‖ ≤ L_C ρ`, `|v₁ - v₀| ≤ L_V ρ`, `v₀, v₁ ≥ c > 0`; with `c = c₁ + θσ` this is the
  `σ`-decay of the Lipschitz constant `B₁(σ)` of the face lemma.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

variable {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {pp : Fin (m + 1) → Fin 4 → ℝ}
  {z : Fin (m + 1) → ℝ} {ρ a b c : ℝ} {b₁ : Fin 4 → ℝ}

theorem dot_smul_left_face (t : ℝ) (x y : Fin 4 → ℝ) :
    Minkowski.dot (t • x) y = t * Minkowski.dot x y := by
  simp only [Minkowski.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem dot_smul_right_face (t : ℝ) (x y : Fin 4 → ℝ) :
    Minkowski.dot x (t • y) = t * Minkowski.dot x y := by
  simp only [Minkowski.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The quadratic form of `V` on a face, rescaled.** -/
theorem quadForm_face (h : IsFaceMat (symanzikMatrix α z) ρ a b c) (hρ : ρ ≠ 0)
    (hu : uHat ρ a b c ≠ 0) (hβ : ∀ μ, symanzikVector α pp z 1 μ = ρ * b₁ μ) :
    ∑ s, ∑ t, (symanzikMatrix α z)⁻¹ s t *
        Minkowski.dot (symanzikVector α pp z s) (symanzikVector α pp z t) =
      (c * Minkowski.dot (symanzikVector α pp z 0) (symanzikVector α pp z 0) -
        2 * ρ * b * Minkowski.dot (symanzikVector α pp z 0) b₁ +
        ρ * a * Minkowski.dot b₁ b₁) / uHat ρ a b c := by
  have hv : symanzikVector α pp z 1 = ρ • b₁ := funext fun μ => by
    rw [hβ μ, Pi.smul_apply, smul_eq_mul]
  rw [inv_face h hρ hu, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, hv,
    dot_smul_left_face, dot_smul_right_face, dot_smul_left_face, dot_smul_right_face,
    Minkowski.dot_comm b₁ (symanzikVector α pp z 0)]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, faceG, eS, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Fin.isValue]
  simp
  field_simp
  ring

/-- **A coefficient times an inverse power, Lipschitz in `ρ`.** -/
theorem norm_mul_inv_pow_sub_le {C₀ C₁ : ℂ} {v₀ v₁ c' L_C B_C L_V ρ' : ℝ} (hc : 0 < c')
    (h0 : c' ≤ v₀) (h1 : c' ≤ v₁) (hC : ‖C₁ - C₀‖ ≤ L_C * ρ') (hB : ‖C₀‖ ≤ B_C)
    (hV : |v₁ - v₀| ≤ L_V * ρ') (k : ℕ) :
    ‖C₁ * ((v₁ : ℂ) ^ k)⁻¹ - C₀ * ((v₀ : ℂ) ^ k)⁻¹‖ ≤
      ρ' * (L_C * (c' ^ k)⁻¹ + B_C * k * L_V * (c' ^ (k + 1))⁻¹) := by
  have hv1 : 0 < v₁ := hc.trans_le h1
  have e : C₁ * ((v₁ : ℂ) ^ k)⁻¹ - C₀ * ((v₀ : ℂ) ^ k)⁻¹ =
      (C₁ - C₀) * ((v₁ : ℂ) ^ k)⁻¹ + C₀ * (((v₁ ^ k)⁻¹ - (v₀ ^ k)⁻¹ : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_inv, norm_pow, norm_real, norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hv1]
  have hp : (v₁ ^ k)⁻¹ ≤ (c' ^ k)⁻¹ :=
    inv_anti₀ (pow_pos hc k) (pow_le_pow_left₀ hc.le h1 k)
  have hd := abs_inv_pow_sub_inv_pow_le hc h1 h0 k
  have hLC : 0 ≤ L_C * ρ' := (norm_nonneg _).trans hC
  have hBC : 0 ≤ B_C := (norm_nonneg _).trans hB
  have hk : (0 : ℝ) ≤ k * (c' ^ (k + 1))⁻¹ := by positivity
  calc ‖C₁ - C₀‖ * (v₁ ^ k)⁻¹ + ‖C₀‖ * |(v₁ ^ k)⁻¹ - (v₀ ^ k)⁻¹| ≤
        (L_C * ρ') * (c' ^ k)⁻¹ + B_C * (k * (L_V * ρ') * (c' ^ (k + 1))⁻¹) := by
          refine add_le_add (mul_le_mul hC hp (by positivity) hLC)
            (mul_le_mul hB (hd.trans ?_) (abs_nonneg _) hBC)
          have := mul_le_mul_of_nonneg_right hV hk
          nlinarith [this]
    _ = ρ' * (L_C * (c' ^ k)⁻¹ + B_C * k * L_V * (c' ^ (k + 1))⁻¹) := by ring

end QED.GradedProof.RPi4

end
