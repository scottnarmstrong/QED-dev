/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSESpat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The spatial integral of the self-energy building block at zero prescription, quadratic numerator

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan, for the
quadratic numerator `seQuad p = (p·ℓ) (ℓ̸)_{αβ}` (the affine case is
`QED/ChainProof/SetCRegDispShellSESpat.lean`). After the translation `v⃗ ↦ v⃗ - y P⃗` the
numerator is `Q(-y P) + ∑ₖ vₖ Lₖ + ∑ₖₗ pₖ (γ̸ₗ)_{αβ} vₖ vₗ`; odd and mixed moments vanish and the
diagonal second moments are a third of the radial one.

* **`seQuad_cons_shift`**: the decomposition of the shifted quadratic numerator.
* **`integral_coord_mul_coord_mul_rpow`**: `∫ vₖ vₗ X^{-s} = δₖₗ ⅓ ∫ |v|² X^{-s}` for `s > 5/2`.

The closed form `integral_seTime_seQuad_zero` (for `n = i + 2`) assembles these as in the affine
case and is not yet in this file.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.WickModel.SelfEnergyLimit QED.OneLoop QED.Integration
open QED.ChainProof.SetCRegDispSE (seTime seSpatial seWt seEff seRadC neg_ofReal_cpow_neg
  integral_sum_sq_add_rpow_half integral_sum_sq_mul_sum_sq_add_rpow_half)
open QED.TwoLoop.VPHalfAtLimit (energyConst)

theorem seDot_cons_zero (p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    Minkowski.dot p (Fin.cons 0 v : Fin 4 → ℝ) = ∑ k, p k.succ * v k := by
  rw [Minkowski.dot_eq, Fin.sum_univ_three]
  simp only [Fin.cons_zero, mul_zero, neg_zero, zero_add]
  rfl

theorem seCons_shift_eq (y : ℝ) (P : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    (Fin.cons (-(y * P 0)) (v - fun k => y * P k.succ) : Fin 4 → ℝ) =
      -(y • P) + (Fin.cons 0 v : Fin 4 → ℝ) := by
  funext μ
  refine Fin.cases ?_ (fun k => ?_) μ
  · simp
  · simp only [Fin.cons_succ, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

theorem seSlash_add_apply (a b : Fin 4 → ℝ) (α β : Fin 4) :
    Dirac.slash (a + b) α β = Dirac.slash a α β + Dirac.slash b α β := by
  rw [QED.Dirac.slash_add, Matrix.add_apply]

/-- The linear coefficients of the shifted quadratic numerator. -/
noncomputable def seQL (p : Fin 4 → ℝ) (α β : Fin 4) (y : ℝ) (P : Fin 4 → ℝ) (k : Fin 3) : ℂ :=
  (p k.succ : ℂ) * Dirac.slash (-(y • P)) α β + (Minkowski.dot p (-(y • P)) : ℂ) * seSl α β k

/-- The shifted quadratic numerator. -/
theorem seQuad_cons_shift (p : Fin 4 → ℝ) (α β : Fin 4) (y : ℝ) (P : Fin 4 → ℝ)
    (v : Fin 3 → ℝ) :
    seQuad p α β (Fin.cons (-(y * P 0)) (v - fun k => y * P k.succ) : Fin 4 → ℝ) =
      seQuad p α β (-(y • P)) + ∑ k, seQL p α β y P k * (v k : ℂ) +
        ∑ k, ∑ l, ((p k.succ : ℂ) * seSl α β l) * ((v k * v l : ℝ) : ℂ) := by
  rw [seCons_shift_eq]
  have hd : Minkowski.dot p (-(y • P) + (Fin.cons 0 v : Fin 4 → ℝ)) =
      Minkowski.dot p (-(y • P)) + Minkowski.dot p (Fin.cons 0 v : Fin 4 → ℝ) := by
    rw [Minkowski.dot_eq, Minkowski.dot_eq, Minkowski.dot_eq]
    simp only [Pi.add_apply]
    ring
  have hq : ∀ ℓ, seQuad p α β ℓ = (Minkowski.dot p ℓ : ℂ) * Dirac.slash ℓ α β := fun _ => rfl
  have hL : ∀ k, seQL p α β y P k = (p k.succ : ℂ) * Dirac.slash (-(y • P)) α β +
      (Minkowski.dot p (-(y • P)) : ℂ) * seSl α β k := fun _ => rfl
  rw [hq, hq, hd, seSlash_add_apply, slash_cons_zero_apply, seDot_cons_zero]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, hL, hL, hL]
  push_cast
  ring

theorem integrable_coord_mul_coord_mul_rpow {D s : ℝ} (hD : 0 < D) (hs : 5 / 2 < s)
    (k l : Fin 3) :
    Integrable fun v : Fin 3 → ℝ => v k * v l * (∑ j, v j ^ 2 + D) ^ (-s) := by
  have hi := integrable_sum_sq_add_rpow hD (by linarith : 3 / 2 < s - 1)
  refine hi.mono' (by fun_prop : Measurable _).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have hX : 0 < ∑ j, v j ^ 2 + D := by positivity
  have hk := QED.OneLoop.VertexLimit.sq_le_sum_sq v k
  have hl := QED.OneLoop.VertexLimit.sq_le_sum_sq v l
  have hkl : |v k * v l| ≤ ∑ j, v j ^ 2 + D := by
    rw [abs_mul]
    nlinarith [abs_nonneg (v k), abs_nonneg (v l), sq_abs (v k), sq_abs (v l),
      sq_nonneg (|v k| - |v l|)]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hX _)]
  calc |v k * v l| * (∑ j, v j ^ 2 + D) ^ (-s)
      ≤ (∑ j, v j ^ 2 + D) * (∑ j, v j ^ 2 + D) ^ (-s) := by gcongr
    _ = (∑ j, v j ^ 2 + D) ^ (-(s - 1)) := by
        rw [show -(s - 1) = 1 + -s by ring, Real.rpow_add hX, Real.rpow_one]

/-- The second moments: `∫ vₖ vₗ X^{-s} = δₖₗ ⅓ ∫ |v|² X^{-s}`. -/
theorem integral_coord_mul_coord_mul_rpow {D s : ℝ} (hD : 0 < D) (hs : 5 / 2 < s)
    (k l : Fin 3) :
    ∫ v : Fin 3 → ℝ, v k * v l * (∑ j, v j ^ 2 + D) ^ (-s) =
      if k = l then (1 / 3 : ℝ) * ∫ v : Fin 3 → ℝ, (∑ j, v j ^ 2) * (∑ j, v j ^ 2 + D) ^ (-s)
      else 0 := by
  split_ifs with h
  · subst h
    have hg : Integrable fun v : Fin 3 → ℝ =>
        (∑ j, v j ^ 2) • (fun x : ℝ => (x + D) ^ (-s)) (∑ j, v j ^ 2) := by
      have := integrable_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ =>
        integrable_coord_mul_coord_mul_rpow hD hs j j
      refine this.congr (Eventually.of_forall fun v => ?_)
      simp only [smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h := integral_coord_sq_smul_radial (fun x : ℝ => (x + D) ^ (-s)) hg k
    simp only [smul_eq_mul] at h
    simp_rw [← sq]
    exact h
  · have h' := integral_coord_mul_coord_smul_radial (fun x : ℝ => (x + D) ^ (-s)) h
    simpa only [smul_eq_mul] using h'


end QED.ChainProof.SetCRegDisp

end
