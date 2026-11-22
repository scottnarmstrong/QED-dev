/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSEQTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c): the covariant form of the `x`-integrand limit

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step b3 (second half). The constants
of the closed forms are evaluated: `K₁ = π`, `K₃ = 3π/8`, `K₄ = 5π/16` for the energy integrals,
`e^{-5iπ/2} = -i`, `e^{-7iπ/2} = i`, and the radial constants `1/3`, `2/15`. Then

* `seAffG_eq`: `seAffG = (iπ²/2) (c + b ℓ̸)` at `ℓ = -yP`;
* `seQuadG₂_eq`: `seQuadG₂ = (iπ²/6) (p·ℓ) ℓ̸` at `ℓ = -yP`;
* `seQuadG₁_eq`: `seQuadG₁ = -(iπ²/12) p̸`;
* **`sePieceLim_eq_tails`**: for distinct squares `mγ², Λ², μ²` (`μ = specMu M_f x`), below
  threshold, the limit `sePieceLim` is `i c₁ w₁(x)` times the `y`-integrals
  `iπ² k ∫ (-3m 1 + (3y - 1) p̸) Tail_R(w)` and
  `iπ² k ∫ p̸ (-2y² p² T₁(w) - (1 - y) T₂(w))`, with `k = μ²/(mγ² - Λ²)²`,
  `w = seArg m p² y`, `T₁ = quadTailVP`, `T₂ = bubTailVP - w T₁`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.WickModel.SelfEnergyLimit QED.OneLoop
open QED.ChainProof.SetCRegDispSE (seWt seRadC seProdLim)
open QED.TwoLoop.VPHalfAtLimit (energyConst)
open QED.TwoLoop.VPHalfAtAssembly (cOne wOne specMu)

/-! ### The constants -/

theorem seEnergyConst_one : energyConst 1 = π := by
  simp only [energyConst, pow_one]
  exact integral_univ_inv_one_add_sq

theorem seEnergyConst_three : energyConst 3 = 3 * π / 8 := by
  rw [energyConst_succ_succ 1, energyConst_succ_succ 0, seEnergyConst_one]
  push_cast
  ring

theorem seEnergyConst_four : energyConst 4 = 5 * π / 16 := by
  rw [energyConst_succ_succ 2, seEnergyConst_three]
  push_cast
  ring

theorem seRadC_zero : seRadC 0 = 1 / 3 := rfl

theorem seRadC_one : seRadC 1 = 2 / 15 := by
  simp only [seRadC]
  norm_num

theorem seExp_five_halves : exp (π * I * (-((5 / 2 : ℝ) : ℂ))) = -I := by
  have h : (π : ℂ) * I * (-((5 / 2 : ℝ) : ℂ)) = -(π / 2 * I) + ((-1 : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    ring
  rw [h, exp_add, exp_int_mul_two_pi_mul_I, mul_one, exp_neg, exp_pi_div_two_mul_I, inv_I]

theorem seExp_seven_halves : exp (π * I * (-((7 / 2 : ℝ) : ℂ))) = I := by
  have h : (π : ℂ) * I * (-((7 / 2 : ℝ) : ℂ)) = π / 2 * I + ((-2 : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    ring
  rw [h, exp_add, exp_int_mul_two_pi_mul_I, mul_one, exp_pi_div_two_mul_I]

/-! ### The numerators -/

theorem seAffG_eq (c b : ℂ) (α β : Fin 4) (P : Fin 4 → ℝ) (y : ℝ) :
    seAffG c b α β P y = I * ((π ^ 2 / 2 : ℝ) : ℂ) * seAff c b α β (-(y • P)) := by
  rw [seAffG, seEnergyConst_three, seExp_five_halves, seRadC_zero]
  push_cast
  ring

theorem seQuadG₂_eq (p : Fin 4 → ℝ) (α β : Fin 4) (P : Fin 4 → ℝ) (y : ℝ) :
    seQuadG₂ p α β P y = I * ((π ^ 2 / 6 : ℝ) : ℂ) * seQuad p α β (-(y • P)) := by
  rw [seQuadG₂, seEnergyConst_four, seExp_seven_halves, seRadC_one]
  push_cast
  ring

theorem seQuadG₁_eq (p : Fin 4 → ℝ) (α β : Fin 4) :
    seQuadG₁ p α β = -(I * ((π ^ 2 / 12 : ℝ) : ℂ)) * Dirac.slash p α β := by
  rw [seQuadG₁, seEnergyConst_three, seEnergyConst_four, seExp_five_halves, seRadC_zero]
  push_cast
  ring

theorem seAff_seCL_neg (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (y : ℝ) :
    seAff (seCL P p α β) 3 α β (-(y • -p)) =
      -3 * (P.m : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ) α β +
        (3 * (y : ℂ) - 1) * Dirac.slash p α β := by
  rw [smul_neg, neg_neg, seAff, seCL, QED.Dirac.slash_smul]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem seQuad_neg (p : Fin 4 → ℝ) (α β : Fin 4) (y : ℝ) :
    seQuad p α β (-(y • -p)) = (y : ℂ) ^ 2 * (Minkowski.dot p p : ℂ) * Dirac.slash p α β := by
  rw [smul_neg, neg_neg, seQuad, QED.Dirac.slash_smul]
  have h : Minkowski.dot p (y • p) = y * Minkowski.dot p p := by
    simp only [Minkowski.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h]
  simp only [Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-! ### The `x`-integrand limit -/

/-- **The covariant form of one flavour piece of the limit**, below threshold, for pairwise
distinct squares of `m_γ`, `Λ` and `μ = specMu M_f x`. -/
theorem sePieceLim_eq_tails {M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) (P : Params)
    (p : Fin 4 → ℝ) (α β : Fin 4) (x : ℝ) (f : Fin 3)
    (hP : ∀ y ∈ Icc (0 : ℝ) 1,
      c₀ ≤ selfEnergyFeynmanMass P.m M₀ (Minkowski.dot (-p) (-p)) y)
    (hm : P.m ≠ 0) (ha : M₀ ≤ P.mγ) (hb : M₀ ≤ P.Λ) (hμ : M₀ ≤ specMu (P.mass f) x)
    (hAB : P.mγ ^ 2 ≠ P.Λ ^ 2) (hAU : P.mγ ^ 2 ≠ specMu (P.mass f) x ^ 2)
    (hBU : P.Λ ^ 2 ≠ specMu (P.mass f) x ^ 2) :
    sePieceLim P p α β x f = I * cOne P * wOne x *
      ((∫ y in Ioo (0 : ℝ) 1, I * ((π ^ 2 : ℝ) : ℂ) *
          ((specMu (P.mass f) x ^ 2 / (P.mγ ^ 2 - P.Λ ^ 2) ^ 2 *
            photonTail (vpPhotonT P.m P.mγ P.Λ (specMu (P.mass f) x ^ 2 / P.m ^ 2))
              (seArg P.m (Minkowski.dot p p) y) : ℝ) : ℂ) *
          (-3 * (P.m : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ) α β +
            (3 * (y : ℂ) - 1) * Dirac.slash p α β)) +
        ∫ y in Ioo (0 : ℝ) 1, I * ((π ^ 2 : ℝ) : ℂ) *
          ((specMu (P.mass f) x ^ 2 / (P.mγ ^ 2 - P.Λ ^ 2) ^ 2 *
            (-2 * y ^ 2 * Minkowski.dot p p *
                quadTailVP (P.mγ ^ 2) (P.Λ ^ 2) (specMu (P.mass f) x ^ 2)
                  (seArg P.m (Minkowski.dot p p) y) -
              (1 - y) * (bubTailVP (P.mγ ^ 2) (P.Λ ^ 2) (specMu (P.mass f) x ^ 2)
                  (seArg P.m (Minkowski.dot p p) y) -
                seArg P.m (Minkowski.dot p p) y *
                  quadTailVP (P.mγ ^ 2) (P.Λ ^ 2) (specMu (P.mass f) x ^ 2)
                    (seArg P.m (Minkowski.dot p p) y))) : ℝ) : ℂ) *
          Dirac.slash p α β) := by
  have hneg : Minkowski.dot (-p) (-p) = Minkowski.dot p p := by
    simp only [Minkowski.dot, Pi.neg_apply, neg_mul, mul_neg, neg_neg]
  have cAB : ((P.mγ : ℂ) ^ 2 - (P.Λ : ℂ) ^ 2) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hAB
  have cAU : ((P.mγ : ℂ) ^ 2 - (specMu (P.mass f) x : ℂ) ^ 2) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hAU
  have cBU : ((P.Λ : ℂ) ^ 2 - (specMu (P.mass f) x : ℂ) ^ 2) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hBU
  rw [sePieceLim_eq_blocks hM₀ hc₀ P p α β x f hP ha hb hμ cAB cAU cBU,
    seAffBlk_eq_tail hM₀ hc₀ hP hm ha hb hμ hAB hAU hBU,
    seQuadBlk_eq_tail hM₀ hc₀ hP ha hb hμ hAB hAU hBU, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo, hneg]
  congr 2
  · refine setIntegral_congr_fun measurableSet_Ioo fun y _ => ?_
    rw [seAffG_eq, seAff_seCL_neg]
    push_cast
    ring
  · refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    have h1 : (1 - (y : ℂ)) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hy.2.ne'
    rw [seQuadG₂_eq, seQuadG₁_eq, seQuad_neg, seWt]
    push_cast
    field_simp
    ring

end QED.ChainProof.SetCRegDisp

end
