/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKAsmRho
public import QED.ChainProof.SetCKSelfInFub
public import QED.ChainProof.SetCKCornInFub
public import QED.ChainProof.SetCKCrossTFub
public import QED.ChainProof.SetCKScOutSH
public import QED.ChainProof.SetCKScOutCH

/-!
# Set (c), Stage K, assembly: the Stieltjes representation of the kernel sum

Helper level (no frozen statement). The set (c) kernel at spectral parameter `t > 0` is the
sum of the seven unit placements of the plan (`docs/campaign/SETC-KERNEL-PLAN.md`, check 2):

`A(t) = L(t,0) + L(0,t) + S(t,0) + C(t,0) + X(t,0) + X(0,t) + [S(0,t) + C_ct(0,t)] + C(0,t)`.

In Lean the pieces are `lPair` (the L pair), `selfIn` (`S(t,0)`), `cornIn` (`C(t,0)`),
`crossT` (`X(t,0)`), `scOutS` (`S(0,t) + C_ct(0,t)`) and `scOutC` (`C(0,t)`, two-loop part).
The mirror placement `X(0,t)` is replaced by `X(t,0)` (**`setCKKernelSum`** has `2 crossT`):
the mirror identity `X(t,0) = X(0,t)` is proved in `SetCKCrossLink` (`setCKKernelSum_eq'`).

**`setCKKernelSum_eq`**: for every `t > 0`,

`setCKKernelSum t = ∫₀¹ H(X) Q'(X)/(Q(X) + t)² dX`,

`H = H_{ρ_L} + H_{ρ_S} + H_{ρ_C} + 2 H_X + H_{S,out} + H_{C,out}` (**`setCKHTot`**), where
`H_ρ(X) = ∫₀^X ρ Q` converts the three Stieltjes (`ρ`-) densities (`setCKStieltjes_eq_rhoH`).
The integrability of each `ρ Q/(Q + t)` and of each `H Q'/(Q + t)²` is read off the Fubini
proofs of the pieces.

Numerically (scratch `stageK/asm/chk.py`) the sum of the piece values with `2 X(t,0)` is
`-0.48021841969014402` (`t = 1`) against BLP's `∫₀¹ λ⁽⁴⁾ Q/(Q + t) = -0.48021841969015085`
(difference `6.8·10⁻¹⁵`), and `-0.29836585573947700` (`t = 4`, level-8 pieces) against
`-0.29836585576128852` (difference `2.2·10⁻¹¹`, the level-8 floor).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink

section

variable {t : ℝ}

theorem setCKQ_add_ne (ht : 0 < t) {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) : setCKQ X + t ≠ 0 := by
  have := setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩; linarith

/-- `ρ_L Q/(Q + t)` is integrable. -/
theorem integrableOn_rhoL_mul (ht : 0 < t) :
    IntegrableOn (fun X => rhoL X * (setCKQ X / (setCKQ X + t))) (Ioo 0 1) := by
  have H := pairKerIntegrable ht
  have e2 : ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ x, pairKerT t (x, X) ∂(volume.restrict (Ioo (0 : ℝ) 1)) =
        pairS X * (setCKdQ X / (setCKQ X + t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, H.prod_left_ae] with X hX hs
    exact integral_pairKerT_X ht hX hs
  refine ((integrableOn_dispE1 ht).add (H.integral_prod_right.congr e2)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with X hX
  have h := rhoL_mul_setCKQ hX
  have hu := setCKQ_add_ne ht hX
  simp only [Pi.add_apply]
  field_simp
  linear_combination -h

/-- `ρ_S Q/(Q + t)` is integrable. -/
theorem integrableOn_rhoSelfIn_mul (ht : 0 < t) :
    IntegrableOn (fun X => rhoSelfIn X * (setCKQ X / (setCKQ X + t))) (Ioo 0 1) := by
  have H := integrable_selfInKerT ht
  have e2 : ∀ᵐ X ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫ x, selfInKerT t (x, X) ∂(volume.restrict (Ioo (0 : ℝ) 1)) =
        selfInS X * (setCKdQ X / (setCKQ X + t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, H.prod_left_ae] with X hX hs
    exact integral_selfInKerT_X ht hX hs
  refine (((integrableOn_selfInE1 ht).add (H.integral_prod_right.congr e2)).const_mul 2).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with X hX
  have h := rhoSelfIn_mul_setCKQ hX
  have hu := setCKQ_add_ne ht hX
  simp only [Pi.add_apply]
  unfold selfInS
  field_simp
  linear_combination -h

/-- `ρ_C Q/(Q + t)` is integrable. -/
theorem integrableOn_rhoCornIn_mul (ht : 0 < t) :
    IntegrableOn (fun X => rhoCornIn X * (setCKQ X / (setCKQ X + t))) (Ioo 0 1) := by
  have H := integrable_cornInKerT ht
  have hS : Integrable (fun X => cornInSig X * (setCKdQ X / (setCKQ X + t)))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine H.integral_prod_right.congr (Eventually.of_forall fun X => ?_)
    simp only [cornInKerT, cornInSig]
    exact integral_mul_const _ _
  refine (((integrableOn_cornInE1 ht).const_mul 2).add (hS.const_mul 2)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with X hX
  have hQ : 0 < setCKQ X := div_pos (pow_pos hX.1 2) (by linarith [hX.2])
  have hu : setCKQ X + t ≠ 0 := by linarith
  simp only [Pi.add_apply]
  unfold rhoCornIn
  field_simp

theorem intervalIntegrable_crossTH_mul (ht : 0 < t) :
    IntervalIntegrable (fun X => crossTH X * (setCKdQ X / (setCKQ X + t) ^ 2)) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
    ((integrable_crossTKerT ht).integral_prod_right.congr (Eventually.of_forall fun X => by
      simp only [crossTKerT, crossTH]
      exact integral_mul_const _ _))

theorem intervalIntegrable_scOutCH_mul (ht : 0 < t) :
    IntervalIntegrable (fun X => scOutCH X * (setCKdQ X / (setCKQ X + t) ^ 2)) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
    (((integrable_scOutCKerT ht (scOutC_bound ht)).integral_prod_right.const_mul 2).congr
      (Eventually.of_forall fun X => by
        simp only [scOutCKerT, scOutCH]
        rw [integral_mul_const]
        ring))

theorem intervalIntegrable_scOutSH_mul (ht : 0 < t) :
    IntervalIntegrable (fun X => scOutSH X * (setCKdQ X / (setCKQ X + t) ^ 2)) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
    (((integrableOn_scOutSHk_mul ht).add (integral_scOutSAt_square ht).1).congr_fun
      (fun X _ => by simp only [Pi.add_apply, scOutSH]; ring) measurableSet_Ioo)

end

/-- **The set (c) kernel sum** at `t` (mirror placement `X(0,t)` replaced by `X(t,0)`). -/
noncomputable def setCKKernelSum (t : ℝ) : ℝ :=
  lPair t + selfIn t + cornIn t + 2 * crossT t + scOutS t + scOutC t

/-- **The assembled `Q`-derivative-form weight** of the kernel sum. -/
noncomputable def setCKHTot (X : ℝ) : ℝ :=
  setCKRhoH rhoL X + setCKRhoH rhoSelfIn X + setCKRhoH rhoCornIn X + 2 * crossTH X +
    scOutSH X + scOutCH X

/-- **The Stieltjes representation of the set (c) kernel sum** (`Q`-derivative form). -/
theorem setCKKernelSum_eq {t : ℝ} (ht : 0 < t) :
    setCKKernelSum t = ∫ X in (0 : ℝ)..1, setCKHTot X * (setCKdQ X / (setCKQ X + t) ^ 2) := by
  obtain ⟨iL, vL⟩ := setCKStieltjes_eq_rhoH ht (integrableOn_rhoL_mul ht)
  obtain ⟨iS, vS⟩ := setCKStieltjes_eq_rhoH ht (integrableOn_rhoSelfIn_mul ht)
  obtain ⟨iC, vC⟩ := setCKStieltjes_eq_rhoH ht (integrableOn_rhoCornIn_mul ht)
  have iX := intervalIntegrable_crossTH_mul ht
  have iSo := intervalIntegrable_scOutSH_mul ht
  have iCo := intervalIntegrable_scOutCH_mul ht
  set w : ℝ → ℝ := fun X => setCKdQ X / (setCKQ X + t) ^ 2 with hw
  have e : (fun X => setCKHTot X * w X) = fun X =>
      setCKRhoH rhoL X * w X + setCKRhoH rhoSelfIn X * w X + setCKRhoH rhoCornIn X * w X +
        2 * (crossTH X * w X) + scOutSH X * w X + scOutCH X * w X := by
    funext X; simp only [setCKHTot]; ring
  rw [setCKKernelSum, rhoL_isLPairDensity t ht, vL, rhoSelfIn_isSelfInDensity t ht, vS,
    rhoCornIn_isCornInDensity t ht, vC, crossTH_isCrossTHDensity t ht,
    scOutSH_isScOutSHDensity t ht, scOutCH_isScOutCHDensity t ht, e,
    intervalIntegral.integral_add ((((iL.add iS).add iC).add (iX.const_mul 2)).add iSo) iCo,
    intervalIntegral.integral_add (((iL.add iS).add iC).add (iX.const_mul 2)) iSo,
    intervalIntegral.integral_add ((iL.add iS).add iC) (iX.const_mul 2),
    intervalIntegral.integral_add (iL.add iS) iC, intervalIntegral.integral_add iL iS,
    intervalIntegral.integral_const_mul]

end QED.ChainProof.SetCK

end
