/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndAE
public import QED.ChainProof.SetCRegKKGe

/-!
# Regulator estimates from the Feynman identity above threshold

Only the spectral range of the integral in `QED/ChainProof/SetCRegBndAE.lean`
is used. The real-kernel identity transfers the centered Feynman bound to the
almost-everywhere regulator predicate. At unit mass it also transfers the
pointwise obstruction from `QED/ChainProof/SetCRegBndCoincidence.lean`.
-/

@[expose] public section

open Complex Real Set Filter Topology MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.TwoLoop.UnitLLink (oneLoopF2)
open QED.TwoLoop.VPUnit

/-- The real Feynman kernel is the sum of the main and fixed counterterm part and the shares. -/
private theorem kerRe_split_uSF (P₀ : Params) (mγ Λ T : ℝ) :
    kerRe P₀ (uBDT P₀) (uCBC P₀) (uSF P₀) mγ Λ T =
      kerRe P₀ (uBDT P₀) (uCBC P₀) (fun _ _ _ _ => 0) mγ Λ T +
      kerRe P₀ (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (uSF P₀) mγ Λ T := by
  simp only [kerRe, Finset.sum_const_zero, add_zero, zero_add, mul_add, Complex.add_re]

private theorem measurable_vpInsert_spectral (a b : ℝ) : Measurable fun T => vpInsert T a b := by
  have hf : Measurable f2 := by
    have h : Measurable (fun p : ℝ × ℝ => f2Kernel p.1 p.2) := by unfold f2Kernel; fun_prop
    unfold f2
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact (h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 1))).measurable
  unfold vpInsert
  fun_prop

private theorem measurable_sum_uCBC_spectral (P₀ : Params) (mγ Λ : ℝ) :
    Measurable fun T => ∑ k, uCBC P₀ k mγ Λ T := by
  have hF := measurable_vpInsert_spectral ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2)
  have hW := measurable_vpInsertW ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2)
  simp_rw [sum_uCBC_eq, cbVPKer]
  fun_prop

/-- The total kernel is measurable on the spectral range once the longitudinal terms cancel. -/
theorem measurable_setCKerRe_cut_of_isKKCancelGe (P₀ : Params)
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hKK : IsKKCancelGe P₀)
    {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : mγ < Λ) :
    Measurable fun T => setCKerRe P₀ (uBD P₀) mγ Λ (max T 4) := by
  have hf (T : ℝ) := setCKerRe_eq_feyn_ge he hm hKK hmγ hΛ (le_max_right T 4)
  simp_rw [hf]
  let t : ℝ → ℝ := fun T => max T 4
  have ht : Continuous t := continuous_id.max continuous_const
  have ht₀ (T : ℝ) : 0 < t T := (by norm_num : 0 < (4 : ℝ)).trans_le (le_max_right _ _)
  have hU (i : Fin 12) : Continuous fun T => uBDT P₀ i mγ Λ (t T) :=
    continuous_iff_continuousAt.2 fun T =>
      (continuousAt_uBDT P₀ i hm hmγ (hmγ.trans hΛ) (ht₀ T)).comp ht.continuousAt
  have hS : Continuous fun T => ∑ k, uSF P₀ k mγ Λ (t T) :=
    continuous_iff_continuousAt.2 fun T =>
      (continuousAt_sum_uSF P₀ hm hmγ (hmγ.trans hΛ) (ht₀ T)).comp ht.continuousAt
  have hC := (measurable_sum_uCBC_spectral P₀ mγ Λ).comp ht.measurable
  have hM : Measurable fun T => ∑ i, uBDT P₀ i mγ Λ (t T) :=
    (continuous_finsetSum _ fun i _ => hU i).measurable
  have hsum := (hM.add hC).add hS.measurable
  change Measurable fun T => kerRe P₀ (uBDT P₀) (uCBC P₀) (uSF P₀) mγ Λ (t T)
  unfold kerRe
  exact (Complex.continuous_re.measurable.comp (hsum.const_mul (1 / I))).const_mul _

/-- A centered main and fixed counterterm bound yields the bound for the full set (c) kernel. -/
theorem isRegPieceAE_of_centered_main_of_isKKCancelGe (P₀ : Params) {A : ℝ → ℝ}
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hKK : IsKKCancelGe P₀)
    (hlim : ∀ T, 4 ≤ T → Tendsto (fun p : ℝ × ℝ => setCKerRe P₀ (uBD P₀) p.1 p.2 T)
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (A T)))
    (hMain : ∃ C δ Λ₀ : ℝ, 0 < δ ∧ ∀ mγ Λ, 0 < mγ → mγ < δ → Λ₀ < Λ → mγ < Λ →
      ∀ᵐ T ∂volume.restrict (Ici (4 : ℝ)),
        |kerRe P₀ (uBDT P₀) (uCBC P₀) (fun _ _ _ _ => 0) mγ Λ T -
          ((oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ) / 4 +
            3 * dVm P₀.m mγ Λ / 2) * photonTail (vpPhotonT P₀.m mγ Λ T) 0| ≤ C / √T) :
    IsRegPieceAE (setCKerRe P₀ (uBD P₀)) A where
  meas := by
    filter_upwards [eventually_regRange one_pos 1] with p hp
    exact measurable_setCKerRe_cut_of_isKKCancelGe P₀ he hm hKK hp.1 (hp.2.1.trans hp.2.2)
  lim := hlim
  bound := by
    obtain ⟨C, δ, Λ₀, hδ, hC⟩ := hMain
    refine ⟨C + 56, min δ 1, max Λ₀ 1, lt_min hδ one_pos, fun mγ Λ h0 h1 h2 => ?_⟩
    have hγΛ := (h1.trans_le (min_le_right δ 1)).trans ((le_max_right Λ₀ 1).trans_lt h2)
    have hb := hC mγ Λ h0 (h1.trans_le (min_le_left δ 1))
      ((le_max_left Λ₀ 1).trans_lt h2) hγΛ
    filter_upwards [ae_restrict_mem measurableSet_Ici, hb] with T hT h
    rw [setCKerRe_eq_feyn_ge he hm hKK h0 hγΛ hT, kerRe_split_uSF]
    have hS := abs_kerRe_uSF_add_tail_le P₀ he hm h0 hγΛ.le
      ((by norm_num : (1 : ℝ) ≤ 4).trans hT)
    have e (a b q : ℝ) : |a + b| ≤ |a - q| + |b + q| := by
      rw [show a + b = (a - q) + (b + q) by ring]
      exact abs_add_le _ _
    exact (e _ _ _).trans ((add_le_add h hS).trans_eq (add_div _ _ _).symm)

/-- With longitudinal cancellation, the regulator-limit bound for the current total
kernel would imply the impossible Feynman bound at unit mass. -/
theorem not_uniform_setCKerRe_of_isKKCancelGe (P₀ : Params) (hm : P₀.m = 1)
    (he : P₀.e ≠ 0) (hKK : IsKKCancelGe P₀) :
    ¬ ∃ C δ Λ₀ : ℝ, 0 < δ ∧ ∀ a b, 0 < a → a < δ → Λ₀ < b → ∀ t, 4 ≤ t →
      |setCKerRe P₀ (uBD P₀) a b t| ≤ C / Real.sqrt t := by
  rintro ⟨C, δ, Λ₀, hδ, hbd⟩
  apply not_uniform_feyn_kerRe P₀ hm he
  refine ⟨C, min δ 1, max Λ₀ 1, lt_min hδ one_pos, fun a b ha haδ hb t ht => ?_⟩
  have hab : a < b := (haδ.trans_le (min_le_right _ _)).trans
    ((le_max_right _ _).trans_lt hb)
  rw [← setCKerRe_eq_feyn_ge he (hm ▸ one_pos) hKK ha hab ht]
  exact hbd a b ha (haδ.trans_le (min_le_left _ _)) ((le_max_left _ _).trans_lt hb) t ht

/-- The bound field rules out the current predicate under longitudinal cancellation. -/
theorem not_isRegPieceE_of_isKKCancelGe (P₀ : Params) (hm : P₀.m = 1) (he : P₀.e ≠ 0)
    (hKK : IsKKCancelGe P₀) (A : ℝ → ℝ) :
    ¬ IsRegPieceE (setCKerRe P₀ (uBD P₀)) A := by
  intro h
  exact not_uniform_setCKerRe_of_isKKCancelGe P₀ hm he hKK h.bound

end QED.ChainProof.SetCRegDisp

end
