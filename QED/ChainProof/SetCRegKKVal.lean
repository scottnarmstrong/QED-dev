/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKVtx
public import QED.ChainProof.SetCRegKKCov
public import QED.ChainProof.SetCRegKKGe
public import QED.TwoLoop.PauliZeroExplicitCt

/-!
# Set (c): the cancellation above threshold from the value of the scalar tadpole

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSumGe` (`QED/ChainProof/SetCRegKKGe.lean`).
By `QED/ChainProof/SetCRegKKVtx.lean`, `Q(5, 1, 0)` is the one-loop vertex at charge `1` times
the limit `L` of the scalar factor `kkScl`. The Pauli-weighted vertex is the Pauli numerator of a
`δ₁` counterterm class at charge `1` and `δ₁ = 1`, whose Pauli limit is known
(`QED.TwoLoop.PauliZeroExplicit.tendsto_d1_explicit`, value `d1Zero`). Hence:

* **`kkSumP_eq`**: `kkSumP = kCst · (2π)⁴/(Λ² - m_γ²) · L · d1Zero`;
* `IsKKSclLim m`: the scalar factor at spectral mass `t = √(m² T)/2` tends to
  `4 i π² ∫₀^∞ R_T / (Λ² - m_γ²)²` (the Euclidean value `π² ∫ s f(s) ds` of the tadpole times
  the `i` of the energy rotation);
* **`isKKSumGe_of_sclLim`**, **`isKKCancelGe_of_sclLim`**: under `IsKKSclLim P₀.m` the
  cancellation of the longitudinal parts above threshold holds.
-/

@[expose] public section

open Complex Filter Topology Set
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.Relabel (CtClass)
open QED.TwoLoop.UnitLLink (oneLoopF2)

/-- The parameters of the comparison `δ₁` class: charge `1` and `δ₁ = 1`. -/
def kkD1Params (R : Params) : Params := { R with e := 1, δ₁ := 1 }

theorem kkD1Params_m (R : Params) : (kkD1Params R).m = R.m := rfl

theorem kkQ5_eq_pauliNum {R : Params} (hm : 0 < R.m) (hmγ : 0 < R.mγ) (hΛ : R.mγ < R.Λ) {t : ℝ}
    {L : ℂ} (hL : Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (kkScl R.mγ R.Λ t ε))
      (𝓝[>] 0) (𝓝 L)) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    kkQ5 R t u = kkVtxC R * L * pauliNum R.m (curveMomentum R.m u) (restMomentum R.m)
      (ctLimitV .d1At1 (kkD1Params R) (restMomentum R.m) (curveMomentum R.m u)) := by
  rw [ctLimitV_d1_eq_vertexOneLoop (Or.inl rfl) (kkD1Params R) hm hmγ (hmγ.trans hΛ)
    (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu) (restMomentum_pos hm)
    (curveMomentum_pos hm hu), pauliNum_smul, pauliNum_eq_sum_idx]
  simp only [kkQ5, kkPW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [kkQ_five_eq R _ _ _ _ _ hm hmγ hΛ (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
    (restMomentum_pos hm) (curveMomentum_pos hm hu) hL]
  simp only [kkD1Params, Complex.ofReal_one, one_mul]
  ring

/-- **The sum of the twelve longitudinal Pauli limits from the scalar limit `L`**:
`kkSumP = kCst · (2π)⁴/(Λ² - m_γ²) · L · d1Zero` (charge `1`, `δ₁ = 1`). -/
theorem kkSumP_eq (P₀ : Params) (hm : 0 < P₀.m) {mγ Λ T : ℝ} (hmγ : 0 < mγ) (hΛ : mγ < Λ)
    (hT : 4 ≤ T) {L : ℂ} (hL : Tendsto (fun ε => QED.OneLoop.energyFirstIntegral
      (kkScl mγ Λ (√(P₀.m ^ 2 * T) / 2) ε)) (𝓝[>] 0) (𝓝 L)) :
    kkSumP P₀ mγ Λ T = kCst { P₀ with mγ := mγ, Λ := Λ } *
      (kkVtxC { P₀ with mγ := mγ, Λ := Λ } * L *
        QED.TwoLoop.PauliZeroExplicit.d1Zero (kkD1Params { P₀ with mγ := mγ, Λ := Λ })) := by
  set R : Params := { P₀ with mγ := mγ, Λ := Λ }
  have hd := QED.TwoLoop.PauliZeroExplicit.tendsto_d1_explicit (c := .d1At1) (Or.inl rfl)
    (kkD1Params R) hm hmγ (hmγ.trans hΛ)
  simp only [kkD1Params_m] at hd
  refine tendsto_nhds_unique (tendsto_kkQ_five P₀ hm hmγ hΛ hT)
    (((hd.const_mul (kkVtxC R * L)).const_mul (kCst R)).congr' ?_)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioo_mem_nhds
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))] with u (hu0 : u ≠ 0) hu
  simp only [evenQuot]
  rw [kkQ5_eq_pauliNum (R := R) hm hmγ hΛ hL hu,
    kkQ5_eq_pauliNum (R := R) hm hmγ hΛ hL (neg_mem_Ioo_one' hu)]
  ring

/-- **The value of the scalar tadpole** at the spectral masses above threshold: the
energy-first integral of `kkScl` at `t = √(m² T)/2` tends to `4 i π² ∫₀^∞ R_T / (Λ² - m_γ²)²`. -/
def IsKKSclLim (m : ℝ) : Prop :=
  ∀ mγ Λ T : ℝ, 0 < mγ → mγ < Λ → 4 ≤ T →
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (kkScl mγ Λ (√(m ^ 2 * T) / 2) ε))
      (𝓝[>] 0) (𝓝 (((4 * Real.pi ^ 2 * photonTail (vpPhotonT m mγ Λ T) 0 /
        (Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ) * I))

/-- **The cancellation above threshold in its Pauli-limit form, from the scalar tadpole.** -/
theorem isKKSumGe_of_sclLim (P₀ : Params) (hm : 0 < P₀.m) (hS : IsKKSclLim P₀.m) :
    IsKKSumGe P₀ := by
  intro mγ Λ T hmγ hΛ hT
  rw [kkSumP_eq P₀ hm hmγ hΛ hT (hS mγ Λ T hmγ hΛ hT)]
  have hB := QED.TwoLoop.UnitLLink.oneLoopPauliZero_eq
    (kkD1Params { P₀ with mγ := mγ, Λ := Λ }) hm hmγ (hmγ.trans hΛ)
  simp only [kkD1Params] at hB
  have hd : (Λ ^ 2 - mγ ^ 2 : ℝ) ≠ 0 := by nlinarith
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hm' : P₀.m ≠ 0 := hm.ne'
  simp only [kCst, kkVtxC, QED.TwoLoop.PauliZeroExplicit.d1Zero, kkD1Params, hB]
  set A := photonTail (vpPhotonT P₀.m mγ Λ T) 0
  set F := oneLoopF2 P₀.m mγ - oneLoopF2 P₀.m Λ
  have key : (QED.TwoLoop.ClassLimit.twoLoopNorm * ((I * (P₀.e : ℂ)) ^ 5 * (1 / I) ^ 4) *
      ((1 / I) * ((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ))) *
      ((((2 * Real.pi) ^ 4 / (Λ ^ 2 - mγ ^ 2) : ℝ) : ℂ) *
        (((4 * Real.pi ^ 2 * A / (Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ) * I) *
        (((1 : ℝ) : ℂ) * I * (((1 : ℝ) : ℂ) * (4 * (P₀.m : ℂ) ^ 2) ^ 3 *
          (((1 : ℝ) ^ 2 / (8 * Real.pi ^ 2) * (2 * F) : ℝ) : ℂ) / (P₀.m : ℂ)))) =
      ((-(4 * P₀.e ^ 5 * P₀.m ^ 5 / (Real.pi ^ 4 * (Λ ^ 2 - mγ ^ 2) ^ 2) * A * F) : ℝ) : ℂ) := by
    simp only [QED.TwoLoop.ClassLimit.twoLoopNorm]
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [key, Complex.ofReal_re]

/-- **The cancellation of the longitudinal parts above threshold, from the scalar tadpole.** -/
theorem isKKCancelGe_of_sclLim (P₀ : Params) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hS : IsKKSclLim P₀.m) : IsKKCancelGe P₀ :=
  (isKKCancelGe_iff P₀ he hm.ne').2 (isKKSumGe_of_sclLim P₀ hm hS)

end QED.ChainProof.SetCRegDisp

end
