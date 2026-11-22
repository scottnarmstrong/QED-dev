/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSECt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (c): the T1 sum of the vacuum-polarization self-energy limits

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`. The selected self-energy is split
into T1 parameter sets `zParams`, `gParams g` with weights `1`, `w_g`
(`SetCLink.selfEnergySelPart_split`). Here the weighted sum of their limits `seVPLim` is computed:

* `integrableOn_seGIntLim`: the `x`-integrand limit is integrable on `(0, 1)`, below threshold;
* `seGIntM`: the `x`-integrand of one loop of mass `M`, so that
  `seGIntLim S x = ∑ᵢ cᵢ(S) seGIntM(Mᵢ(S)) x` (`seGIntLim_eq_sum`);
* `gParams_eq_zParams`: the set of the open-line flavour is `zParams`, with weight `-1`;
* **`t1_sum_seVPLim`**: if every other flavour is heavier than the open line,
  `seVPLim z + ∑ w_g seVPLim g_g = ∫₀¹ ∑_g a_g seGIntM(M_g) + κ_SE (c₁ L/6 - δ₃) seCtComb`,
  `L = ∑_g a_g log M_g²` (the counterterm part is the same multiple for every set, and the
  weights resum the loop coefficients by `V5Zero.Split.loop_split`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.OneLoop
open QED.TwoLoop.VPHalfAtAssembly (cOne cTwo wOne specMu logSum)
open QED.GradedProof.SE2 (kappaSE)
open QED.ChainProof.SetCRegDispSE (seProdLim seL1 seL2 seL3 GoodEF4)
open QED.GradedProof.V5Zero.Split (zParams gParams weight loop_split sum_weight)

/-- **The `x`-integrand limit is integrable on `(0, 1)`**, below threshold. -/
theorem integrableOn_seGIntLim {P : Params} {M₀ : ℝ} (hM₀ : 0 < M₀) (hmγ : M₀ ≤ P.mγ)
    (hΛ : M₀ ≤ P.Λ) (hmass : ∀ f, M₀ ≤ P.mass f) {p : Fin 4 → ℝ}
    (hp : -(P.m + M₀) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    IntegrableOn (seGIntLim P p α β) (Ioo (0 : ℝ) 1) := by
  have hm : 0 < P.m := hM₀.trans_le (hmass 0)
  have hpp : Minkowski.dot (-p) (-p) = Minkowski.dot p p := by
    simp only [Minkowski.dot, Pi.neg_apply]; ring_nf
  obtain ⟨c₀, hc₀, hPc⟩ := exists_pos_le_selfEnergyFeynmanMass hm hM₀ (hpp ▸ hp)
  obtain ⟨KL, hKL, hL⟩ := exists_seEngU_seAff hM₀.le hc₀ hPc (seCL P p α β) 3 α β
  obtain ⟨KG, hKG, hG⟩ := exists_seEngU_seAff hM₀.le hc₀ hPc (seCG P p α β) 2 α β
  obtain ⟨KQ, hKQ, hQ⟩ := exists_seEngU_seQuad hM₀.le hc₀ hPc p α β
  have hL' := hL.mono (K := KL + KG + KQ) (by linarith)
  have hQ' := hQ.mono (K := KL + KG + KQ) (by linarith)
  have hG' := hG.mono (K := KL + KG + KQ) (by linarith)
  have hK0 : 0 ≤ KL + KG + KQ := by positivity
  obtain ⟨C, hC⟩ := exists_goodEF4_seGInt_unif hM₀ hmγ hΛ hmass hK0 hL' hQ' hG'
  have hlim : ∀ x ∈ Ioo (0 : ℝ) 1, Tendsto
      (fun ε => energyFirstIntegral (seGInt (withEps P ε) p α β x)) (𝓝[>] 0)
      (𝓝 (seGIntLim P p α β x)) := fun x hx =>
    tendsto_efi_seGInt hM₀ hmγ hΛ hmass hK0 hL' hQ' hG' (seLimU_seAff hM₀.le hc₀ hPc _ _ α β)
      (seLimU_seQuad hM₀.le hc₀ hPc p α β) (seLimU_seAff hM₀.le hc₀ hPc _ _ α β) hx
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT zero_lt_one
  have hbd : ∀ x ∈ Ioo (0 : ℝ) 1,
      ‖seGIntLim P p α β x‖ ≤ C * ∫ v : Fin 3 → ℝ, (1 + ‖v‖) ^ (-(4 : ℝ)) := fun x hx =>
    le_of_tendsto (hlim x hx).norm (hev.mono fun ε hε => (hC ε hε x hx).norm_efi_le)
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  have hae : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  have hmeas : AEStronglyMeasurable (seGIntLim P p α β) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ))
      (f := fun ε x => energyFirstIntegral (seGInt (withEps P ε) p α β x)) (fun ε => ?_)
      (hae.mono fun x hx => hlim x hx)
    have hm := (measurable_seGInt (withEps P ε) p α β).stronglyMeasurable
    exact (hm.integral_prod_right' (ν := (volume : Measure ℝ))).integral_prod_left'
      (μ := (volume : Measure (Fin 3 → ℝ))) |>.aestronglyMeasurable
  exact Integrable.mono' (integrable_const _) hmeas (hae.mono fun x hx => hbd x hx)

theorem intervalIntegrable_seGIntLim {P : Params} {M₀ : ℝ} (hM₀ : 0 < M₀) (hmγ : M₀ ≤ P.mγ)
    (hΛ : M₀ ≤ P.Λ) (hmass : ∀ f, M₀ ≤ P.mass f) {p : Fin 4 → ℝ}
    (hp : -(P.m + M₀) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    IntervalIntegrable (seGIntLim P p α β) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact (integrableOn_Ioc_iff_integrableOn_Ioo).2
    (integrableOn_seGIntLim hM₀ hmγ hΛ hmass hp α β)

/-! ### One loop of mass `M` -/

/-- The `x`-integrand limit of one loop of mass `M` and coefficient `1`. -/
noncomputable def seGIntM (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (x M : ℝ) : ℂ :=
  seVK P * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ) * ((1 - 2 * x : ℝ) : ℂ) * ((M ^ 2 : ℝ) : ℂ)⁻¹ *
    (I * cOne P * wOne x *
      (seL2 0 (seAff (seCL P p α β) 3 α β) P.m (seMs4 P) (-p) -
        2 * seL1 (seQuadA p α β) (seQuad p α β) P.m (seMs4 P) (-p) -
        seL3 0 (seAff (seCL P p α β) 3 α β) P.m (seMs5 P (specMu M x)) (-p) +
        2 * seL2 (seQuadA p α β) (seQuad p α β) P.m (seMs5 P (specMu M x)) (-p)))

theorem seGIntLim_eq_sum (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (x : ℝ) :
    seGIntLim P p α β x = ∑ i, P.loopCoeff i • seGIntM P p α β x (P.mass i) := by
  simp only [seGIntLim, seCfLim, sePieceLim, seGIntM, Complex.real_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem logSum_zero_eq_sum (P : Params) :
    logSum P 0 = ∑ i, P.loopCoeff i • log (((P.mass i ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) := by
  simp only [logSum, Complex.real_smul]

/-! ### The T1 sum -/

section T1

variable {F : Type} (Q : Params) (Φ : Lepton.Flavors F) (X : ℝ)

/-- The set of the open-line flavour is `zParams`. -/
theorem gParams_eq_zParams (hQm : Q.m = Φ.mass Φ.openLine) (hXm : X ^ 2 ≠ Q.m ^ 2) :
    gParams Q Φ X Φ.openLine = zParams Q X := by
  have h : QED.Lepton.Proof.HM.auxC₁ Q.m X Q.m = -1 := by
    rw [QED.Lepton.Proof.HM.auxC₁]
    have : Q.m ^ 2 - X ^ 2 ≠ 0 := sub_ne_zero.mpr hXm.symm
    field_simp
    ring
  simp only [gParams, zParams, h, ← hQm]
  norm_num

/-- The weight of the open-line flavour. -/
theorem weight_openLine (hQm : Q.m = Φ.mass Φ.openLine) (hco : Φ.coeff Φ.openLine = 1)
    (hXm : X ^ 2 ≠ Q.m ^ 2) : weight Q Φ X Φ.openLine = -1 := by
  have : X ^ 2 - Q.m ^ 2 ≠ 0 := sub_ne_zero.mpr hXm
  rw [weight, hco, ← hQm]
  field_simp
  ring

variable [Fintype F] [DecidableEq F] {Q Φ X}

/-- **The T1 sum of the limits `seVPLim`**: if every flavour other than the open line is heavier
than it, the weighted sum is the `x`-integral of the flavour sum of one-loop integrands plus
`κ_SE (c₁ L/6 - δ₃)` times the counterterm integral, `L = ∑_g a_g log M_g²`. -/
theorem t1_sum_seVPLim (hm : 0 < Q.m) (hγ : 0 < Q.mγ) (hΛ : 0 < Q.Λ)
    (hQm : Q.m = Φ.mass Φ.openLine) (hco : Φ.coeff Φ.openLine = 1)
    (hgt : ∀ g, g ≠ Φ.openLine → Q.m < Φ.mass g) (hPV₁ : ∑ g, Φ.coeff g = 0)
    (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) (hmX : Q.m < X) (hXm : X ^ 2 ≠ Q.m ^ 2)
    (hX : ∀ g, Φ.mass g ^ 2 ≠ X ^ 2) {ν : ℝ} (hν0 : 0 < ν) (hν : ν ≤ min Q.mγ Q.Λ)
    (hνm : ν ≤ Q.m) {p : Fin 4 → ℝ} (hp : -(Q.m + ν) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    SetCLink.seVPLim (zParams Q X) p α β +
        ∑ g, (weight Q Φ X g : ℂ) * SetCLink.seVPLim (gParams Q Φ X g) p α β =
      (∫ x in (0 : ℝ)..1, ∑ g, Φ.coeff g • seGIntM Q p α β x (Φ.mass g)) +
        kappaSE Q.e * (cOne Q * (1 / 6) *
          ∑ g, Φ.coeff g • log (((Φ.mass g ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) - Q.δ₃) *
          seCtComb Q p α β := by
  have hmassΦ : ∀ g, ν ≤ Φ.mass g := fun g => by
    by_cases h : g = Φ.openLine
    · rw [h, ← hQm]; exact hνm
    · exact hνm.trans (hgt g h).le
  have hνX : ν ≤ X := hνm.trans hmX.le
  have hγν : ν ≤ Q.mγ := hν.trans (min_le_left _ _)
  have hΛν : ν ≤ Q.Λ := hν.trans (min_le_right _ _)
  set T : Params → ℂ := fun S => (∫ x in (0 : ℝ)..1, seGIntLim S p α β x) +
    kappaSE Q.e * (cOne Q * (1 / 6) * logSum S 0 - Q.δ₃) * seCtComb Q p α β with hT
  have hVg : ∀ g, g ≠ Φ.openLine →
      SetCLink.seVPLim (gParams Q Φ X g) p α β = T (gParams Q Φ X g) := fun g hg =>
    seVPLim_eq (Q := gParams Q Φ X g) hm (hgt g hg) hmX hγ hΛ
      (QED.GradedProof.V5Zero.Split.gParams_PV₁ Q Φ X g)
      (QED.GradedProof.V5Zero.Split.gParams_PV₂ Q Φ X g (hX g)) hν0 hν hνm hp α β
  have hzo := gParams_eq_zParams Q Φ X hQm hXm
  have hwo := weight_openLine Q Φ X hQm hco hXm
  have hmem : Φ.openLine ∈ (Finset.univ : Finset F) := Finset.mem_univ _
  have hL : SetCLink.seVPLim (zParams Q X) p α β +
      ∑ g, (weight Q Φ X g : ℂ) * SetCLink.seVPLim (gParams Q Φ X g) p α β =
      ∑ g ∈ Finset.univ.erase Φ.openLine, (weight Q Φ X g : ℂ) * T (gParams Q Φ X g) := by
    rw [← Finset.add_sum_erase _ _ hmem, hzo, hwo,
      Finset.sum_congr rfl fun g hg => by rw [hVg g (Finset.ne_of_mem_erase hg)]]
    push_cast
    ring
  have hR : T (zParams Q X) + ∑ g, (weight Q Φ X g : ℂ) * T (gParams Q Φ X g) =
      ∑ g ∈ Finset.univ.erase Φ.openLine, (weight Q Φ X g : ℂ) * T (gParams Q Φ X g) := by
    rw [← Finset.add_sum_erase _ _ hmem, hzo, hwo]
    push_cast
    ring
  rw [hL, ← hR]
  -- the integrals
  have hIz : IntervalIntegrable (seGIntLim (zParams Q X) p α β) volume 0 1 :=
    intervalIntegrable_seGIntLim (P := zParams Q X) hν0 hγν hΛν (fun f => by
      fin_cases f <;> simp [Params.mass, zParams] <;> linarith) hp α β
  have hIg : ∀ g, IntervalIntegrable (seGIntLim (gParams Q Φ X g) p α β) volume 0 1 :=
    fun g => intervalIntegrable_seGIntLim (P := gParams Q Φ X g) hν0 hγν hΛν (fun f => by
      fin_cases f <;> simp [Params.mass, gParams] <;> linarith [hmassΦ g]) hp α β
  have hpt : ∀ x, seGIntLim (zParams Q X) p α β x +
      ∑ g, (weight Q Φ X g : ℂ) * seGIntLim (gParams Q Φ X g) p α β x =
      ∑ g, Φ.coeff g • seGIntM Q p α β x (Φ.mass g) := by
    intro x
    simp only [seGIntLim_eq_sum, ← Complex.real_smul]
    exact loop_split hPV₁ hPV₂ hXm hX (fun M => seGIntM Q p α β x M)
  have hint : (∫ x in (0 : ℝ)..1, seGIntLim (zParams Q X) p α β x) +
      ∑ g, (weight Q Φ X g : ℂ) * ∫ x in (0 : ℝ)..1, seGIntLim (gParams Q Φ X g) p α β x =
      ∫ x in (0 : ℝ)..1, ∑ g, Φ.coeff g • seGIntM Q p α β x (Φ.mass g) := by
    have h2 : IntervalIntegrable (fun x => ∑ g, (weight Q Φ X g : ℂ) *
        seGIntLim (gParams Q Φ X g) p α β x) volume 0 1 := by
      simpa only [Finset.sum_fn] using
        IntervalIntegrable.sum Finset.univ fun g _ => (hIg g).const_mul (weight Q Φ X g : ℂ)
    simp only [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_finsetSum fun g _ => (hIg g).const_mul _,
      ← intervalIntegral.integral_add hIz h2]
    exact intervalIntegral.integral_congr fun x _ => hpt x
  have hlog : logSum (zParams Q X) 0 + ∑ g, (weight Q Φ X g : ℂ) * logSum (gParams Q Φ X g) 0 =
      ∑ g, Φ.coeff g • log (((Φ.mass g ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) := by
    simp only [logSum_zero_eq_sum, ← Complex.real_smul]
    exact loop_split hPV₁ hPV₂ hXm hX
      (fun M => log (((M ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I))
  have hsw : ∑ g, (weight Q Φ X g : ℂ) = 0 := by
    exact_mod_cast sum_weight (Q := Q) (X := X) hPV₁ hPV₂
  set κC := kappaSE Q.e * seCtComb Q p α β
  have e : ∀ g, (weight Q Φ X g : ℂ) * T (gParams Q Φ X g) =
      (weight Q Φ X g : ℂ) * (∫ x in (0 : ℝ)..1, seGIntLim (gParams Q Φ X g) p α β x) +
        κC * cOne Q * (1 / 6) * ((weight Q Φ X g : ℂ) * logSum (gParams Q Φ X g) 0) -
        κC * Q.δ₃ * (weight Q Φ X g : ℂ) := fun g => by
    simp only [hT, κC]
    ring
  rw [Finset.sum_congr rfl fun g _ => e g, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [hT]
  linear_combination hint + κC * cOne Q * (1 / 6) * hlog - κC * Q.δ₃ * hsw

end T1

end QED.ChainProof.SetCRegDisp

end
