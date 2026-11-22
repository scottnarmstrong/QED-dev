/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegPieceE
public import QED.ChainProof.SetCRegBndCoincidence
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Set (c): regulator limits under an almost-everywhere spectral bound

The spectral variable is integrated against Lebesgue measure. For each fixed
regulator pair the uniform bound can therefore omit a null set, which pulls
back to a null set in each of the three dispersion terms.
-/

@[expose] public section

open Complex Real Set Filter Topology MeasureTheory
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCK QED.ChainProof.SetCPauli QED.ChainProof.SetCMain

/-- **A regulated piece with an almost-everywhere spectral bound**
`a mγ Λ T → A T` for every `T ≥ 4` as
`(mγ, Λ) → (0⁺, ∞)`, eventually `T ↦ a mγ Λ (max T 4)` measurable, and `|a mγ Λ T| ≤ C/√T`
for almost every `T ≥ 4`, uniformly for small `mγ`, large `Λ`. -/
structure IsRegPieceAE (a : ℝ → ℝ → ℝ → ℝ) (A : ℝ → ℝ) : Prop where
  meas : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, Measurable fun T => a p.1 p.2 (max T 4)
  lim : ∀ T, 4 ≤ T → Tendsto (fun p : ℝ × ℝ => a p.1 p.2 T) (𝓝[>] 0 ×ˢ atTop) (𝓝 (A T))
  bound : ∃ C δ Λ₀ : ℝ, 0 < δ ∧ ∀ mγ Λ, 0 < mγ → mγ < δ → Λ₀ < Λ →
    ∀ᵐ T ∂volume.restrict (Ici (4 : ℝ)),
    |a mγ Λ T| ≤ C / √T

variable {a a' : ℝ → ℝ → ℝ → ℝ} {A A' : ℝ → ℝ}

/-- A pointwise uniform bound supplies an almost-everywhere uniform bound. -/
theorem IsRegPieceE.isRegPieceAE (h : IsRegPieceE a A) : IsRegPieceAE a A where
  meas := h.meas
  lim := h.lim
  bound := by
    obtain ⟨C, δ, Λ₀, hδ, hC⟩ := h.bound
    refine ⟨C, δ, Λ₀, hδ, fun mγ Λ h0 h1 h2 => ?_⟩
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ici] with T hT
    exact hC mγ Λ h0 h1 h2 T hT

theorem IsRegPieceAE.add (h : IsRegPieceAE a A) (h' : IsRegPieceAE a' A') :
    IsRegPieceAE (fun mγ Λ T => a mγ Λ T + a' mγ Λ T) (fun T => A T + A' T) where
  meas := by
    filter_upwards [h.meas, h'.meas] with p hp hp'
    exact hp.add hp'
  lim T hT := (h.lim T hT).add (h'.lim T hT)
  bound := by
    obtain ⟨C, δ, Λ₀, hδ, hC⟩ := h.bound
    obtain ⟨C', δ', Λ₀', hδ', hC'⟩ := h'.bound
    refine ⟨C + C', min δ δ', max Λ₀ Λ₀', lt_min hδ hδ', fun mγ Λ h0 h1 h2 => ?_⟩
    have b₁ := hC mγ Λ h0 (h1.trans_le (min_le_left _ _)) ((le_max_left _ _).trans_lt h2)
    have b₂ := hC' mγ Λ h0 (h1.trans_le (min_le_right _ _)) ((le_max_right _ _).trans_lt h2)
    filter_upwards [b₁, b₂] with T hT₁ hT₂
    rw [add_div]
    exact (abs_add_le _ _).trans (add_le_add hT₁ hT₂)

/-- Each flavour's spectral map pulls back Lebesgue null sets to null sets on `(0, 1)`. -/
theorem ae_setCKSpecMass {P : ℝ → Prop} {s : ℝ} (hs : 1 ≤ s)
    (h : ∀ᵐ T ∂volume.restrict (Ici (4 : ℝ)), P T) :
    ∀ᵐ v ∂volume.restrict (Ioo (0 : ℝ) 1), P (s * setCKSpecMass v) := by
  let bad : Set ℝ := {T | ¬ P T} ∩ Ioi (4 * s)
  let g : ℝ → ℝ := fun T => √(1 - 4 * s / T)
  have hs₀ : 0 < s := by linarith
  have hb : volume bad = 0 := by
    apply measure_mono_null _ (ae_iff.1 ((ae_restrict_iff' measurableSet_Ici).1 h))
    intro T hT
    change ¬ (4 ≤ T → P T)
    have ht : 4 * s < T := hT.2
    exact fun h' => hT.1 (h' (by linarith))
  have hg : DifferentiableOn ℝ g bad := by
    intro T hT
    have ht : 4 * s < T := hT.2
    have ht₀ : 0 < T := (by positivity : 0 < 4 * s).trans ht
    have harg : 0 < 1 - 4 * s / T := sub_pos.2 ((div_lt_one ht₀).2 ht)
    exact ((differentiableAt_const _).sub
      ((differentiableAt_const _).div differentiableAt_id ht₀.ne')).sqrt
        harg.ne' |>.differentiableWithinAt
  have hnull := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hg hb
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with v hv h01
  by_contra hv'
  have hw : 0 < 1 - v ^ 2 := by nlinarith [h01.1, h01.2]
  have he : s * setCKSpecMass v = (4 * s) / (1 - v ^ 2) := by
    unfold setCKSpecMass
    ring
  have ht : 4 * s < s * setCKSpecMass v := by
    rw [he, lt_div_iff₀ hw]
    nlinarith [mul_pos hs₀ (sq_pos_of_pos h01.1)]
  apply hv
  refine ⟨s * setCKSpecMass v, ⟨hv', ht⟩, ?_⟩
  have hts : 0 < s * setCKSpecMass v := by linarith
  dsimp [g]
  have e : 1 - 4 * s / (s * setCKSpecMass v) = v ^ 2 := by
    rw [he]
    field_simp
    ring
  rw [e, Real.sqrt_sq h01.1.le]

/-- **Dominated convergence in the spectral variable**: for a regulated kernel of the set (c) kernel
sum, the regulated dispersion integral tends to `K(1) + c₁ K(s₁) + c₂ K(s₂)`. -/
theorem tendsto_jDisp_of_AE {a : ℝ → ℝ → ℝ → ℝ} (h : IsRegPieceAE a setCKKernelPairSum) {s₁ s₂ : ℝ}
    (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (c₁ c₂ : ℝ) :
    Tendsto (fun p : ℝ × ℝ => jDisp a s₁ s₂ c₁ c₂ p.1 p.2) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (kDisp 1 + c₁ * kDisp s₁ + c₂ * kDisp s₂)) := by
  obtain ⟨C, δ, Λ₀, hδ, hC⟩ := h.bound
  have hmt : Measurable setCKSpecMass := by unfold setCKSpecMass; fun_prop
  have hmρ : Measurable setCKSpecRho := by unfold setCKSpecRho; fun_prop
  have hk : ∀ s, kDisp s = ∫ v in Ioo (0 : ℝ) 1,
      setCKSpecRho v * setCKKernelPairSum (s * setCKSpecMass v) := fun s => by
    rw [kDisp, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have i₀ := integrableOn_kDisp (s := 1) le_rfl
  have i₁ := integrableOn_kDisp hs₁
  have i₂ := integrableOn_kDisp hs₂
  have i01 : IntegrableOn (fun v => setCKSpecRho v * setCKKernelPairSum (1 * setCKSpecMass v) +
      c₁ * (setCKSpecRho v * setCKKernelPairSum (s₁ * setCKSpecMass v))) (Ioo 0 1) :=
    i₀.add (i₁.const_mul c₁)
  have hlimv : kDisp 1 + c₁ * kDisp s₁ + c₂ * kDisp s₂ = ∫ v in Ioo (0 : ℝ) 1,
      setCKSpecRho v * (setCKKernelPairSum (setCKSpecMass v) +
        c₁ * setCKKernelPairSum (s₁ * setCKSpecMass v) +
        c₂ * setCKKernelPairSum (s₂ * setCKSpecMass v)) := by
    have e : ∫ v in Ioo (0 : ℝ) 1, setCKSpecRho v * (setCKKernelPairSum (setCKSpecMass v) +
        c₁ * setCKKernelPairSum (s₁ * setCKSpecMass v) +
        c₂ * setCKKernelPairSum (s₂ * setCKSpecMass v)) = ∫ v in Ioo (0 : ℝ) 1,
        ((setCKSpecRho v * setCKKernelPairSum (1 * setCKSpecMass v) +
          c₁ * (setCKSpecRho v * setCKKernelPairSum (s₁ * setCKSpecMass v))) +
          c₂ * (setCKSpecRho v * setCKKernelPairSum (s₂ * setCKSpecMass v))) :=
      setIntegral_congr_fun measurableSet_Ioo fun v _ => by simp only [one_mul]; ring
    rw [e, integral_add i01 (i₂.const_mul c₂), integral_add i₀ (i₁.const_mul c₁),
      integral_const_mul, integral_const_mul, hk, hk, hk]
  rw [hlimv]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun v => |C| * (1 + |c₁| + |c₂|) * (1 - v) ^ (-(1 / 2 : ℝ))) ?_ ?_
    (integrableOn_one_sub_rpow.const_mul _) ?_
  · filter_upwards [h.meas] with p hp
    have ha := measurable_regCut a p.1 p.2
    have hcut : Measurable fun v => setCKSpecRho v *
        (regCut a p.1 p.2 (setCKSpecMass v) +
          c₁ * regCut a p.1 p.2 (s₁ * setCKSpecMass v) +
          c₂ * regCut a p.1 p.2 (s₂ * setCKSpecMass v)) := by
      fun_prop
    refine hcut.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have ht := (four_le_mul_setCKSpecMass le_rfl hv).trans_eq (one_mul _)
    rw [regCut_eq hp ht, regCut_eq hp (four_le_mul_setCKSpecMass hs₁ hv),
      regCut_eq hp (four_le_mul_setCKSpecMass hs₂ hv)]
  · filter_upwards [eventually_regRange hδ Λ₀] with p hp
    have hb := hC p.1 p.2 hp.1 hp.2.1 hp.2.2
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_setCKSpecMass le_rfl hb, ae_setCKSpecMass hs₁ hb, ae_setCKSpecMass hs₂ hb] with
      v hv hv₀ hv₁ hv₂
    have hρ := setCKSpecRho_nonneg hv
    have b₀ := rho_mul_abs_le (a := a p.1 p.2) le_rfl hv hv₀
    have b₁ := rho_mul_abs_le (a := a p.1 p.2) hs₁ hv hv₁
    have b₂ := rho_mul_abs_le (a := a p.1 p.2) hs₂ hv hv₂
    simp only [one_mul] at b₀
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ]
    have tri := abs_add3_le (a p.1 p.2 (setCKSpecMass v)) (a p.1 p.2 (s₁ * setCKSpecMass v))
      (a p.1 p.2 (s₂ * setCKSpecMass v)) c₁ c₂
    calc setCKSpecRho v * |a p.1 p.2 (setCKSpecMass v) +
          c₁ * a p.1 p.2 (s₁ * setCKSpecMass v) + c₂ * a p.1 p.2 (s₂ * setCKSpecMass v)|
        ≤ setCKSpecRho v * |a p.1 p.2 (setCKSpecMass v)| +
          |c₁| * (setCKSpecRho v * |a p.1 p.2 (s₁ * setCKSpecMass v)|) +
          |c₂| * (setCKSpecRho v * |a p.1 p.2 (s₂ * setCKSpecMass v)|) := by
          nlinarith [mul_le_mul_of_nonneg_left tri hρ]
      _ ≤ |C| * (1 - v) ^ (-(1 / 2 : ℝ)) + |c₁| * (|C| * (1 - v) ^ (-(1 / 2 : ℝ))) +
          |c₂| * (|C| * (1 - v) ^ (-(1 / 2 : ℝ))) := by
          gcongr
      _ = |C| * (1 + |c₁| + |c₂|) * (1 - v) ^ (-(1 / 2 : ℝ)) := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact (((h.lim _ (four_le_mul_setCKSpecMass le_rfl hv |>.trans_eq (one_mul _))).add
      ((h.lim _ (four_le_mul_setCKSpecMass hs₁ hv)).const_mul c₁)).add
      ((h.lim _ (four_le_mul_setCKSpecMass hs₂ hv)).const_mul c₂)).const_mul _

open QED.TwoLoop.VPUnit
open QED.OneLoop.VertexLimit (chargeA0)

/-- At fixed positive photon masses, the exceptional heavy coincidence is Lebesgue null. -/
theorem ae_ne_heavy_spectral_mass (m Λ : ℝ) :
    ∀ᵐ T ∂volume.restrict (Ici (4 : ℝ)), T ≠ (Λ / m) ^ 2 :=
  measure_eq_zero_iff_ae_notMem.1
    (measure_mono_null (μ := volume.restrict (Ici (4 : ℝ))) (subset_refl _)
      (by simp : volume.restrict (Ici (4 : ℝ)) ({(Λ / m) ^ 2} : Set ℝ) = 0))

/-- The counterterm equals the dressed-photon integral almost everywhere in the spectral mass. -/
theorem ae_cbVPKer_eq_integral (P₀ : Params) {mγ Λ : ℝ} (hm : 0 < P₀.m)
    (hmγ : 0 < mγ) (hmΛ : mγ < Λ) (hm2 : mγ < 2 * P₀.m) :
    ∀ᵐ T ∂volume.restrict (Ici (4 : ℝ)),
      cbVPKer P₀ mγ Λ T = -(chargeA0 P₀.e P₀.m mγ Λ : ℂ) * I *
        ((P₀.e ^ 4 / (16 * π ^ 4) *
          (∫ x in (0 : ℝ)..1, regKernel T ((mγ / P₀.m) ^ 2) ((Λ / P₀.m) ^ 2) x) : ℝ) : ℂ) := by
  filter_upwards [ae_restrict_mem measurableSet_Ici, ae_ne_heavy_spectral_mass P₀.m Λ] with
    T hT hTb
  change 4 ≤ T at hT
  have ha : 0 < mγ / P₀.m := div_pos hmγ hm
  have hab : mγ / P₀.m < Λ / P₀.m := div_lt_div_of_pos_right hmΛ hm
  have ha2 : mγ / P₀.m < 2 := (div_lt_iff₀ hm).2 (by linarith)
  have hTa : (mγ / P₀.m) ^ 2 < T := by
    have := pow_lt_pow_left₀ ha2 ha.le (by decide : 2 ≠ 0)
    linarith
  unfold cbVPKer
  rw [vpInsert_eq_integral (sq_pos_of_pos ha) (sq_pos_of_pos (ha.trans hab))
    (by linarith) hTa.ne' hTb (pow_lt_pow_left₀ hab ha.le (by decide : 2 ≠ 0)).ne]

/-- The true spectral Pauli integral has the inverse-mass-squared bound even at coincidence. -/
theorem abs_integral_regKernel_le {a b T : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hT : 0 < T) :
    |∫ x in (0 : ℝ)..1, regKernel T a b x| ≤ 1 / (3 * T) := by
  obtain ⟨h0, h1⟩ := integral_regKernel_le hT ha hab
  rwa [abs_of_nonneg h0]

open QED.TwoLoop.UnitLLink (oneLoopF2)

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
theorem measurable_setCKerRe_cut_of_isKKCancel (P₀ : Params)
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hKK : IsKKCancel P₀)
    {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : mγ < Λ) :
    Measurable fun T => setCKerRe P₀ (uBD P₀) mγ Λ (max T 4) := by
  simp_rw [setCKerRe_eq_feyn he hm hKK hmγ hΛ]
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
theorem isRegPieceAE_of_centered_main (P₀ : Params) {A : ℝ → ℝ}
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hKK : IsKKCancel P₀)
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
    exact measurable_setCKerRe_cut_of_isKKCancel P₀ he hm hKK hp.1 (hp.2.1.trans hp.2.2)
  lim := hlim
  bound := by
    obtain ⟨C, δ, Λ₀, hδ, hC⟩ := hMain
    refine ⟨C + 56, min δ 1, max Λ₀ 1, lt_min hδ one_pos, fun mγ Λ h0 h1 h2 => ?_⟩
    have hγΛ := (h1.trans_le (min_le_right δ 1)).trans ((le_max_right Λ₀ 1).trans_lt h2)
    have hb := hC mγ Λ h0 (h1.trans_le (min_le_left δ 1))
      ((le_max_left Λ₀ 1).trans_lt h2) hγΛ
    filter_upwards [ae_restrict_mem measurableSet_Ici, hb] with T hT h
    rw [setCKerRe_eq_feyn he hm hKK h0 hγΛ, kerRe_split_uSF]
    have hS := abs_kerRe_uSF_add_tail_le P₀ he hm h0 hγΛ.le
      ((by norm_num : (1 : ℝ) ≤ 4).trans hT)
    have e (a b q : ℝ) : |a + b| ≤ |a - q| + |b + q| := by
      rw [show a + b = (a - q) + (b + q) by ring]
      exact abs_add_le _ _
    exact (e _ _ _).trans ((add_le_add h hS).trans_eq (add_div _ _ _).symm)

/-! ### The regulator limit of set (c) -/

section Kernels

variable {P₀ : Params} {βM : MainIdx → ClsPauliVal} {uBD : Fin 12 → ℝ → ℝ → ℝ → ℂ}
  {uCB uS : Fin 5 → ℝ → ℝ → ℝ → ℂ}

/-- **The regulator limit from the dispersion form of the class values and the regulator limit
of the real part of the total kernel**, with an almost-everywhere bound. -/
theorem setCRegLimitDisp_of_kernelsAE (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hMainBD : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ i : Fin 12,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uBD i mγ Λ) (βM (.inl i) M₁ M₂ c₁ c₂ mγ Λ D s +
        βM (.inr (i, 0)) M₁ M₂ c₁ c₂ mγ Λ D s + βM (.inr (i, 1)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtCB : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uCB k mγ Λ) (ctPauliAll P₀ (.inl k) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 0))) M₁ M₂ c₁ c₂ mγ Λ D s +
        ctPauliAll P₀ (.inr (.inl (k, 1))) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hCtS : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s → ∀ k : Fin 5,
      IsDispPV P₀.m M₁ M₂ c₁ c₂ (uS k mγ Λ) (ctPauliAll P₀ (.inr (.inr k)) M₁ M₂ c₁ c₂ mγ Λ D s))
    (hReg : IsRegPieceAE (kerRe P₀ uBD uCB uS) setCKKernelPairSum) :
    SetCRegLimitDisp P₀ (setCPauliB P₀ βM) := by
  refine setCRegLimitDisp_of_fixLim hm fun M₁ M₂ c₁ c₂ hM₁ hM₂ hc hc' η hη => ?_
  set K : ℝ := P₀.e ^ 6 / (64 * π ^ 6) with hK
  have hlim := (tendsto_jDisp_of_AE hReg (one_le_sq_div hm hM₁) (one_le_sq_div hm hM₂) c₁
    c₂).const_mul K
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := exists_of_eventually_regRange (Metric.tendsto_nhds.1 hlim η hη)
  refine ⟨min δ (min 1 (2 * P₀.m)), lt_min hδ (lt_min one_pos (by linarith)), max Λ₀ 1,
    fun mγ Λ h0 h1 h2 => ?_⟩
  have hδ' : mγ < δ := h1.trans_le (min_le_left _ _)
  have h1' : mγ < 1 := h1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h2m : mγ < 2 * P₀.m := h1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hΛ : Λ₀ < Λ := (le_max_left _ _).trans_lt h2
  have hmΛ : mγ < Λ := h1'.trans ((le_max_right _ _).trans_lt h2)
  have hd := hΛ₀ mγ Λ h0 hδ' hΛ
  rw [Real.dist_eq] at hd
  rw [setCPauliB_eq_kerRe hMainBD hCtCB hCtS he hM₁ hM₂ hc hc' h0 hmΛ h2m]
  have e : P₀.e ^ 6 * kDispPV P₀.m M₁ M₂ c₁ c₂ / (64 * π ^ 6) =
      K * (kDisp 1 + c₁ * kDisp (M₁ ^ 2 / P₀.m ^ 2) + c₂ * kDisp (M₂ ^ 2 / P₀.m ^ 2)) := by
    rw [hK, kDispPV]
    ring
  rw [e]
  exact hd

end Kernels

/-- **The regulator limit of set (c) from the counterterm leaves and the Stage L limit**, with
an almost-everywhere bound. -/
theorem setCRegLimitB_of_shell_cbLoAE {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hS : ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀)) (hB : CBLoBEq P₀)
    (hReg : IsRegPieceAE (setCKerRe P₀ (uBD P₀)) setCKKernelPairSum) :
    SetCRegLimitB P₀ (setCPauliB P₀ (setCBetaM P₀ fun i => clsPauliLim mainFam P₀ (.inl i))) :=
  setCRegLimitB_of_disp (setCRegLimitDisp_of_kernelsAE he hm
    (βM := setCBetaM P₀ fun i => clsPauliLim mainFam P₀ (.inl i))
    (fun _ _ _ _ _ _ _ _ hA i => isDispPV_mainBD hA i)
    (isDispPV_CB_of_loB he hB) (isDispPV_S_of_shell he hS) hReg)

end QED.ChainProof.SetCRegDisp

namespace QED.ThreeLoop

open QED.ChainProof.SetCRegDisp QED.ChainProof.SetCK

/-- **(HS₆) from the counterterm leaves and the Stage L limit**, with an almost-everywhere bound on
the total kernel. -/
theorem isFormFactorPair_vertexSetC_pauli_limit_of_shell_cbLoAE (P₀ : Params)
    (hS : ShellDisp P₀ (shellKer₀ P₀) (shellKer₁C P₀))
    (hB : CBLoBEq P₀) (hReg : IsRegPieceAE (setCKerRe P₀ (uBD P₀)) setCKKernelPairSum)
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          (∃ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s) ∧
          ∀ s : ℝ × ℝ × ℝ, IsVPShareOnShell
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D s →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) (D.withLevel 1 (fun _ => s) (D.d₃ 1))
              (fun C g => IsOnePI C ∧ IsSetC C g) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 - (a1SixSetC : ℂ)‖ < η :=
  isFormFactorPair_vertexSetC_pauli_limit_of_regB P₀
    (setCRegLimitB_of_shell_cbLoAE he hm hS hB hReg) he hm η hη

end QED.ThreeLoop

end
