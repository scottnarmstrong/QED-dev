/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCFinal

/-!
# Set (c), regulator limit: the decoupling of the bubble's regulator fermions

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, regulator limit
`QED.ChainProof.SetCPauli.SetCRegLimitDisp`. A bubble flavour of mass `M` contributes the spectral
weight `ρ(v)` at the mass² `s t_v`, `s = M²/m²`, `t_v = 4/(1 - v²)`, so at photon regulators
removed the set (c) value of the flavour is the dispersion integral

`K(s) = ∫₀¹ ρ(v) A_(c)(s t_v) dv` (`kDisp`; `K(1) = setCKDisp`, `kDisp_one`).

This file proves that the two Pauli–Villars regulator flavours decouple, uniformly in the
regulator masses (the coefficients `c₁, c₂` are unbounded as `M₁ → M₂`):

* `kDisp_eq`: by the Stieltjes identity (S) (`QED.ChainProof.SetCK.isSetCKStieltjes_proved`) and
  Fubini, `K(s) = ∫₀¹ λ⁽⁴⁾(x) Π̂(Q(x)/s) dx` for `s ≥ 1`; `integrableOn_kDisp`: the integrand
  `ρ(v) A_(c)(s t_v)` is integrable;
* `piHat_nonneg_spec`, `piHat_le_quarter` (`Π̂(y) ≤ y/4`), `piHat_mono_spec`;
* `abs_pvComb_le`: for `1 + c₁ + c₂ = 0`, `1 + c₁ s₁ + c₂ s₂ = 0`,
  `|c₁ Q/(Q + s₁ t) + c₂ Q/(Q + s₂ t)| ≤ Q/(Q + s₁ t) + Q/(Q + s₂ t)`;
* `abs_pvComb_kDisp_le`: `|c₁ K(s₁) + c₂ K(s₂)| ≤ T(s₁) + T(s₂)`, `T(s) = ∫|λ⁽⁴⁾| Π̂(Q/s)`;
* `tendsto_kTail`: `T(s) → 0` as `s → ∞` (dominated convergence);
* **`kDisp_decouple`**: `|c₁ K(s₁) + c₂ K(s₂)| < η` for `s₁, s₂ ≥ R(η)`, under the PV conditions.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCRegDisp

open QED.Chain QED.ChainProof.SetCK

/-! ### The spectral weight and `Π̂` -/

theorem setCKSpecMass_pos {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) : 0 < setCKSpecMass v :=
  div_pos (by norm_num) (by nlinarith [hv.1, hv.2])

theorem setCKSpecRho_nonneg {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) : 0 ≤ setCKSpecRho v := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have : 0 ≤ 1 - v ^ 2 / 3 := by nlinarith [hv.1, hv.2]
  unfold setCKSpecRho
  positivity

theorem piHat_nonneg_spec {y : ℝ} (hy : 0 ≤ y) : 0 ≤ piHat y := by
  rw [← (integral_setCKSpec hy).2]
  exact setIntegral_nonneg measurableSet_Ioo fun v hv => setCKSpec_nonneg hy hv

/-- `Π̂(y) ≤ y/4` for `y ≥ 0`. -/
theorem piHat_le_quarter {y : ℝ} (hy : 0 ≤ y) : piHat y ≤ y / 4 := by
  rw [← (integral_setCKSpec hy).2]
  have hc : IntegrableOn (fun _ : ℝ => y / 4) (Ioo 0 1) := integrableOn_const (by simp)
  refine (setIntegral_mono_on (integral_setCKSpec hy).1 hc measurableSet_Ioo
    fun v hv => ?_).trans_eq (by simp)
  rw [setCKSpec_eq hy hv]
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have hd : 0 < (1 - v ^ 2) * y + 4 := by nlinarith [mul_nonneg h1.le hy]
  rw [div_le_iff₀ hd]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
  nlinarith [mul_nonneg (pow_nonneg hv.1.le 4) hy, mul_nonneg h1.le (mul_nonneg hy hy),
    mul_nonneg (sub_nonneg.2 hv2) hy]

/-- `Π̂` is monotone on `[0, ∞)`. -/
theorem piHat_mono_spec {y y' : ℝ} (hy : 0 ≤ y) (hyy : y ≤ y') : piHat y ≤ piHat y' := by
  have hy' : 0 ≤ y' := hy.trans hyy
  rw [← (integral_setCKSpec hy).2, ← (integral_setCKSpec hy').2]
  refine setIntegral_mono_on (integral_setCKSpec hy).1 (integral_setCKSpec hy').1
    measurableSet_Ioo fun v hv => mul_le_mul_of_nonneg_left ?_ (setCKSpecRho_nonneg hv)
  have ht := setCKSpecMass_pos hv
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The scaled spectral kernel: `Q/(Q + s t) = (Q/s)/(Q/s + t)`. -/
theorem div_add_mul_eq {Q s t : ℝ} (hs : 0 < s) :
    Q / (Q + s * t) = Q / s / (Q / s + t) := by
  rw [div_add' _ _ _ hs.ne', div_div_div_cancel_right₀ hs.ne', mul_comm t s]

theorem integrableOn_specScale {Q s : ℝ} (hQ : 0 ≤ Q) (hs : 0 < s) :
    IntegrableOn (fun v => setCKSpecRho v * (Q / (Q + s * setCKSpecMass v))) (Ioo 0 1) :=
  (integral_setCKSpec (div_nonneg hQ hs.le)).1.congr_fun
    (fun v _ => by simp only [div_add_mul_eq hs]) measurableSet_Ioo

theorem piHat_div_eq {Q s : ℝ} (hQ : 0 ≤ Q) (hs : 0 < s) :
    piHat (Q / s) = ∫ v in Ioo (0 : ℝ) 1, setCKSpecRho v * (Q / (Q + s * setCKSpecMass v)) := by
  rw [← (integral_setCKSpec (div_nonneg hQ hs.le)).2]
  exact setIntegral_congr_fun measurableSet_Ioo fun v _ => by simp only [div_add_mul_eq hs]

/-! ### The dispersion integral of one flavour -/

/-- **The dispersion integral of one bubble flavour** of mass² `s m²`:
`K(s) = ∫₀¹ ρ(v) A_(c)(s t_v) dv`. -/
noncomputable def kDisp (s : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, setCKSpecRho v * setCKKernelPairSum (s * setCKSpecMass v)

theorem kDisp_one : kDisp 1 = setCKDisp := by
  simp only [kDisp, one_mul, setCKDisp]

/-- The Fubini integrand `λ⁽⁴⁾(x) ρ(v) Q(x)/(Q(x) + s t_v)`. -/
noncomputable def kDispF (s x v : ℝ) : ℝ :=
  setCLambda x * (setCKSpecRho v * (setCKQ x / (setCKQ x + s * setCKSpecMass v)))

theorem integral_kDispF_v {s x : ℝ} (hs : 0 < s) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ v in Ioo (0 : ℝ) 1, kDispF s x v = setCLambda x * piHat (setCKQ x / s) := by
  rw [piHat_div_eq (setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩) hs, ← integral_const_mul]
  rfl

theorem integral_norm_kDispF_v {s x : ℝ} (hs : 0 < s) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ v in Ioo (0 : ℝ) 1, ‖kDispF s x v‖ = |setCLambda x| * piHat (setCKQ x / s) := by
  have hQ := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  rw [piHat_div_eq hQ hs, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  have h0 : 0 ≤ setCKSpecRho v * (setCKQ x / (setCKQ x + s * setCKSpecMass v)) :=
    mul_nonneg (setCKSpecRho_nonneg hv)
      (div_nonneg hQ (by nlinarith [setCKSpecMass_pos hv]))
  show ‖setCLambda x * _‖ = _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]

theorem integral_kDispF_x {s v : ℝ} (hs : 0 < s) (hv : v ∈ Ioo (0 : ℝ) 1) :
    ∫ x in Ioo (0 : ℝ) 1, kDispF s x v =
      setCKSpecRho v * setCKKernelPairSum (s * setCKSpecMass v) := by
  rw [isSetCKStieltjes_proved _ (mul_pos hs (setCKSpecMass_pos hv)), setCKStieltjes,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
  simp only [kDispF]
  ring

theorem integrable_kDispF {s : ℝ} (hs : 1 ≤ s) :
    Integrable (Function.uncurry (kDispF s))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hs0 : 0 < s := by linarith
  have hm : AEStronglyMeasurable (Function.uncurry (kDispF s))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    have hg : Measurable fun p : ℝ × ℝ =>
        setCKSpecRho p.2 * (setCKQ p.1 / (setCKQ p.1 + s * setCKSpecMass p.2)) := by
      unfold setCKSpecRho setCKQ setCKSpecMass; fun_prop
    exact aestronglyMeasurable_setCLambda.comp_fst.mul hg.aestronglyMeasurable
  refine (integrable_prod_iff hm).2 ⟨?_, ?_⟩
  · refine (ae_restrict_mem measurableSet_Ioo).mono fun x hx => ?_
    show Integrable (fun v => setCLambda x *
      (setCKSpecRho v * (setCKQ x / (setCKQ x + s * setCKSpecMass v)))) _
    exact (integrableOn_specScale (setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩) hs0).const_mul _
  · refine Integrable.mono' integrableOn_abs_setCLambda_mul hm.norm.integral_prod_right' ?_
    refine (ae_restrict_mem measurableSet_Ioo).mono fun x hx => ?_
    have hQ := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    have e : ∫ v, ‖Function.uncurry (kDispF s) (x, v)‖ ∂(volume.restrict (Ioo (0 : ℝ) 1)) =
        |setCLambda x| * piHat (setCKQ x / s) := integral_norm_kDispF_v hs0 hx
    rw [e, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
      (piHat_nonneg_spec (div_nonneg hQ hs0.le)))]
    exact mul_le_mul_of_nonneg_left (piHat_mono_spec (div_nonneg hQ hs0.le) (div_le_self hQ hs))
      (abs_nonneg _)

/-- The integrand `ρ(v) A_(c)(s t_v)` of `K(s)` is integrable on `(0, 1)` for `s ≥ 1`. -/
theorem integrableOn_kDisp {s : ℝ} (hs : 1 ≤ s) :
    IntegrableOn (fun v => setCKSpecRho v * setCKKernelPairSum (s * setCKSpecMass v))
      (Ioo 0 1) := by
  refine (integrable_kDispF hs).integral_prod_right.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  exact integral_kDispF_x (by linarith) hv

/-- **`K(s) = ∫₀¹ λ⁽⁴⁾(x) Π̂(Q(x)/s) dx`** for `s ≥ 1` (by (S) and Fubini). -/
theorem kDisp_eq {s : ℝ} (hs : 1 ≤ s) :
    kDisp s = ∫ x in Ioo (0 : ℝ) 1, setCLambda x * piHat (setCKQ x / s) := by
  have hs0 : 0 < s := by linarith
  have hswap := integral_integral_swap (integrable_kDispF hs)
  rw [kDisp, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hL : ∫ v in Ioo (0 : ℝ) 1, setCKSpecRho v * setCKKernelPairSum (s * setCKSpecMass v) =
      ∫ v in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1, kDispF s x v :=
    setIntegral_congr_fun measurableSet_Ioo fun v hv => (integral_kDispF_x hs0 hv).symm
  have hR : ∫ x in Ioo (0 : ℝ) 1, setCLambda x * piHat (setCKQ x / s) =
      ∫ x in Ioo (0 : ℝ) 1, ∫ v in Ioo (0 : ℝ) 1, kDispF s x v :=
    setIntegral_congr_fun measurableSet_Ioo fun x hx => (integral_kDispF_v hs0 hx).symm
  rw [hL, hR, hswap]

theorem integrableOn_lambda_piHat {s : ℝ} (hs : 1 ≤ s) :
    IntegrableOn (fun x => setCLambda x * piHat (setCKQ x / s)) (Ioo 0 1) := by
  refine (integrable_kDispF hs).integral_prod_left.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact integral_kDispF_v (by linarith) hx

theorem integrableOn_abs_lambda_piHat {s : ℝ} (hs : 1 ≤ s) :
    IntegrableOn (fun x => |setCLambda x| * piHat (setCKQ x / s)) (Ioo 0 1) := by
  refine (integrable_kDispF hs).integral_norm_prod_left.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact integral_norm_kDispF_v (by linarith) hx

/-! ### The Pauli–Villars combination -/

/-- **The PV combination of two spectral kernels**: for `1 + c₁ + c₂ = 0`,
`1 + c₁ s₁ + c₂ s₂ = 0`, `s₁, s₂ ≥ 1`,
`|c₁ Q/(Q + s₁ t) + c₂ Q/(Q + s₂ t)| ≤ Q/(Q + s₁ t) + Q/(Q + s₂ t)`. -/
theorem abs_pvComb_le {Q t s₁ s₂ c₁ c₂ : ℝ} (hQ : 0 ≤ Q) (ht : 0 < t) (hs₁ : 1 ≤ s₁)
    (hs₂ : 1 ≤ s₂) (hc : 1 + c₁ + c₂ = 0) (hc' : 1 + c₁ * s₁ + c₂ * s₂ = 0) :
    |c₁ * (Q / (Q + s₁ * t)) + c₂ * (Q / (Q + s₂ * t))| ≤
      Q / (Q + s₁ * t) + Q / (Q + s₂ * t) := by
  have hA₁ : 0 < Q + s₁ * t := by nlinarith
  have hA₂ : 0 < Q + s₂ * t := by nlinarith
  have hcs : c₁ * s₂ + c₂ * s₁ = 1 - s₁ - s₂ := by
    have : (c₁ + c₂) * (s₁ + s₂) = -(s₁ + s₂) := by rw [show c₁ + c₂ = -1 by linarith]; ring
    nlinarith
  have key : c₁ * (Q / (Q + s₁ * t)) + c₂ * (Q / (Q + s₂ * t)) =
      -(Q * (Q + t * (s₁ + s₂ - 1)) / ((Q + s₁ * t) * (Q + s₂ * t))) := by
    rw [eq_neg_iff_add_eq_zero]
    field_simp
    linear_combination Q ^ 2 * hc + Q * t * hcs
  have hnum : 0 ≤ Q * (Q + t * (s₁ + s₂ - 1)) := mul_nonneg hQ (by nlinarith)
  rw [key, abs_neg, abs_of_nonneg (div_nonneg hnum (mul_pos hA₁ hA₂).le),
    div_add_div _ _ hA₁.ne' hA₂.ne', div_le_div_iff_of_pos_right (mul_pos hA₁ hA₂)]
  nlinarith [mul_nonneg hQ ht.le]

/-- **The PV combination of `Π̂`**: `|c₁ Π̂(Q/s₁) + c₂ Π̂(Q/s₂)| ≤ Π̂(Q/s₁) + Π̂(Q/s₂)`. -/
theorem abs_pvComb_piHat {Q s₁ s₂ c₁ c₂ : ℝ} (hQ : 0 ≤ Q) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (hc : 1 + c₁ + c₂ = 0) (hc' : 1 + c₁ * s₁ + c₂ * s₂ = 0) :
    |c₁ * piHat (Q / s₁) + c₂ * piHat (Q / s₂)| ≤ piHat (Q / s₁) + piHat (Q / s₂) := by
  have i₁ := integrableOn_specScale hQ (s := s₁) (by linarith)
  have i₂ := integrableOn_specScale hQ (s := s₂) (by linarith)
  rw [piHat_div_eq hQ (by linarith), piHat_div_eq hQ (by linarith), ← integral_const_mul,
    ← integral_const_mul, ← integral_add (i₁.const_mul _) (i₂.const_mul _),
    ← integral_add i₁ i₂, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (i₁.add i₂) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  have hρ := setCKSpecRho_nonneg hv
  have e : c₁ * (setCKSpecRho v * (Q / (Q + s₁ * setCKSpecMass v))) +
      c₂ * (setCKSpecRho v * (Q / (Q + s₂ * setCKSpecMass v))) =
      setCKSpecRho v * (c₁ * (Q / (Q + s₁ * setCKSpecMass v)) +
        c₂ * (Q / (Q + s₂ * setCKSpecMass v))) := by ring
  rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ, ← mul_add]
  exact mul_le_mul_of_nonneg_left
    (abs_pvComb_le hQ (setCKSpecMass_pos hv) hs₁ hs₂ hc hc') hρ

/-- The tail `T(s) = ∫₀¹ |λ⁽⁴⁾(x)| Π̂(Q(x)/s) dx`. -/
noncomputable def kTail (s : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) 1, |setCLambda x| * piHat (setCKQ x / s)

/-- `|c₁ K(s₁) + c₂ K(s₂)| ≤ T(s₁) + T(s₂)` under the PV conditions. -/
theorem abs_pvComb_kDisp_le {s₁ s₂ c₁ c₂ : ℝ} (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (hc : 1 + c₁ + c₂ = 0) (hc' : 1 + c₁ * s₁ + c₂ * s₂ = 0) :
    |c₁ * kDisp s₁ + c₂ * kDisp s₂| ≤ kTail s₁ + kTail s₂ := by
  have i₁ := integrableOn_lambda_piHat hs₁
  have i₂ := integrableOn_lambda_piHat hs₂
  have j₁ := integrableOn_abs_lambda_piHat hs₁
  have j₂ := integrableOn_abs_lambda_piHat hs₂
  rw [kDisp_eq hs₁, kDisp_eq hs₂, kTail, kTail, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (i₁.const_mul _) (i₂.const_mul _), ← integral_add j₁ j₂, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (j₁.add j₂) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hQ := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have e : c₁ * (setCLambda x * piHat (setCKQ x / s₁)) +
      c₂ * (setCLambda x * piHat (setCKQ x / s₂)) =
      setCLambda x * (c₁ * piHat (setCKQ x / s₁) + c₂ * piHat (setCKQ x / s₂)) := by ring
  rw [e, Real.norm_eq_abs, abs_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_pvComb_piHat hQ hs₁ hs₂ hc hc') (abs_nonneg _)

/-- **The tail tends to `0`**: `∫|λ⁽⁴⁾| Π̂(Q/s) → 0` as `s → ∞`. -/
theorem tendsto_kTail : Tendsto kTail atTop (𝓝 0) := by
  have h0 : (∫ _x in Ioo (0 : ℝ) 1, (0 : ℝ)) = 0 := by simp
  rw [← h0]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => |setCLambda x| * setCDeltaAlpha x) ?_ ?_ integrableOn_abs_setCLambda_mul ?_
  · filter_upwards [eventually_ge_atTop 1] with s hs
    exact (integrableOn_abs_lambda_piHat hs).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hQ := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    have hs0 : 0 < s := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
      (piHat_nonneg_spec (div_nonneg hQ hs0.le)))]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact piHat_mono_spec (div_nonneg hQ hs0.le) (div_le_self hQ hs)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hQ := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    have hup : Tendsto (fun s : ℝ => |setCLambda x| * (setCKQ x / s / 4)) atTop (𝓝 0) := by
      have h := ((tendsto_const_nhds (x := setCKQ x)).div_atTop tendsto_id).div_const 4
      simpa using h.const_mul |setCLambda x|
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with s hs
      exact mul_nonneg (abs_nonneg _) (piHat_nonneg_spec (div_nonneg hQ hs.le))
    · filter_upwards [eventually_gt_atTop 0] with s hs
      exact mul_le_mul_of_nonneg_left (piHat_le_quarter (div_nonneg hQ hs.le)) (abs_nonneg _)

/-- **The regulator flavours decouple**: for every `η > 0` there is `R ≥ 1` such that
`|c₁ K(s₁) + c₂ K(s₂)| < η` whenever `s₁, s₂ ≥ R`, `1 + c₁ + c₂ = 0` and
`1 + c₁ s₁ + c₂ s₂ = 0`. -/
theorem kDisp_decouple {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ s₁ s₂ c₁ c₂ : ℝ, R ≤ s₁ → R ≤ s₂ → 1 + c₁ + c₂ = 0 →
      1 + c₁ * s₁ + c₂ * s₂ = 0 → |c₁ * kDisp s₁ + c₂ * kDisp s₂| < η := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 ((tendsto_order.1 tendsto_kTail).2 _ (half_pos hη))
  refine ⟨max R 1, le_max_right _ _, fun s₁ s₂ c₁ c₂ h₁ h₂ hc hc' => ?_⟩
  have hs₁ : 1 ≤ s₁ := (le_max_right _ _).trans h₁
  have hs₂ : 1 ≤ s₂ := (le_max_right _ _).trans h₂
  have t₁ := hR s₁ ((le_max_left _ _).trans h₁)
  have t₂ := hR s₂ ((le_max_left _ _).trans h₂)
  calc |c₁ * kDisp s₁ + c₂ * kDisp s₂| ≤ kTail s₁ + kTail s₂ :=
        abs_pvComb_kDisp_le hs₁ hs₂ hc hc'
    _ < η / 2 + η / 2 := add_lt_add t₁ t₂
    _ = η := add_halves η

end QED.ChainProof.SetCRegDisp

end
