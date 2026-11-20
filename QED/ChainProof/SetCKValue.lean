/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCrossLink
public import QED.Chain.SetCValue

/-!
# Set (c), Stage K4: the dispersion integral of the kernel and the set (c) value

Helper level (no frozen statement). The set (c) value `aSetC` is proved in
`QED.Chain.integral_setC_eq_aSetC` as `∫₀¹ λ⁽⁴⁾(x) Δα(x) dx`, with the Balzani–Laporta–Passera
kernel `λ⁽⁴⁾ = setCLambda` and `Δα(x) = Π̂(Q(x))`, `Q(x) = x²/(1-x)`. The Stage K kernel sum
`setCKKernelPairSum t` (the twelve placements of a massive photon of mass² `t`) is a parametric
object. With the bubble's spectral weight `ρ(v) = v²(1 - v²/3)/(1 - v²)` at mass²
`t_v = 4/(1 - v²)` (`QED.Chain.piHat_eq_spectral`), the set (c) dispersion integral is

`a_(c) = ∫₀¹ ρ(v) A_(c)(t_v) dv` (`setCKDisp`).

The step from `a_(c)` to `aSetC` is the Stieltjes identity (S) of the kernel plan,
`A_(c)(t) = ∫₀¹ λ⁽⁴⁾(x) Q(x)/(Q(x) + t) dx` (`IsSetCKStieltjes`), followed by Fubini and the
spectral form of `Π̂`. (S) itself is checked numerically only (to `1.6·10⁻¹⁴` at `t = 1`); in
Lean the kernel sum is known in the `Q`-derivative form `∫₀¹ H_tot Q'/(Q + t)²`
(`setCKKernelSum_eq'`), and (S) is equivalent to `H_tot = H_λ`, `H_λ(X) = ∫₀^X λ⁽⁴⁾ Q`.

## Main statements

* `piHat_ge_div`: `Π̂(s) ≥ (4/15) s/(s + 4)` for `s ≥ 0` (from the spectral form).
* `integrableOn_setCLambda_mul`: `λ⁽⁴⁾ Q/(Q + t)` is integrable on `(0, 1)` for `t > 0`.
* `setCKDisp_eq_aSetC`: **(S) implies `a_(c) = aSetC`**.
* `isSetCKStieltjes_of_hTot`: the pointwise identity `H_tot = H_λ` on `(0, 1)` implies (S).
* `setCKDisp_eq_aSetC_of_hTot`: hence `H_tot = H_λ` implies `a_(c) = aSetC`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.Chain

/-- The one-loop bubble's spectral weight `ρ(v) = v²(1 - v²/3)/(1 - v²)`. -/
noncomputable def setCKSpecRho (v : ℝ) : ℝ := v ^ 2 * (1 - v ^ 2 / 3) / (1 - v ^ 2)

/-- The spectral mass² `t_v = 4/(1 - v²)` of the bubble (`m = 1`). -/
noncomputable def setCKSpecMass (v : ℝ) : ℝ := 4 / (1 - v ^ 2)

/-- **The set (c) dispersion integral** `a_(c) = ∫₀¹ ρ(v) A_(c)(t_v) dv` of the kernel sum. -/
noncomputable def setCKDisp : ℝ :=
  ∫ v in (0 : ℝ)..1, setCKSpecRho v * setCKKernelPairSum (setCKSpecMass v)

/-- **The Stieltjes identity (S)** of the set (c) kernel:
`A_(c)(t) = ∫₀¹ λ⁽⁴⁾(x) Q(x)/(Q(x) + t) dx` for every `t > 0`. -/
def IsSetCKStieltjes : Prop :=
  ∀ t : ℝ, 0 < t → setCKKernelPairSum t = setCKStieltjes setCLambda t

section Spectral

variable {s v : ℝ}

/-- The spectral integrand without the pole at `v = 1`. -/
theorem setCKSpec_eq (hs : 0 ≤ s) (hv : v ∈ Ioo (0 : ℝ) 1) :
    setCKSpecRho v * (s / (s + setCKSpecMass v)) =
      v ^ 2 * (1 - v ^ 2 / 3) * s / ((1 - v ^ 2) * s + 4) := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have h2 : 0 < (1 - v ^ 2) * s + 4 := by nlinarith
  unfold setCKSpecRho setCKSpecMass
  field_simp

theorem continuousOn_setCKSpecReg (hs : 0 ≤ s) :
    ContinuousOn (fun v : ℝ => v ^ 2 * (1 - v ^ 2 / 3) * s / ((1 - v ^ 2) * s + 4))
      (Icc 0 1) := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => ?_
  have : 0 ≤ (1 - v ^ 2) * s := mul_nonneg (by nlinarith [hv.1, hv.2]) hs
  linarith

/-- The spectral integrand is integrable on `(0, 1)` and integrates to `Π̂(s)`. -/
theorem integral_setCKSpec (hs : 0 ≤ s) :
    IntegrableOn (fun v => setCKSpecRho v * (s / (s + setCKSpecMass v))) (Ioo 0 1) ∧
      ∫ v in Ioo (0 : ℝ) 1, setCKSpecRho v * (s / (s + setCKSpecMass v)) = piHat s := by
  have hreg := ((continuousOn_setCKSpecReg hs).integrableOn_Icc (μ := volume)).mono_set
    Ioo_subset_Icc_self
  have heq : EqOn (fun v => v ^ 2 * (1 - v ^ 2 / 3) * s / ((1 - v ^ 2) * s + 4))
      (fun v => setCKSpecRho v * (s / (s + setCKSpecMass v))) (Ioo 0 1) :=
    fun v hv => (setCKSpec_eq hs hv).symm
  refine ⟨hreg.congr_fun heq measurableSet_Ioo, ?_⟩
  rw [piHat_eq_spectral (by linarith), intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  rfl

theorem setCKSpec_nonneg (hs : 0 ≤ s) (hv : v ∈ Ioo (0 : ℝ) 1) :
    0 ≤ setCKSpecRho v * (s / (s + setCKSpecMass v)) := by
  rw [setCKSpec_eq hs hv]
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have : 0 ≤ (1 - v ^ 2) * s := mul_nonneg h1.le hs
  have : 0 ≤ 1 - v ^ 2 / 3 := by nlinarith
  positivity

/-- **A lower bound for `Π̂`**: `Π̂(s) ≥ (4/15) s/(s + 4)` for `s ≥ 0`. -/
theorem piHat_ge_div (hs : 0 ≤ s) : 4 / 15 * (s / (s + 4)) ≤ piHat s := by
  obtain ⟨-, hv⟩ := integral_setCKSpec hs
  have hreg := (continuousOn_setCKSpecReg hs).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hlow : IntervalIntegrable (fun v : ℝ => v ^ 2 * (1 - v ^ 2 / 3) * (s / (s + 4)))
      volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hmono := intervalIntegral.integral_mono_on zero_le_one hlow hreg fun v hv => by
    have hv2 : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    have h0 : 0 ≤ v ^ 2 * (1 - v ^ 2 / 3) := mul_nonneg (sq_nonneg v) (by linarith)
    have h1 : 0 ≤ (1 - v ^ 2) * s := mul_nonneg (by linarith) hs
    have h4 : 0 < (1 - v ^ 2) * s + 4 := by linarith
    have hle : (1 - v ^ 2) * s + 4 ≤ s + 4 := by nlinarith [sq_nonneg v]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hs h4 hle) h0
  have hpoly : ∫ v in (0 : ℝ)..1, v ^ 2 * (1 - v ^ 2 / 3) * (s / (s + 4)) =
      4 / 15 * (s / (s + 4)) := by
    rw [intervalIntegral.integral_mul_const]
    have : (fun v : ℝ => v ^ 2 * (1 - v ^ 2 / 3)) = fun v => v ^ 2 - v ^ 4 / 3 := by
      funext v; ring
    rw [this, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_div,
      integral_pow, integral_pow]
    norm_num
  rw [hpoly, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hmono
  rw [← hv]
  refine hmono.trans_eq (setIntegral_congr_fun measurableSet_Ioo fun v hv' => ?_)
  exact (setCKSpec_eq hs hv').symm

end Spectral

/-- `Δα = Π̂ ∘ Q` is positive on `(0, 1)`. -/
theorem setCDeltaAlpha_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < setCDeltaAlpha x := by
  have hQ : 0 < setCKQ x := div_pos (pow_pos hx.1 2) (by linarith [hx.2])
  have := piHat_ge_div hQ.le
  have : 0 < 4 / 15 * (setCKQ x / (setCKQ x + 4)) := by positivity
  unfold setCDeltaAlpha; change 0 < piHat (setCKQ x); linarith

/-- `λ⁽⁴⁾` is a.e. strongly measurable on `(0, 1)`: it is `(λ⁽⁴⁾ Δα)/Δα` there, with
`Δα = piHatX` (`QED.Chain.piHat_photonVar`). -/
theorem aestronglyMeasurable_setCLambda :
    AEStronglyMeasurable setCLambda (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hI := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 intervalIntegrable_setC
  have hm : AEStronglyMeasurable (fun x => setCLambda x * setCDeltaAlpha x * (piHatX x)⁻¹)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine hI.aestronglyMeasurable.mul (Measurable.aestronglyMeasurable ?_)
    unfold piHatX; fun_prop
  refine hm.congr ((ae_restrict_mem measurableSet_Ioo).mono fun x hx => ?_)
  have hp := setCDeltaAlpha_pos hx
  have he : setCDeltaAlpha x = piHatX x := piHat_photonVar hx
  show setCLambda x * setCDeltaAlpha x * (piHatX x)⁻¹ = setCLambda x
  rw [← he]; field_simp

/-- `|λ⁽⁴⁾| Δα` is integrable on `(0, 1)`. -/
theorem integrableOn_abs_setCLambda_mul :
    IntegrableOn (fun x => |setCLambda x| * setCDeltaAlpha x) (Ioo 0 1) := by
  have hI := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 intervalIntegrable_setC
  have hA : IntegrableOn (fun x => |setCLambda x * setCDeltaAlpha x|) (Ioo 0 1) := hI.abs
  refine hA.congr_fun (fun x hx => ?_) measurableSet_Ioo
  show |setCLambda x * setCDeltaAlpha x| = _
  rw [abs_mul, abs_of_pos (setCDeltaAlpha_pos hx)]

theorem setCK_div_le_max_mul_div {q t : ℝ} (hq : 0 ≤ q) (ht : 0 < t) :
    q / (q + t) ≤ max 1 (4 / t) * (q / (q + 4)) := by
  have h4 : 0 ≤ q / (q + 4) := by positivity
  rcases le_total t 4 with h | h
  · have e : 4 / t * (q / (q + 4)) = 4 * q / (t * (q + 4)) := by field_simp
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) h4)
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hq (sub_nonneg.2 h)]
  · refine le_trans ?_ (le_mul_of_one_le_left h4 (le_max_left _ _))
    exact div_le_div_of_nonneg_left hq (by positivity) (by linarith)

/-- `Q/(Q + t) ≤ (15/4) max 1 (4/t) Δα` on `(0, 1)` for `t > 0`. -/
theorem setCKQ_div_le {t x : ℝ} (ht : 0 < t) (hx : x ∈ Ioo (0 : ℝ) 1) :
    setCKQ x / (setCKQ x + t) ≤ 15 / 4 * max 1 (4 / t) * setCDeltaAlpha x := by
  have hQ : 0 ≤ setCKQ x := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hge := piHat_ge_div hQ
  change 4 / 15 * (setCKQ x / (setCKQ x + 4)) ≤ setCDeltaAlpha x at hge
  have key : setCKQ x / (setCKQ x + t) ≤ max 1 (4 / t) * (setCKQ x / (setCKQ x + 4)) :=
    setCK_div_le_max_mul_div hQ ht
  have hM : 0 ≤ max 1 (4 / t) := le_trans zero_le_one (le_max_left _ _)
  calc setCKQ x / (setCKQ x + t) ≤ max 1 (4 / t) * (setCKQ x / (setCKQ x + 4)) := key
    _ = 15 / 4 * max 1 (4 / t) * (4 / 15 * (setCKQ x / (setCKQ x + 4))) := by ring
    _ ≤ 15 / 4 * max 1 (4 / t) * setCDeltaAlpha x := by gcongr

/-- `λ⁽⁴⁾ Q/(Q + t)` is integrable on `(0, 1)` for `t > 0`. -/
theorem integrableOn_setCLambda_mul {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => setCLambda x * (setCKQ x / (setCKQ x + t))) (Ioo 0 1) := by
  have hdom := integrableOn_abs_setCLambda_mul.const_mul (15 / 4 * max 1 (4 / t))
  have hmeas : AEStronglyMeasurable (fun x => setCLambda x * (setCKQ x / (setCKQ x + t)))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    aestronglyMeasurable_setCLambda.mul
      (Measurable.aestronglyMeasurable (by unfold setCKQ; fun_prop))
  refine Integrable.mono' hdom hmeas ?_
  refine (ae_restrict_mem measurableSet_Ioo).mono fun x hx => ?_
  have hQ : 0 ≤ setCKQ x := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hq : 0 ≤ setCKQ x / (setCKQ x + t) := div_nonneg hQ (by linarith)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq]
  calc |setCLambda x| * (setCKQ x / (setCKQ x + t))
      ≤ |setCLambda x| * (15 / 4 * max 1 (4 / t) * setCDeltaAlpha x) :=
        mul_le_mul_of_nonneg_left (setCKQ_div_le ht hx) (abs_nonneg _)
    _ = 15 / 4 * max 1 (4 / t) * (|setCLambda x| * setCDeltaAlpha x) := by ring

/-- The Fubini integrand `λ⁽⁴⁾(x) ρ(v) Q(x)/(Q(x) + t_v)` on `(0, 1)²`. -/
noncomputable def setCKDispF (x v : ℝ) : ℝ :=
  setCLambda x * (setCKSpecRho v * (setCKQ x / (setCKQ x + setCKSpecMass v)))

theorem integrable_setCKDispF :
    Integrable (Function.uncurry setCKDispF)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hm : AEStronglyMeasurable (Function.uncurry setCKDispF)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    have hg : Measurable fun p : ℝ × ℝ =>
        setCKSpecRho p.2 * (setCKQ p.1 / (setCKQ p.1 + setCKSpecMass p.2)) := by
      unfold setCKSpecRho setCKQ setCKSpecMass; fun_prop
    exact aestronglyMeasurable_setCLambda.comp_fst.mul hg.aestronglyMeasurable
  refine (integrable_prod_iff hm).2 ⟨?_, ?_⟩
  · refine (ae_restrict_mem measurableSet_Ioo).mono fun x hx => ?_
    show Integrable (fun v => setCLambda x *
      (setCKSpecRho v * (setCKQ x / (setCKQ x + setCKSpecMass v)))) _
    exact ((integral_setCKSpec (setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩)).1).const_mul _
  · refine integrableOn_abs_setCLambda_mul.congr_fun (fun x hx => ?_) measurableSet_Ioo
    have hQ := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    simp only [Function.uncurry_apply_pair, setCKDispF, norm_mul, Real.norm_eq_abs]
    rw [integral_const_mul]
    congr 1
    change piHat (setCKQ x) = _
    rw [← (integral_setCKSpec hQ).2]
    refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
    rw [← abs_mul, abs_of_nonneg (setCKSpec_nonneg hQ hv)]

/-- **K4 from (S)**: if the kernel sum is the Stieltjes transform of `λ⁽⁴⁾`, then the set (c)
dispersion integral is the set (c) value, `∫₀¹ ρ(v) A_(c)(t_v) dv = aSetC`. -/
theorem setCKDisp_eq_aSetC (hS : IsSetCKStieltjes) : setCKDisp = aSetC := by
  have hswap := integral_integral_swap integrable_setCKDispF
  simp only [setCKDispF] at hswap
  rw [← integral_setC_eq_aSetC, setCKDisp, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  have hL : ∫ x in Ioo (0 : ℝ) 1, setCLambda x * setCDeltaAlpha x =
      ∫ x in Ioo (0 : ℝ) 1, ∫ v in Ioo (0 : ℝ) 1,
        setCLambda x * (setCKSpecRho v * (setCKQ x / (setCKQ x + setCKSpecMass v))) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [integral_const_mul, (integral_setCKSpec (setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩)).2]
    rfl
  have hR : ∫ v in Ioo (0 : ℝ) 1, setCKSpecRho v * setCKKernelPairSum (setCKSpecMass v) =
      ∫ v in Ioo (0 : ℝ) 1, ∫ x in Ioo (0 : ℝ) 1,
        setCLambda x * (setCKSpecRho v * (setCKQ x / (setCKQ x + setCKSpecMass v))) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
    have ht : 0 < setCKSpecMass v := div_pos (by norm_num) (by nlinarith [hv.1, hv.2])
    rw [hS _ ht, setCKStieltjes, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    ring
  rw [hL, hR, hswap]

/-- The integral `H_λ(X) = ∫₀^X λ⁽⁴⁾ Q` turns (S) into the `Q`-derivative form: if
`H_tot = H_λ` on `(0, 1)`, then (S) holds. -/
theorem isSetCKStieltjes_of_hTot
    (hH : ∀ X ∈ Ioo (0 : ℝ) 1, setCKHTot X = setCKRhoH setCLambda X) : IsSetCKStieltjes := by
  intro t ht
  rw [setCKKernelSum_eq' ht, (setCKStieltjes_eq_rhoH ht (integrableOn_setCLambda_mul ht)).2,
    intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun X hX => by rw [hH X hX]

/-- **K4 from the pointwise identity `H_tot = H_λ`** on `(0, 1)`. -/
theorem setCKDisp_eq_aSetC_of_hTot
    (hH : ∀ X ∈ Ioo (0 : ℝ) 1, setCKHTot X = setCKRhoH setCLambda X) : setCKDisp = aSetC :=
  setCKDisp_eq_aSetC (isSetCKStieltjes_of_hTot hH)

end QED.ChainProof.SetCK

end
