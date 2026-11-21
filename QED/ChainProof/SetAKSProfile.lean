/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.SetASpectral
public import QED.GradedProof.RPi4DecScal

/-!
# R-KS: the Källén–Sabry profile and its regularity at `0`

Helper level for the identification (R-KS) of the regulator limit `Π_∞` of the frozen goal
(R-Π₄) `QED.Graded.vacuumPolarizationPart_two_lepton_limit` with the Källén–Sabry function used on
the set (a) value side (`QED.Chain.piHat4`, `QED.Chain.integral_setA_eq_aSetA`).

The model's order-`e⁴` form factor is normalized by `e⁴`, and `(α/π)² = e⁴/(16π⁴)`; at one loop
the model gives `Π_loop(s) - Π_loop(0) = (e²/4π²) Π̂₂(s/M²)` (`vacuumPolarizationLoop`). The
Källén–Sabry profile in the model's normalization is therefore
`ksG σ = Π̂⁽⁴⁾(σ)/(16π⁴)`, with `σ = s/m²`.

Main results:

* `ksG`, `ksPinf`: the profile and `Π_∞(s) = ksG(s/m²)` for the electron alone;
* `abs_piHat4_sub_le`: `Π̂⁽⁴⁾` is Lipschitz on `[-1, 1]`, with constant `∫₀¹ |ρ⁽⁴⁾|`;
* `ksG_zero`, `norm_ksG_sub_le`: the profile vanishes at `0` and is Lipschitz on `[-1, 1]`;
* `decDecay_decT_ksG`: the scaling form built on `ksG` decouples (`DecDecay` of R-Π₄ step L9).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

open QED.Chain

/-- The integrand of `piHat4`. -/
noncomputable def ksKer (σ δ : ℝ) : ℝ :=
  2 * δ / (1 - δ ^ 2) * ksRho δ * (σ / (σ + 4 / (1 - δ ^ 2)))

theorem piHat4_eq_integral_ksKer (σ : ℝ) : piHat4 σ = ∫ δ in (0 : ℝ)..1, ksKer σ δ := rfl

/-- The pointwise Lipschitz bound of the integrand on `δ ∈ (0, 1]`, `|σ|, |σ'| ≤ 1`. -/
theorem abs_ksKer_sub_le {σ σ' δ : ℝ} (hσ : |σ| ≤ 1) (hσ' : |σ'| ≤ 1) (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    |ksKer σ δ - ksKer σ' δ| ≤ |σ - σ'| * |ksRho δ| := by
  obtain ⟨h0, h1⟩ := hδ
  rcases h1.lt_or_eq with h1 | rfl
  · have hd : 0 < 1 - δ ^ 2 := by nlinarith
    set t : ℝ := 4 / (1 - δ ^ 2) with ht
    have ht4 : 4 ≤ t := by
      rw [ht, le_div_iff₀ hd]
      nlinarith
    obtain ⟨hσl, hσu⟩ := abs_le.1 hσ
    obtain ⟨hσl', hσu'⟩ := abs_le.1 hσ'
    have ha : 0 < σ + t := by linarith
    have hb : 0 < σ' + t := by linarith
    have hw : 2 * δ / (1 - δ ^ 2) = δ * t / 2 := by
      rw [ht]
      field_simp
      ring
    have key : ksKer σ δ - ksKer σ' δ =
        ksRho δ * (σ - σ') * (δ * t ^ 2 / (2 * ((σ + t) * (σ' + t)))) := by
      simp only [ksKer]
      rw [hw, ← ht]
      field_simp
      ring
    have hq0 : 0 ≤ δ * t ^ 2 / (2 * ((σ + t) * (σ' + t))) := by positivity
    have hq1 : δ * t ^ 2 / (2 * ((σ + t) * (σ' + t))) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have hab : (t - 1) ^ 2 ≤ (σ + t) * (σ' + t) := by
        have h1' : t - 1 ≤ σ + t := by linarith
        have h2' : t - 1 ≤ σ' + t := by linarith
        have h3 : 0 ≤ t - 1 := by linarith
        calc (t - 1) ^ 2 = (t - 1) * (t - 1) := by ring
          _ ≤ (σ + t) * (σ' + t) := mul_le_mul h1' h2' h3 ha.le
      have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
      nlinarith
    rw [key, abs_mul, abs_mul, abs_of_nonneg hq0]
    calc |ksRho δ| * |σ - σ'| * (δ * t ^ 2 / (2 * ((σ + t) * (σ' + t))))
        ≤ |ksRho δ| * |σ - σ'| * 1 := by gcongr
      _ = |σ - σ'| * |ksRho δ| := by ring
  · simp only [ksKer]
    norm_num
    positivity

theorem ksKer_zero (δ : ℝ) : ksKer 0 δ = 0 := by
  simp [ksKer]

theorem aestronglyMeasurable_ksKer (σ : ℝ) :
    AEStronglyMeasurable (ksKer σ) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hA : Measurable fun δ : ℝ => 2 * δ / (1 - δ ^ 2) := by fun_prop
  have hB : Measurable fun δ : ℝ => σ / (σ + 4 / (1 - δ ^ 2)) := by fun_prop
  exact (hA.aestronglyMeasurable.mul aestronglyMeasurable_ksRho).mul hB.aestronglyMeasurable

theorem integrableOn_abs_ksRho : IntegrableOn (fun δ => |ksRho δ|) (Ioc 0 1) :=
  integrableOn_ksRho.abs

/-- The integrand of `piHat4` is integrable for `|σ| ≤ 1`. -/
theorem intervalIntegrable_ksKer {σ : ℝ} (hσ : |σ| ≤ 1) :
    IntervalIntegrable (ksKer σ) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Integrable.mono' (integrableOn_abs_ksRho.const_mul |σ|) (aestronglyMeasurable_ksKer σ)
    ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun δ hδ => ?_)
  have h := abs_ksKer_sub_le hσ (σ' := 0) (by simp) hδ
  rw [ksKer_zero, sub_zero, sub_zero] at h
  rwa [Real.norm_eq_abs]

/-- The Lipschitz constant of `Π̂⁽⁴⁾` on `[-1, 1]`. -/
noncomputable def ksLip : ℝ := ∫ δ in (0 : ℝ)..1, |ksRho δ|

theorem ksLip_nonneg : 0 ≤ ksLip :=
  intervalIntegral.integral_nonneg zero_le_one fun _ _ => abs_nonneg _

/-- **`Π̂⁽⁴⁾` is Lipschitz on `[-1, 1]`.** -/
theorem abs_piHat4_sub_le {σ σ' : ℝ} (hσ : |σ| ≤ 1) (hσ' : |σ'| ≤ 1) :
    |piHat4 σ - piHat4 σ'| ≤ ksLip * |σ - σ'| := by
  rw [piHat4_eq_integral_ksKer, piHat4_eq_integral_ksKer,
    ← intervalIntegral.integral_sub (intervalIntegrable_ksKer hσ) (intervalIntegrable_ksKer hσ')]
  have hg : IntervalIntegrable (fun δ => |σ - σ'| * |ksRho δ|) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact integrableOn_abs_ksRho.const_mul _
  have h := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (f := fun δ => ksKer σ δ - ksKer σ' δ) (Eventually.of_forall fun δ hδ => by
      rw [Real.norm_eq_abs]
      exact abs_ksKer_sub_le hσ hσ' hδ) hg
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at h
  rw [ksLip]
  linarith

/-- **The Källén–Sabry profile** in the model's normalization: `Π̂⁽⁴⁾(σ)/(16π⁴)`. -/
noncomputable def ksG (σ : ℝ) : ℂ :=
  ((piHat4 σ / (16 * π ^ 4) : ℝ) : ℂ)

/-- **The Källén–Sabry limit function** of the electron of mass `m`: `Π̂⁽⁴⁾(s/m²)/(16π⁴)`. -/
noncomputable def ksPinf (m s : ℝ) : ℂ :=
  ksG (s / m ^ 2)

theorem ksG_zero : ksG 0 = 0 := by
  simp [ksG, QED.Chain.piHat4_zero]

/-- The Lipschitz constant of `ksG` on `[-1, 1]`. -/
noncomputable def ksGLip : ℝ := ksLip / (16 * π ^ 4)

theorem ksGLip_nonneg : 0 ≤ ksGLip := div_nonneg ksLip_nonneg (by positivity)

theorem norm_ksG_sub_le {σ σ' : ℝ} (hσ : |σ| ≤ 1) (hσ' : |σ'| ≤ 1) :
    ‖ksG σ - ksG σ'‖ ≤ ksGLip * |σ - σ'| := by
  have hp : 0 < 16 * π ^ 4 := by positivity
  rw [ksG, ksG, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← sub_div,
    abs_div, abs_of_pos hp, ksGLip, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hp]
  exact abs_piHat4_sub_le hσ hσ'

open QED.GradedProof.RPi4 in
/-- **The scaling form built on the Källén–Sabry profile decouples** (`DecDecay`, R-Π₄ step L9),
for every mismatch profile `φ` vanishing at `0` and Lipschitz near `0`. -/
theorem decDecay_decT_ksG {φ : ℝ → ℂ} {κ : ℂ} {δ L : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (hφ0 : φ 0 = 0) (hφ : ∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖φ σ - φ σ'‖ ≤ L * |σ - σ'|)
    {μ : ℝ} (hμ : 0 < μ) : DecDecay (decT ksG φ κ) μ := by
  set δ' : ℝ := min δ 1 with hδ'
  set L' : ℝ := max L ksGLip with hL'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  refine dec_decay_decT (δ := δ') (L := L') hδ'0 (hL.trans (le_max_left _ _)) ksG_zero hφ0
    (fun σ σ' h h' => ?_) (fun σ σ' h h' => ?_) hμ
  · exact (norm_ksG_sub_le (h.trans (min_le_right _ _)) (h'.trans (min_le_right _ _))).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
  · exact (hφ σ σ' (h.trans (min_le_left _ _)) (h'.trans (min_le_left _ _))).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

end QED.ChainProof.SetAKS

end
