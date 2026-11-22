/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUFlav
public import QED.ChainProof.SetAKSKSSpec
public import QED.ChainProof.SetAKSMis

/-!
# Set (a), stage D4: the reduction of `SetAKSScal` to one identity of the vertex classes

Helper level for `SetAKSScal e` (Set (a) of the three-loop coefficient). By
`ksU_ksSpecForm_of_flavour` the output of stage D is a statement about the single-flavour finite
part `ksUGf e μ (√x) s`. That finite part is `e⁴` times the vertex part
`ksUKe 1 · (2 ΔF + ΔF_B)` of one flavour of mass `M = √x`, plus the mass class
`-(e⁴/32π⁴) c_m(μ) D(s/M²)`. The constant `c_m(μ)` of the mass class depends on `μ` only through
`c_m(μ) = c_m(1) - (3/2) log μ²`, and this is the whole `log μ²` dependence of the target.

So the whole of stage D (and of stage S: the target density is fixed in advance, so no
derivative of a density is needed) follows from one identity `KsCore` about the vertex classes
of a single flavour, which involves neither `e` nor `μ`:

  `ksUKe 1 · (2 (F(M, s) - F(M, 0)) + F_B(M, s) - F_B(M, 0))`
  `  = (Π̂⁽⁴⁾(s/M²) - (3/4) log M² · D(s/M²))/(16π⁴) + c_m(1) D(s/M²)/(32π⁴)`.

Numerically (`F` and `F_B` from their formal definitions, at `M ∈ {1, 3/2}`,
`s ∈ {-2, 1, 3}`) the two sides agree to relative accuracy `10⁻¹²`, with `c_m(1) = 3/4`.

Main results:

* `ksV_ksUcm_eq`: `c_m(μ) = c_m(1) - (3/2) log μ²`;
* `ksV_ksDm_zero`: `D(0) = 0`;
* `KsCore`: the identity above;
* **`ksV_setAKSFix_of_core`**, **`ksV_setAKSScal_of_core`**: `KsCore → SetAKSScal e` for
  every `e ≠ 0`, with the affine part `α = β = 0`.
-/

@[expose] public section

open Real MeasureTheory Set

namespace QED.ChainProof.SetAKS

open QED.Chain QED.GradedProof.RPi4

/-- The mass-class constant at unit mass is integrable. -/
theorem ksV_integrableOn_ksUcm_one :
    IntegrableOn (fun x => (1 + x) * Real.log (ksUam 1 x)) (Ioo (0 : ℝ) 1) := by
  have hme := ksU_measurable_ksUam 1
  refine Integrable.mono' ((ksU_integrableOn_ksUg.const_mul (2 * (6 + 2 * |Real.log 1|))))
    (by fun_prop : Measurable fun x => (1 + x) * Real.log (ksUam 1 x)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have h := ksU_abs_log_ksUam_le_g one_pos hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith [hx.1] : (0 : ℝ) < 1 + x)]
  have hg : 0 ≤ (6 + 2 * |Real.log 1|) * ksUg x := (abs_nonneg _).trans h
  calc (1 + x) * |Real.log (ksUam 1 x)| ≤ 2 * ((6 + 2 * |Real.log 1|) * ksUg x) :=
        mul_le_mul (by linarith [hx.2]) h (abs_nonneg _) (by norm_num)
    _ = 2 * (6 + 2 * |Real.log 1|) * ksUg x := by ring

/-- **The `μ`-dependence of the mass class**: `c_m(μ) = c_m(1) - (3/2) log μ²`. -/
theorem ksV_ksUcm_eq {μ : ℝ} (hμ : 0 < μ) :
    ksUcm μ = ksUcm 1 - 3 / 2 * Real.log (μ ^ 2) := by
  have hc : IntegrableOn (fun x : ℝ => (1 + x) * Real.log (μ ^ 2)) (Ioo (0 : ℝ) 1) :=
    (by fun_prop : Continuous fun x : ℝ => (1 + x) * Real.log (μ ^ 2)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have e : ksUcm μ = ∫ x in Ioo (0 : ℝ) 1,
      ((1 + x) * Real.log (ksUam 1 x) - (1 + x) * Real.log (μ ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have ha := ksU_ksUam_pos one_pos hx
    have e1 : ksUam μ x = ksUam 1 x / μ ^ 2 := by
      simp only [ksUam]
      field_simp
    rw [e1, Real.log_div ha.ne' (by positivity)]
    ring
  rw [e, integral_sub ksV_integrableOn_ksUcm_one hc, MeasureTheory.integral_mul_const,
    ksU_integral_one_add]
  rfl

theorem ksV_ksDm_zero : ksDm 0 = 0 := by
  simp [ksDm, ksDmKer]

theorem ksV_ksUKe_eq (e : ℝ) : ksUKe e = e ^ 4 * ksUKe 1 := by
  simp only [ksUKe]
  ring

/-- **The core identity of stage D4**: the vertex classes `VA` (twice) and `VB` of one flavour of
mass `M`, subtracted at `s = 0`, are the Källén–Sabry function `Π̂⁽⁴⁾(s/M²)` plus multiples of
the one-loop mass derivative `D(s/M²)`. -/
def KsCore : Prop :=
  ∀ M s : ℝ, 0 < M → -(4 * M ^ 2) < s →
    ksUKe 1 * (2 * (ksUF M s - ksUF M 0) + (ksUFB M s - ksUFB M 0)) =
      (piHat4 (s / M ^ 2) - 3 / 4 * Real.log (M ^ 2) * ksDm (s / M ^ 2)) / (16 * π ^ 4) +
        ksUcm 1 * ksDm (s / M ^ 2) / (32 * π ^ 4)

/-- **The single-flavour finite part at `M = √x`** from `KsCore`. -/
theorem ksV_ksUGf_eq (hC : KsCore) {e μ x s : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hs : -(4 * μ ^ 2) < s) :
    ksUGf e μ (Real.sqrt x) s / e ^ 4 =
      (piHat4 (s / x) - 3 / 4 * Real.log (x / μ ^ 2) * ksDm (s / x)) / (16 * π ^ 4) := by
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hx0 : 0 < x := hμ2.trans_le hx
  have hM : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hM2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hsM : -(4 * Real.sqrt x ^ 2) < s := by rw [hM2]; linarith
  have hcore := hC (Real.sqrt x) s hM hsM
  rw [hM2] at hcore
  have he4 : e ^ 4 ≠ 0 := pow_ne_zero 4 he
  have hπ : π ≠ 0 := Real.pi_ne_zero
  unfold ksUGf
  rw [hM2, zero_div, ksV_ksDm_zero, sub_zero, ksV_ksUKe_eq, mul_assoc, hcore, ksV_ksUcm_eq hμ,
    Real.log_div hx0.ne' hμ2.ne']
  simp only [ksUme]
  field_simp
  ring

/-- **Stage D and stage S from `KsCore`**: `SetAKSFix e`, with the affine part zero. -/
theorem ksV_setAKSFix_of_core (hC : KsCore) {e : ℝ} (he : e ≠ 0) : SetAKSFix e := by
  have hD : KsSpecForm e fun μ x δ => ksSpecRho (Real.log (x / μ ^ 2)) δ := by
    refine ksU_ksSpecForm_of_flavour he ⟨fun _ _ => 0, fun _ _ => 0, fun μ x s hμ hx hs => ?_⟩
    rw [ksV_ksUGf_eq hC he hμ hx hs, ← ksS_piHat4_sub_ksDm_eq (ksA_neg_four_lt_div hμ hx hs)]
    ring
  exact ksA_setAKSFix_of_eqOn hD fun _ _ _ _ => fun _ _ => rfl

/-- **`SetAKSScal e` from `KsCore`.** -/
theorem ksV_setAKSScal_of_core (hC : KsCore) {e : ℝ} (he : e ≠ 0) : SetAKSScal e :=
  setAKSScal_of_fix (ksV_setAKSFix_of_core hC he)

end QED.ChainProof.SetAKS

end
