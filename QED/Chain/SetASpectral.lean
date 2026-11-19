/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ExtraIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The fourth-order (Källén–Sabry) vacuum-polarization function

Helper analysis for the sixth-order set (a) of `docs/HIGHER-LOOP-PLAN.md` (section 3 (a)): the
fourth-order vacuum-polarization (VP) insertion. It is **not** frozen. The objects are exposed
for reuse in VP-insertion families at higher orders.

## Source

L. P. Kaptari, V. I. Lashkevich, O. P. Solovtsova, *The sixth order QED radiative corrections to
lepton anomalies due to the fourth order vacuum polarization insertions within the Mellin–Barnes
representation*, Phys. Rev. D 112 (2025) 073008, arXiv:2508.05119v1:

* eq. (20): the Källén–Sabry spectral function `ρ⁽⁴⁾(δ) = (1/π) Im Π₄(δ) / (α/π)²` of the
  fourth-order (one internal photon) VP operator, in the velocity `δ = √(1 - 4m²/t)`, `t > 4m²`;
* eqs. (4), (6), (18): the insertion of a VP operator into the one-loop vertex through the
  dispersion relation, with measure `dt/t = 2δ dδ/(1-δ²)`;
* eq. (25): at equal masses (`r = 1`), the set (a) coefficient
  `A₂⁽⁶⁾(1) = ∫₀¹ 2δ/(1-δ²) K̃₂(δ,1) ρ⁽⁴⁾(δ) dδ`, with `K̃₂` the `x`-integral of eq. (3) at
  `t/m² = 4/(1-δ²)`.

## Objects (electron mass `m = 1`)

* `ksRho δ`: `ρ⁽⁴⁾(δ)`, written literally from eq. (20) for `0 < δ < 1` (where `Θ(1-δ) = 1`).
* `piHat4 s = ∫₀¹ 2δ/(1-δ²) ρ⁽⁴⁾(δ) · s/(s + 4/(1-δ²)) dδ`: the renormalized fourth-order VP
  function `Π̂⁽⁴⁾(s)` at Euclidean `s = k²/m²`, by the once-subtracted dispersion relation
  (`Π̂⁽⁴⁾(0) = 0`). It is normalized like `QED.Chain.piHat` (Euclidean sign, coefficient of
  `(α/π)²`): with the one-loop weight `ρ⁽²⁾(v) = v(1 - v²/3)/2` in place of `ρ⁽⁴⁾` the same
  formula is `QED.Chain.piHat_eq_spectral`.

## Main statements

* `abs_ksRho_le`: `|ρ⁽⁴⁾(δ)| ≤ 22 - 2 log δ - 3 log(1-δ)` on `(0,1)`.
* `integrableOn_ksRho`: `ρ⁽⁴⁾` is integrable on `(0,1]`.
* `tendsto_ksRho_zero`: `ρ⁽⁴⁾(δ) → π²/4` at threshold (`δ → 0⁺`, `t → 4m²`; Coulomb enhancement).
* `tendsto_ksRho_one`: `ρ⁽⁴⁾(δ) → 1/4` at high energy (`δ → 1⁻`, `t → ∞`).
* `piHat4_zero`, `intervalIntegrable_piHat4_integrand`, `abs_piHat4_le`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology QED.Polylog

namespace QED.Chain

/-- **The Källén–Sabry spectral function** `ρ⁽⁴⁾(δ)` (Kaptari–Lashkevich–Solovtsova 2025,
arXiv:2508.05119, eq. (20)), for `0 < δ < 1`:
`ρ⁽⁴⁾(δ) = [11/16 + 11δ²/24 - 7δ⁴/48 + (1/2 + δ²/3 - δ⁴/6) ln((1+δ)³/(8δ²))] ln((1+δ)/(1-δ))
  + δ [5/8 - 3δ²/8 - (1/2 - δ²/6) ln(64δ⁴/(1-δ²)³)]
  + 2 (1/2 + δ²/3 - δ⁴/6) [2 Li₂((1-δ)/(1+δ)) + Li₂(-(1-δ)/(1+δ))]`. -/
noncomputable def ksRho (δ : ℝ) : ℝ :=
  (11 / 16 + 11 / 24 * δ ^ 2 - 7 / 48 * δ ^ 4 +
      (1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) * log ((1 + δ) ^ 3 / (8 * δ ^ 2))) *
      log ((1 + δ) / (1 - δ)) +
    δ * (5 / 8 - 3 / 8 * δ ^ 2 - (1 / 2 - δ ^ 2 / 6) * log (64 * δ ^ 4 / (1 - δ ^ 2) ^ 3)) +
    2 * (1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) *
      (2 * Li₂ ((1 - δ) / (1 + δ)) + Li₂ (-((1 - δ) / (1 + δ))))

/-- **The renormalized fourth-order VP function** `Π̂⁽⁴⁾(s)` (Euclidean `s = k²/m²`), by the
once-subtracted dispersion relation over the Källén–Sabry spectral function, with
`t = 4/(1-δ²)` and `dt/t = 2δ dδ/(1-δ²)` (Kaptari et al. 2025, eqs. (4), (6), (18)). -/
noncomputable def piHat4 (s : ℝ) : ℝ :=
  ∫ δ in (0 : ℝ)..1, 2 * δ / (1 - δ ^ 2) * ksRho δ * (s / (s + 4 / (1 - δ ^ 2)))

/-- The conformal variable `u = (1-δ)/(1+δ)` lies in `(0,1)` for `δ ∈ (0,1)`. -/
theorem ksU_mem {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) : (1 - δ) / (1 + δ) ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hδ
  refine ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

theorem ksU_mem_Icc {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    (1 - δ) / (1 + δ) ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hδ
  have hp : 0 < 1 + δ := by linarith
  refine ⟨?_, (div_le_one hp).2 (by linarith)⟩
  rw [le_div_iff₀ hp]
  linarith

theorem neg_ksU_mem_Icc {δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) :
    -((1 - δ) / (1 + δ)) ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := ksU_mem_Icc hδ
  constructor <;> linarith

/-! ### Continuity and a logarithmic majorant -/

theorem continuousOn_ksRho : ContinuousOn ksRho (Ioo 0 1) := by
  have hLi : ∀ {f : ℝ → ℝ}, ContinuousOn f (Ioo 0 1) → (∀ δ ∈ Ioo (0 : ℝ) 1, f δ ∈ Icc (-1) 1) →
      ContinuousOn (fun δ => Li₂ (f δ)) (Ioo 0 1) := fun hf hm =>
    continuousOn_Li₂.comp hf fun δ hδ => hm δ hδ
  have hu : ContinuousOn (fun δ : ℝ => (1 - δ) / (1 + δ)) (Ioo 0 1) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun δ hδ => by linarith [hδ.1]
  have h1 := hLi hu fun δ hδ => ksU_mem_Icc (Ioo_subset_Icc_self hδ)
  have h2 := hLi hu.neg fun δ hδ => neg_ksU_mem_Icc (Ioo_subset_Icc_self hδ)
  have hl1 : ContinuousOn (fun δ : ℝ => log ((1 + δ) ^ 3 / (8 * δ ^ 2))) (Ioo 0 1) := by
    refine ContinuousOn.log (ContinuousOn.div (by fun_prop) (by fun_prop) fun δ hδ => ?_)
      fun δ hδ => ?_
    · have := hδ.1; positivity
    · have := hδ.1; positivity
  have hl2 : ContinuousOn (fun δ : ℝ => log ((1 + δ) / (1 - δ))) (Ioo 0 1) := by
    refine ContinuousOn.log (ContinuousOn.div (by fun_prop) (by fun_prop) fun δ hδ => ?_)
      fun δ hδ => ?_
    · linarith [hδ.2]
    · exact (div_pos (by linarith [hδ.1]) (by linarith [hδ.2])).ne'
  have hl3 : ContinuousOn (fun δ : ℝ => log (64 * δ ^ 4 / (1 - δ ^ 2) ^ 3)) (Ioo 0 1) := by
    refine ContinuousOn.log (ContinuousOn.div (by fun_prop) (by fun_prop) fun δ hδ => ?_)
      fun δ hδ => ?_
    · have : 0 < 1 - δ ^ 2 := by nlinarith [hδ.1, hδ.2]
      positivity
    · have : 0 < 1 - δ ^ 2 := by nlinarith [hδ.1, hδ.2]
      have := hδ.1
      positivity
  unfold ksRho
  exact (((continuousOn_const.add (continuousOn_const.mul (continuousOn_id.pow 2))).sub
    (continuousOn_const.mul (continuousOn_id.pow 4))).add
    ((by fun_prop : ContinuousOn (fun δ : ℝ => 1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) (Ioo 0 1)).mul
      hl1)).mul hl2 |>.add (continuousOn_id.mul
    ((by fun_prop : ContinuousOn (fun δ : ℝ => 5 / 8 - 3 / 8 * δ ^ 2) (Ioo 0 1)).sub
      ((by fun_prop : ContinuousOn (fun δ : ℝ => 1 / 2 - δ ^ 2 / 6) (Ioo 0 1)).mul hl3)))
    |>.add ((by fun_prop : ContinuousOn (fun δ : ℝ => 2 * (1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6))
      (Ioo 0 1)).mul ((continuousOn_const.mul h1).add h2))

/-- `log((1+δ)/(1-δ)) ≤ 2δ/(1-δ)` for `0 < δ < 1`. -/
theorem log_one_add_div_one_sub_le {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    log ((1 + δ) / (1 - δ)) ≤ 2 * δ / (1 - δ) := by
  have hs : 0 < 1 - δ := by linarith
  have h := log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < 1 + δ) hs)
  have he : (1 + δ) / (1 - δ) - 1 = 2 * δ / (1 - δ) := by field_simp; ring
  linarith

/-- `-log δ ≤ (1-δ)/δ` for `0 < δ`. -/
theorem neg_log_le {δ : ℝ} (h0 : 0 < δ) : -log δ ≤ (1 - δ) / δ := by
  have h := log_le_sub_one_of_pos (inv_pos.2 h0)
  rw [log_inv] at h
  have he : δ⁻¹ - 1 = (1 - δ) / δ := by field_simp
  linarith

/-- The logarithm `ln((1+δ)³/(8δ²))` of eq. (20) lies in `[0, -2 log δ]` for `0 < δ < 1`. -/
theorem ksLog1_mem {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    0 ≤ log ((1 + δ) ^ 3 / (8 * δ ^ 2)) ∧ log ((1 + δ) ^ 3 / (8 * δ ^ 2)) ≤ -2 * log δ := by
  have hd : 0 < 8 * δ ^ 2 := by positivity
  constructor
  · refine log_nonneg ?_
    rw [le_div_iff₀ hd]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - δ) (by nlinarith : (0 : ℝ) < 1 + 4 * δ - δ ^ 2)]
  · have he : (1 + δ) ^ 3 / (8 * δ ^ 2) = (1 + δ) ^ 3 / 8 * (δ ^ 2)⁻¹ := by
      field_simp
    have hle : (1 + δ) ^ 3 / 8 ≤ 1 := by
      rw [div_le_one (by norm_num)]
      nlinarith
    have hn := log_nonpos (by positivity) hle
    rw [he, log_mul (by positivity) (by positivity), log_inv, log_pow]
    push_cast
    linarith

/-- `|ln(64δ⁴/(1-δ²)³)| ≤ 7 - 4 log δ - 3 log(1-δ)` for `0 < δ < 1`. -/
theorem abs_ksLog2_le {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    |log (64 * δ ^ 4 / (1 - δ ^ 2) ^ 3)| ≤ 7 - 4 * log δ - 3 * log (1 - δ) := by
  have hm : 0 < 1 - δ := by linarith
  have hp : 0 < 1 + δ := by linarith
  have he : log (64 * δ ^ 4 / (1 - δ ^ 2) ^ 3) =
      6 * log 2 + 4 * log δ - 3 * log (1 - δ) - 3 * log (1 + δ) := by
    rw [show 64 * δ ^ 4 / (1 - δ ^ 2) ^ 3 = 2 ^ 6 * δ ^ 4 / ((1 - δ) ^ 3 * (1 + δ) ^ 3) by ring,
      log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_pow, log_pow, log_pow, log_pow]
    push_cast
    ring
  have hl2 := Real.log_two_lt_d9
  have hl20 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha : log δ ≤ 0 := log_nonpos h0.le h1.le
  have hb : log (1 - δ) ≤ 0 := log_nonpos hm.le (by linarith)
  have hc0 : 0 ≤ log (1 + δ) := log_nonneg (by linarith)
  have hc1 : log (1 + δ) ≤ δ := by linarith [log_le_sub_one_of_pos hp]
  rw [he, abs_le]
  constructor <;> nlinarith

/-- **A logarithmic majorant.** `|ρ⁽⁴⁾(δ)| ≤ 22 - 2 log δ - 3 log(1-δ)` for `0 < δ < 1`. -/
theorem abs_ksRho_le {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    |ksRho δ| ≤ 22 - 2 * log δ - 3 * log (1 - δ) := by
  obtain ⟨h0, h1⟩ := hδ
  have hm : 0 < 1 - δ := by linarith
  have hp : 0 < 1 + δ := by linarith
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
  have hδ4 : δ ^ 4 ≤ 1 := by nlinarith
  have ha : log δ ≤ 0 := log_nonpos h0.le h1.le
  have hb : log (1 - δ) ≤ 0 := log_nonpos hm.le (by linarith)
  -- the logarithm `L = ln((1+δ)/(1-δ))`
  have hL : log ((1 + δ) / (1 - δ)) = log (1 + δ) - log (1 - δ) :=
    log_div hp.ne' hm.ne'
  have hc1 : log (1 + δ) ≤ δ := by linarith [log_le_sub_one_of_pos hp]
  have hL0 : 0 ≤ log ((1 + δ) / (1 - δ)) := log_nonneg ((one_le_div hm).2 (by linarith))
  have hLle := log_one_add_div_one_sub_le h0 h1
  -- piece 1
  set A1 := 11 / 16 + 11 / 24 * δ ^ 2 - 7 / 48 * δ ^ 4 with hA1
  have hA10 : 0 ≤ A1 := by nlinarith
  have hA11 : A1 ≤ 6 / 5 := by nlinarith
  have hT1 : |A1 * log ((1 + δ) / (1 - δ))| ≤ 6 / 5 * (1 - log (1 - δ)) := by
    rw [abs_of_nonneg (mul_nonneg hA10 hL0)]
    have : log ((1 + δ) / (1 - δ)) ≤ 1 - log (1 - δ) := by rw [hL]; linarith
    calc A1 * log ((1 + δ) / (1 - δ)) ≤ 6 / 5 * log ((1 + δ) / (1 - δ)) :=
          mul_le_mul_of_nonneg_right hA11 hL0
      _ ≤ 6 / 5 * (1 - log (1 - δ)) := by linarith
  -- piece 2
  set B := 1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6 with hB
  have hB0 : 0 ≤ B := by nlinarith
  have hB1 : B ≤ 1 := by nlinarith
  obtain ⟨hl10, hl11⟩ := ksLog1_mem h0 h1
  have hnl := neg_log_le h0
  have hprod : log ((1 + δ) ^ 3 / (8 * δ ^ 2)) * log ((1 + δ) / (1 - δ)) ≤ 4 := by
    calc log ((1 + δ) ^ 3 / (8 * δ ^ 2)) * log ((1 + δ) / (1 - δ))
        ≤ (2 * ((1 - δ) / δ)) * (2 * δ / (1 - δ)) :=
          mul_le_mul (by linarith) hLle hL0 (by positivity)
      _ = 4 := by field_simp; ring
  have hT2 : |B * log ((1 + δ) ^ 3 / (8 * δ ^ 2)) * log ((1 + δ) / (1 - δ))| ≤ 4 := by
    rw [mul_assoc, abs_of_nonneg (mul_nonneg hB0 (mul_nonneg hl10 hL0))]
    calc B * (log ((1 + δ) ^ 3 / (8 * δ ^ 2)) * log ((1 + δ) / (1 - δ)))
        ≤ 1 * (log ((1 + δ) ^ 3 / (8 * δ ^ 2)) * log ((1 + δ) / (1 - δ))) :=
          mul_le_mul_of_nonneg_right hB1 (mul_nonneg hl10 hL0)
      _ ≤ 4 := by linarith
  -- piece 3
  have hT3 : |δ * (5 / 8 - 3 / 8 * δ ^ 2)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  -- piece 4
  have hl2 := abs_ksLog2_le h0 h1
  have hc40 : 0 ≤ δ * (1 / 2 - δ ^ 2 / 6) := mul_nonneg h0.le (by nlinarith)
  have hc41 : δ * (1 / 2 - δ ^ 2 / 6) ≤ 1 / 2 := by nlinarith
  have hT4 : |δ * (1 / 2 - δ ^ 2 / 6) * log (64 * δ ^ 4 / (1 - δ ^ 2) ^ 3)| ≤
      1 / 2 * (7 - 4 * log δ - 3 * log (1 - δ)) := by
    rw [abs_mul, abs_of_nonneg hc40]
    exact mul_le_mul hc41 hl2 (abs_nonneg _) (by norm_num)
  -- piece 5
  have hpi : π ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hu1 := abs_Li₂_le_of_mem (ksU_mem_Icc ⟨h0.le, h1.le⟩)
  have hu2 := abs_Li₂_le_of_mem (neg_ksU_mem_Icc ⟨h0.le, h1.le⟩)
  have hT5 : |2 * B * (2 * Li₂ ((1 - δ) / (1 + δ)) + Li₂ (-((1 - δ) / (1 + δ))))| ≤ 12 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * B)]
    have : |2 * Li₂ ((1 - δ) / (1 + δ)) + Li₂ (-((1 - δ) / (1 + δ)))| ≤ 6 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two]
      linarith
    calc 2 * B * |2 * Li₂ ((1 - δ) / (1 + δ)) + Li₂ (-((1 - δ) / (1 + δ)))| ≤ 2 * 1 * 6 :=
          mul_le_mul (by linarith) this (abs_nonneg _) (by norm_num)
      _ = 12 := by norm_num
  have hsplit : ksRho δ = A1 * log ((1 + δ) / (1 - δ)) +
      B * log ((1 + δ) ^ 3 / (8 * δ ^ 2)) * log ((1 + δ) / (1 - δ)) +
      δ * (5 / 8 - 3 / 8 * δ ^ 2) -
      δ * (1 / 2 - δ ^ 2 / 6) * log (64 * δ ^ 4 / (1 - δ ^ 2) ^ 3) +
      2 * B * (2 * Li₂ ((1 - δ) / (1 + δ)) + Li₂ (-((1 - δ) / (1 + δ)))) := by
    rw [hA1, hB]; unfold ksRho; ring
  rw [hsplit]
  have e1 := abs_le.1 hT1
  have e2 := abs_le.1 hT2
  have e3 := abs_le.1 hT3
  have e4 := abs_le.1 hT4
  have e5 := abs_le.1 hT5
  rw [abs_le]
  constructor <;> linarith

/-- The majorant `22 - 2 log δ - 3 log(1-δ)` is interval integrable on `[0,1]`. -/
theorem intervalIntegrable_ksMajorant :
    IntervalIntegrable (fun δ : ℝ => 22 - 2 * log δ - 3 * log (1 - δ)) volume 0 1 := by
  have h1 : IntervalIntegrable (fun δ : ℝ => log (1 - δ)) volume 0 1 := by
    have := (intervalIntegral.intervalIntegrable_log' (a := 1) (b := 0)).comp_sub_left 1
    simpa using this
  exact (intervalIntegrable_const.sub
    (intervalIntegral.intervalIntegrable_log'.const_mul 2)).sub (h1.const_mul 3)

/-- Almost every point of `(0,1]` lies in `(0,1)`. -/
theorem ae_mem_Ioo_Ioc : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact ae_restrict_mem measurableSet_Ioo

theorem aestronglyMeasurable_ksRho :
    AEStronglyMeasurable ksRho (volume.restrict (Ioc (0 : ℝ) 1)) := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact continuousOn_ksRho.aestronglyMeasurable measurableSet_Ioo

/-- `ρ⁽⁴⁾` is integrable on `(0,1]`. -/
theorem integrableOn_ksRho : IntegrableOn ksRho (Ioc 0 1) := by
  refine Integrable.mono' ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
    intervalIntegrable_ksMajorant) aestronglyMeasurable_ksRho ?_
  filter_upwards [ae_mem_Ioo_Ioc] with δ hδ
  rw [Real.norm_eq_abs]
  exact abs_ksRho_le hδ

/-! ### Threshold and high-energy behaviour -/

/-- `δ log δ → 0` gives `(1+δ)³/(8δ²)`-log times `δ` tending to `0`. -/
theorem tendsto_mul_ksLog1_zero :
    Tendsto (fun δ : ℝ => log ((1 + δ) ^ 3 / (8 * δ ^ 2)) * log ((1 + δ) / (1 - δ)))
      (𝓝[>] 0) (𝓝 0) := by
  -- squeeze between `0` and `-4 δ log δ / (1 - δ)`
  have hup : Tendsto (fun δ : ℝ => -4 * (δ * log δ) / (1 - δ)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((tendsto_mul_log_zero.const_mul (-4)).div
      ((tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds) (by norm_num :
        (1 : ℝ) - 0 ≠ 0))
    rw [mul_zero, zero_div] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    obtain ⟨h0, h1⟩ := hδ
    exact mul_nonneg (ksLog1_mem h0 h1).1 (log_nonneg ((one_le_div (by linarith)).2
      (by linarith)))
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    obtain ⟨h0, h1⟩ := hδ
    have hm : 0 < 1 - δ := by linarith
    obtain ⟨hl0, hl1⟩ := ksLog1_mem h0 h1
    have hL0 : 0 ≤ log ((1 + δ) / (1 - δ)) := log_nonneg ((one_le_div hm).2 (by linarith))
    have hLle := log_one_add_div_one_sub_le h0 h1
    have hla : 0 ≤ -log δ := by linarith [log_nonpos h0.le h1.le]
    calc log ((1 + δ) ^ 3 / (8 * δ ^ 2)) * log ((1 + δ) / (1 - δ))
        ≤ (-2 * log δ) * (2 * δ / (1 - δ)) := mul_le_mul hl1 hLle hL0 (by linarith)
      _ = -4 * (δ * log δ) / (1 - δ) := by field_simp; ring

/-- **Threshold behaviour.** `ρ⁽⁴⁾(δ) → π²/4` as `δ → 0⁺` (`t → 4m²`). -/
theorem tendsto_ksRho_zero : Tendsto ksRho (𝓝[>] 0) (𝓝 (π ^ 2 / 4)) := by
  have hc : ∀ {f : ℝ → ℝ}, ContinuousAt f 0 → Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := fun hf =>
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have hL : ContinuousAt (fun δ : ℝ => log ((1 + δ) / (1 - δ))) 0 :=
    (continuousAt_log (by norm_num)).comp (by fun_prop (disch := norm_num))
  have hLt := hc hL
  simp only [add_zero, sub_zero, div_one, log_one] at hLt
  have hu : Tendsto (fun δ : ℝ => (1 - δ) / (1 + δ)) (𝓝[>] 0) (𝓝 1) := by
    have := hc (f := fun δ : ℝ => (1 - δ) / (1 + δ)) (by fun_prop (disch := norm_num))
    simpa using this
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    exact Ioo_subset_Icc_self hδ
  have hP := tendsto_Li₂_comp (by norm_num) hu (hev.mono fun δ hδ => ksU_mem_Icc hδ)
  have hM := tendsto_Li₂_comp (by norm_num) hu.neg (hev.mono fun δ hδ => neg_ksU_mem_Icc hδ)
  rw [Li₂_one] at hP
  rw [Li₂_neg_one] at hM
  -- the term `δ ln(64δ⁴/(1-δ²)³) = δ(6 ln 2 - 3 ln(1-δ²)) + 4 δ ln δ`
  have hT4 : Tendsto (fun δ : ℝ => δ * log (64 * δ ^ 4 / (1 - δ ^ 2) ^ 3)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => δ * (log 64 - 3 * log (1 - δ ^ 2)) + 4 * (δ * log δ))
        (𝓝[>] 0) (𝓝 (0 * (log 64 - 3 * log (1 - 0 ^ 2)) + 4 * 0)) := by
      refine (Tendsto.mul (tendsto_id.mono_left nhdsWithin_le_nhds) ?_).add
        (tendsto_mul_log_zero.const_mul 4)
      exact hc (f := fun δ : ℝ => log 64 - 3 * log (1 - δ ^ 2))
        (ContinuousAt.sub continuousAt_const (((continuousAt_log (by norm_num)).comp
          (by fun_prop)).const_mul 3))
    simp only [zero_mul, mul_zero, add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    obtain ⟨h0, h1⟩ := hδ
    have hs : 0 < 1 - δ ^ 2 := by nlinarith
    rw [log_div (by positivity) (by positivity), log_mul (by norm_num) (by positivity),
      log_pow, log_pow]
    push_cast
    ring
  have hδ : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hpoly : ∀ (p : ℝ → ℝ), Continuous p → Tendsto p (𝓝[>] 0) (𝓝 (p 0)) := fun p hp =>
    hc hp.continuousAt
  have hA := hpoly (fun δ : ℝ => 11 / 16 + 11 / 24 * δ ^ 2 - 7 / 48 * δ ^ 4) (by fun_prop)
  have hB := hpoly (fun δ : ℝ => 1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) (by fun_prop)
  have hC := hpoly (fun δ : ℝ => 5 / 8 - 3 / 8 * δ ^ 2) (by fun_prop)
  have hD := hpoly (fun δ : ℝ => 1 / 2 - δ ^ 2 / 6) (by fun_prop)
  have h := (((hA.mul hLt).add (hB.mul tendsto_mul_ksLog1_zero)).add
    ((hδ.mul hC).sub (hD.mul hT4))).add ((hB.const_mul 2).mul ((hP.const_mul 2).add hM))
  have hv : (11 / 16 + 11 / 24 * (0 : ℝ) ^ 2 - 7 / 48 * 0 ^ 4) * 0 +
      (1 / 2 + 0 ^ 2 / 3 - 0 ^ 4 / 6) * 0 + (0 * (5 / 8 - 3 / 8 * 0 ^ 2) -
      (1 / 2 - 0 ^ 2 / 6) * 0) + 2 * (1 / 2 + 0 ^ 2 / 3 - 0 ^ 4 / 6) *
      (2 * (π ^ 2 / 6) + -π ^ 2 / 12) = π ^ 2 / 4 := by ring
  rw [hv] at h
  refine h.congr' (Eventually.of_forall fun δ => ?_)
  simp only [ksRho]
  ring

/-- The coefficient of `log(1-δ)` in `ρ⁽⁴⁾`, which vanishes at `δ = 1`. -/
noncomputable def ksCoefOne (δ : ℝ) : ℝ :=
  -(11 / 16 + 11 / 24 * δ ^ 2 - 7 / 48 * δ ^ 4 +
      (1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) * log ((1 + δ) ^ 3 / (8 * δ ^ 2))) +
    3 * δ * (1 / 2 - δ ^ 2 / 6)

/-- The part of `ρ⁽⁴⁾` that is continuous at `δ = 1`. -/
noncomputable def ksRegOne (δ : ℝ) : ℝ :=
  (11 / 16 + 11 / 24 * δ ^ 2 - 7 / 48 * δ ^ 4 +
      (1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) * log ((1 + δ) ^ 3 / (8 * δ ^ 2))) * log (1 + δ) +
    δ * (5 / 8 - 3 / 8 * δ ^ 2 -
      (1 / 2 - δ ^ 2 / 6) * (6 * log 2 + 4 * log δ - 3 * log (1 + δ))) +
    2 * (1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) *
      (2 * Li₂ ((1 - δ) / (1 + δ)) + Li₂ (-((1 - δ) / (1 + δ))))

theorem ksRho_eq_one_form {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ksRho δ = ksRegOne δ + ksCoefOne δ * log (1 - δ) := by
  obtain ⟨h0, h1⟩ := hδ
  have hm : 0 < 1 - δ := by linarith
  have hp : 0 < 1 + δ := by linarith
  have hL : log ((1 + δ) / (1 - δ)) = log (1 + δ) - log (1 - δ) := log_div hp.ne' hm.ne'
  have he : log (64 * δ ^ 4 / (1 - δ ^ 2) ^ 3) =
      6 * log 2 + 4 * log δ - 3 * log (1 - δ) - 3 * log (1 + δ) := by
    rw [show 64 * δ ^ 4 / (1 - δ ^ 2) ^ 3 = 2 ^ 6 * δ ^ 4 / ((1 - δ) ^ 3 * (1 + δ) ^ 3) by ring,
      log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_pow, log_pow, log_pow, log_pow]
    push_cast
    ring
  unfold ksRho ksRegOne ksCoefOne
  rw [hL, he]
  ring

theorem differentiableAt_ksCoefOne : DifferentiableAt ℝ ksCoefOne 1 := by
  unfold ksCoefOne
  fun_prop (disch := norm_num)

theorem ksCoefOne_one : ksCoefOne 1 = 0 := by
  norm_num [ksCoefOne]

/-- **High-energy behaviour.** `ρ⁽⁴⁾(δ) → 1/4` as `δ → 1⁻` (`t → ∞`). -/
theorem tendsto_ksRho_one : Tendsto ksRho (𝓝[<] 1) (𝓝 (1 / 4)) := by
  have hc : ∀ {f : ℝ → ℝ}, ContinuousAt f 1 → Tendsto f (𝓝[<] 1) (𝓝 (f 1)) := fun hf =>
    hf.tendsto.mono_left nhdsWithin_le_nhds
  -- the singular part: `c(δ) log(1-δ) = (c(δ)/(δ-1)) · (-(1-δ) log(1-δ))`
  have hslope : Tendsto (fun δ => (ksCoefOne δ - ksCoefOne 1) / (δ - 1)) (𝓝[<] 1)
      (𝓝 (deriv ksCoefOne 1)) := by
    have h := differentiableAt_ksCoefOne.hasDerivAt.tendsto_slope
    refine (h.mono_left (nhdsWithin_mono _ ?_)).congr' (Eventually.of_forall fun δ => ?_)
    · intro x hx
      exact ne_of_lt hx
    · simp [slope_def_field]
  have hsing : Tendsto (fun δ => ksCoefOne δ * log (1 - δ)) (𝓝[<] 1) (𝓝 0) := by
    have h := hslope.mul ((tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one).neg)
    rw [neg_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : δ < 1)
    rw [ksCoefOne_one, sub_zero]
    have : δ - 1 ≠ 0 := by linarith
    simp only [Function.comp_apply]
    field_simp
    ring
  have hev : ∀ᶠ δ in 𝓝[<] (1 : ℝ), δ ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    exact Ioo_subset_Icc_self hδ
  have hu : Tendsto (fun δ : ℝ => (1 - δ) / (1 + δ)) (𝓝[<] 1) (𝓝 0) := by
    have := hc (f := fun δ : ℝ => (1 - δ) / (1 + δ)) (by fun_prop (disch := norm_num))
    simpa using this
  have hP := tendsto_Li₂_comp (by norm_num) hu (hev.mono fun δ hδ => ksU_mem_Icc hδ)
  have hM := tendsto_Li₂_comp (by norm_num) hu.neg (hev.mono fun δ hδ => neg_ksU_mem_Icc hδ)
  simp only [neg_zero] at hM
  have hreg : ContinuousAt (fun δ : ℝ =>
      (11 / 16 + 11 / 24 * δ ^ 2 - 7 / 48 * δ ^ 4 +
        (1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6) * log ((1 + δ) ^ 3 / (8 * δ ^ 2))) * log (1 + δ) +
      δ * (5 / 8 - 3 / 8 * δ ^ 2 -
        (1 / 2 - δ ^ 2 / 6) * (6 * log 2 + 4 * log δ - 3 * log (1 + δ)))) 1 := by
    have h1 : ContinuousAt (fun δ : ℝ => log ((1 + δ) ^ 3 / (8 * δ ^ 2))) 1 :=
      (continuousAt_log (by norm_num)).comp (by fun_prop (disch := norm_num))
    have h2 : ContinuousAt (fun δ : ℝ => log (1 + δ)) 1 :=
      (continuousAt_log (by norm_num)).comp (by fun_prop)
    have h3 : ContinuousAt log 1 := continuousAt_log (by norm_num)
    fun_prop
  have h := ((hc hreg).add ((((hc (f := fun δ : ℝ => 1 / 2 + δ ^ 2 / 3 - δ ^ 4 / 6)
    (by fun_prop)).const_mul 2).mul ((hP.const_mul 2).add hM)))).add hsing
  have hv : (11 / 16 + 11 / 24 * (1 : ℝ) ^ 2 - 7 / 48 * 1 ^ 4 +
      (1 / 2 + 1 ^ 2 / 3 - 1 ^ 4 / 6) * log ((1 + 1) ^ 3 / (8 * 1 ^ 2))) * log (1 + 1) +
      1 * (5 / 8 - 3 / 8 * 1 ^ 2 - (1 / 2 - 1 ^ 2 / 6) * (6 * log 2 + 4 * log 1 -
        3 * log (1 + 1))) + 2 * (1 / 2 + 1 ^ 2 / 3 - 1 ^ 4 / 6) * (2 * Li₂ 0 + Li₂ 0) + 0 =
      1 / 4 := by
    norm_num [Li₂_zero]
    ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
  rw [ksRho_eq_one_form hδ, ksRegOne]

/-! ### The fourth-order VP function -/

theorem piHat4_zero : piHat4 0 = 0 := by
  simp [piHat4]

/-- For `s ≥ 0` and `0 ≤ δ < 1`, `0 ≤ 2δ/(1-δ²) · s/(s + 4/(1-δ²)) ≤ s/2`. -/
theorem piHat4_weight_mem {s δ : ℝ} (hs : 0 ≤ s) (h0 : 0 ≤ δ) (h1 : δ < 1) :
    0 ≤ 2 * δ / (1 - δ ^ 2) * (s / (s + 4 / (1 - δ ^ 2))) ∧
      2 * δ / (1 - δ ^ 2) * (s / (s + 4 / (1 - δ ^ 2))) ≤ s / 2 := by
  have hq : 0 < 1 - δ ^ 2 := by nlinarith
  have he : 2 * δ / (1 - δ ^ 2) * (s / (s + 4 / (1 - δ ^ 2))) =
      2 * δ * s / (s * (1 - δ ^ 2) + 4) := by
    field_simp
  rw [he]
  have hd : 0 < s * (1 - δ ^ 2) + 4 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ hd (by norm_num)]
  nlinarith [mul_nonneg hs hq.le]

/-- The dispersion integrand of `Π̂⁽⁴⁾(s)` is interval integrable for `s ≥ 0`. -/
theorem intervalIntegrable_piHat4_integrand {s : ℝ} (hs : 0 ≤ s) :
    IntervalIntegrable (fun δ => 2 * δ / (1 - δ ^ 2) * ksRho δ * (s / (s + 4 / (1 - δ ^ 2))))
      volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hmeas : AEStronglyMeasurable (fun δ => 2 * δ / (1 - δ ^ 2) * ksRho δ *
      (s / (s + 4 / (1 - δ ^ 2)))) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    refine ContinuousOn.mul (ContinuousOn.mul ?_ continuousOn_ksRho) ?_
    · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun δ hδ => by
        nlinarith [hδ.1, hδ.2]
    · refine ContinuousOn.div continuousOn_const ?_ fun δ hδ => ?_
      · exact continuousOn_const.add (ContinuousOn.div continuousOn_const (by fun_prop)
          fun δ hδ => by nlinarith [hδ.1, hδ.2])
      · have : 0 < 1 - δ ^ 2 := by nlinarith [hδ.1, hδ.2]
        positivity
  refine Integrable.mono' (integrableOn_ksRho.norm.const_mul (s / 2)) hmeas ?_
  filter_upwards [ae_mem_Ioo_Ioc] with δ hδ
  obtain ⟨hw0, hw1⟩ := piHat4_weight_mem hs hδ.1.le hδ.2
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    show 2 * δ / (1 - δ ^ 2) * ksRho δ * (s / (s + 4 / (1 - δ ^ 2))) =
      (2 * δ / (1 - δ ^ 2) * (s / (s + 4 / (1 - δ ^ 2)))) * ksRho δ by ring,
    abs_mul, abs_of_nonneg hw0]
  exact mul_le_mul_of_nonneg_right hw1 (abs_nonneg _)

end QED.Chain
