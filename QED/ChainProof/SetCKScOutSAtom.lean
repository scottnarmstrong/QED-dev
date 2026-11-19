/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutSFub
public import QED.TwoLoop.UnitLLinkLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G4: the pole part of the self-energy unit

Helper level (no frozen statement). The `1/u²` atoms of the self-energy part of G4 at `(Y, x)`,
`u = Q(x) + t`, are `(B(x) - 2 k₂(Y, x) ρ(x)² log Y²)/u²` (`scOutSAt`): the pole of
`2 scOutSG` (`scOutSG_eq`) and the `1/u²` part of the counterterm (`scOutSCt_eq`). The
`Y`-integral is elementary (`∫₀¹ log Y = -1`, `∫₀¹ Y log Y = -1/4`, `k₂` affine in `Y`):

`∫₀¹ (B - 2 k₂ ρ² log Y²) dY = E₂(x) = x⁴(2 - x)/(2(1 - x))`,

and `E₂(x)/u² = (x³(1 - x)/2) Q'(x)/(Q(x) + t)²` (**`integral_scOutSAt`**). So the pole part
contributes `X³(1 - X)/2` to the weight `H` of the `Q`-derivative form, at the same point.
On the square the atom is bounded by `(4/t)(1 - log Y)` (`abs_scOutSAt_le`), hence integrable,
and **`integral_scOutSAt_square`** gives its double integral as a node integral.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The pole part at `(Y, x)`: `(B(x) - 2 k₂ ρ² log Y²)/u²`, `u = Q(x) + t`. -/
noncomputable def scOutSAt (t Y x : ℝ) : ℝ :=
  (scOutSB x - 2 * (selfK2 Y x * scOutRho x ^ 2 * log (Y ^ 2))) / (setCKQ x + t) ^ 2

theorem measurable_scOutSAt (t : ℝ) : Measurable fun p : ℝ × ℝ => scOutSAt t p.1 p.2 := by
  unfold scOutSAt scOutSB selfK2 scOutRho setCKQ
  fun_prop

section

variable {t Y x : ℝ}

/-- **The size of the pole part.** -/
theorem abs_scOutSAt_le (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |scOutSAt t Y x| ≤ 4 / t * (1 + -log Y) := by
  have hu : 0 < setCKQ x + t := scOutSu_pos ht hx
  have hQ := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hx0 := hx.1
  have hx1 := hx.2
  have hY0 := hY.1
  have hY1 := hY.2
  have hlY : 0 ≤ -log Y := neg_nonneg.2 (log_nonpos hY0.le hY1.le)
  have e : scOutSAt t Y x = setCKQ x / (setCKQ x + t) * (1 / (setCKQ x + t)) *
      (5 * x ^ 2 * (3 - x) / 4 - x ^ 2 * (3 - x - Y * (1 - x)) / 2 * (2 * -log Y)) := by
    unfold scOutSAt scOutSB selfK2 scOutRho setCKQ
    rw [log_pow]
    have : 1 - x ≠ 0 := by linarith
    have : x - 1 ≠ 0 := by linarith
    have : x ^ 2 / (1 - x) + t ≠ 0 := by
      have : 0 < x ^ 2 / (1 - x) + t := by unfold setCKQ at hu; exact hu
      exact this.ne'
    field_simp
    ring
  have h1 : |setCKQ x / (setCKQ x + t)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one hu]
    linarith
  have h2 : |1 / (setCKQ x + t)| ≤ 1 / t := by
    rw [abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le ht (by linarith)
  have cB0 : 0 ≤ 5 * x ^ 2 * (3 - x) / 4 := by
    have : 0 ≤ 3 - x := by linarith
    positivity
  have cB1 : 5 * x ^ 2 * (3 - x) / 4 ≤ 4 := by nlinarith
  have cb0 : 0 ≤ x ^ 2 * (3 - x - Y * (1 - x)) / 2 := by
    have : 0 ≤ 3 - x - Y * (1 - x) := by nlinarith
    positivity
  have cb1 : x ^ 2 * (3 - x - Y * (1 - x)) / 2 ≤ 2 := by
    have : x ^ 2 ≤ 1 := by nlinarith
    have h3 : 0 ≤ 3 - x - Y * (1 - x) := by nlinarith
    have : 3 - x - Y * (1 - x) ≤ 3 := by nlinarith
    have : x ^ 2 * (3 - x - Y * (1 - x)) ≤ 1 * 3 :=
      mul_le_mul (by assumption) this h3 zero_le_one
    linarith
  have h3 : |5 * x ^ 2 * (3 - x) / 4 - x ^ 2 * (3 - x - Y * (1 - x)) / 2 * (2 * -log Y)| ≤
      4 * (1 + -log Y) := by
    have hm : 0 ≤ x ^ 2 * (3 - x - Y * (1 - x)) / 2 * (2 * -log Y) := by positivity
    have hM : x ^ 2 * (3 - x - Y * (1 - x)) / 2 * (2 * -log Y) ≤ 2 * (2 * -log Y) :=
      mul_le_mul_of_nonneg_right cb1 (by positivity)
    rw [abs_le]
    constructor <;> linarith
  rw [e, abs_mul, abs_mul]
  calc |setCKQ x / (setCKQ x + t)| * |1 / (setCKQ x + t)| *
        |5 * x ^ 2 * (3 - x) / 4 - x ^ 2 * (3 - x - Y * (1 - x)) / 2 * (2 * -log Y)|
      ≤ 1 * (1 / t) * (4 * (1 + -log Y)) := by gcongr
    _ = 4 / t * (1 + -log Y) := by ring

end

/-- The pole part is integrable on the square. -/
theorem integrable_scOutSAt {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : ℝ × ℝ => scOutSAt t p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have iL : Integrable (fun x => -log x) μ := integrableOn_neg_log_Ioo
  have hD : Integrable (fun p : ℝ × ℝ => 4 / t * (1 + -log p.1)) (μ.prod μ) :=
    ((integrable_const (1 : ℝ)).add (iL.comp_fst μ)).const_mul (4 / t)
  refine Integrable.mono' hD (measurable_scOutSAt t).aestronglyMeasurable ?_
  filter_upwards [ae_mem_square_Ioo] with p hp
  rw [Real.norm_eq_abs]
  exact abs_scOutSAt_le ht hp.1 hp.2

/-- **The `Y`-integral of the pole part** at a node `x`. -/
theorem integral_scOutSAt {t x : ℝ} (ht : 0 < t) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ Y in Ioo (0 : ℝ) 1, scOutSAt t Y x =
      x ^ 3 * (1 - x) / 2 * (setCKdQ x / (setCKQ x + t) ^ 2) := by
  set u := setCKQ x + t with hu_def
  have hu : 0 < u := scOutSu_pos ht hx
  set P := scOutSB x / u ^ 2 with hP
  set R := -(4 * scOutRho x ^ 2 * (x ^ 2 * (x - 1) * (3 - x) / 4)) / u ^ 2 with hR
  set S := -(4 * scOutRho x ^ 2 * (x ^ 2 * (x - 1) ^ 2 / 4)) / u ^ 2 with hS
  have e : ∀ Y, scOutSAt t Y x = P + R * log Y + S * (Y * log Y) := fun Y => by
    rw [scOutSAt, ← hu_def, hP, hR, hS, selfK2, log_pow]
    push_cast
    ring
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  simp only [e]
  obtain ⟨iYL, vYL⟩ := intervalIntegrable_and_integral_mul_log
  have iL : IntervalIntegrable (fun Y : ℝ => log Y) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'
  have i1 : IntervalIntegrable (fun Y : ℝ => P + R * log Y) volume 0 1 :=
    intervalIntegrable_const.add (iL.const_mul R)
  rw [intervalIntegral.integral_add i1 (iYL.const_mul S),
    intervalIntegral.integral_add intervalIntegrable_const (iL.const_mul R),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, vYL,
    integral_log, intervalIntegral.integral_const]
  simp only [log_one, mul_zero, sub_zero, zero_mul, smul_eq_mul]
  rw [hP, hR, hS]
  unfold scOutSB scOutRho setCKdQ
  have : 1 - x ≠ 0 := by linarith [hx.2]
  have : x - 1 ≠ 0 := by linarith [hx.2]
  have := hu.ne'
  field_simp
  ring

/-- **The pole part as a node integral**: integrable, with
`∫_{(0,1)²} scOutSAt = ∫₀¹ (X³(1 - X)/2) Q'(X)/(Q(X) + t)² dX`. -/
theorem integral_scOutSAt_square {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun X => X ^ 3 * (1 - X) / 2 * (setCKdQ X / (setCKQ X + t) ^ 2))
        (Ioo (0 : ℝ) 1) ∧
      ∫ p, scOutSAt t p.1 p.2 ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
        ∫ X in Ioo (0 : ℝ) 1, X ^ 3 * (1 - X) / 2 * (setCKdQ X / (setCKQ X + t) ^ 2) := by
  have hI := integrable_scOutSAt ht
  have hr := hI.integral_prod_right
  have he : ∀ X ∈ Ioo (0 : ℝ) 1, ∫ Y in Ioo (0 : ℝ) 1, scOutSAt t Y X =
      X ^ 3 * (1 - X) / 2 * (setCKdQ X / (setCKQ X + t) ^ 2) := fun X hX =>
    integral_scOutSAt ht hX
  refine ⟨IntegrableOn.congr_fun (f := fun X => ∫ Y in Ioo (0 : ℝ) 1, scOutSAt t Y X) hr he
    measurableSet_Ioo, ?_⟩
  rw [integral_prod_symm _ hI]
  exact setIntegral_congr_fun measurableSet_Ioo he

end QED.ChainProof.SetCK

end
