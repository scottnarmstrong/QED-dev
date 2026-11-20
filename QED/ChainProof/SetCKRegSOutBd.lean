/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutSDom
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K: the outer-massive self-energy integrand at inner photon mass `λ`, bound

Helper level (no frozen statement). In the self-energy unit with the outer photon of mass²
`t > 0` and the inner photon of mass `λ`, the two-loop `x`-integrand of eq. (5.3) is
`selfGm (√t) λ Y x + k₂/h_t²` (`scOutRegS`; at `λ = 0` it is `scOutSG`). Its `(u + v)⁻²`-form
(`scOut_sForm_eq` at `M = M_λ(Y) = Y² + (1-Y) λ²`) has `V = M ρ/c ≥ Y ρ/(1-Y)` and
`|p| = |k₁ ρ log M| ≤ 3 (-log Y)` for `λ² ≤ 1` (`Y² ≤ M ≤ 1`), so the bound of
`scOutSW_abs_integral_le` holds uniformly in `λ`:

* **`abs_scOutRegS_le`**: `|scOutRegS t λ Y x| ≤ 20 (1 + 1/t)(1 - log Y - log x)` for `λ² ≤ 1`;
* **`continuousAt_scOutRegS`**: `scOutRegS t λ Y x` is continuous in `λ` at `λ = 0`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The two-loop `x`-integrand of the outer-massive self-energy unit at inner photon mass `λ`. -/
noncomputable def scOutRegS (t lam Y x : ℝ) : ℝ :=
  selfGm (√t) lam Y x + selfK2 Y x / hOut t x ^ 2

/-- The dominating function `20 (1 + 1/t)(1 - log Y - log x)`. -/
noncomputable def scOutRegSDom (t Y x : ℝ) : ℝ := 20 * (1 + 1 / t) * (1 + -log Y + -log x)

theorem scOutRegS_zero (t Y x : ℝ) : scOutRegS t 0 Y x = scOutSG t Y x := rfl

theorem regMassOut_bounds {lam Y : ℝ} (hl : lam ^ 2 ≤ 1) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    Y ^ 2 ≤ ladderInnerMass 1 lam Y ∧ ladderInnerMass 1 lam Y ≤ 1 := by
  have h1 : 0 < 1 - Y := by linarith [hY.2]
  unfold ladderInnerMass
  constructor
  · nlinarith [mul_nonneg h1.le (sq_nonneg lam)]
  · nlinarith [mul_le_mul_of_nonneg_left hl h1.le, hY.1]

theorem regAbs_log_mass_le {lam Y : ℝ} (hl : lam ^ 2 ≤ 1) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    |log (ladderInnerMass 1 lam Y)| ≤ 2 * -log Y := by
  obtain ⟨hl1, hu1⟩ := regMassOut_bounds hl hY
  have hY2 : 0 < Y ^ 2 := pow_pos hY.1 2
  have hM : 0 < ladderInnerMass 1 lam Y := hY2.trans_le hl1
  have a1 : log (ladderInnerMass 1 lam Y) ≤ 0 := log_nonpos hM.le hu1
  have a2 : 2 * log Y ≤ log (ladderInnerMass 1 lam Y) := by
    have := log_le_log hY2 hl1
    rw [log_pow] at this
    push_cast at this
    exact this
  rw [abs_of_nonpos a1]
  linarith

theorem regScOut_abs_alpha {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |selfK1 Y x * scOutRho x| ≤ 3 / 2 := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  have ea : 2 * (selfK1 Y x * scOutRho x) = x ^ 2 * (Y * (2 * x + 1) + 2 * (1 - x)) := by
    unfold selfK1 scOutRho
    have : 1 - x ≠ 0 := by linarith
    field_simp
    ring
  have c0 : 0 ≤ Y * (2 * x + 1) + 2 * (1 - x) := by nlinarith
  have c1 : Y * (2 * x + 1) + 2 * (1 - x) ≤ 3 := by nlinarith
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have h2 : 0 ≤ x ^ 2 * (Y * (2 * x + 1) + 2 * (1 - x)) := by positivity
  have h3 : x ^ 2 * (Y * (2 * x + 1) + 2 * (1 - x)) ≤ 3 := by nlinarith
  rw [abs_le]
  constructor <;> linarith only [ea, h2, h3]

theorem regScOut_abs_beta {t Y x : ℝ} (ht : 0 ≤ t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : |selfK2 Y x * scOutRho x ^ 2| ≤ setCKQ x + t := by
  have hQ := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hx0, hx1⟩ := hx
  have eb : 2 * (selfK2 Y x * scOutRho x ^ 2) =
      -(setCKQ x * (x ^ 2 * (3 - x - Y * (1 - x)) / 2)) := by
    unfold selfK2 scOutRho setCKQ
    have : 1 - x ≠ 0 := by linarith
    field_simp
    ring
  have c0 : 0 ≤ 3 - x - Y * (1 - x) := by nlinarith
  have c1 : x ^ 2 * (3 - x - Y * (1 - x)) / 2 ≤ 2 := by
    have : x ^ 2 ≤ 1 := by nlinarith
    have : 3 - x - Y * (1 - x) ≤ 3 := by nlinarith
    have : x ^ 2 * (3 - x - Y * (1 - x)) ≤ 1 * 3 :=
      mul_le_mul (by assumption) this c0 zero_le_one
    linarith
  have c2 : 0 ≤ x ^ 2 * (3 - x - Y * (1 - x)) / 2 := by positivity
  have h2 : 0 ≤ setCKQ x * (x ^ 2 * (3 - x - Y * (1 - x)) / 2) := mul_nonneg hQ c2
  have h3 : setCKQ x * (x ^ 2 * (3 - x - Y * (1 - x)) / 2) ≤ setCKQ x * 2 :=
    mul_le_mul_of_nonneg_left c1 hQ
  rw [abs_le]
  constructor <;> linarith only [eb, h2, h3, hQ, ht]

/-- The size of the terms of the bound, in abstract variables. -/
theorem regScOut_terms_le {α β lM u V t ℓ LY Lx : ℝ} (ht : 0 < t) (htu : t ≤ u) (hV : 0 < V)
    (ha : |α| ≤ 3 / 2) (hb : |β| ≤ u) (hlM : |lM| ≤ 2 * LY) (hlY : 0 ≤ LY) (hlx : 0 ≤ Lx)
    (hℓ : ℓ / u ≤ 1 + (LY + Lx) * (1 / t)) (hℓ0 : 0 ≤ ℓ / u) :
    (5 / 2 * |α| + |-(α * lM)|) / u + 3 * |β| / u ^ 2 + (3 / 2 * |α| + |-(α * lM)|) / (u + V) +
        |α| * (ℓ / u) + |β| * (ℓ / u ^ 2) + |β * lM / u ^ 2| ≤
      20 * (1 + 1 / t) * (1 + LY + Lx) := by
  have hu : 0 < u := ht.trans_le htu
  set s := 1 / t with hs_def
  have hs0 : 0 ≤ s := by positivity
  have hsu : 1 / u ≤ s := one_div_le_one_div_of_le ht htu
  have hsuV : 1 / (u + V) ≤ s := one_div_le_one_div_of_le ht (by linarith)
  have hp : |-(α * lM)| ≤ 3 * LY := by
    rw [abs_neg, abs_mul]
    calc |α| * |lM| ≤ 3 / 2 * (2 * LY) := mul_le_mul ha hlM (abs_nonneg _) (by norm_num)
      _ = 3 * LY := by ring
  have hbu : |β| / u ≤ 1 := by rw [div_le_iff₀ hu]; linarith
  have t1 : (5 / 2 * |α| + |-(α * lM)|) / u ≤ (15 / 4 + 3 * LY) * s := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hsu (by positivity) (by positivity)
  have t2 : 3 * |β| / u ^ 2 ≤ 3 * s := by
    have : 3 * |β| / u ^ 2 = 3 * (|β| / u) * (1 / u) := by field_simp
    rw [this]
    calc 3 * (|β| / u) * (1 / u) ≤ 3 * 1 * s := by gcongr
      _ = 3 * s := by ring
  have t3 : (3 / 2 * |α| + |-(α * lM)|) / (u + V) ≤ (9 / 4 + 3 * LY) * s := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hsuV (by positivity) (by positivity)
  have t4 : |α| * (ℓ / u) ≤ 3 / 2 * (1 + (LY + Lx) * s) :=
    mul_le_mul ha hℓ hℓ0 (by norm_num)
  have t5 : |β| * (ℓ / u ^ 2) ≤ 1 * (1 + (LY + Lx) * s) := by
    have e5 : |β| * (ℓ / u ^ 2) = (|β| / u) * (ℓ / u) := by field_simp
    rw [e5]
    exact mul_le_mul hbu hℓ hℓ0 (by norm_num)
  have t6 : |β * lM / u ^ 2| ≤ 2 * (LY * s) := by
    have e6 : |β * lM / u ^ 2| = (|β| / u) * (1 / u) * |lM| := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < u ^ 2)]
      field_simp
    rw [e6]
    calc (|β| / u) * (1 / u) * |lM| ≤ 1 * s * (2 * LY) := by gcongr
      _ = 2 * (LY * s) := by ring
  have hLYs : 0 ≤ LY * s := mul_nonneg hlY hs0
  have hLxs : 0 ≤ Lx * s := mul_nonneg hlx hs0
  have e1 : (15 / 4 + 3 * LY) * s = 15 / 4 * s + 3 * (LY * s) := by ring
  have e3 : (9 / 4 + 3 * LY) * s = 9 / 4 * s + 3 * (LY * s) := by ring
  have e4 : 3 / 2 * (1 + (LY + Lx) * s) = 3 / 2 + 3 / 2 * (LY * s) + 3 / 2 * (Lx * s) := by
    ring
  have e5 : 1 * (1 + (LY + Lx) * s) = 1 + LY * s + Lx * s := by ring
  have e : 20 * (1 + s) * (1 + LY + Lx) = 20 + 20 * s + 20 * LY + 20 * Lx + 20 * (LY * s) +
      20 * (Lx * s) := by ring
  rw [e1] at t1
  rw [e3] at t3
  rw [e4] at t4
  rw [e5] at t5
  rw [e]
  linarith only [t1, t2, t3, t4, t5, t6, hLYs, hLxs, hs0, hlY, hlx]

/-- **The bound on the outer-massive self-energy integrand, uniform in `λ² ≤ 1`.** -/
theorem abs_scOutRegS_le {t lam Y x : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |scOutRegS t lam Y x| ≤ scOutRegSDom t Y x := by
  obtain ⟨hMl, -⟩ := regMassOut_bounds hl hY
  have hM : 0 < ladderInnerMass 1 lam Y := (pow_pos hY.1 2).trans_le hMl
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 (by linarith [hY.2])
  have hu : 0 < setCKQ x + t := scOutSu_pos ht hx
  have hρ := scOutRho_pos hx
  have hQ := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have e := scOut_sForm_eq (k₁ := selfK1 Y x) (k₂ := selfK2 Y x) hc hM hρ hu
  have hrep : scOutRegS t lam Y x =
      (∫ v in Ioi 0, scOutTg (selfK1 Y x * scOutRho x) (selfK2 Y x * scOutRho x ^ 2)
        (ladderInnerMass 1 lam Y * scOutRho x / (Y * (1 - Y)))
        (-(selfK1 Y x * scOutRho x * log (ladderInnerMass 1 lam Y))) v /
          (setCKQ x + t + v) ^ 2) -
        selfK2 Y x * scOutRho x ^ 2 * log (ladderInnerMass 1 lam Y) / (setCKQ x + t) ^ 2 := by
    unfold scOutRegS selfGm
    rw [← hOut, hOut_eq_div_scOutRho ht.le hx, e]
  have hV : 0 < ladderInnerMass 1 lam Y * scOutRho x / (Y * (1 - Y)) := by positivity
  have hV0 := scOutSV_pos hY hx
  have hVV : Y ^ 2 * scOutRho x / (Y * (1 - Y)) ≤
      ladderInnerMass 1 lam Y * scOutRho x / (Y * (1 - Y)) := by gcongr
  have hI := scOutTg_abs_integral_le (α := selfK1 Y x * scOutRho x)
    (β := selfK2 Y x * scOutRho x ^ 2)
    (p := -(selfK1 Y x * scOutRho x * log (ladderInnerMass 1 lam Y))) hu hV
  have hlog0 := scOutS_log_div_le ht hY hx
  have hℓ : log (1 + (setCKQ x + t) / (ladderInnerMass 1 lam Y * scOutRho x / (Y * (1 - Y)))) /
      (setCKQ x + t) ≤ 1 + (-log Y + -log x) * (1 / t) := by
    refine le_trans ?_ hlog0
    gcongr
  have hℓ0 : 0 ≤ log (1 + (setCKQ x + t) /
      (ladderInnerMass 1 lam Y * scOutRho x / (Y * (1 - Y)))) / (setCKQ x + t) :=
    div_nonneg (log_nonneg (by
      have : 0 ≤ (setCKQ x + t) / (ladderInnerMass 1 lam Y * scOutRho x / (Y * (1 - Y))) := by
        positivity
      linarith)) hu.le
  have hlY : 0 ≤ -log Y := neg_nonneg.2 (log_nonpos hY.1.le hY.2.le)
  have hlx : 0 ≤ -log x := neg_nonneg.2 (log_nonpos hx.1.le hx.2.le)
  have key := regScOut_terms_le ht (by linarith) hV (regScOut_abs_alpha hY hx)
    (regScOut_abs_beta ht.le hY hx) (regAbs_log_mass_le hl hY) hlY hlx (by linarith) hℓ0
  rw [hrep]
  have hint := abs_integral_le_integral_abs (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun v => scOutTg (selfK1 Y x * scOutRho x) (selfK2 Y x * scOutRho x ^ 2)
      (ladderInnerMass 1 lam Y * scOutRho x / (Y * (1 - Y)))
      (-(selfK1 Y x * scOutRho x * log (ladderInnerMass 1 lam Y))) v / (setCKQ x + t + v) ^ 2)
  refine (abs_sub _ _).trans ?_
  unfold scOutRegSDom
  linarith only [hint, hI, key]

/-- **Continuity at `λ = 0`** of the outer-massive self-energy integrand in the inner mass. -/
theorem continuousAt_scOutRegS {t Y x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : ContinuousAt (fun lam => scOutRegS t lam Y x) 0 := by
  have hh : 0 < ladderInnerMass 1 (√t) x / x :=
    div_pos (ladderInnerMass_pos one_pos (sqrt_pos.2 ht) ⟨hx.1.le, hx.2.le⟩) hx.1
  have hY0 := hY.1
  have hr : 0 < 1 - Y := by linarith [hY.2]
  unfold scOutRegS selfGm sForm
  generalize ladderInnerMass 1 (√t) x / x = h at hh ⊢
  unfold ladderInnerMass
  generalize 1 - Y = r at hr ⊢
  fun_prop (disch := (apply ne_of_gt; first
    | (simp only [one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, add_zero]; positivity)
    | positivity))

end QED.ChainProof.SetCK
