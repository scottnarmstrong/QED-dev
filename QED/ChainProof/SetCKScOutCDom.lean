/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutCBd
public import QED.ChainProof.SetCKScOutCFub

/-!
# Set (c), Stage K, group G4: the domination of the outer-massive corner, and G4C

Helper level (no frozen statement). At a point `(Y, y₃, x)` of the cube with `y₃ < Y` and
`M = Y² - t y₃ (Y - y₃) ≠ 0` (**`scOutC_abs_integral_le_dom`**)

`∫₀^∞ |T(Y, y₃, x, v)|/(Q(x) + t + v)² dv ≤ 200 (1 + 1/t) (Y^(-2/3) + (1-Y)^(-1/2))
  y₃^(-5/6) x^(-2/3)` (`scOutCDom`, written with twelfth roots).

The chain (numerically checked, scratch `stageK/g4c/bnd*.py`): the generic bound
`scOutCTg_abs_integral_le`; the coefficient sizes `≤ 3x`, `≤ 2x`; `a = m + s u = Y² + βx + t s`
with `a ≥ max(Y², x y₃)`, `z₀ ≥ β x ≥ g x`, `a ≤ Y² + z₀`, `w/u ≤ 1/x`; the master bound
`scOutC_J1_le` with `log(1 + a/z₀) ≤ log(3/(g x))`; `|log m| ≤ -2 log Y + u` and
`x² z₀/(2u) ≤ 1`; then `scOutC_dom_alg`.

The dominating function is integrable on the cube (`integrable_scOutCDom`), so
**`scOutC_bound : ScOutCBound t`** for every `t > 0`, and the G4C Stieltjes identity holds
unconditionally (**`scOutCH_isScOutCHDensity : IsScOutCHDensity scOutCH`**).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The dominating function of the outer-massive corner.** -/
noncomputable def scOutCDom (t Y y3 x : ℝ) : ℝ :=
  200 * (1 + 1 / t) * ((1 / (Y ^ ((1 : ℝ) / 12)) ^ 8 + 1 / √(1 - Y)) *
    (1 / (y3 ^ ((1 : ℝ) / 12)) ^ 10) * (1 / (x ^ ((1 : ℝ) / 12)) ^ 8))

/-- A twelfth root on `(0, 1)`. -/
theorem scOutC_root {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 < y ^ ((1 : ℝ) / 12) ∧ y ^ ((1 : ℝ) / 12) ≤ 1 ∧ y = (y ^ ((1 : ℝ) / 12)) ^ 12 := by
  refine ⟨rpow_pos_of_pos hy.1 _, rpow_le_one hy.1.le hy.2.le (by norm_num), ?_⟩
  rw [← rpow_natCast, ← rpow_mul hy.1.le]
  norm_num

/-- The geometry of `a = m + s u`. -/
theorem scOutC_geom {t Y y3 x e Q m w s u β g : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1) (he : e = y3 * (Y - y3))
    (hQ : Q = x * w) (hm : m = Y ^ 2 + e * Q) (hu : u = Q + t) (hβ : β = w * (s + e))
    (hg : g = y3 * (1 - Y)) (hgβ : g ≤ β) (hs : 0 ≤ s) (hw : 0 < w) :
    Y ^ 2 ≤ m + s * u ∧ x * y3 ≤ m + s * u ∧ m + s * u ≤ Y ^ 2 + (s + e) * u ∧
      g * x ≤ (s + e) * u ∧ m - e * u + (s + e) * u = m + s * u ∧ Y ^ 2 ≤ m ∧ m - 1 ≤ u ∧
      g * x ≤ 1 := by
  subst he hQ hm hu hβ hg
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨h30, h3Y⟩ := h3
  obtain ⟨hx0, hx1⟩ := hx
  have hY4 : 0 < Y - y3 := by linarith
  have he0 : 0 < y3 * (Y - y3) := mul_pos h30 hY4
  have hse : 0 ≤ s + y3 * (Y - y3) := by linarith
  have hQ0 : 0 ≤ x * w := (mul_pos hx0 hw).le
  have ha : Y ^ 2 + y3 * (Y - y3) * (x * w) + s * (x * w + t) =
      Y ^ 2 + w * (s + y3 * (Y - y3)) * x + s * t := by ring
  have hβx : 0 ≤ w * (s + y3 * (Y - y3)) * x := by positivity
  have hst : 0 ≤ s * t := mul_nonneg hs ht.le
  have hgx : y3 * (1 - Y) * x ≤ w * (s + y3 * (Y - y3)) * x :=
    mul_le_mul_of_nonneg_right hgβ hx0.le
  have hxy3 : x * y3 ≤ y3 := by nlinarith
  have h1 : x * y3 * Y ≤ Y ^ 2 := by nlinarith
  have hz : w * (s + y3 * (Y - y3)) * x ≤ (s + y3 * (Y - y3)) * (x * w + t) := by
    nlinarith [mul_nonneg hse ht.le]
  have e1 : y3 * (Y - y3) ≤ 1 := by nlinarith
  have e2 : Y ^ 2 ≤ 1 := by nlinarith
  have hy1 : y3 * (1 - Y) ≤ 1 := by nlinarith
  refine ⟨by rw [ha]; linarith, by rw [ha]; nlinarith, ?_, by linarith, by ring, ?_, ?_, ?_⟩
  · have : 0 ≤ y3 * (Y - y3) * t := by positivity
    nlinarith
  · have : 0 ≤ y3 * (Y - y3) * (x * w) := by positivity
    linarith
  · nlinarith [mul_le_mul_of_nonneg_right e1 hQ0]
  · nlinarith

/-- Term 1 of the corner bound (threshold part). -/
theorem scOutC_T1 {Ac x a z M Y g ly lx l1 : ℝ} (hx : 0 < x) (hAc0 : 0 ≤ Ac)
    (hAc : Ac ≤ 3 * x) (hz : 0 < z) (ha : M + z = a) (ha0 : 0 < a) (hM : M ≠ 0)
    (haY : a ≤ Y ^ 2 + z) (hY1 : Y ^ 2 ≤ 1) (hg : 0 < g) (hgz : g * x ≤ z)
    (hgx1 : g * x ≤ 1) (hlog : log (g * x) = -(ly + l1 + lx)) :
    Ac * (log (1 + M / z) / M) ≤ 6 * x * (3 + ly + lx + l1) / a := by
  have hJ := scOutC_J1_le hz (by rw [ha]; exact ha0) hM
  rw [ha] at hJ
  have hgx0 : 0 < g * x := mul_pos hg hx
  have hlog3 : log 3 ≤ 2 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hlogaz : log (1 + a / z) ≤ log 3 + ly + l1 + lx := by
    have h1 : 1 + a / z ≤ 3 / (g * x) := by
      have e1 : a / z ≤ 1 + Y ^ 2 / z := by
        rw [div_le_iff₀ hz, add_mul, one_mul, div_mul_cancel₀ _ hz.ne']; linarith
      have e2 : Y ^ 2 / z ≤ 1 / (g * x) := by
        rw [div_le_div_iff₀ hz hgx0]; nlinarith
      have e3 : 2 ≤ 2 / (g * x) := by rw [le_div_iff₀ hgx0]; linarith
      have : 3 / (g * x) = 2 / (g * x) + 1 / (g * x) := by ring
      linarith
    calc log (1 + a / z) ≤ log (3 / (g * x)) := log_le_log (by positivity) h1
      _ = log 3 + ly + l1 + lx := by rw [log_div (by norm_num) hgx0.ne', hlog]; ring
  have hJb0 : 0 ≤ 2 * (1 + log (1 + a / z)) / a := by
    have h0 : 0 ≤ a / z := by positivity
    have : 0 ≤ log (1 + a / z) := log_nonneg (by linarith)
    positivity
  calc Ac * (log (1 + M / z) / M) ≤ Ac * (2 * (1 + log (1 + a / z)) / a) :=
        mul_le_mul_of_nonneg_left hJ hAc0
    _ ≤ 3 * x * (2 * (1 + log (1 + a / z)) / a) := mul_le_mul_of_nonneg_right hAc hJb0
    _ ≤ 3 * x * (2 * (1 + (log 3 + ly + l1 + lx)) / a) := by gcongr
    _ ≤ 3 * x * (2 * (1 + (2 + ly + l1 + lx)) / a) := by gcongr
    _ = 6 * x * (3 + ly + lx + l1) / a := by ring

/-- Term 2 of the corner bound (the `κ` part). -/
theorem scOutC_T2 {Aa x w u a : ℝ} (hx : 0 < x) (hAa : Aa ≤ 2 * x)
    (hw : 0 < w) (hwu : x * w ≤ u) (ha : 0 < a) : Aa * (w / u) * (1 / a) ≤ 2 / a := by
  have hu : 0 < u := lt_of_lt_of_le (mul_pos hx hw) hwu
  have h : w / u ≤ 1 / x := by rw [div_le_div_iff₀ hu hx, one_mul]; linarith
  calc Aa * (w / u) * (1 / a) ≤ 2 * x * (1 / x) * (1 / a) := by gcongr
    _ = 2 / a := by field_simp

/-- `|log m| ≤ -2 log Y + u` for `Y² ≤ m ≤ 1 + u`. -/
theorem scOutC_abs_log_m {m Y u : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) (hmY : Y ^ 2 ≤ m)
    (hm1 : m - 1 ≤ u) : |log m| ≤ 2 * -log Y + u := by
  have hm : 0 < m := lt_of_lt_of_le (by have := hY.1; positivity) hmY
  have l1 : 2 * log Y ≤ log m := by
    have := log_le_log (by have := hY.1; positivity) hmY
    rw [log_pow] at this
    push_cast at this
    exact this
  have l2 : log m ≤ m - 1 := log_le_sub_one_of_pos hm
  have l3 : log Y ≤ 0 := log_nonpos hY.1.le hY.2.le
  rw [abs_le]
  constructor <;> linarith

/-- Terms 3 and 4 of the corner bound (beyond the threshold, and the pole). -/
theorem scOutC_T34 {x a m u z t lY : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) (htu : t ≤ u)
    (hloga : log a ≤ z) (hlogm : |log m| ≤ 2 * lY + u) (hlY : 0 ≤ lY)
    (hxz : x ^ 2 / 2 * (z / u) ≤ 1) :
    x ^ 2 / 2 * ((log a - log m) / u) + x ^ 2 / 2 * |log m| * (1 / u) ≤ 2 + 2 / t * lY := by
  have hu : 0 < u := ht.trans_le htu
  have hlm : -log m ≤ |log m| := neg_le_abs _
  have h1 : x ^ 2 / 2 * ((log a - log m) / u) ≤
      x ^ 2 / 2 * (z / u) + x ^ 2 / 2 * (|log m| / u) := by
    rw [← mul_add, ← add_div]
    gcongr
    linarith
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  have hlu : |log m| / u ≤ 2 * lY / t + 1 := by
    rw [div_le_iff₀ hu]
    have : 2 * lY ≤ 2 * lY / t * u := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ht]
      nlinarith
    nlinarith
  have h0 : 0 ≤ |log m| / u := by positivity
  have h2 : x ^ 2 * (|log m| / u) ≤ 2 * lY / t + 1 :=
    (mul_le_of_le_one_left h0 hx2).trans hlu
  have e : x ^ 2 / 2 * |log m| * (1 / u) + x ^ 2 / 2 * (|log m| / u) =
      x ^ 2 * (|log m| / u) := by ring
  have e2 : 2 * lY / t = 2 / t * lY := by ring
  linarith

/-- `x² β/(2w) ≤ 1` for `β ≤ g + e w`, `g, e ≤ 1`, `w = x/(1-x)`. -/
theorem scOutC_xz {x g e w β : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w = x / (1 - x))
    (hβ : β ≤ g + e * w) (hg1 : g ≤ 1) (he1 : e ≤ 1) :
    x ^ 2 / 2 * (β / w) ≤ 1 := by
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hw0 : 0 < w := by rw [hw]; exact div_pos hx.1 h1x
  have e2 : x ^ 2 * (β / w) ≤ x ^ 2 * ((g + e * w) / w) := by gcongr
  have e3 : x ^ 2 * ((g + e * w) / w) = x * g * (1 - x) + x ^ 2 * e := by
    rw [hw]; field_simp
  have h4 : x * (1 - x) ≤ 1 := by nlinarith [hx.1, hx.2]
  have h5 : x * g * (1 - x) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hg1 (mul_nonneg hx.1.le h1x.le)
    nlinarith
  have h6 : x ^ 2 * e ≤ 1 := by
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    nlinarith
  nlinarith

/-- **The pointwise domination.** -/
theorem scOutC_abs_integral_le_dom {t Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hM : Y ^ 2 - t * (y3 * (Y - y3)) ≠ 0) :
    ∫ v in Ioi 0, |scOutCT Y y3 x v / (setCKQ x + t + v) ^ 2| ≤ scOutCDom t Y y3 x := by
  have hY4 : 0 < Y - y3 := by linarith [h3.2]
  have he : 0 < y3 * (Y - y3) := mul_pos h3.1 hY4
  have hm := scOutCm_pos hY h3 hx
  have hw : 0 < scOutRho x := scOutRho_pos hx
  have hQ0 : 0 ≤ setCKQ x := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hu : 0 < setCKQ x + t := by linarith
  have hs : 0 ≤ scOutCs Y y3 x := scOutCs_nonneg hx
  have hβ : betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x =
      scOutRho x * (scOutCs Y y3 x + y3 * (Y - y3)) := by
    unfold scOutCs
    field_simp
    ring
  have hMe : scOutCm Y y3 x - y3 * (Y - y3) * (setCKQ x + t) = Y ^ 2 - t * (y3 * (Y - y3)) := by
    rw [scOutCm]; ring
  have hM' : scOutCm Y y3 x - y3 * (Y - y3) * (setCKQ x + t) ≠ 0 := by rw [hMe]; exact hM
  have hQ : setCKQ x = x * scOutRho x := by
    rw [setCKQ, scOutRho]; field_simp
  have hg : cornerG y3 (Y - y3) = y3 * (1 - Y) := by rw [cornerG]; ring
  have hg0 : 0 < cornerG y3 (Y - y3) := by rw [hg]; exact mul_pos h3.1 (by linarith [hY.2])
  have hgβ : cornerG y3 (Y - y3) ≤ betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x :=
    le_max_left _ _
  have hgen := scOutCTg_abs_integral_le hm he hw hu hs hM'
    (cornerA0 x y3 (Y - y3)) (cornerA1 x y3 (Y - y3)) (cornerA2 x y3 (Y - y3)) (cornerC0 x)
    (cornerC1 x y3 (Y - y3)) (cornerC2 x y3 (Y - y3)) (cornerC3 x y3 (Y - y3))
  rw [← hβ] at hgen
  refine hgen.trans ?_
  have hYs : y3 + (Y - y3) ≤ 1 := by linarith only [hY.2]
  have hAc := scOutC_Ac_le hx.1.le hx.2.le h3.1.le hY4.le hYs hg0 hgβ
  have hAa := scOutC_Aa_le hx.1.le hx.2.le h3.1.le hY4.le hYs hg0 hgβ
  have hβw : betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x ≤
      cornerG y3 (Y - y3) + y3 * (Y - y3) * scOutRho x := by
    refine max_le (le_add_of_nonneg_right (by positivity)) ?_
    rw [scOutRho, mul_div_assoc]
    exact le_add_of_nonneg_left hg0.le
  have hc0 : |cornerC0 x| * scOutRho x = x ^ 2 / 2 := by
    have : 0 < 1 - x := by linarith [hx.2]
    rw [cornerC0, abs_of_pos (by have := hx.1; positivity), scOutRho]
    field_simp
  have hc0' : |cornerC0 x * scOutRho x * log (scOutCm Y y3 x)| =
      x ^ 2 / 2 * |log (scOutCm Y y3 x)| := by
    rw [abs_mul, abs_mul, abs_of_pos hw, ← hc0]
  rw [hc0, hc0']
  have hmdef : scOutCm Y y3 x = Y ^ 2 + y3 * (Y - y3) * setCKQ x := rfl
  have hρ : scOutRho x = x / (1 - x) := rfl
  have hlogg : log (cornerG y3 (Y - y3) * x) = -(-log y3 + -log (1 - Y) + -log x) := by
    rw [hg, log_mul (mul_pos h3.1 (by linarith [hY.2])).ne' hx.1.ne',
      log_mul h3.1.ne' (by linarith [hY.2])]
    ring
  -- the twelfth roots
  obtain ⟨hyy, hyy1, hYe⟩ := scOutC_root hY
  obtain ⟨hb, hb1, h3e⟩ := scOutC_root ⟨h3.1, h3.2.trans hY.2⟩
  obtain ⟨hzz, hzz1, hxe⟩ := scOutC_root hx
  have hly : -log y3 ≤ 12 / y3 ^ ((1 : ℝ) / 12) := scOutC_neg_log_le h3.1
  have hlx : -log x ≤ 12 / x ^ ((1 : ℝ) / 12) := scOutC_neg_log_le hx.1
  have hlY : -log Y ≤ 12 / Y ^ ((1 : ℝ) / 12) := scOutC_neg_log_le hY.1
  have hS : 0 < √(1 - Y) := sqrt_pos.2 (by linarith [hY.2])
  have hl1 : -log (1 - Y) ≤ 2 * (Y ^ ((1 : ℝ) / 12)) ^ 6 / √(1 - Y) := by
    have hsq : √Y = (Y ^ ((1 : ℝ) / 12)) ^ 6 := by
      conv_lhs => rw [hYe]
      rw [show (Y ^ ((1 : ℝ) / 12)) ^ 12 = ((Y ^ ((1 : ℝ) / 12)) ^ 6) ^ 2 by ring,
        sqrt_sq (by positivity)]
    rw [← hsq]
    exact scOutC_neg_log_one_sub_le hY
  have hly0 : 0 ≤ -log y3 := by
    have := log_nonpos h3.1.le (h3.2.trans hY.2).le; linarith
  have hlx0 : 0 ≤ -log x := by have := log_nonpos hx.1.le hx.2.le; linarith
  have hl10 : 0 ≤ -log (1 - Y) := by
    have := log_nonpos (by linarith [hY.2] : (0 : ℝ) ≤ 1 - Y) (by linarith [hY.1]); linarith
  have hlY0 : 0 ≤ -log Y := by have := log_nonpos hY.1.le hY.2.le; linarith
  unfold scOutCDom
  -- forget the definitions
  generalize scOutCs Y y3 x = s at *
  generalize scOutCm Y y3 x = m at *
  generalize betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x = β at *
  generalize cornerG y3 (Y - y3) = g at *
  generalize setCKQ x = Q at *
  generalize scOutRho x = w at *
  generalize Y ^ ((1 : ℝ) / 12) = yy at *
  generalize y3 ^ ((1 : ℝ) / 12) = b at *
  generalize x ^ ((1 : ℝ) / 12) = zz at *
  obtain ⟨hY2, hxy, haz2, hgz, haz, hmY, hm1, hgx1⟩ :=
    scOutC_geom (e := y3 * (Y - y3)) (u := Q + t) ht hY h3 hx rfl hQ hmdef rfl hβ hg hgβ hs hw
  have hβpos : 0 < β := hg0.trans_le hgβ
  have ha0 : 0 < m + s * (Q + t) := lt_of_lt_of_le (by have := hY.1; positivity) hY2
  have hz : 0 < (s + y3 * (Y - y3)) * (Q + t) := by positivity
  have hY1 : Y ^ 2 ≤ 1 := pow_le_one₀ hY.1.le hY.2.le
  have hT1 := scOutC_T1 (Ac := |cornerC1 x y3 (Y - y3)| + |cornerC2 x y3 (Y - y3)| / β +
      |cornerC3 x y3 (Y - y3)| / β ^ 2) hx.1 (add_nonneg (add_nonneg (abs_nonneg _)
        (div_nonneg (abs_nonneg _) hβpos.le)) (div_nonneg (abs_nonneg _) (pow_nonneg hβpos.le 2)))
      hAc hz haz ha0 hM' haz2 hY1
    hg0 hgz hgx1 hlogg
  have hT2 := scOutC_T2 (Aa := |cornerA0 x y3 (Y - y3)| + |cornerA1 x y3 (Y - y3)| / β +
      |cornerA2 x y3 (Y - y3)| / β ^ 2) (u := Q + t) hx.1 hAa hw (by linarith only [ht, hQ]) ha0
  have hloga : log (m + s * (Q + t)) ≤ (s + y3 * (Y - y3)) * (Q + t) := by
    have := log_le_sub_one_of_pos ha0
    linarith only [this, haz2, hY1]
  have hlogm := scOutC_abs_log_m hY hu.le hmY hm1
  have hxz : x ^ 2 / 2 * ((s + y3 * (Y - y3)) * (Q + t) / (Q + t)) ≤ 1 := by
    have e : (s + y3 * (Y - y3)) * (Q + t) / (Q + t) = β / w := by
      rw [hβ]; field_simp
    rw [e]
    have hg1 : g ≤ 1 := by
      rw [hg]; exact scOutC_mul_le_one (h3.2.trans hY.2).le (by linarith only [hY.2])
        (by linarith only [hY.1])
    have he1 : y3 * (Y - y3) ≤ 1 :=
      scOutC_mul_le_one (h3.2.trans hY.2).le hY4.le (by linarith only [hY.2, h3.1])
    exact scOutC_xz hx hρ hβw hg1 he1
  have hT34 := scOutC_T34 hx ht (by linarith only [hQ0]) hloga hlogm hlY0 hxz
  have hxy0 : 0 ≤ x * y3 := (mul_pos hx.1 h3.1).le
  have ha1 : yy ^ 6 * zz ^ 9 * b ^ 9 ≤ m + s * (Q + t) := by
    have h4 : (yy ^ 6 * zz ^ 9 * b ^ 9) ^ 4 ≤ (m + s * (Q + t)) ^ 4 := by
      have e : (yy ^ 6 * zz ^ 9 * b ^ 9) ^ 4 = (yy ^ 12) ^ 2 * (zz ^ 12 * b ^ 12) ^ 3 := by ring
      rw [e, ← hYe, ← hxe, ← h3e]
      calc Y ^ 2 * (x * y3) ^ 3 ≤ (m + s * (Q + t)) * (m + s * (Q + t)) ^ 3 :=
            mul_le_mul hY2 (pow_le_pow_left₀ hxy0 hxy 3) (by positivity) ha0.le
        _ = (m + s * (Q + t)) ^ 4 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) ha0.le (by norm_num)).1 h4
  have ha2 : yy ^ 8 * zz ^ 8 * b ^ 8 ≤ m + s * (Q + t) := by
    have h4 : (yy ^ 8 * zz ^ 8 * b ^ 8) ^ 3 ≤ (m + s * (Q + t)) ^ 3 := by
      have e : (yy ^ 8 * zz ^ 8 * b ^ 8) ^ 3 = (yy ^ 12) ^ 2 * (zz ^ 12 * b ^ 12) ^ 2 := by ring
      rw [e, ← hYe, ← hxe, ← h3e]
      calc Y ^ 2 * (x * y3) ^ 2 ≤ (m + s * (Q + t)) * (m + s * (Q + t)) ^ 2 :=
            mul_le_mul hY2 (pow_le_pow_left₀ hxy0 hxy 2) (by positivity) ha0.le
        _ = (m + s * (Q + t)) ^ 3 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) ha0.le (by norm_num)).1 h4
  have halg := scOutC_dom_alg hyy hyy1 hb hb1 hzz hzz1 hS ht ha1 ha2 hly0 hly hlx0 hlx hl10
    hl1 hlY
  rw [← hxe] at halg
  linarith only [hT1, hT2, hT34, halg]
