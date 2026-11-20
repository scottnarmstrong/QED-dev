/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutCDom

/-!
# Set (c), Stage K: the outer-massive corner at inner photon mass `λ`, domination

Helper level (no frozen statement). In the corner with the outer photon of mass² `t > 0` and the
inner photon of mass `λ`, the mass function is `M = Y² + (1-Y) λ² - t e = m_λ - e u` with
`m_λ = Y² + e Q(x) + (1-Y) λ²` (`regScOutCm`, `regScOutC_mass_eq`), `u = Q(x) + t`. The
`(u + v)⁻²`-form of `SetCKScOutCId` is generic in `m > 0`, so (**`regCornerGm_out_eq`**)

`cornerGm (√t) λ y₃ (Y - y₃) x = ∫₀^∞ T_λ(Y, y₃, x, v)/(u + v)² dv` (`regScOutCT`, `M ≠ 0`),

and the session-11 domination goes through with `m_λ` in place of `m₀`: it used only
`Y² ≤ m`, `m - 1 ≤ u`, `Y² ≤ a = m + s u`, `x y₃ ≤ a` and `a ≤ Y² + z₀`, `Y² ≤ 1`; with
`δ = (1-Y) λ² ∈ [0, 1 - Y²]` for `λ² ≤ 1` the last pair becomes `a ≤ (Y² + δ) + z₀`,
`Y² + δ ≤ 1` (`regScOutC_geom`). So, uniformly in `λ² ≤ 1`
(**`regScOutC_abs_integral_le_dom`**, **`abs_regCornerGm_out_le`**):

`|cornerGm (√t) λ y₃ (Y - y₃) x| ≤ ∫₀^∞ |T_λ|/(u + v)² ≤ scOutCDom t Y y₃ x`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- `m_λ = Y² + e Q(x) + (1-Y) λ²`, `e = y₃ (Y - y₃)`. -/
noncomputable def regScOutCm (lam Y y3 x : ℝ) : ℝ := scOutCm Y y3 x + (1 - Y) * lam ^ 2

/-- **The `(u + v)⁻²`-weight of the outer-massive corner at inner photon mass `λ`.** -/
noncomputable def regScOutCT (lam Y y3 x v : ℝ) : ℝ :=
  scOutCTg (cornerA0 x y3 (Y - y3)) (cornerA1 x y3 (Y - y3)) (cornerA2 x y3 (Y - y3))
    (cornerC0 x) (cornerC1 x y3 (Y - y3)) (cornerC2 x y3 (Y - y3)) (cornerC3 x y3 (Y - y3))
    (regScOutCm lam Y y3 x) (y3 * (Y - y3)) (scOutRho x) (scOutCs Y y3 x) v

theorem regScOutCm_pos {Y y3 x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (h3 : y3 ∈ Ioo (0 : ℝ) Y)
    (hx : x ∈ Ioo (0 : ℝ) 1) (lam : ℝ) : 0 < regScOutCm lam Y y3 x := by
  have := scOutCm_pos hY h3 hx
  have : 0 ≤ (1 - Y) * lam ^ 2 := mul_nonneg (by linarith [hY.2]) (sq_nonneg lam)
  unfold regScOutCm
  linarith

theorem regScOutC_mass_eq {t lam Y y3 x : ℝ} (ht : 0 ≤ t) :
    cornerMass (√t) lam y3 (Y - y3) =
      regScOutCm lam Y y3 x - y3 * (Y - y3) * (setCKQ x + t) := by
  unfold cornerMass regScOutCm scOutCm
  rw [sq_sqrt ht]
  ring

/-- **The `(u + v)⁻²`-representation at inner photon mass `λ`** (`M ≠ 0`). -/
theorem regCornerGm_out_eq {t lam Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hM : cornerMass (√t) lam y3 (Y - y3) ≠ 0) :
    cornerGm (√t) lam y3 (Y - y3) x =
      ∫ v in Ioi 0, regScOutCT lam Y y3 x v / (setCKQ x + t + v) ^ 2 := by
  have hρ := scOutRho_pos hx
  have he : 0 < y3 * (Y - y3) := mul_pos h3.1 (by linarith [h3.2])
  have hu : 0 < setCKQ x + t := by
    have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
    linarith
  have hβ : betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x =
      scOutRho x * (scOutCs Y y3 x + y3 * (Y - y3)) := by
    unfold scOutCs
    field_simp
    ring
  have hh : ladderInnerMass 1 (√t) x / x = (setCKQ x + t) / scOutRho x :=
    hOut_eq_div_scOutRho ht.le hx
  have hMm := regScOutC_mass_eq (lam := lam) (Y := Y) (y3 := y3) (x := x) ht.le
  have hM' : regScOutCm lam Y y3 x - y3 * (Y - y3) * (setCKQ x + t) ≠ 0 := by
    rw [← hMm]; exact hM
  unfold cornerGm
  rw [hβ, hh, hMm]
  exact scOutC_cForm_eq (regScOutCm_pos hY h3 hx lam) he hρ hu (scOutCs_nonneg hx) hM' _ _ _ _
    _ _ _

/-- The geometry of `a = m + s u` at `m = Y² + e Q + δ`, `0 ≤ δ`, `Y² + δ ≤ 1`. -/
theorem regScOutC_geom {t Y y3 x e Q m w s u β g δ : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1) (he : e = y3 * (Y - y3))
    (hQ : Q = x * w) (hm : m = Y ^ 2 + e * Q + δ) (hu : u = Q + t) (hβ : β = w * (s + e))
    (hg : g = y3 * (1 - Y)) (hgβ : g ≤ β) (hs : 0 ≤ s) (hw : 0 < w) (hδ0 : 0 ≤ δ)
    (hδ1 : Y ^ 2 + δ ≤ 1) :
    Y ^ 2 ≤ m + s * u ∧ x * y3 ≤ m + s * u ∧ m + s * u ≤ Y ^ 2 + δ + (s + e) * u ∧
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
  have ha : Y ^ 2 + y3 * (Y - y3) * (x * w) + δ + s * (x * w + t) =
      Y ^ 2 + w * (s + y3 * (Y - y3)) * x + s * t + δ := by ring
  have hβx : 0 ≤ w * (s + y3 * (Y - y3)) * x := by positivity
  have hst : 0 ≤ s * t := mul_nonneg hs ht.le
  have hgx : y3 * (1 - Y) * x ≤ w * (s + y3 * (Y - y3)) * x :=
    mul_le_mul_of_nonneg_right hgβ hx0.le
  have hxy3 : x * y3 ≤ y3 := by nlinarith
  have h1 : x * y3 * Y ≤ Y ^ 2 := by nlinarith
  have hz : w * (s + y3 * (Y - y3)) * x ≤ (s + y3 * (Y - y3)) * (x * w + t) := by
    nlinarith [mul_nonneg hse ht.le]
  have e1 : y3 * (Y - y3) ≤ 1 := by nlinarith
  have hy1 : y3 * (1 - Y) ≤ 1 := by nlinarith
  refine ⟨by rw [ha]; linarith, by rw [ha]; nlinarith, ?_, by linarith, by ring, ?_, ?_, ?_⟩
  · have : 0 ≤ y3 * (Y - y3) * t := by positivity
    nlinarith
  · have : 0 ≤ y3 * (Y - y3) * (x * w) := by positivity
    linarith
  · nlinarith [mul_le_mul_of_nonneg_right e1 hQ0]
  · nlinarith

/-- **The domination of the outer-massive corner weight, uniform in `λ² ≤ 1`.** -/
theorem regScOutC_abs_integral_le_dom {t lam Y y3 x : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hM : cornerMass (√t) lam y3 (Y - y3) ≠ 0) :
    ∫ v in Ioi 0, |regScOutCT lam Y y3 x v / (setCKQ x + t + v) ^ 2| ≤ scOutCDom t Y y3 x := by
  have hY4 : 0 < Y - y3 := by linarith [h3.2]
  have he : 0 < y3 * (Y - y3) := mul_pos h3.1 hY4
  have hm := regScOutCm_pos hY h3 hx lam
  have hδ0 : 0 ≤ (1 - Y) * lam ^ 2 := mul_nonneg (by linarith [hY.2]) (sq_nonneg lam)
  have hδ1 : Y ^ 2 + (1 - Y) * lam ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hl (show 0 ≤ 1 - Y by linarith [hY.2])
    nlinarith [hY.1, hY.2]
  have hw : 0 < scOutRho x := scOutRho_pos hx
  have hQ0 : 0 ≤ setCKQ x := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have hu : 0 < setCKQ x + t := by linarith
  have hs : 0 ≤ scOutCs Y y3 x := scOutCs_nonneg hx
  have hβ : betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x =
      scOutRho x * (scOutCs Y y3 x + y3 * (Y - y3)) := by
    unfold scOutCs
    field_simp
    ring
  have hM' : regScOutCm lam Y y3 x - y3 * (Y - y3) * (setCKQ x + t) ≠ 0 := by
    rw [← regScOutC_mass_eq ht.le]; exact hM
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
  have hc0' : |cornerC0 x * scOutRho x * log (regScOutCm lam Y y3 x)| =
      x ^ 2 / 2 * |log (regScOutCm lam Y y3 x)| := by
    rw [abs_mul, abs_mul, abs_of_pos hw, ← hc0]
  rw [hc0, hc0']
  have hmdef : regScOutCm lam Y y3 x =
      Y ^ 2 + y3 * (Y - y3) * setCKQ x + (1 - Y) * lam ^ 2 := rfl
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
  generalize regScOutCm lam Y y3 x = m at *
  generalize (1 - Y) * lam ^ 2 = δ at *
  generalize betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x = β at *
  generalize cornerG y3 (Y - y3) = g at *
  generalize setCKQ x = Q at *
  generalize scOutRho x = w at *
  generalize Y ^ ((1 : ℝ) / 12) = yy at *
  generalize y3 ^ ((1 : ℝ) / 12) = b at *
  generalize x ^ ((1 : ℝ) / 12) = zz at *
  obtain ⟨hY2, hxy, haz2, hgz, haz, hmY, hm1, hgx1⟩ :=
    regScOutC_geom (e := y3 * (Y - y3)) (u := Q + t) ht hY h3 hx rfl hQ hmdef rfl hβ hg hgβ hs hw
      hδ0 hδ1
  have hβpos : 0 < β := hg0.trans_le hgβ
  have ha0 : 0 < m + s * (Q + t) := lt_of_lt_of_le (by have := hY.1; positivity) hY2
  have hz : 0 < (s + y3 * (Y - y3)) * (Q + t) := by positivity
  have hT1 := scOutC_T1 (Ac := |cornerC1 x y3 (Y - y3)| + |cornerC2 x y3 (Y - y3)| / β +
      |cornerC3 x y3 (Y - y3)| / β ^ 2) hx.1 (add_nonneg (add_nonneg (abs_nonneg _)
        (div_nonneg (abs_nonneg _) hβpos.le)) (div_nonneg (abs_nonneg _) (pow_nonneg hβpos.le 2)))
      hAc hz haz ha0 hM' (Y := √(Y ^ 2 + δ))
      (by rw [sq_sqrt (by positivity)]; linarith only [haz2])
      (by rw [sq_sqrt (by positivity)]; exact hδ1) hg0 hgz hgx1 hlogg
  have hT2 := scOutC_T2 (Aa := |cornerA0 x y3 (Y - y3)| + |cornerA1 x y3 (Y - y3)| / β +
      |cornerA2 x y3 (Y - y3)| / β ^ 2) (u := Q + t) hx.1 hAa hw (by linarith only [ht, hQ]) ha0
  have hloga : log (m + s * (Q + t)) ≤ (s + y3 * (Y - y3)) * (Q + t) := by
    have := log_le_sub_one_of_pos ha0
    linarith only [this, haz2, hδ1]
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

/-- **The pointwise bound on the outer-massive corner integrand, uniform in `λ² ≤ 1`.** -/
theorem abs_regCornerGm_out_le {t lam Y y3 x : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hM : cornerMass (√t) lam y3 (Y - y3) ≠ 0) :
    |cornerGm (√t) lam y3 (Y - y3) x| ≤ scOutCDom t Y y3 x := by
  rw [regCornerGm_out_eq ht hY h3 hx hM]
  exact (abs_integral_le_integral_abs).trans (regScOutC_abs_integral_le_dom ht hl hY h3 hx hM)

end QED.ChainProof.SetCK
