/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutCDom
public import QED.ChainProof.SetCKScOutCAbs

/-!
# Set (c), Stage K, closed forms: the domination of the `k`-part of the outer-massive corner

Helper level (no frozen statement). For the `ρ_oC` route (Stage K notes, Session 29+) the part
`K(v) = ∫₀^v k` of the outer-massive corner weight is moved to the node variable by Fubini,
which needs a bound for `k` alone. With the notation of `SetCKScOutCAbs`
(**`formOC_abs_k_le`**): `∫₀^∞ |k(v)|/(u + v) dv` is at most the right-hand side of
`scOutCTg_abs_integral_le` (it is the sum of its threshold and beyond-threshold `k`-terms, the
other terms being nonnegative). The chain of `scOutC_abs_integral_le_dom` then gives
(**`formOC_abs_k_le_dom`**), at a point `(Y, y₃, x)` of the cube with `y₃ < Y` and
`Y² - t y₃ (Y - y₃) ≠ 0`,

`∫₀^∞ |k(Y, y₃, x, v)|/(Q(x) + t + v) dv ≤ scOutCDom t Y y₃ x`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

section

variable {m e w u s : ℝ}

/-- **The `k`-part alone** is bounded by the right-hand side of `scOutCTg_abs_integral_le`. -/
theorem formOC_abs_k_le (hm : 0 < m) (he : 0 < e) (hw : 0 < w) (hu : 0 < u)
    (hs : 0 ≤ s) (hM : m - e * u ≠ 0) (a₀ a₁ a₂ c₀ c₁ c₂ c₃ : ℝ) :
    ∫ v in Ioi 0, |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)| ≤
      (|c₁| + |c₂| / (w * (s + e)) + |c₃| / (w * (s + e)) ^ 2) *
          (log (1 + (m - e * u) / ((s + e) * u)) / (m - e * u)) +
        (|a₀| + |a₁| / (w * (s + e)) + |a₂| / (w * (s + e)) ^ 2) * (w / u) *
          (1 / (m + s * u)) +
        |c₀| * w * ((log (m + s * u) - log m) / u) + |c₀ * w * log m| * (1 / u) := by
  have hkI : IntegrableOn (fun v => |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)|) (Ioi 0) :=
    Integrable.abs (scOutC_k_int hm he hw hu hs hM c₀ c₁ c₂ c₃).1
  have hS : IntegrableOn (fun v => |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)|) (scOutCS m s) :=
    hkI.mono_set fun v hv => hv.1
  have hR : IntegrableOn (fun v => |scOutCk c₀ c₁ c₂ c₃ m e w s v / (u + v)|) (scOutCR m s) :=
    hkI.mono_set fun v hv => hv.1
  rw [← scOutCS_union, setIntegral_union scOutCS_disjoint (measurableSet_scOutCR m s) hS hR,
    scOutC_abs_k_R hm hw hu hs]
  have h1 := scOutC_abs_k_S hm he hw hu hs hM c₀ c₁ c₂ c₃
  have h2 := scOutC_abs_kap hm he hw hu hs hM a₀ a₁ a₂
  have h2' : 0 ≤ ∫ v in Ioi 0, |scOutCkap a₀ a₁ a₂ m e w s v / (u + v) ^ 2| :=
    integral_nonneg fun _ => abs_nonneg _
  have h3 : 0 ≤ |c₀ * w * log m| * (1 / u) := by positivity
  linarith

end

/-- **The pointwise domination of the `k`-part.** -/
theorem formOC_abs_k_le_dom {t Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hM : Y ^ 2 - t * (y3 * (Y - y3)) ≠ 0) :
    ∫ v in Ioi 0, |scOutCk (cornerC0 x) (cornerC1 x y3 (Y - y3)) (cornerC2 x y3 (Y - y3))
        (cornerC3 x y3 (Y - y3)) (scOutCm Y y3 x) (y3 * (Y - y3)) (scOutRho x) (scOutCs Y y3 x) v /
        (setCKQ x + t + v)| ≤ scOutCDom t Y y3 x := by
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
  have hgen := formOC_abs_k_le hm he hw hu hs hM'
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

end QED.ChainProof.SetCK

end
