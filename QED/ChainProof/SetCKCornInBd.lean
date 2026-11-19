/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCornInKt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G2: an integrable bound for the corner node weight

Helper level (no frozen statement). On the second branch `x* ≤ x < 1` write
`u = 1 - y₃`, `v = (Y - y₃)/(1 - y₃)` and `s = (1 - x)/v`, all in `[0, 1]`; then `x = 1 - s v`,
`Y - y₃ = v u`, and the numerator of `φ'` is `v² u² Ñ(s, u, v)` with a polynomial `Ñ`
(`cornInNt_eq`, scratch `g2/bnd.py`, `g2/mkNt.py`). Hence (`cornInDPhi_mul_w0`)

`φ'(x) w₀(x) = Ñ(s, u, v)/(2 x (x - 2)²)`,

which is `O(1/x)` although `φ'` alone carries `1/(y₃ (Y-y₃)³)`. Bounding the polynomials `Ñ` and
`B = |c₁| + |P₂| + |P₃|` on compact cubes, with `M ≥ m = min(1, t)/2`, `w₀ ≥ y₃(1-Y)x`,
`(1-x) w₀ ≤ 1`, `log(1 + z) ≤ z` and `x ≥ x* ≥ 1 - Y`, gives (**`cornIn_exists_bound`**)

`∫₀^∞ |K_tot(w)|/(M + w) dw ≤ C₁(1 + (-log y₃ - log(1-Y) - log x)/m) + 1/(2m)
  + C₂ (√(1-Y))⁻¹ (√x)⁻¹/m`  (`cornInDom`),

a sum of products of integrable functions of one variable each.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- `Ñ(s, u, v)` as a Horner list in `s`. -/
noncomputable def cornInNtl (u v : ℝ) : List ℝ :=
  [2 * u - 1, 3 * u ^ 2 * v ^ 3 - 3 * u * v ^ 2 + 4 * u * v - 6 * u - 5 * v + 3,
    u ^ 2 * v ^ 4 - 12 * u ^ 2 * v ^ 3 + 3 * u * v ^ 3 + 10 * u * v ^ 2 - 10 * u * v + 4 * u -
      2 * v ^ 2 + 9 * v - 2,
    -v * (3 * u ^ 2 * v ^ 3 - 15 * u ^ 2 * v ^ 2 - u * v ^ 3 + 8 * u * v ^ 2 + 7 * u * v -
      6 * u - 2 * v + 3),
    v ^ 3 * (3 * u ^ 2 * v ^ 2 + 3 * u ^ 2 * v - 6 * u ^ 2 - u * v ^ 2 - 4 * u * v + 7 * u - 2),
    -v ^ 3 * (6 * u ^ 2 * v ^ 2 + u ^ 2 * v - 4 * u * v ^ 2 - 3 * u * v + 2 * u - 1),
    3 * u * v ^ 5 * (u - 1)]

/-- The lower bound `m = min(1, t)/2` of `M_t(Y)` on `[0, 1]`. -/
noncomputable def cornInM0 (t : ℝ) : ℝ := min 1 t / 2

/-- **The dominating function** of the node weight. -/
noncomputable def cornInDom (t C₁ C₂ Y y3 x : ℝ) : ℝ :=
  C₁ * (1 + (-log y3 - log (1 - Y) - log x) / cornInM0 t) + 1 / (2 * cornInM0 t) +
    C₂ * ((√(1 - Y))⁻¹ * (√x)⁻¹) / cornInM0 t

theorem cornInNt_eq (s u v : ℝ) :
    hpoly (cornInNl (1 - u + v * u) (1 - u)) (1 - s * v) =
      v ^ 2 * u ^ 2 * hpoly (cornInNtl u v) s := by
  simp only [hpoly, cornInNl, cornInNtl]
  ring

theorem cornInM0_pos {t : ℝ} (ht : 0 < t) : 0 < cornInM0 t := by
  unfold cornInM0; have := lt_min one_pos ht; positivity

theorem cornInM0_le_massIn {t Y : ℝ} (ht : 0 < t) (hY : Y ∈ Icc (0 : ℝ) 1) :
    cornInM0 t ≤ massIn t Y := by
  have h1 : min 1 t ≤ 1 := min_le_left 1 t
  have h2 : min 1 t ≤ t := min_le_right 1 t
  have h0 : 0 < min 1 t := lt_min one_pos ht
  unfold massIn ladderInnerMass cornInM0
  rw [sq_sqrt ht.le]
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith [hY.2] : (0 : ℝ) ≤ 1 - Y),
    mul_nonneg h0.le (sq_nonneg (Y - 1 / 2)), hY.1, hY.2]

theorem exists_bound_cornInNt : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
    ∀ v ∈ Icc (0 : ℝ) 1, |hpoly (cornInNtl u v) s| ≤ C := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hc : Continuous fun p : ℝ × ℝ × ℝ => hpoly (cornInNtl p.2.1 p.2.2) p.1 := by
    simp only [hpoly, cornInNtl]
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun s hs u hu v hv => ?_⟩
  have := hC (s, u, v) ⟨hs, hu, hv⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem exists_bound_cornInBd : ∃ C : ℝ, 0 ≤ C ∧ ∀ Y ∈ Icc (0 : ℝ) 1, ∀ y3 ∈ Icc (0 : ℝ) 1,
    ∀ x ∈ Icc (0 : ℝ) 1, cornInBd Y y3 x ≤ C := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hc : Continuous fun p : ℝ × ℝ × ℝ => cornInBd p.1 p.2.1 p.2.2 := by
    simp only [cornInBd, cornerC1, cornerG, cornInP2, cornInP3,
      QED.TwoLoop.UnitSCReduce.cornerP2]
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun Y hY y3 h3 x hx => ?_⟩
  have := hC (Y, y3, x) ⟨hY, h3, hx⟩
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

section

variable {Y y3 x : ℝ}

/-- **`φ' w₀ = Ñ(s, u, v)/(2x(x-2)²)`** on the second branch. -/
theorem cornInDPhi_mul_w0 (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hb : cornInXs Y y3 ≤ x) :
    cornInDPhi Y y3 x * cornInW0 Y y3 x =
      hpoly (cornInNtl (1 - y3) ((Y - y3) / (1 - y3))) ((1 - x) / ((Y - y3) / (1 - y3))) /
        (2 * x * (x - 2) ^ 2) := by
  rw [cornInW0_of_branch2 h3 hx.2 (cornIn_branch2_of_xs h3 h34 hY hb)]
  have hu0 : 0 < 1 - y3 := by linarith
  have hv0 : 0 < (Y - y3) / (1 - y3) := div_pos (by linarith) hu0
  obtain ⟨u, hu⟩ : ∃ u, u = 1 - y3 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = (Y - y3) / (1 - y3) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = (1 - x) / v := ⟨_, rfl⟩
  rw [← hv, ← hs, ← hu]
  rw [← hv] at hv0
  rw [← hu] at hu0
  have hvu : v * u = Y - y3 := by
    have : (1 : ℝ) - y3 ≠ 0 := by linarith
    rw [hv, hu]; field_simp
  have hsv : s * v = 1 - x := by rw [hs]; field_simp
  have key := cornInNt_eq s u v
  rw [show 1 - u + v * u = Y by rw [hvu, hu]; ring, show 1 - s * v = x by rw [hsv]; ring,
    show 1 - u = y3 by rw [hu]; ring] at key
  unfold cornInDPhi
  rw [key]
  have hY' : Y = y3 + v * u := by linarith
  subst hY'
  have hx0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hx2 : x - 2 ≠ 0 := by linarith [hx.2]
  have := h3.ne'
  have := hu0.ne'
  have := hv0.ne'
  field_simp
  ring

theorem one_sub_mul_cornInW0_le (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : (1 - x) * cornInW0 Y y3 x ≤ 1 := by
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have hg : 0 ≤ cornerG y3 (Y - y3) := (cornerG_pos hY h3).le
  have he : 0 ≤ y3 * (Y - y3) * x / (1 - x) := by
    have : 0 ≤ Y - y3 := by linarith
    have := hx.1.le
    positivity
  have hβ : betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x ≤
      cornerG y3 (Y - y3) + y3 * (Y - y3) * x / (1 - x) :=
    max_le (by linarith) (by linarith)
  have hw : (1 - x) * cornInW0 Y y3 x ≤
      (1 - x) * x * cornerG y3 (Y - y3) + y3 * (Y - y3) * x ^ 2 := by
    unfold cornInW0
    have := mul_le_mul_of_nonneg_left hβ (mul_nonneg h1.le hx.1.le)
    have e : (1 - x) * x * (cornerG y3 (Y - y3) + y3 * (Y - y3) * x / (1 - x)) =
        (1 - x) * x * cornerG y3 (Y - y3) + y3 * (Y - y3) * x ^ 2 := by
      field_simp
    nlinarith
  have hg1 : cornerG y3 (Y - y3) ≤ 1 := by
    unfold cornerG; nlinarith
  have he1 : y3 * (Y - y3) * x ^ 2 ≤ 1 / 2 := by
    have : y3 * (Y - y3) ≤ 1 / 2 := by nlinarith
    have : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    nlinarith [mul_nonneg h3.le (by linarith : (0 : ℝ) ≤ Y - y3)]
  have : (1 - x) * x ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  nlinarith [mul_nonneg (mul_nonneg h1.le hx.1.le) hg]

end

/-- **The integrable bound on the node weight.** -/
theorem cornIn_exists_bound : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
    ∀ {t Y y3 x : ℝ}, 0 < t → 0 < y3 → y3 < Y → Y < 1 → x ∈ Ioo (0 : ℝ) 1 →
      ∫ w in Ioi 0, |cornInKt Y y3 x w / (massIn t Y + w)| ≤ cornInDom t C₁ C₂ Y y3 x := by
  obtain ⟨C₁, hC₁, hB⟩ := exists_bound_cornInBd
  obtain ⟨C, hC, hN⟩ := exists_bound_cornInNt
  refine ⟨C₁, C / 2, hC₁, by positivity, fun {t Y y3 x} ht h3 h34 hY hx => ?_⟩
  have hY0 : 0 < Y := h3.trans h34
  have hx0 : 0 < x := hx.1
  have hM := massIn_pos ht ⟨hY0.le, hY.le⟩
  have hm := cornInM0_pos ht
  have hmM := cornInM0_le_massIn ht ⟨hY0.le, hY.le⟩
  set M := massIn t Y
  set m := cornInM0 t
  have hw₀ := cornInW0_pos hY h3 hx.1
  set w₀ := cornInW0 Y y3 x with hw₀def
  have hg := cornerG_pos hY h3
  have hgx : 0 < cornerG y3 (Y - y3) * x := mul_pos hg hx.1
  have hgw := cornerG_mul_le_cornInW0 Y y3 x hx.1.le
  have hgE : cornerG y3 (Y - y3) * x = y3 * (1 - Y) * x := by unfold cornerG; ring
  have h1Y : 0 < 1 - Y := by linarith
  -- the three logarithms
  have lY := log_nonpos h1Y.le (by linarith)
  have l3 := log_nonpos h3.le (by linarith)
  have lx := log_nonpos hx.1.le hx.2.le
  set L := -log y3 - log (1 - Y) - log x with hL
  have hL0 : 0 ≤ L := by linarith
  have hBd := hB Y ⟨hY0.le, hY.le⟩ y3 ⟨h3.le, by linarith⟩ x ⟨hx.1.le, hx.2.le⟩
  have hBd0 : 0 ≤ cornInBd Y y3 x := by unfold cornInBd; positivity
  -- T1: `log(1 + M/w₀)/M ≤ 1 + L/m`
  have T1 : log (1 + M / w₀) / M ≤ 1 + L / m := by
    have hgx1 : y3 * (1 - Y) * x ≤ 1 := by
      have : y3 * (1 - Y) ≤ 1 := by nlinarith
      nlinarith [hx.2, mul_nonneg h3.le h1Y.le]
    have hpos : 0 < y3 * (1 - Y) * x := by rw [← hgE]; exact hgx
    have a1 : 1 + M / w₀ ≤ (1 + M) / (y3 * (1 - Y) * x) := by
      rw [← hgE]
      have : M / w₀ ≤ M / (cornerG y3 (Y - y3) * x) :=
        div_le_div_of_nonneg_left hM.le hgx hgw
      have : 1 ≤ 1 / (cornerG y3 (Y - y3) * x) := by
        rw [le_div_iff₀ hgx, one_mul, hgE]; exact hgx1
      rw [add_div]
      linarith
    have a2 : log (1 + M / w₀) ≤ log (1 + M) + L := by
      have := log_le_log (by positivity) a1
      rw [log_div (by positivity) hpos.ne', log_mul (by positivity) hx.1.ne',
        log_mul h3.ne' h1Y.ne'] at this
      linarith
    have a3 : log (1 + M) ≤ M := by
      have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + M)
      linarith
    rw [div_le_iff₀ hM]
    have : L / m * M ≥ L := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hm]
      exact mul_le_mul_of_nonneg_left hmM hL0
    nlinarith
  -- T2: `(1-x)/2 · log(1 + w₀/M) ≤ 1/(2m)`
  have lz : log (1 + w₀ / M) ≤ w₀ / M := by
    have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + w₀ / M)
    linarith
  have lz0 : 0 ≤ log (1 + w₀ / M) := log_nonneg (by linarith [show 0 ≤ w₀ / M by positivity])
  have T2 : (1 - x) / 2 * log (1 + w₀ / M) ≤ 1 / (2 * m) := by
    have h1x : 0 ≤ (1 - x) / 2 := by linarith [hx.2]
    calc (1 - x) / 2 * log (1 + w₀ / M) ≤ (1 - x) / 2 * (w₀ / M) :=
          mul_le_mul_of_nonneg_left lz h1x
      _ = (1 - x) * w₀ / (2 * M) := by field_simp
      _ ≤ 1 / (2 * M) := div_le_div_of_nonneg_right
          (one_sub_mul_cornInW0_le h3 h34 hY hx) (by positivity)
      _ ≤ 1 / (2 * m) := div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
  -- T3: the boundary weight
  have T3 : |cornInDPhiC Y y3 x| * log (1 + w₀ / M) ≤ C / 2 * ((√(1 - Y))⁻¹ * (√x)⁻¹) / m := by
    have hR : 0 ≤ C / 2 * ((√(1 - Y))⁻¹ * (√x)⁻¹) / m := by positivity
    unfold cornInDPhiC
    split_ifs with hb
    · have hxs := cornInXs_mem h3 h34 hY
      have hdw := cornInDPhi_mul_w0 h3 h34 hY hx hb.le
      have hu : 1 - y3 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hv : (Y - y3) / (1 - y3) ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩
      have hs : (1 - x) / ((Y - y3) / (1 - y3)) ∈ Icc (0 : ℝ) 1 := by
        have hv0 : 0 < (Y - y3) / (1 - y3) := div_pos (by linarith) (by linarith)
        refine ⟨div_nonneg (by linarith [hx.2]) hv0.le, (div_le_one hv0).2 ?_⟩
        have := cornIn_branch2_of_xs h3 h34 hY hb.le
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      have hNb := hN _ hs _ hu _ hv
      -- `|φ' w₀| ≤ (C/2)/x`
      have hpw : |cornInDPhi Y y3 x| * w₀ ≤ C / 2 / x := by
        rw [← abs_of_pos hw₀, ← abs_mul, hdw, abs_div]
        have hx2 : 1 ≤ (x - 2) ^ 2 := by nlinarith [hx.2]
        have hd : 2 * x ≤ |2 * x * (x - 2) ^ 2| := by
          rw [abs_of_pos (by positivity)]
          nlinarith [hx.1]
        calc _ ≤ C / |2 * x * (x - 2) ^ 2| := div_le_div_of_nonneg_right hNb (abs_nonneg _)
          _ ≤ C / (2 * x) := div_le_div_of_nonneg_left hC (by positivity) hd
          _ = C / 2 / x := by ring
      -- `1/x ≤ (√(1-Y))⁻¹ (√x)⁻¹` since `x ≥ x* ≥ 1 - Y`
      have hxY : 1 - Y ≤ x := by
        have := cornIn_branch2_of_xs h3 h34 hY hb.le
        nlinarith [hx.1]
      have hinv : 1 / x ≤ (√(1 - Y))⁻¹ * (√x)⁻¹ := by
        have hs1 : √(1 - Y) ≤ √x := sqrt_le_sqrt hxY
        have hs0 : 0 < √(1 - Y) := sqrt_pos.2 h1Y
        have hsx : 0 < √x := sqrt_pos.2 hx.1
        rw [← mul_inv, inv_eq_one_div, one_div_le_one_div hx.1 (by positivity)]
        calc √(1 - Y) * √x ≤ √x * √x := mul_le_mul_of_nonneg_right hs1 hsx.le
          _ = x := mul_self_sqrt hx.1.le
      calc |cornInDPhi Y y3 x| * log (1 + w₀ / M) ≤ |cornInDPhi Y y3 x| * (w₀ / M) :=
            mul_le_mul_of_nonneg_left lz (abs_nonneg _)
        _ = |cornInDPhi Y y3 x| * w₀ / M := by ring
        _ ≤ C / 2 / x / M := div_le_div_of_nonneg_right hpw hM.le
        _ ≤ C / 2 / x / m := div_le_div_of_nonneg_left (by positivity) hm hmM
        _ = C / 2 * (1 / x) / m := by ring
        _ ≤ C / 2 * ((√(1 - Y))⁻¹ * (√x)⁻¹) / m := by
            gcongr
    · simpa using hR
  have hmain := cornInKt_abs_le hM h3 hY hx
  rw [← hw₀def] at hmain
  have T1' : cornInBd Y y3 x * (log (1 + M / w₀) / M) ≤ C₁ * (1 + L / m) := by
    have : 0 ≤ log (1 + M / w₀) / M :=
      div_nonneg (log_nonneg (by linarith [show 0 ≤ M / w₀ by positivity])) hM.le
    exact mul_le_mul hBd T1 this hC₁
  unfold cornInDom
  rw [← hL]
  nlinarith [mul_nonneg (abs_nonneg (cornInDPhiC Y y3 x)) lz0]

end QED.ChainProof.SetCK

end
