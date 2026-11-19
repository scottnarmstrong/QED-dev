/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCornInIBP
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G2: the total `w`-weight of the corner unit and its size

Helper level (no frozen statement). After the integration by parts of `SetCKCornInIBP`, the
boundary term of the unit becomes a `w`-integral below the threshold `w₀`, and the full weight at
`(Y, y₃, x)` is (`cornInKt`)

`K_tot(w) = K(w) - 1{x* < x} φ'(x) 1{w ≤ w₀}`,

so that (**`cornInKt_integral`**)
`∫₀^∞ K_tot(w)/(M + w) dw = ∫₀^∞ K(w)/(M + w) dw - 1{x* < x} φ'(x) log(1 + w₀/M)`.

Size (**`cornInKt_abs_le`**): beyond the threshold `w > w₀ ≥ g x` the weight is
`c₁/w + g x P₂/w² + (g x)² P₃/w³` with polynomials `P₂`, `P₃` (`cornInP2_eq`, `cornInP3_eq`), so
`|K(w)| ≤ B/w` with `B = |c₁| + |P₂| + |P₃|` (`cornInBd`); below it `|K_tot| ≤ (1-x)/2 + |φ'|`.
Hence `∫₀^∞ |K_tot|/(M + w) ≤ B log(1 + M/w₀)/M + ((1-x)/2 + 1{x* < x}|φ'|) log(1 + w₀/M)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- `φ'` on the second branch `x* < x`, zero on the first. -/
noncomputable def cornInDPhiC (Y y3 x : ℝ) : ℝ :=
  if cornInXs Y y3 < x then cornInDPhi Y y3 x else 0

/-- **The total `w`-weight** `K_tot(w) = K(w) - 1{x* < x} φ'(x) 1{w ≤ w₀}` of the unit. -/
noncomputable def cornInKt (Y y3 x w : ℝ) : ℝ :=
  cornInKw Y y3 x w - cornInDPhiC Y y3 x * (if w ≤ cornInW0 Y y3 x then 1 else 0)

/-- The boundary piece `1{x* < x} φ'(x) log(1 + w₀/M)`. -/
noncomputable def cornInBphi (M Y y3 x : ℝ) : ℝ :=
  cornInDPhiC Y y3 x * log (1 + cornInW0 Y y3 x / M)

/-- `P₂ = (c₂ x - a₁)/(g x)`. -/
noncomputable def cornInP2 (Y y3 x : ℝ) : ℝ :=
  (-Y ^ 2 - 4 * Y * x ^ 2 * y3 + 4 * Y * x * y3 - Y * x + 2 * Y + 5 * x ^ 3 * y3 ^ 2 -
    5 * x ^ 3 * y3 - 4 * x ^ 2 * y3 ^ 2 + 4 * x ^ 2 + 2 * x * y3 - 3 * x) / 2

/-- `P₃ = (c₃ x² - 2 a₂ x)/(g x)²`. -/
noncomputable def cornInP3 (_Y y3 x : ℝ) : ℝ := x * (5 * x - 4) * (2 * y3 - 1) / 4

/-- The size `B = |c₁| + |P₂| + |P₃|` of the weight beyond the threshold. -/
noncomputable def cornInBd (Y y3 x : ℝ) : ℝ :=
  |cornerC1 x y3 (Y - y3)| + |cornInP2 Y y3 x| + |cornInP3 Y y3 x|

section

variable {M Y y3 x : ℝ}

theorem cornInP2_eq (Y y3 x : ℝ) :
    cornerC2 x y3 (Y - y3) * x - cornerA1 x y3 (Y - y3) =
      cornerG y3 (Y - y3) * x * cornInP2 Y y3 x := by
  simp only [cornerC2, cornerA1, cornerG, cornerR, cornerQ, cornInP2,
    QED.TwoLoop.UnitSCReduce.cornerP1, QED.TwoLoop.UnitSCReduce.cornerP2]
  ring

theorem cornInP3_eq (Y y3 x : ℝ) :
    cornerC3 x y3 (Y - y3) * x ^ 2 - 2 * cornerA2 x y3 (Y - y3) * x =
      (cornerG y3 (Y - y3) * x) ^ 2 * cornInP3 Y y3 x := by
  simp only [cornerC3, cornerA2, cornerG, cornerR, cornerQ, cornInP3]
  ring

theorem cornerG_mul_le_cornInW0 (Y y3 x : ℝ) (hx : 0 ≤ x) :
    cornerG y3 (Y - y3) * x ≤ cornInW0 Y y3 x :=
  mul_le_mul_of_nonneg_right (le_max_left _ _) hx

theorem cornInKw_of_lt {w : ℝ} (hw : cornInW0 Y y3 x < w) :
    cornInKw Y y3 x w = cornInOm (cornerA1 x y3 (Y - y3)) (cornerA2 x y3 (Y - y3))
      (cornerC1 x y3 (Y - y3)) (cornerC2 x y3 (Y - y3)) (cornerC3 x y3 (Y - y3)) x w := by
  simp only [cornInKw, cornInK, hw, ↓reduceIte]

theorem cornInKw_of_le {w : ℝ} (hx : x ≠ 0) (hw : w ≤ cornInW0 Y y3 x) :
    cornInKw Y y3 x w = -((1 - x) / 2) := by
  simp only [cornInKw, cornInK, not_lt.2 hw, ↓reduceIte, cornerC0]
  field_simp

/-- Beyond the threshold, `|K(w)| ≤ B/w`. -/
theorem abs_cornInKw_le {w : ℝ} (hx : 0 < x) (hg : 0 < cornerG y3 (Y - y3))
    (hw : cornInW0 Y y3 x < w) : |cornInKw Y y3 x w| ≤ cornInBd Y y3 x / w := by
  have hgx : 0 < cornerG y3 (Y - y3) * x := mul_pos hg hx
  have hgw : cornerG y3 (Y - y3) * x < w :=
    (cornerG_mul_le_cornInW0 Y y3 x hx.le).trans_lt hw
  have hw0 : 0 < w := hgx.trans hgw
  set G := cornerG y3 (Y - y3) * x with hG
  rw [cornInKw_of_lt hw]
  unfold cornInOm
  rw [cornInP2_eq, cornInP3_eq, ← hG]
  have e : cornerC1 x y3 (Y - y3) / w + G * cornInP2 Y y3 x / w ^ 2 +
      G ^ 2 * cornInP3 Y y3 x / w ^ 3 =
      (cornerC1 x y3 (Y - y3) + (G / w) * cornInP2 Y y3 x +
        (G / w) ^ 2 * cornInP3 Y y3 x) / w := by
    field_simp
  rw [e, abs_div, abs_of_pos hw0]
  refine div_le_div_of_nonneg_right ?_ hw0.le
  have hq : 0 ≤ G / w := (div_pos hgx hw0).le
  have hq1 : G / w ≤ 1 := (div_le_one hw0).2 hgw.le
  have hq2 : (G / w) ^ 2 ≤ 1 := pow_le_one₀ hq hq1
  unfold cornInBd
  calc |cornerC1 x y3 (Y - y3) + G / w * cornInP2 Y y3 x + (G / w) ^ 2 * cornInP3 Y y3 x|
      ≤ |cornerC1 x y3 (Y - y3)| + |G / w * cornInP2 Y y3 x| +
          |(G / w) ^ 2 * cornInP3 Y y3 x| := abs_add_three _ _ _
    _ ≤ |cornerC1 x y3 (Y - y3)| + |cornInP2 Y y3 x| + |cornInP3 Y y3 x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hq, abs_of_nonneg (pow_nonneg hq 2)]
        gcongr
        · exact mul_le_of_le_one_left (abs_nonneg _) hq1
        · exact mul_le_of_le_one_left (abs_nonneg _) hq2

theorem cornIn_log_one_add_div {M c : ℝ} (hM : 0 < M) (hc : 0 ≤ c) :
    log (1 + c / M) = log (M + c) - log M := by
  rw [show 1 + c / M = (M + c) / M by field_simp, log_div (by positivity) hM.ne']

/-- **The total weight integrated against `1/(M + w)`.** -/
theorem cornInKt_integral (hM : 0 < M) (h3 : 0 < y3) (hY : Y < 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun w => cornInKt Y y3 x w / (M + w)) (Ioi 0) ∧
      ∫ w in Ioi 0, cornInKt Y y3 x w / (M + w) =
        (∫ w in Ioi 0, cornInKw Y y3 x w / (M + w)) - cornInBphi M Y y3 x := by
  have hw₀ := cornInW0_pos hY h3 hx.1
  set w₀ := cornInW0 Y y3 x with hw₀def
  set c := cornInDPhiC Y y3 x
  have hK : IntegrableOn (fun w => cornInKw Y y3 x w / (M + w)) (Ioi 0) :=
    integrableOn_cornInK (a₁ := cornerA1 x y3 (Y - y3)) (a₂ := cornerA2 x y3 (Y - y3))
      (c₀ := cornerC0 x) (c₁ := cornerC1 x y3 (Y - y3)) (c₂ := cornerC2 x y3 (Y - y3))
      (c₃ := cornerC3 x y3 (Y - y3)) (h := x) hM hw₀
  obtain ⟨i0, v0⟩ := cornIn_integral_Ioc hM hw₀
  have hind : IntegrableOn (fun w => (Iic w₀).indicator (fun w => 1 / (M + w)) w) (Ioi 0) := by
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict
      measurableSet_Iic, Iic_inter_Ioi]
    exact i0
  have e : (fun w => cornInKt Y y3 x w / (M + w)) =
      fun w => cornInKw Y y3 x w / (M + w) - c * (Iic w₀).indicator (fun w => 1 / (M + w)) w := by
    funext w
    simp only [cornInKt, indicator, mem_Iic, ← hw₀def]
    split_ifs <;> ring
  rw [e]
  refine ⟨hK.sub (hind.const_mul c), ?_⟩
  rw [integral_sub hK (hind.const_mul c), integral_const_mul, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi, v0, cornInBphi,
    cornIn_log_one_add_div hM hw₀.le]

/-- **The size of the total weight**:
`∫₀^∞ |K_tot|/(M + w) ≤ B log(1 + M/w₀)/M + ((1-x)/2 + |1{x* < x} φ'|) log(1 + w₀/M)`. -/
theorem cornInKt_abs_le (hM : 0 < M) (h3 : 0 < y3) (hY : Y < 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∫ w in Ioi 0, |cornInKt Y y3 x w / (M + w)| ≤
      cornInBd Y y3 x * (log (1 + M / cornInW0 Y y3 x) / M) +
        ((1 - x) / 2 + |cornInDPhiC Y y3 x|) * log (1 + cornInW0 Y y3 x / M) := by
  have hw₀ := cornInW0_pos hY h3 hx.1
  have hg := cornerG_pos hY h3
  set w₀ := cornInW0 Y y3 x with hw₀def
  set c := cornInDPhiC Y y3 x
  have hI : IntegrableOn (fun w => |cornInKt Y y3 x w / (M + w)|) (Ioi 0) :=
    (cornInKt_integral hM h3 hY hx).1.abs
  obtain ⟨i1, v1⟩ := cornInIoi1 hM hw₀
  obtain ⟨i0, v0⟩ := cornIn_integral_Ioc hM hw₀
  rw [← Ioc_union_Ioi_eq_Ioi hw₀.le] at hI ⊢
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hI.mono_set subset_union_left) (hI.mono_set subset_union_right)]
  have hb1 : ∫ w in Ioc 0 w₀, |cornInKt Y y3 x w / (M + w)| ≤
      ((1 - x) / 2 + |c|) * log (1 + w₀ / M) := by
    rw [cornIn_log_one_add_div hM hw₀.le, ← v0, ← integral_const_mul]
    refine setIntegral_mono_on (hI.mono_set subset_union_left) (i0.const_mul _) measurableSet_Ioc
      fun w hw => ?_
    have hMw : 0 < M + w := by linarith [hw.1]
    simp only [cornInKt, cornInKw_of_le hx.1.ne' hw.2, ← hw₀def, hw.2, ↓reduceIte, mul_one]
    rw [abs_div, abs_of_pos hMw, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc |-((1 - x) / 2) - c| ≤ |(1 - x) / 2| + |c| := by
          rw [show -((1 - x) / 2) - c = -((1 - x) / 2 + c) by ring, abs_neg]
          exact abs_add_le _ _
      _ = (1 - x) / 2 + |c| := by rw [abs_of_pos (by linarith [hx.2])]
  have hb2 : ∫ w in Ioi w₀, |cornInKt Y y3 x w / (M + w)| ≤
      cornInBd Y y3 x * (log (1 + M / w₀) / M) := by
    rw [← v1, ← integral_const_mul]
    refine setIntegral_mono_on (hI.mono_set subset_union_right) (i1.const_mul _) measurableSet_Ioi
      fun w hw => ?_
    have hw0 : 0 < w := hw₀.trans hw
    have hMw : 0 < M + w := by linarith
    simp only [cornInKt, ← hw₀def, not_le.2 hw, ↓reduceIte, mul_zero, sub_zero]
    rw [abs_div, abs_of_pos hMw]
    calc |cornInKw Y y3 x w| / (M + w) ≤ cornInBd Y y3 x / w / (M + w) :=
          div_le_div_of_nonneg_right (abs_cornInKw_le hx.1 hg hw) hMw.le
      _ = cornInBd Y y3 x * (1 / (w * (M + w))) := by field_simp
  linarith

end

end QED.ChainProof.SetCK

end
