/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCLimitCMasters
public import QED.TwoLoop.UnitSCLimitSMasters
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K: the outer integration of the L, S, C integrands at any two photon masses

Helper level (no frozen statement). The `a`- (or `b`-) integrations of the ladder, self-energy
and corner integrands, `QED.TwoLoop.UnitLLink.hasIoiInt_ladderAX_sub`,
`QED.TwoLoop.UnitSCLimit.hasIoiInt_selfAX_sub` and `hasIoiInt_cornerAX_sub`, are stated for
positive photon masses `la, lb > 0`. The Stage K pieces use them at one photon massless: the
inner-massive placements `L(t, 0)`, `S(t, 0)`, `C(t, 0)` at outer mass `la = 0` (`h = x`), the
outer-massive ones at inner mass `lb = 0` (`M = Y²`). The proofs only use `h > 0` and `M > 0`;
this file restates them under exactly these hypotheses:

* `hasIoiInt_ladderAX_sub_of_pos`: `∫₀^∞ [ladderAX la lb₁ - ladderAX la lb₂](z + Y(1-Y)) dz =
  ladderGm la lb₁ - ladderGm la lb₂`, for `h = (x² + (1-x) la²)/x > 0` and `M(lbᵢ) > 0`;
* `hasIoiInt_selfAX_sub_of_pos`: the same for `selfAX` and `selfGm`;
* `hasIoiInt_cornerAX_sub_of_pos`: the same for `cornerAX` and `cornerGm` at `b = z + β(x)`;
* `ladderInnerMass_zero_div_pos`: `h = x > 0` at `la = 0`.

The Pauli–Villars differences remain: the identification of `ladderGm`, `selfGm`, `cornerGm` at
`Λ = ∞` with the regulated units is the regulator link (not done here).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit

theorem ladderInnerMass_zero_div_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < ladderInnerMass 1 0 x / x := by
  unfold ladderInnerMass
  have := hx.1
  have : 0 < x ^ 2 * 1 ^ 2 + (1 - x) * 0 ^ 2 := by
    simp only [one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, add_zero]
    positivity
  positivity

theorem ladderInnerMass_ne_of_div_pos {la x : ℝ} (hh : 0 < ladderInnerMass 1 la x / x) :
    ladderInnerMass 1 la x ≠ 0 := fun h0 => by simp [h0] at hh

/-! ### The ladder -/

theorem ladderAX_eq_of_pos {la lb Y x a : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < ladderInnerMass 1 lb Y) (hh : 0 < ladderInnerMass 1 la x / x) (ha : 0 < a) :
    ladderAX la lb Y x a = Y * x * (1 - x) / 2 *
      (1 / (ladderInnerMass 1 lb Y + a * (ladderInnerMass 1 la x / x)) +
        8 * (Y * (1 - Y)) * masterK2 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a -
        9 * (Y * (1 - Y)) ^ 2 *
          masterK3 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a +
        x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) -
          2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2) *
          masterK4 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a -
        x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) -
          2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2) * (Y * (1 - Y)) *
          masterK5 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a) := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hD : 0 < ladderInnerMass 1 lb Y + a * (ladderInnerMass 1 la x / x) := by positivity
  have hU : a + a * (1 - x) / x = a / x := by field_simp; ring
  have eD : Y ^ 2 + (1 - Y) * lb ^ 2 + a ^ 2 / (a / x) + la ^ 2 * (a * (1 - x) / x) =
      ladderInnerMass 1 lb Y + a * (ladderInnerMass 1 la x / x) := by
    unfold ladderInnerMass
    field_simp
    ring
  unfold ladderAX QED.TwoLoop.UnitLGraphReduce.ladderDocF
  rw [hU, eD]
  unfold masterK2 masterK3 masterK4 masterK5
  field_simp
  ring

/-- **The `a`-integration of the ladder at any two photon masses with `h, M > 0`.** -/
theorem hasIoiInt_ladderAX_sub_of_pos {la lb₁ lb₂ Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hh : 0 < ladderInnerMass 1 la x / x)
    (hM₁ : 0 < ladderInnerMass 1 lb₁ Y) (hM₂ : 0 < ladderInnerMass 1 lb₂ Y) :
    HasIoiInt (fun z => ladderAX la lb₁ Y x (z + Y * (1 - Y)) -
        ladderAX la lb₂ Y x (z + Y * (1 - Y)))
      (ladderGm la lb₁ Y x - ladderGm la lb₂ Y x) := by
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 (by linarith [hY.2])
  have I1 := hasIoiInt_master1 hM₁ hM₂ hh hc
  have I2 := (hasIoiInt_master2 hM₁ hh hc).sub (hasIoiInt_master2 hM₂ hh hc)
  have I3 := (hasIoiInt_master3 hM₁ hh hc).sub (hasIoiInt_master3 hM₂ hh hc)
  have I4 := (hasIoiInt_master4 hM₁ hh hc).sub (hasIoiInt_master4 hM₂ hh hc)
  have I5 := (hasIoiInt_master5 hM₁ hh hc).sub (hasIoiInt_master5 hM₂ hh hc)
  set q := x * ((3 * Y - 2) + (4 * Y - Y ^ 2 - 2) * ((1 - x) / x) -
    2 * (Y * (1 - Y)) * ((1 - x) / x) ^ 2) with hq
  have I := (((((I1.add (I2.const_mul (8 * (Y * (1 - Y))))).sub
    (I3.const_mul (9 * (Y * (1 - Y)) ^ 2))).add (I4.const_mul q)).sub
    (I5.const_mul (q * (Y * (1 - Y))))).const_mul (Y * x * (1 - x) / 2))
  refine I.congr (fun z hz => ?_) ?_
  · have ha : 0 < z + Y * (1 - Y) := by simp only [mem_Ioi] at hz; linarith
    rw [ladderAX_eq_of_pos hx hM₁ hh ha, ladderAX_eq_of_pos hx hM₂ hh ha]
    ring
  · rw [ladderGm_eq_form, ladderGm_eq_form, ← hq,
      gForm_eq_masters hM₁ hh hc (by positivity), gForm_eq_masters hM₂ hh hc (by positivity)]
    ring

/-! ### The self-energy unit -/

theorem selfAX_eq_of_pos {la lb Y x a : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hM : 0 < ladderInnerMass 1 lb Y) (hh : 0 < ladderInnerMass 1 la x / x) (ha : 0 < a) :
    selfAX la lb Y x a =
      (selfK1 Y x + selfK2 Y x / (ladderInnerMass 1 la x / x)) *
          (1 / (ladderInnerMass 1 lb Y + a * (ladderInnerMass 1 la x / x))) +
        (-(selfK2 Y x * ladderInnerMass 1 lb Y / (ladderInnerMass 1 la x / x)) -
            2 * (Y * (1 - Y)) * selfK2 Y x) *
          masterK4 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a +
        selfK2 Y x * (Y * (1 - Y)) ^ 2 *
          masterK5 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a -
        2 * (Y * (1 - Y)) * selfK1 Y x *
          masterK2 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a +
        selfK1 Y x * (Y * (1 - Y)) ^ 2 *
          masterK3 (ladderInnerMass 1 lb Y) (ladderInnerMass 1 la x / x) a := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hD : 0 < ladderInnerMass 1 lb Y + a * (ladderInnerMass 1 la x / x) := by positivity
  unfold selfAX
  rw [QED.TwoLoop.UnitSCReduce.selfDocF_subst hY ha hx (sq_nonneg la) (sq_nonneg lb)]
  have eD : Y ^ 2 + (1 - Y) * lb ^ 2 + a * ((x ^ 2 + (1 - x) * la ^ 2) / x) =
      ladderInnerMass 1 lb Y + a * (ladderInnerMass 1 la x / x) := by
    unfold ladderInnerMass; ring
  rw [eD]
  have hh0 := hh.ne'
  have hD0 := hD.ne'
  have hM0 := hM.ne'
  have hL0 := ladderInnerMass_ne_of_div_pos hh
  have ha0 := ha.ne'
  unfold masterK2 masterK3 masterK4 masterK5 selfK1 selfK2
  field_simp
  ring

/-- **The `a`-integration of the self-energy unit at any two photon masses with `h, M > 0`.** -/
theorem hasIoiInt_selfAX_sub_of_pos {la lb₁ lb₂ Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hh : 0 < ladderInnerMass 1 la x / x)
    (hM₁ : 0 < ladderInnerMass 1 lb₁ Y) (hM₂ : 0 < ladderInnerMass 1 lb₂ Y) :
    HasIoiInt (fun z => selfAX la lb₁ Y x (z + Y * (1 - Y)) - selfAX la lb₂ Y x (z + Y * (1 - Y)))
      (selfGm la lb₁ Y x - selfGm la lb₂ Y x) := by
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 (by linarith [hY.2])
  set M₁ := ladderInnerMass 1 lb₁ Y with hM₁def
  set M₂ := ladderInnerMass 1 lb₂ Y with hM₂def
  set h := ladderInnerMass 1 la x / x with hhdef
  set c := Y * (1 - Y) with hcdef
  have I1 := hasIoiInt_master1 hM₁ hM₂ hh hc
  have I2 := (hasIoiInt_master2 hM₁ hh hc).sub (hasIoiInt_master2 hM₂ hh hc)
  have I3 := (hasIoiInt_master3 hM₁ hh hc).sub (hasIoiInt_master3 hM₂ hh hc)
  have I5 := (hasIoiInt_master5 hM₁ hh hc).sub (hasIoiInt_master5 hM₂ hh hc)
  have I4a := (hasIoiInt_master4 hM₁ hh hc).const_mul
    (-(selfK2 Y x * M₁ / h) - 2 * c * selfK2 Y x)
  have I4b := (hasIoiInt_master4 hM₂ hh hc).const_mul
    (-(selfK2 Y x * M₂ / h) - 2 * c * selfK2 Y x)
  have I := ((((I1.const_mul (selfK1 Y x + selfK2 Y x / h)).add (I4a.sub I4b)).add
    (I5.const_mul (selfK2 Y x * c ^ 2))).sub (I2.const_mul (2 * c * selfK1 Y x))).add
    (I3.const_mul (selfK1 Y x * c ^ 2))
  refine I.congr (fun z hz => ?_) ?_
  · have ha : 0 < z + c := by simp only [mem_Ioi] at hz; linarith
    rw [selfAX_eq_of_pos (lb := lb₁) hY hx hM₁ hh ha,
      selfAX_eq_of_pos (lb := lb₂) hY hx hM₂ hh ha]
    ring
  · simp only [QED.TwoLoop.UnitSCLimit.selfGm, sForm_eq_masters]
    rw [← hM₁def, ← hM₂def, ← hhdef, ← hcdef]
    have h1 : log (M₂ + c * h) - log (M₁ + c * h) = -log (M₁ + c * h) - -log (M₂ + c * h) := by
      ring
    rw [div_eq_mul_inv (log (M₂ + c * h) - log (M₁ + c * h)), h1]
    ring

/-! ### The corner -/

theorem cornerAX_eq_of_pos {la lb y3 y4 x b : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hh : 0 < ladderInnerMass 1 la x / x) (hb : 0 < b)
    (hD : 0 < cornerMass la lb y3 y4 + b * (ladderInnerMass 1 la x / x)) :
    cornerAX la lb y3 y4 x b =
      cornerC0 x * (1 / (cornerMass la lb y3 y4 + b * (ladderInnerMass 1 la x / x))) +
        cornerA0 x y3 y4 * masterK4 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        cornerA1 x y3 y4 * masterK5 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        cornerA2 x y3 y4 * masterK6 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        cornerC1 x y3 y4 * masterK2 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        cornerC2 x y3 y4 * masterK3 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b +
        cornerC3 x y3 y4 * masterK7 (cornerMass la lb y3 y4) (ladderInnerMass 1 la x / x) b := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have eD : (y3 + y4) ^ 2 + (1 - (y3 + y4)) * lb ^ 2 - la ^ 2 * (y3 * y4) +
      b * ((x ^ 2 + (1 - x) * la ^ 2) / x) =
      cornerMass la lb y3 y4 + b * (ladderInnerMass 1 la x / x) := by
    unfold cornerMass ladderInnerMass; ring
  have hD' : 0 < (y3 + y4) ^ 2 + (1 - (y3 + y4)) * lb ^ 2 - la ^ 2 * (y3 * y4) +
      b * ((x ^ 2 + (1 - x) * la ^ 2) / x) := eD ▸ hD
  unfold cornerAX
  rw [show cornerG y3 y4 = y3 * (1 - y3 - y4) from rfl,
    QED.TwoLoop.UnitSCReduce.cornerTerm_subst hb hx hD', eD]
  have hL0 := ladderInnerMass_ne_of_div_pos hh
  have hD0 := hD.ne'
  have hb0 := hb.ne'
  unfold masterK2 masterK3 masterK4 masterK5 masterK6 masterK7 cornerA0 cornerA1 cornerA2 cornerC0
    cornerC1 cornerC2 cornerC3 cornerQ cornerR cornerG
  field_simp
  ring

/-- **The `b`-integration of the corner at any two photon masses with `h, M > 0`.** -/
theorem hasIoiInt_cornerAX_sub_of_pos {la lb₁ lb₂ y3 y4 x : ℝ} (h3 : 0 < y3)
    (hY : y3 + y4 < 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hh : 0 < ladderInnerMass 1 la x / x)
    (hM₁ : 0 < cornerMass la lb₁ y3 y4) (hM₂ : 0 < cornerMass la lb₂ y3 y4) :
    HasIoiInt (fun z => cornerAX la lb₁ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x) -
        cornerAX la lb₂ y3 y4 x (z + betaG (cornerG y3 y4) (y3 * y4) x))
      (cornerGm la lb₁ y3 y4 x - cornerGm la lb₂ y3 y4 x) := by
  have hg : 0 < cornerG y3 y4 := by
    unfold cornerG; have : 0 < 1 - y3 - y4 := by linarith
    positivity
  have hβ := betaG_pos (e := y3 * y4) (x := x) hg
  set M₁ := cornerMass la lb₁ y3 y4 with hM₁def
  set M₂ := cornerMass la lb₂ y3 y4 with hM₂def
  set h := ladderInnerMass 1 la x / x with hhdef
  set β := betaG (cornerG y3 y4) (y3 * y4) x with hβdef
  have I1 := hasIoiInt_master1 hM₁ hM₂ hh hβ
  have I2 := (hasIoiInt_master2 hM₁ hh hβ).sub (hasIoiInt_master2 hM₂ hh hβ)
  have I3 := (hasIoiInt_master3 hM₁ hh hβ).sub (hasIoiInt_master3 hM₂ hh hβ)
  have I4 := (hasIoiInt_master4 hM₁ hh hβ).sub (hasIoiInt_master4 hM₂ hh hβ)
  have I5 := (hasIoiInt_master5 hM₁ hh hβ).sub (hasIoiInt_master5 hM₂ hh hβ)
  have I6 := (hasIoiInt_master6 hM₁ hh hβ).sub (hasIoiInt_master6 hM₂ hh hβ)
  have I7 := (hasIoiInt_master7 hM₁ hh hβ).sub (hasIoiInt_master7 hM₂ hh hβ)
  have I := ((((((I1.const_mul (cornerC0 x)).add (I4.const_mul (cornerA0 x y3 y4))).add
    (I5.const_mul (cornerA1 x y3 y4))).add (I6.const_mul (cornerA2 x y3 y4))).add
    (I2.const_mul (cornerC1 x y3 y4))).add (I3.const_mul (cornerC2 x y3 y4))).add
    (I7.const_mul (cornerC3 x y3 y4))
  refine I.congr (fun z hz => ?_) ?_
  · have hb : 0 < z + β := by simp only [mem_Ioi] at hz; linarith
    rw [cornerAX_eq_of_pos (lb := lb₁) hx hh hb (by positivity),
      cornerAX_eq_of_pos (lb := lb₂) hx hh hb (by positivity)]
    ring
  · simp only [QED.TwoLoop.UnitSCLimit.cornerGm, cForm]
    rw [← hM₁def, ← hM₂def, ← hhdef, ← hβdef]
    have h1 : log (M₂ + β * h) - log (M₁ + β * h) = -log (M₁ + β * h) - -log (M₂ + β * h) := by
      ring
    rw [div_eq_mul_inv (log (M₂ + β * h) - log (M₁ + β * h)), h1]
    ring

end QED.ChainProof.SetCK

end
