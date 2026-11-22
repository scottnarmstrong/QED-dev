/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import QED.ThreeLoopD.SetDMastersI2Def
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Set (d), master `I₂`: the photon lines of the `ℱ`-part through `s = a b / (a + b)`

In the `ℱ`-part of `P'(0)` the two photon lines `a = y₇ + A`, `b = y₈ + B` enter only through
`a + b` and the parallel combination `s = a b / (a + b)`, with weight `(a + b)⁻²`. We prove

  `∫_{a > A} ∫_{b > B} g(a b / (a + b)) / (a + b)² = ∫_{s > 0} len(s) g(s)`,
  `len(s) = min(1/A, 1/s) - max(0, 1/s - 1/B)` (clipped at `0`),

for every measurable `g ≥ 0`: with `u = 1/a`, `v = 1/b` the left side is
`∫∫_{[0, 1/A] × [0, 1/B]} h(u + v)`, `h(S) = g(1/S) / S²`; the slices of the rectangle along
`u + v = S` have length `len(1/S)`, and `S = 1/s`.

## Main results

* `QED.ThreeLoopD.i2P1FRect_inv`, `QED.ThreeLoopD.i2P1FRect_inv₀`: `x = 1/u` on `(c, ∞)`.
* `QED.ThreeLoopD.i2P1FRect_lint`.
* `QED.ThreeLoopD.i2P1FRect_y78`: the `y₇, y₈` integrals of `(1 - w) log (ℱ / 𝒰) / 𝒰²`.
-/

@[expose] public section

open Set MeasureTheory Filter Real
open scoped ENNReal

namespace QED.ThreeLoopD

/-- The slice length `len(s) = min(1/A, 1/s) - max(0, 1/s - 1/B)`. -/
noncomputable def i2P1FLen (A B s : ℝ) : ℝ := min A⁻¹ s⁻¹ - max 0 (s⁻¹ - B⁻¹)

theorem i2P1FRect_hasDerivWithinAt_inv {t : Set ℝ} {x : ℝ} (hx : x ≠ 0) :
    HasDerivWithinAt (fun u : ℝ => u⁻¹) (-(x ^ 2)⁻¹) t x :=
  (hasDerivAt_inv hx).hasDerivWithinAt

/-- `x = 1/u`: `∫_{x > c} F(x) = ∫_{0 < u < 1/c} F(1/u) / u²` for `c > 0`. -/
theorem i2P1FRect_inv {c : ℝ} (hc : 0 < c) (F : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioi c, F x = ∫⁻ u in Ioo 0 c⁻¹, ENNReal.ofReal (1 / u ^ 2) * F u⁻¹ := by
  have himg : (fun u : ℝ => u⁻¹) '' Ioo 0 c⁻¹ = Ioi c := by
    ext x
    constructor
    · rintro ⟨u, ⟨h0, h1⟩, rfl⟩
      exact (lt_inv_comm₀ h0 hc).1 h1
    · intro (hx : c < x)
      have hx0 : 0 < x := hc.trans hx
      exact ⟨x⁻¹, ⟨inv_pos.2 hx0, inv_lt_inv₀ hx0 hc |>.2 hx⟩, inv_inv x⟩
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun x hx => i2P1FRect_hasDerivWithinAt_inv hx.1.ne') (inv_injective.injOn) F]
  refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  rw [abs_neg, abs_of_pos (by have := hu.1; positivity), one_div]

/-- `x = 1/u` on `(0, ∞)`. -/
theorem i2P1FRect_inv₀ (F : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioi 0, F x = ∫⁻ u in Ioi 0, ENNReal.ofReal (1 / u ^ 2) * F u⁻¹ := by
  have himg : (fun u : ℝ => u⁻¹) '' Ioi 0 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨u, (h0 : 0 < u), rfl⟩
      exact inv_pos.2 h0
    · intro (hx : 0 < x)
      exact ⟨x⁻¹, inv_pos.2 hx, inv_inv x⟩
  conv_lhs => rw [← himg]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun x hx => i2P1FRect_hasDerivWithinAt_inv (ne_of_gt hx)) (inv_injective.injOn) F]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
  rw [abs_neg, abs_of_pos (by positivity), one_div]

/-- Translation `S = u + v`. -/
theorem i2P1FRect_add (u L : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ v in Ioo 0 L, F (u + v) = ∫⁻ S in Ioo u (u + L), F S := by
  have himg : (fun v : ℝ => u + v) '' Ioo 0 L = Ioo u (u + L) := by
    rw [image_const_add_Ioo, add_zero]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun x _ => ((hasDerivAt_id' x).const_add u).hasDerivWithinAt)
    ((add_right_injective u).injOn) F]
  simp

/-- **The slices of the rectangle**: `∫_{0 < u < L₁} ∫_{u < S < u + L₂} h(S)
= ∫ h(S) |(max(0, S - L₂), min(L₁, S))|`. -/
theorem i2P1FRect_swap (L₁ L₂ : ℝ) {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ u in Ioo 0 L₁, ∫⁻ S in Ioo u (u + L₂), h S =
      ∫⁻ S, h S * volume (Ioo (max 0 (S - L₂)) (min L₁ S)) := by
  set T : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < L₁ ∧ p.1 < p.2 ∧ p.2 < p.1 + L₂} with hT
  have hTm : MeasurableSet T := by
    refine (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.add measurable_const))))
  have e1 : ∀ u, (Ioo 0 L₁).indicator (fun u => ∫⁻ S in Ioo u (u + L₂), h S) u =
      ∫⁻ S, T.indicator (fun p => h p.2) (u, S) := by
    intro u
    by_cases hu : u ∈ Ioo 0 L₁
    · rw [indicator_of_mem hu, ← lintegral_indicator measurableSet_Ioo]
      congr 1
      ext S
      by_cases hS : S ∈ Ioo u (u + L₂)
      · rw [indicator_of_mem hS, indicator_of_mem (show (u, S) ∈ T from
          ⟨hu.1, hu.2, hS.1, hS.2⟩)]
      · rw [indicator_of_notMem hS, indicator_of_notMem (show (u, S) ∉ T from
          fun h => hS ⟨h.2.2.1, h.2.2.2⟩)]
    · rw [indicator_of_notMem hu]
      symm
      refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun S => ?_)
      exact indicator_of_notMem (fun h => hu ⟨h.1, h.2.1⟩) _
  have e2 : ∀ S, ∫⁻ u, T.indicator (fun p => h p.2) (u, S) =
      h S * volume (Ioo (max 0 (S - L₂)) (min L₁ S)) := by
    intro S
    rw [← lintegral_indicator_const measurableSet_Ioo]
    congr 1
    ext u
    by_cases hu : (u, S) ∈ T
    · have hu' : u ∈ Ioo (max 0 (S - L₂)) (min L₁ S) := by
        obtain ⟨h1, h2, h3, h4⟩ := hu
        exact ⟨max_lt h1 (by linarith), lt_min h2 h3⟩
      rw [indicator_of_mem hu, indicator_of_mem hu']
    · have hu' : u ∉ Ioo (max 0 (S - L₂)) (min L₁ S) := by
        rintro ⟨h1, h2⟩
        exact hu ⟨(le_max_left _ _).trans_lt h1, h2.trans_le (min_le_left _ _),
          h2.trans_le (min_le_right _ _), by linarith [(le_max_right 0 (S - L₂)).trans_lt h1]⟩
      rw [indicator_of_notMem hu, indicator_of_notMem hu']
  have hm : Measurable (Function.uncurry fun u S => T.indicator (fun p : ℝ × ℝ => h p.2) (u, S)) :=
    (hh.comp measurable_snd).indicator hTm
  rw [← lintegral_indicator measurableSet_Ioo, lintegral_congr e1,
    lintegral_lintegral_swap hm.aemeasurable]
  exact lintegral_congr e2

/-- **The two photon lines through `s = a b / (a + b)`**:
`∫_{a > A} ∫_{b > B} g(a b / (a + b)) / (a + b)² = ∫_{s > 0} len(s) g(s)`. -/
theorem i2P1FRect_lint {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ a in Ioi A, ∫⁻ b in Ioi B, ENNReal.ofReal (1 / (a + b) ^ 2) * g (a * b / (a + b)) =
      ∫⁻ s in Ioi 0, ENNReal.ofReal (i2P1FLen A B s) * g s := by
  set H : ℝ → ℝ≥0∞ := fun S => ENNReal.ofReal (1 / S ^ 2) * g S⁻¹ with hH
  have hHm : Measurable H :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hg.comp measurable_inv)
  calc ∫⁻ a in Ioi A, ∫⁻ b in Ioi B, ENNReal.ofReal (1 / (a + b) ^ 2) * g (a * b / (a + b))
      = ∫⁻ a in Ioi A, ∫⁻ v in Ioo 0 B⁻¹, ENNReal.ofReal (1 / v ^ 2) *
          (ENNReal.ofReal (1 / (a + v⁻¹) ^ 2) * g (a * v⁻¹ / (a + v⁻¹))) :=
        setLIntegral_congr_fun measurableSet_Ioi fun a _ => i2P1FRect_inv hB _
    _ = ∫⁻ u in Ioo 0 A⁻¹, ENNReal.ofReal (1 / u ^ 2) * ∫⁻ v in Ioo 0 B⁻¹,
          ENNReal.ofReal (1 / v ^ 2) * (ENNReal.ofReal (1 / (u⁻¹ + v⁻¹) ^ 2) *
            g (u⁻¹ * v⁻¹ / (u⁻¹ + v⁻¹))) := i2P1FRect_inv hA _
    _ = ∫⁻ u in Ioo 0 A⁻¹, ∫⁻ v in Ioo 0 B⁻¹, H (u + v) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
        have hu0 : 0 < u := hu.1
        have hv0 : 0 < v := hv.1
        simp only [hH]
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        · field_simp; ring
        · field_simp; ring
    _ = ∫⁻ u in Ioo 0 A⁻¹, ∫⁻ S in Ioo u (u + B⁻¹), H S :=
        setLIntegral_congr_fun measurableSet_Ioo fun u _ => i2P1FRect_add u B⁻¹ H
    _ = ∫⁻ S, H S * volume (Ioo (max 0 (S - B⁻¹)) (min A⁻¹ S)) := i2P1FRect_swap _ _ hHm
    _ = ∫⁻ S in Ioi 0, H S * ENNReal.ofReal (min A⁻¹ S - max 0 (S - B⁻¹)) := by
        rw [← setLIntegral_eq_of_support_subset (s := Ioi 0)]
        · refine setLIntegral_congr_fun measurableSet_Ioi fun S _ => ?_
          rw [Real.volume_Ioo]
        · intro S hS
          by_contra hS0
          have hS0 : S ≤ 0 := not_lt.1 hS0
          apply hS
          simp only
          rw [Ioo_eq_empty (not_lt.2 ((min_le_right _ _).trans (hS0.trans (le_max_left _ _)))),
            measure_empty, mul_zero]
    _ = ∫⁻ s in Ioi 0, ENNReal.ofReal (1 / s ^ 2) *
          (H s⁻¹ * ENNReal.ofReal (min A⁻¹ s⁻¹ - max 0 (s⁻¹ - B⁻¹))) := i2P1FRect_inv₀ _
    _ = ∫⁻ s in Ioi 0, ENNReal.ofReal (i2P1FLen A B s) * g s := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
        simp only [hH, i2P1FLen, inv_inv]
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          show 1 / s ^ 2 * (1 / s⁻¹ ^ 2) = 1 by field_simp, ENNReal.ofReal_one, one_mul,
          mul_comm]

/-- Translation `a = y + A` on `(0, ∞)`. -/
theorem i2P1FRect_shift (A : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ y in Ioi 0, F (y + A) = ∫⁻ a in Ioi A, F a := by
  have himg : (fun y : ℝ => y + A) '' Ioi 0 = Ioi A := by
    rw [image_add_const_Ioi, zero_add]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun x _ => ((hasDerivAt_id' x).add_const A).hasDerivWithinAt)
    ((add_left_injective A).injOn) F]
  simp

/-- The integrand of the `ℱ`-part after the photon lines, `log (1 + y² / (s + c)) / (s + c)²`
with `c = y + α₁ α₃` the electron line. -/
noncomputable def i2P1Fg (x w y s : ℝ) : ℝ :=
  log (1 + y ^ 2 / (s + i2LineC x w y)) / (s + i2LineC x w y) ^ 2

/-- **The photon lines of the `ℱ`-part**: for fixed `x, w, y₄ = y`,
`∫∫ (1 - w) log (ℱ / 𝒰) / 𝒰² dy₇ dy₈ = ∫_{s > 0} len(s) (1 - w) log (1 + y² / (s + c)) / (s + c)²`
with `A = α₁ α₂`, `B = α₂ α₃`. -/
theorem i2P1FRect_y78 {x w y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
    (hy : 0 < y) :
    ∫⁻ y₇ in Ioi 0, ∫⁻ y₈ in Ioi 0, ENNReal.ofReal ((1 - w) *
        log (i2F x w y y₇ y₈ / i2U x w y y₇ y₈) / i2U x w y y₇ y₈ ^ 2) =
      ∫⁻ s in Ioi 0, ENNReal.ofReal (i2P1FLen (w * (1 - w) * x) (w * (1 - w) * (1 - x)) s) *
        ENNReal.ofReal ((1 - w) * i2P1Fg x w y s) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hw0, hw1⟩ := hw
  have hA : 0 < w * (1 - w) * x := by
    have : 0 < 1 - w := by linarith
    positivity
  have hB : 0 < w * (1 - w) * (1 - x) := by
    have : 0 < 1 - w := by linarith
    have : 0 < 1 - x := by linarith
    positivity
  have hc : 0 < i2LineC x w y := by
    have : 0 < 1 - x := by linarith
    simp only [i2LineC]
    positivity
  have hgm : Measurable fun s => ENNReal.ofReal ((1 - w) * i2P1Fg x w y s) := by
    unfold i2P1Fg
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [← i2P1FRect_lint hA hB hgm, ← i2P1FRect_shift (w * (1 - w) * x)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y₇ (h7 : 0 < y₇) => ?_
  rw [← i2P1FRect_shift (w * (1 - w) * (1 - x))]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y₈ (h8 : 0 < y₈) => ?_
  set a := y₇ + w * (1 - w) * x with ha
  set b := y₈ + w * (1 - w) * (1 - x) with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hU : i2U x w y y₇ y₈ = (a + b) * (a * b / (a + b) + i2LineC x w y) := by
    simp only [i2U, i2LineA, i2LineB, ha, hb]
    field_simp
    ring
  have hF : i2F x w y y₇ y₈ = (a + b) * (a * b / (a + b) + i2LineC x w y + y ^ 2) := by
    simp only [i2F, hU, i2LineA, i2LineB, ha, hb]
    ring
  rw [← ENNReal.ofReal_mul (by positivity), hU, hF, i2P1Fg]
  congr 1
  have hs : 0 < a * b / (a + b) + i2LineC x w y := by positivity
  field_simp

end QED.ThreeLoopD
