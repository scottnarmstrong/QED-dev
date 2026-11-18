/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXXiLimits
import QED.Polylog.Reflection
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Three dilogarithm identities on `(0, 1)`

Eq. (4.6) of `docs/TWO-LOOP-UNITS.md`, for the dilogarithm `Li = dilogI` on `(-∞, 1)`, whose
arguments here leave `[-1, 1]` on part of `(0, 1)`. With `D(Y) = Li₂ (1 - 2Y) - Li₂ (2Y - 1)`
(`QED.TwoLoop.Units.crossedD`) and `ζ(2) = π²/6`, for `0 < Y < 1`:

* `dilogI_neg_div_one_sub` (Landen): `Li(-Y/(1 - Y)) = -Li₂ Y - log² (1 - Y)/2`;
* `dilogI_two_mul_sub_one_div`: `Li((2Y - 1)/Y) = -D(Y) - Li₂ Y - log² Y/2 + ζ(2)/2`;
* `dilogI_one_sub_two_mul_div`:
  `Li((1 - 2Y)/(1 - Y)) = D(Y) + Li₂ Y - log² (1 - Y)/2 + log Y log (1 - Y) - ζ(2)/2`.

Each difference of the two sides has derivative `0` on `(0, 1)` off `Y = 1/2` and is continuous
on `(0, 1)`. The first vanishes at `Y = 0`; the other two vanish at `Y = 1/2`, by
`Li₂ (1/2) = π²/12 - log² 2/2` (`QED.Polylog.Li₂_one_half`).
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.TwoLoop.UnitXXi

open QED.TwoLoop.UnitXClose

/-- A function continuous on `[a, b]` with derivative `0` on `(a, b)` takes the same value at the
ends. -/
theorem eq_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : f a = f b := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · obtain ⟨c, -, hc'⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) h hc hd
    have : f b - f a = 0 := by
      rw [eq_div_iff (sub_ne_zero.mpr h.ne')] at hc'
      linarith
    linarith

theorem continuousOn_dilogI_comp {f : ℝ → ℝ} {s : Set ℝ} (hf : ContinuousOn f s)
    (h1 : ∀ x ∈ s, f x < 1) : ContinuousOn (fun x => dilogI (f x)) s :=
  ContinuousOn.comp (g := dilogI) continuousOn_dilogI hf h1

theorem dilogI_eq_Li₂_of_mem {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : dilogI x = Li₂ x :=
  dilogI_eq_Li₂ hx

/-! ### Landen's identity -/

/-- The difference of the two sides of Landen's identity, in terms of `dilogI`. -/
noncomputable def landenDiff (Y : ℝ) : ℝ :=
  dilogI (-(Y / (1 - Y))) + dilogI Y + log (1 - Y) ^ 2 / 2

theorem hasDerivAt_landenDiff {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt landenDiff 0 Y := by
  obtain ⟨hY0, hY1⟩ := hY
  have hY1' : 0 < 1 - Y := by linarith
  have hY1'' : (1 : ℝ) - Y ≠ 0 := hY1'.ne'
  have hg : HasDerivAt (fun Y => -(Y / (1 - Y))) (-(1 / (1 - Y) ^ 2)) Y := by
    have := ((hasDerivAt_id' Y).div ((hasDerivAt_id' Y).const_sub 1) hY1'').neg
    convert this using 1
    field_simp
    ring
  have hpos : 0 < Y / (1 - Y) := by positivity
  have h1 := hasDerivAt_dilogI_comp hg (by linarith) (by linarith)
  have h2 := hasDerivAt_dilogI_of_ne hY1 hY0.ne'
  have h3 := ((hasDerivAt_id' Y).const_sub 1).log hY1'' |>.pow 2 |>.div_const 2
  have h := (h1.add h2).add h3
  have e : 1 - -(Y / (1 - Y)) = 1 / (1 - Y) := by field_simp; ring
  convert h using 1
  · funext x
    simp [landenDiff]
  · rw [e, log_div one_ne_zero hY1'', log_one]
    field_simp
    ring

theorem continuousOn_landenDiff {b : ℝ} (hb : b < 1) : ContinuousOn landenDiff (Icc 0 b) := by
  have hc : ContinuousOn (fun Y : ℝ => 1 - Y) (Icc 0 b) := by fun_prop
  have hpos : ∀ Y ∈ Icc (0 : ℝ) b, 0 < 1 - Y := fun Y hY => by linarith [hY.2]
  have h1 := continuousOn_dilogI_comp (s := Icc 0 b) (f := fun Y => -(Y / (1 - Y)))
    (by fun_prop (disch := exact fun Y hY => (hpos Y hY).ne'))
    (fun Y hY => by
      have := div_nonneg hY.1 (hpos Y hY).le
      linarith)
  have h2 := continuousOn_dilogI_comp (s := Icc 0 b) (f := fun Y => Y) continuousOn_id
    (fun Y hY => by linarith [hY.2])
  have h3 : ContinuousOn (fun Y : ℝ => log (1 - Y) ^ 2 / 2) (Icc 0 b) :=
    ((hc.log fun Y hY => (hpos Y hY).ne').pow 2).div_const 2
  exact (h1.add h2).add h3

/-- **Landen's identity** on `(0, 1)`: `Li(-Y/(1 - Y)) = -Li₂ Y - log² (1 - Y)/2`. -/
theorem dilogI_neg_div_one_sub {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    dilogI (-(Y / (1 - Y))) = -Li₂ Y - log (1 - Y) ^ 2 / 2 := by
  have h := eq_of_hasDerivAt_zero hY.1.le (continuousOn_landenDiff hY.2)
    (fun x hx => hasDerivAt_landenDiff ⟨hx.1, hx.2.trans hY.2⟩)
  have h0 : landenDiff 0 = 0 := by simp [landenDiff]
  rw [h0] at h
  have hL := dilogI_eq_Li₂_of_mem ⟨by linarith [hY.1], hY.2⟩
  unfold landenDiff at h
  linarith

/-! ### The two identities with `D` -/

section DIdentities

variable {Y : ℝ}

theorem log_one_sub_one_sub_two_mul (hY : 0 < Y) : log (1 - (1 - 2 * Y)) = log 2 + log Y := by
  rw [show (1 : ℝ) - (1 - 2 * Y) = 2 * Y by ring, log_mul two_ne_zero hY.ne']

theorem log_one_sub_two_mul_sub_one (hY : Y < 1) :
    log (1 - (2 * Y - 1)) = log 2 + log (1 - Y) := by
  rw [show (1 : ℝ) - (2 * Y - 1) = 2 * (1 - Y) by ring, log_mul two_ne_zero (by linarith)]

/-- `∂ Li(1 - 2Y) = 2 (log 2 + log Y)/(1 - 2Y)` and
`∂ Li(2Y - 1) = 2 (log 2 + log (1 - Y))/(1 - 2Y)` on `(0, 1) \ {1/2}`. -/
theorem hasDerivAt_dilogI_D_parts (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2) :
    HasDerivAt (fun Y => dilogI (1 - 2 * Y)) (2 * (log 2 + log Y) / (1 - 2 * Y)) Y ∧
      HasDerivAt (fun Y => dilogI (2 * Y - 1)) (2 * (log 2 + log (1 - Y)) / (1 - 2 * Y)) Y := by
  obtain ⟨hY0, hY1⟩ := hY
  have h2 : 1 - 2 * Y ≠ 0 := fun h => hY2 (by linarith)
  have h2' : 2 * Y - 1 ≠ 0 := fun h => hY2 (by linarith)
  constructor
  · have h := hasDerivAt_dilogI_comp (((hasDerivAt_id' Y).const_mul 2).const_sub 1)
      (by linarith) h2
    convert h using 1
    rw [log_one_sub_one_sub_two_mul hY0]
    field_simp
  · have h := hasDerivAt_dilogI_comp (((hasDerivAt_id' Y).const_mul 2).sub_const 1)
      (by linarith) h2'
    convert h using 1
    rw [log_one_sub_two_mul_sub_one hY1]
    field_simp
    ring

/-- The difference of the two sides of the second identity. -/
noncomputable def dDiff2 (Y : ℝ) : ℝ :=
  dilogI ((2 * Y - 1) / Y) + (dilogI (1 - 2 * Y) - dilogI (2 * Y - 1)) + dilogI Y +
    log Y ^ 2 / 2 - π ^ 2 / 12

/-- The difference of the two sides of the third identity. -/
noncomputable def dDiff3 (Y : ℝ) : ℝ :=
  dilogI ((1 - 2 * Y) / (1 - Y)) - (dilogI (1 - 2 * Y) - dilogI (2 * Y - 1)) - dilogI Y +
    log (1 - Y) ^ 2 / 2 - log Y * log (1 - Y) + π ^ 2 / 12

theorem hasDerivAt_dDiff2 (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2) :
    HasDerivAt dDiff2 0 Y := by
  obtain ⟨hD1, hD2⟩ := hasDerivAt_dilogI_D_parts hY hY2
  obtain ⟨hY0, hY1⟩ := hY
  have h2 : 1 - 2 * Y ≠ 0 := fun h => hY2 (by linarith)
  have h2' : 2 * Y - 1 ≠ 0 := fun h => hY2 (by linarith)
  have h2'' : 1 - Y * 2 ≠ 0 := fun h => hY2 (by linarith)
  have h2''' : Y * 2 - 1 ≠ 0 := fun h => hY2 (by linarith)
  have hY1' : 0 < 1 - Y := by linarith
  have hg : HasDerivAt (fun Y => (2 * Y - 1) / Y) (1 / Y ^ 2) Y := by
    have := (((hasDerivAt_id' Y).const_mul 2).sub_const 1).div (hasDerivAt_id' Y) hY0.ne'
    convert this using 1
    field_simp
    ring
  have e : 1 - (2 * Y - 1) / Y = (1 - Y) / Y := by field_simp; ring
  have hlt : (2 * Y - 1) / Y < 1 := by rw [← sub_pos, e]; positivity
  have h1 := hasDerivAt_dilogI_comp hg hlt (div_ne_zero h2' hY0.ne')
  have h3 := hasDerivAt_dilogI_of_ne hY1 hY0.ne'
  have h4 := ((hasDerivAt_log hY0.ne').pow 2).div_const 2
  have h := ((((h1.add (hD1.sub hD2)).add h3).add h4).sub_const (π ^ 2 / 12))
  convert h using 1
  · funext x
    simp [dDiff2]
  · rw [e, log_div hY1'.ne' hY0.ne']
    field_simp
    ring

theorem hasDerivAt_dDiff3 (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2) :
    HasDerivAt dDiff3 0 Y := by
  obtain ⟨hD1, hD2⟩ := hasDerivAt_dilogI_D_parts hY hY2
  obtain ⟨hY0, hY1⟩ := hY
  have h2 : 1 - 2 * Y ≠ 0 := fun h => hY2 (by linarith)
  have h2'' : 1 - Y * 2 ≠ 0 := fun h => hY2 (by linarith)
  have h2''' : Y * 2 - 1 ≠ 0 := fun h => hY2 (by linarith)
  have hY1' : 0 < 1 - Y := by linarith
  have hY1'' : (1 : ℝ) - Y ≠ 0 := hY1'.ne'
  have hg : HasDerivAt (fun Y => (1 - 2 * Y) / (1 - Y)) (-(1 / (1 - Y) ^ 2)) Y := by
    have := (((hasDerivAt_id' Y).const_mul 2).const_sub 1).div ((hasDerivAt_id' Y).const_sub 1)
      hY1''
    convert this using 1
    field_simp
    ring
  have e : 1 - (1 - 2 * Y) / (1 - Y) = Y / (1 - Y) := by field_simp; ring
  have hlt : (1 - 2 * Y) / (1 - Y) < 1 := by rw [← sub_pos, e]; positivity
  have h1 := hasDerivAt_dilogI_comp hg hlt (div_ne_zero h2 hY1'')
  have h3 := hasDerivAt_dilogI_of_ne hY1 hY0.ne'
  have hl1 := ((hasDerivAt_id' Y).const_sub 1).log hY1''
  have h4 := (hl1.pow 2).div_const 2
  have h5 := (hasDerivAt_log hY0.ne').mul hl1
  have h := (((((h1.sub (hD1.sub hD2)).sub h3).add h4).sub h5).add_const (π ^ 2 / 12))
  convert h using 1
  · funext x
    simp [dDiff3]
  · rw [e, log_div hY0.ne' hY1'']
    field_simp
    ring

theorem continuousOn_dDiff {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ContinuousOn dDiff2 (Icc a b) ∧ ContinuousOn dDiff3 (Icc a b) := by
  have hpos : ∀ Y ∈ Icc a b, 0 < Y := fun Y hY => ha.trans_le hY.1
  have hpos' : ∀ Y ∈ Icc a b, 0 < 1 - Y := fun Y hY => by linarith [hY.2]
  have c1 := continuousOn_dilogI_comp (s := Icc a b) (f := fun Y => 1 - 2 * Y) (by fun_prop)
    (fun Y hY => by linarith [hpos Y hY])
  have c2 := continuousOn_dilogI_comp (s := Icc a b) (f := fun Y => 2 * Y - 1) (by fun_prop)
    (fun Y hY => by linarith [hpos' Y hY])
  have c3 := continuousOn_dilogI_comp (s := Icc a b) (f := fun Y => Y) continuousOn_id
    (fun Y hY => by linarith [hpos' Y hY])
  have cA := continuousOn_dilogI_comp (s := Icc a b) (f := fun Y => (2 * Y - 1) / Y)
    (by fun_prop (disch := exact fun Y hY => (hpos Y hY).ne'))
    (fun Y hY => by
      show (2 * Y - 1) / Y < 1
      rw [div_lt_one (hpos Y hY)]
      linarith [hpos' Y hY])
  have cB := continuousOn_dilogI_comp (s := Icc a b) (f := fun Y => (1 - 2 * Y) / (1 - Y))
    (by fun_prop (disch := exact fun Y hY => (hpos' Y hY).ne'))
    (fun Y hY => by
      show (1 - 2 * Y) / (1 - Y) < 1
      rw [div_lt_one (hpos' Y hY)]
      linarith [hpos Y hY])
  have cl : ContinuousOn (fun Y : ℝ => log Y) (Icc a b) :=
    continuousOn_log.mono fun Y hY => (hpos Y hY).ne'
  have cl' : ContinuousOn (fun Y : ℝ => log (1 - Y)) (Icc a b) :=
    (by fun_prop : ContinuousOn (fun Y : ℝ => 1 - Y) (Icc a b)).log fun Y hY => (hpos' Y hY).ne'
  constructor
  · exact ((((cA.add (c1.sub c2)).add c3).add ((cl.pow 2).div_const 2)).sub continuousOn_const)
  · exact (((((cB.sub (c1.sub c2)).sub c3).add ((cl'.pow 2).div_const 2)).sub (cl.mul cl')).add
      continuousOn_const)

theorem dDiff_half : dDiff2 (1 / 2) = 0 ∧ dDiff3 (1 / 2) = 0 := by
  have hL := Li₂_one_half
  have hd : dilogI (1 / 2) = Li₂ (1 / 2) := dilogI_eq_Li₂_of_mem ⟨by norm_num, by norm_num⟩
  have hl : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, log_inv]
  constructor
  · simp only [dDiff2]
    norm_num
    rw [hd, hL, hl]
    ring
  · simp only [dDiff3]
    norm_num
    rw [hd, hL, hl]
    ring

/-- A function on `(0, 1)` with derivative `0` off `1/2`, continuous on compact subintervals and
vanishing at `1/2`, vanishes. -/
theorem eq_zero_of_hasDerivAt_zero_off_half {f : ℝ → ℝ}
    (hd : ∀ Y ∈ Ioo (0 : ℝ) 1, Y ≠ 1 / 2 → HasDerivAt f 0 Y)
    (hc : ∀ a b : ℝ, 0 < a → b < 1 → ContinuousOn f (Icc a b)) (h0 : f (1 / 2) = 0)
    (hY : Y ∈ Ioo (0 : ℝ) 1) : f Y = 0 := by
  rcases le_total Y (1 / 2) with h | h
  · refine (eq_of_hasDerivAt_zero h (hc _ _ hY.1 (by norm_num)) fun x hx => ?_).trans h0
    exact hd x ⟨hY.1.trans hx.1, by linarith [hx.2]⟩ hx.2.ne
  · refine (eq_of_hasDerivAt_zero h (hc _ _ (by norm_num) hY.2) fun x hx => ?_).symm.trans h0
    exact hd x ⟨by linarith [hx.1], hx.2.trans hY.2⟩ hx.1.ne'

/-- `dDiff2 = dDiff3 = 0` on `(0, 1)`. -/
theorem dDiff_eq_zero (hY : Y ∈ Ioo (0 : ℝ) 1) : dDiff2 Y = 0 ∧ dDiff3 Y = 0 :=
  ⟨eq_zero_of_hasDerivAt_zero_off_half (fun _ h h' => hasDerivAt_dDiff2 h h')
    (fun _ _ ha hb => (continuousOn_dDiff ha hb).1) dDiff_half.1 hY,
    eq_zero_of_hasDerivAt_zero_off_half (fun _ h h' => hasDerivAt_dDiff3 h h')
    (fun _ _ ha hb => (continuousOn_dDiff ha hb).2) dDiff_half.2 hY⟩

/-- **`D(Y) = Li₂ (1 - 2Y) - Li₂ (2Y - 1)`** on `(0, 1)`, recovered from the derivative and the
value at `1/2` of `QED.TwoLoop.Units.crossedD`, whose body is not exposed. -/
theorem crossedD_eq (hY : Y ∈ Ioo (0 : ℝ) 1) :
    QED.TwoLoop.Units.crossedD Y = Li₂ (1 - 2 * Y) - Li₂ (2 * Y - 1) := by
  have key : QED.TwoLoop.Units.crossedD Y - (dilogI (1 - 2 * Y) - dilogI (2 * Y - 1)) = 0 := by
    refine eq_zero_of_hasDerivAt_zero_off_half (f := fun Y =>
      QED.TwoLoop.Units.crossedD Y - (dilogI (1 - 2 * Y) - dilogI (2 * Y - 1))) ?_ ?_ ?_ hY
    · intro Y hY hY2
      obtain ⟨hD1, hD2⟩ := hasDerivAt_dilogI_D_parts hY hY2
      have h := (QED.TwoLoop.Units.hasDerivAt_crossedD hY hY2).sub (hD1.sub hD2)
      have h2 : 1 - 2 * Y ≠ 0 := fun h => hY2 (by linarith)
      convert h using 1
      field_simp
      ring
    · intro a b ha hb
      have c1 := continuousOn_dilogI_comp (s := Icc a b) (f := fun Y => 1 - 2 * Y) (by fun_prop)
        (fun Y hY => by linarith [ha.trans_le hY.1])
      have c2 := continuousOn_dilogI_comp (s := Icc a b) (f := fun Y => 2 * Y - 1) (by fun_prop)
        (fun Y hY => by linarith [hY.2])
      exact (QED.TwoLoop.Units.continuousOn_crossedD.mono fun Y hY =>
        ⟨ha.le.trans hY.1, hY.2.trans hb.le⟩).sub (c1.sub c2)
    · show QED.TwoLoop.Units.crossedD (1 / 2) - _ = 0
      rw [QED.TwoLoop.Units.crossedD_half]
      norm_num
  obtain ⟨hY0, hY1⟩ := hY
  rw [← dilogI_eq_Li₂_of_mem ⟨by linarith, by linarith⟩,
    ← dilogI_eq_Li₂_of_mem ⟨by linarith, by linarith⟩]
  linarith

end DIdentities

/-- **Second identity of (4.6)**: `Li((2Y - 1)/Y) = -D(Y) - Li₂ Y - log² Y/2 + ζ(2)/2`. -/
theorem dilogI_two_mul_sub_one_div {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    dilogI ((2 * Y - 1) / Y) =
      -QED.TwoLoop.Units.crossedD Y - Li₂ Y - log Y ^ 2 / 2 + π ^ 2 / 12 := by
  have h := (dDiff_eq_zero hY).1
  obtain ⟨hY0, hY1⟩ := hY
  rw [crossedD_eq ⟨hY0, hY1⟩, ← dilogI_eq_Li₂_of_mem ⟨by linarith, by linarith⟩,
    ← dilogI_eq_Li₂_of_mem ⟨by linarith, by linarith⟩, ← dilogI_eq_Li₂_of_mem ⟨by linarith, hY1⟩]
  unfold dDiff2 at h
  linarith

/-- **Third identity of (4.6)**:
`Li((1 - 2Y)/(1 - Y)) = D(Y) + Li₂ Y - log² (1 - Y)/2 + log Y log (1 - Y) - ζ(2)/2`. -/
theorem dilogI_one_sub_two_mul_div {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) :
    dilogI ((1 - 2 * Y) / (1 - Y)) =
      QED.TwoLoop.Units.crossedD Y + Li₂ Y - log (1 - Y) ^ 2 / 2 + log Y * log (1 - Y) -
        π ^ 2 / 12 := by
  have h := (dDiff_eq_zero hY).2
  obtain ⟨hY0, hY1⟩ := hY
  rw [crossedD_eq ⟨hY0, hY1⟩, ← dilogI_eq_Li₂_of_mem ⟨by linarith, by linarith⟩,
    ← dilogI_eq_Li₂_of_mem ⟨by linarith, by linarith⟩, ← dilogI_eq_Li₂_of_mem ⟨by linarith, hY1⟩]
  unfold dDiff3 at h
  linarith

end QED.TwoLoop.UnitXXi

end
