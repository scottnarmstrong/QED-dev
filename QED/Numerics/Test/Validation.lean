/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Numerics.BoxQuadrature
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Validation of the interval arithmetic and the box-partition checker (milestone NUM.VALIDATION)

Tests for `QED.Numerics.Interval` and `QED.Numerics.Quadrature.check`. Every check below is
decided by the kernel (`decide +kernel`).

* Accepted certificates, each turned into an enclosure theorem by
  `QED.Numerics.Quadrature.integral_bounds_of_check_of_continuousOn`:
  * `f(x, y) = x y` on the uniform `64 × 64` grid, enclosure `[0.24, 0.26]`; the exact value
    `1/4` is proved separately (`integral_fxy`).
  * `f(x, y) = 2(1 - y)` on one strip cut into `10⁴` boxes, enclosure `[0.999, 1.001]`; the
    exact value is `1`. This exercises a long inner loop of the checker.
  * `f(x, y) = 1/(1 + x + y²)` on the uniform `100 × 100` grid (`10⁴` boxes), enclosure
    `[0.57, 0.58]`; the value is `0.57550828...`.
* Rejected certificates (`check ... = false`): a missing box, a missing strip, overlapping
  boxes, overlapping strips, a box outside the square, a lower bound that is too high, an upper
  bound that is too low, a box without an enclosure (reciprocal of an interval meeting `0`), and
  a tampered box enclosure. Accepted controls that differ only in the defect accompany the
  partition tests; for the bound and tampering tests the control is `check_fxy`.
-/

@[expose] public section

open MeasureTheory Set QED.Integration QED.Numerics QED.Numerics.Quadrature

namespace QED.Numerics.Validation

/-- The scale of the tests: endpoints and corners are multiples of `2⁻²⁰`. -/
abbrev S : ℕ := 2 ^ 20

/-! ### Interval arithmetic -/

/-- `1/3 ∈ [0.333, 0.334]` through `ofRat`. -/
example : (Interval.ofRat (1 / 3) : Interval S).geRat (333 / 1000) = true := by decide +kernel
example : (Interval.ofRat (1 / 3) : Interval S).leRat (334 / 1000) = true := by decide +kernel

/-- `(1/3)⁻¹ ∈ [2.999, 3.001]`. -/
example : (Interval.ofRat (1 / 3) : Interval S)⁻¹.geRat (2999 / 1000) = true := by decide +kernel
example : (Interval.ofRat (1 / 3) : Interval S)⁻¹.leRat (3001 / 1000) = true := by decide +kernel

/-- A product of intervals of mixed signs: `[-1, 2] · [-3, 1] ⊆ [-6, 3]`. -/
example : ((⟨-(S : ℤ), 2 * S, true⟩ : Interval S) * ⟨-3 * S, S, true⟩).geRat (-6) = true := by
  decide +kernel
example : ((⟨-(S : ℤ), 2 * S, true⟩ : Interval S) * ⟨-3 * S, S, true⟩).leRat 3 = true := by
  decide +kernel

/-- The square of `[-2, 1]` is `[0, 4]`, not `[-2, 4]`. -/
example : (Interval.sq (⟨-2 * S, S, true⟩ : Interval S)).geRat 0 = true := by decide +kernel

/-- The reciprocal of an interval meeting `0` carries no information. -/
example : (⟨-(S : ℤ), S, true⟩ : Interval S)⁻¹.ok = false := by decide +kernel

/-- A comparison that fails: `1/3` is not known to be at least `0.334`. -/
example : (Interval.ofRat (1 / 3) : Interval S).geRat (334 / 1000) = false := by decide +kernel

/-! ### `x y`, with exact integral `1/4` -/

/-- The integrand `f(x, y) = x y`. -/
def fxy (z : ℝ × ℝ) : ℝ := z.1 * z.2

/-- The interval extension of `fxy`. -/
def Fxy (B : Box S) : Interval S := B.X * B.Y

theorem Fxy_sound :
    ∀ B : Box S, ∀ z ∈ B.toSet, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 → fxy z ∈ Fxy B :=
  fun _ _ hz _ => Interval.mem_mul (Box.fst_mem_X hz) (Box.snd_mem_Y hz)

theorem continuousOn_fxy : ContinuousOn fxy (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  unfold fxy; fun_prop

theorem integral_fxy : ∫ z, fxy z ∂feynmanMeasure = 1 / 4 := by
  rw [feynmanMeasure]
  have h := integral_prod_mul (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (ν := volume.restrict (Ioc (0 : ℝ) 1)) (fun x : ℝ => x) (fun y : ℝ => y)
  simp only [fxy]
  rw [h, ← intervalIntegral.integral_of_le zero_le_one, integral_id]
  norm_num

theorem check_fxy : check Fxy (uniform S 64 64) (24 / 100) (26 / 100) = true := by
  decide +kernel

theorem fxy_bounds :
    (24 / 100 : ℝ) ≤ ∫ z, fxy z ∂feynmanMeasure ∧ ∫ z, fxy z ∂feynmanMeasure ≤ 26 / 100 := by
  have h := integral_bounds_of_check_of_continuousOn continuousOn_fxy Fxy_sound check_fxy
  norm_num at h ⊢
  exact h

/-! ### Rejected certificates -/

/-- Control: the strip `(0, 1]` cut at `1/2` and `1`. -/
example : check Fxy [⟨S, [S / 2, S]⟩] 0 1 = true := by decide +kernel

/-- A missing box: the cuts of the only strip stop at `1/2`. -/
example : check Fxy [⟨S, [S / 2]⟩] 0 1 = false := by decide +kernel

/-- Control: two strips `(0, 1/2]` and `(1/2, 1]`. -/
example : check Fxy [⟨S / 2, [S]⟩, ⟨S, [S]⟩] 0 1 = true := by decide +kernel

/-- A missing strip: the strips stop at `x = 1/2`. -/
example : check Fxy [⟨S / 2, [S]⟩] 0 1 = false := by decide +kernel

/-- Overlapping boxes: the cuts `1/2, 1/4, 1` make `(1/4, 1]` overlap `(0, 1/2]`. -/
example : check Fxy [⟨S, [S / 2, S / 4, S]⟩] 0 1 = false := by decide +kernel

/-- Overlapping strips: the strip ends `1/2, 1/4, 1`. -/
example : check Fxy [⟨S / 2, [S]⟩, ⟨S / 4, [S]⟩, ⟨S, [S]⟩] 0 1 = false := by decide +kernel

/-- A box outside the square: the cuts `1/2, 2, 1`. -/
example : check Fxy [⟨S, [S / 2, 2 * S, S]⟩] 0 4 = false := by decide +kernel

/-- A claimed lower bound that is too high (the box sums give `[0.2422, 0.2579]`). -/
example : check Fxy (uniform S 64 64) (25 / 100) (26 / 100) = false := by decide +kernel

/-- A claimed upper bound that is too low. -/
example : check Fxy (uniform S 64 64) (24 / 100) (25 / 100) = false := by decide +kernel

/-- An interval extension of `1/(y - 1/2)`: it gives no information on the boxes that touch
`y = 1/2`, so no certificate is accepted, however wide the claimed bounds. -/
def Fpole (B : Box S) : Interval S := (B.Y - Interval.ofRat (1 / 2))⁻¹

example : check Fpole (uniform S 4 4) (-1000) 1000 = false := by decide +kernel

/-- `Fxy` with the enclosure of the corner box `(0, 1/64]²` shifted up by `100`. The checker
recomputes every box enclosure from the extension, so the shift moves the sums and the claim
`[0.24, 0.26]` accepted for `Fxy` is rejected. (The checker cannot detect an unsound extension
whose sums stay inside the claim; soundness of the extension is the hypothesis `hF` of
`integral_bounds_of_check`, proved once by the interval lemmas, not a check.) -/
def FxyTampered (B : Box S) : Interval S :=
  bif Nat.beq B.x₀ 0 && Nat.beq B.y₀ 0 then Fxy B + 100 else Fxy B

example : check FxyTampered (uniform S 64 64) (24 / 100) (26 / 100) = false := by decide +kernel

/-! ### `2(1 - y)` on one strip of `10⁴` boxes, exact integral `1` -/

/-- The integrand `f(x, y) = 2(1 - y)`. -/
def flin (z : ℝ × ℝ) : ℝ := 2 * (1 - z.2)

/-- The interval extension of `flin`. -/
def Flin (B : Box S) : Interval S := 2 * (1 - B.Y)

theorem Flin_sound :
    ∀ B : Box S, ∀ z ∈ B.toSet, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 → flin z ∈ Flin B := by
  intro B z hz _
  have hy := Box.snd_mem_Y hz
  simp only [flin, Flin]
  interval_mem

theorem check_flin : check Flin (uniform S 1 10000) (999 / 1000) (1001 / 1000) = true := by
  decide +kernel

theorem flin_bounds :
    (999 / 1000 : ℝ) ≤ ∫ z, flin z ∂feynmanMeasure ∧
      ∫ z, flin z ∂feynmanMeasure ≤ 1001 / 1000 := by
  have h := integral_bounds_of_check_of_continuousOn (by unfold flin; fun_prop) Flin_sound
    check_flin
  norm_num at h ⊢
  exact h

/-! ### `1/(1 + x + y²)` on `10⁴` boxes -/

/-- The integrand `f(x, y) = 1/(1 + x + y²)`. -/
noncomputable def frat (z : ℝ × ℝ) : ℝ := (1 + z.1 + z.2 ^ 2)⁻¹

/-- The interval extension of `frat`. -/
def Frat (B : Box S) : Interval S := (1 + B.X + Interval.sq B.Y)⁻¹

theorem Frat_sound :
    ∀ B : Box S, ∀ z ∈ B.toSet, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 → frat z ∈ Frat B := by
  intro B z hz _
  have hx := Box.fst_mem_X hz
  have hy := Box.snd_mem_Y hz
  simp only [frat, Frat]
  interval_mem

theorem continuousOn_frat : ContinuousOn frat (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  refine ContinuousOn.inv₀ (by fun_prop) fun z hz => ?_
  have := hz.1.1
  nlinarith [sq_nonneg z.2]

theorem check_frat : check Frat (uniform S 100 100) (57 / 100) (58 / 100) = true := by
  decide +kernel

theorem frat_bounds :
    (57 / 100 : ℝ) ≤ ∫ z, frat z ∂feynmanMeasure ∧ ∫ z, frat z ∂feynmanMeasure ≤ 58 / 100 := by
  have h := integral_bounds_of_check_of_continuousOn continuousOn_frat Frat_sound check_frat
  norm_num at h ⊢
  exact h

end QED.Numerics.Validation

end
