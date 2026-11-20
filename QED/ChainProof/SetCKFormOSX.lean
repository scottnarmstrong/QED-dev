/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOSY
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the antiderivative of the outer self-energy node integrand

Helper level (no frozen statement). At an outer node `X ∈ (0, 1)` the kernel part of `H_oS` is
`∫₀^X F(x, Q(X) - Q(x)) dx` with `F = formOSF` (`SetCKFormOSY`). Since
`Q(X) - Q(x) = (X - x)(X + x(1 - X))/((1 - X)(1 - x))` and `ρ(x) + Q(X) - Q(x) = x + Q(X)`,
the integrand is `formOSFx X x`: polynomials in `x` times the logarithms of the five linear
forms `X - x`, `X + x(1 - X)`, `x + Q(X)`, `x`, `1 - x` (`formOSF_eq`). Each `P(x) log L(x)`
has the antiderivative `S(x) L(x) log L(x)` up to a polynomial, with `S` a polynomial of
degree five (`formOSSA`, …, `formOSS1`; the remainder is `formOST`), so the antiderivative
`formOSG X` is continuous on `ℝ` and has derivative `formOSFx X` on `(0, X)`
(`hasDerivAt_formOSG`, five polynomial identities `formOS_idA`, …, `formOS_idT`).
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- A polynomial of degree at most six. -/
noncomputable def formOSP6 (c₀ c₁ c₂ c₃ c₄ c₅ c₆ x : ℝ) : ℝ :=
  c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4 + c₅ * x ^ 5 + c₆ * x ^ 6

theorem hasDerivAt_formOSP6 (c₀ c₁ c₂ c₃ c₄ c₅ c₆ x : ℝ) :
    HasDerivAt (formOSP6 c₀ c₁ c₂ c₃ c₄ c₅ c₆)
      (formOSP6 c₁ (2 * c₂) (3 * c₃) (4 * c₄) (5 * c₅) (6 * c₆) 0 x) x := by
  have h := ((((((hasDerivAt_const x c₀).add ((hasDerivAt_id' x).const_mul c₁)).add
    ((hasDerivAt_pow 2 x).const_mul c₂)).add ((hasDerivAt_pow 3 x).const_mul c₃)).add
    ((hasDerivAt_pow 4 x).const_mul c₄)).add ((hasDerivAt_pow 5 x).const_mul c₅)).add
    ((hasDerivAt_pow 6 x).const_mul c₆)
  unfold formOSP6
  refine h.congr_deriv ?_
  push_cast
  ring

theorem continuous_formOSP6 (c₀ c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) :
    Continuous (formOSP6 c₀ c₁ c₂ c₃ c₄ c₅ c₆) := by
  unfold formOSP6
  fun_prop

/-- **A piece of the antiderivative**: `(S · L log L)' = (a S + L S') log L + a S`. -/
theorem hasDerivAt_formOS_piece {S L : ℝ → ℝ} {S' a x : ℝ} (hS : HasDerivAt S S' x)
    (hL : HasDerivAt L a x) (hL0 : L x ≠ 0) :
    HasDerivAt (fun y => S y * (L y * log (L y)))
      ((a * S x + L x * S') * log (L x) + a * S x) x := by
  refine (hS.mul (hL.mul (hL.log hL0))).congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- The polynomial `S_A` of the antiderivative. -/
noncomputable def formOSSA (X x : ℝ) : ℝ := formOSP6
    (X ^ 3 * (-3 - 2 * X + 2 * X ^ 2) / (12 * (-1 + X) ^ 2))
    (X ^ 2 * (-3 + 2 * X ^ 2 + 16 * X) / (12 * (-1 + X) ^ 2))
    (-X * (-21 + 8 * X + 34 * X ^ 2) / (12 * (-1 + X) ^ 2))
    ((7 - 22 * X + 8 * X ^ 2 + 10 * X ^ 3) / (4 * (-1 + X) ^ 2))
    (-(-8 + 3 * X ^ 2 + 11 * X) / (4 * (-1 + X)))
    (3 / 4)
    (0) x

/-- Its derivative. -/
noncomputable def formOSSA' (X x : ℝ) : ℝ := formOSP6
    (X ^ 2 * (-3 + 2 * X ^ 2 + 16 * X) / (12 * (-1 + X) ^ 2))
    (2 * (-X * (-21 + 8 * X + 34 * X ^ 2) / (12 * (-1 + X) ^ 2)))
    (3 * ((7 - 22 * X + 8 * X ^ 2 + 10 * X ^ 3) / (4 * (-1 + X) ^ 2)))
    (4 * (-(-8 + 3 * X ^ 2 + 11 * X) / (4 * (-1 + X))))
    (5 * (3 / 4))
    (6 * (0))
    0 x

theorem hasDerivAt_formOSSA (X x : ℝ) : HasDerivAt (formOSSA X) (formOSSA' X x) x :=
  hasDerivAt_formOSP6 _ _ _ _ _ _ _ x

/-- The polynomial `S_B` of the antiderivative. -/
noncomputable def formOSSB (X x : ℝ) : ℝ := formOSP6
    (-X ^ 3 * (3 - 8 * X + 3 * X ^ 2) / (12 * (-1 + X) ^ 4))
    (X ^ 2 * (-3 - 10 * X + 15 * X ^ 2) / (12 * (-1 + X) ^ 3))
    (-X * (-21 + 21 * X ^ 2 + 34 * X) / (12 * (-1 + X) ^ 2))
    ((-7 - X + 3 * X ^ 3 + 15 * X ^ 2) / (4 * (-1 + X) ^ 2))
    (-(-8 + 5 * X + 6 * X ^ 2) / (4 * (-1 + X) ^ 2))
    (3 / (4 * (-1 + X)))
    (0) x

/-- Its derivative. -/
noncomputable def formOSSB' (X x : ℝ) : ℝ := formOSP6
    (X ^ 2 * (-3 - 10 * X + 15 * X ^ 2) / (12 * (-1 + X) ^ 3))
    (2 * (-X * (-21 + 21 * X ^ 2 + 34 * X) / (12 * (-1 + X) ^ 2)))
    (3 * ((-7 - X + 3 * X ^ 3 + 15 * X ^ 2) / (4 * (-1 + X) ^ 2)))
    (4 * (-(-8 + 5 * X + 6 * X ^ 2) / (4 * (-1 + X) ^ 2)))
    (5 * (3 / (4 * (-1 + X))))
    (6 * (0))
    0 x

theorem hasDerivAt_formOSSB (X x : ℝ) : HasDerivAt (formOSSB X) (formOSSB' X x) x :=
  hasDerivAt_formOSP6 _ _ _ _ _ _ _ x

/-- The polynomial `S_D` of the antiderivative. -/
noncomputable def formOSSD (X x : ℝ) : ℝ := formOSP6
    (X ^ 4 * (2 + X ^ 2 - 2 * X) / (6 * (-1 + X) ^ 3))
    (X ^ 2 * (-7 + X ^ 2 + 7 * X) / (6 * (-1 + X) ^ 2))
    (-(-5 + 5 * X + 17 * X ^ 2) / (6 * (-1 + X)))
    ((-4 + 4 * X + 5 * X ^ 2) / (2 * (-1 + X)))
    (-(-8 + 3 * X ^ 2 + 8 * X) / (4 * (-1 + X)))
    (3 / 4)
    (0) x

/-- Its derivative. -/
noncomputable def formOSSD' (X x : ℝ) : ℝ := formOSP6
    (X ^ 2 * (-7 + X ^ 2 + 7 * X) / (6 * (-1 + X) ^ 2))
    (2 * (-(-5 + 5 * X + 17 * X ^ 2) / (6 * (-1 + X))))
    (3 * ((-4 + 4 * X + 5 * X ^ 2) / (2 * (-1 + X))))
    (4 * (-(-8 + 3 * X ^ 2 + 8 * X) / (4 * (-1 + X))))
    (5 * (3 / 4))
    (6 * (0))
    0 x

theorem hasDerivAt_formOSSD (X x : ℝ) : HasDerivAt (formOSSD X) (formOSSD' X x) x :=
  hasDerivAt_formOSP6 _ _ _ _ _ _ _ x

/-- The polynomial `S_x` of the antiderivative. -/
noncomputable def formOSSx (_X x : ℝ) : ℝ := formOSP6
    (0)
    (0)
    (5 / 6)
    (-1 / 4)
    (0)
    (0)
    (0) x

/-- Its derivative. -/
noncomputable def formOSSx' (_X x : ℝ) : ℝ := formOSP6
    (0)
    (2 * (5 / 6))
    (3 * (-1 / 4))
    (4 * (0))
    (5 * (0))
    (6 * (0))
    0 x

theorem hasDerivAt_formOSSx (X x : ℝ) : HasDerivAt (formOSSx X) (formOSSx' X x) x :=
  hasDerivAt_formOSP6 _ _ _ _ _ _ _ x

/-- The polynomial `S_1` of the antiderivative. -/
noncomputable def formOSS1 (X x : ℝ) : ℝ := formOSP6
    ((1 - 2 * X - 2 * X ^ 3 + 3 * X ^ 2 + 3 * X ^ 4) / (12 * (-1 + X) ^ 2))
    (-(1 - X + 5 * X ^ 2) * (-1 + X + 3 * X ^ 2) / (12 * (-1 + X) ^ 2))
    ((-1 + X + X ^ 2) * (-1 + X + 21 * X ^ 2) / (12 * (-1 + X) ^ 2))
    (-3 * (1 + X ^ 4 - 3 * X ^ 2 - 2 * X + 4 * X ^ 3) / (4 * (-1 + X) ^ 2))
    ((-5 + 5 * X + 6 * X ^ 2) / (4 * (-1 + X)))
    (-3 / 4)
    (0) x

/-- Its derivative. -/
noncomputable def formOSS1' (X x : ℝ) : ℝ := formOSP6
    (-(1 - X + 5 * X ^ 2) * (-1 + X + 3 * X ^ 2) / (12 * (-1 + X) ^ 2))
    (2 * ((-1 + X + X ^ 2) * (-1 + X + 21 * X ^ 2) / (12 * (-1 + X) ^ 2)))
    (3 * (-3 * (1 + X ^ 4 - 3 * X ^ 2 - 2 * X + 4 * X ^ 3) / (4 * (-1 + X) ^ 2)))
    (4 * ((-5 + 5 * X + 6 * X ^ 2) / (4 * (-1 + X))))
    (5 * (-3 / 4))
    (6 * (0))
    0 x

theorem hasDerivAt_formOSS1 (X x : ℝ) : HasDerivAt (formOSS1 X) (formOSS1' X x) x :=
  hasDerivAt_formOSP6 _ _ _ _ _ _ _ x

/-- The polynomial `S_T` of the antiderivative. -/
noncomputable def formOST (X x : ℝ) : ℝ := formOSP6
    (0)
    (-(1 - X + 2 * X ^ 2) / (12 * (-1 + X)) + (-3 * X ^ 4 / (2 * (-1 + X) ^ 2)) * log (1 - X))
    (-(1 - X + 28 * X ^ 2) / (24 * (-1 + X)) + (X ^ 2 * (-2 + 2 * X + 3 * X ^ 2) / (-1 + X) ^ 2)
        * log (1 - X))
    ((41 - 41 * X + 63 * X ^ 2) / (36 * (-1 + X)) + (-X ^ 2 * (-29 + 15 * X ^ 2 + 29 * X) / (6 * (-1
        + X) ^ 2)) * log (1 - X))
    (-(-2 + 2 * X + 3 * X ^ 2) / (4 * (-1 + X)) + ((7 - 14 * X - 11 * X ^ 2 + 3 * X ^ 4 + 18
        * X ^ 3) / (4 * (-1 + X) ^ 2)) * log (1 - X))
    (3 / 4 + (-(-2 + 3 * X) * (2 + X) / (2 * (-1 + X))) * log (1 - X))
    ((3 / 4) * log (1 - X)) x

/-- Its derivative. -/
noncomputable def formOST' (X x : ℝ) : ℝ := formOSP6
    (-(1 - X + 2 * X ^ 2) / (12 * (-1 + X)) + (-3 * X ^ 4 / (2 * (-1 + X) ^ 2)) * log (1 - X))
    (2 * (-(1 - X + 28 * X ^ 2) / (24 * (-1 + X)) + (X ^ 2 * (-2 + 2 * X + 3 * X ^ 2) / (-1
        + X) ^ 2) * log (1 - X)))
    (3 * ((41 - 41 * X + 63 * X ^ 2) / (36 * (-1 + X)) + (-X ^ 2 * (-29 + 15 * X ^ 2 + 29 * X) / (6
        * (-1 + X) ^ 2)) * log (1 - X)))
    (4 * (-(-2 + 2 * X + 3 * X ^ 2) / (4 * (-1 + X)) + ((7 - 14 * X - 11 * X ^ 2 + 3 * X ^ 4 + 18
        * X ^ 3) / (4 * (-1 + X) ^ 2)) * log (1 - X)))
    (5 * (3 / 4 + (-(-2 + 3 * X) * (2 + X) / (2 * (-1 + X))) * log (1 - X)))
    (6 * ((3 / 4) * log (1 - X)))
    0 x

theorem hasDerivAt_formOST (X x : ℝ) : HasDerivAt (formOST X) (formOST' X x) x :=
  hasDerivAt_formOSP6 _ _ _ _ _ _ _ x

/-- The antiderivative of the node integrand in `x`, at an outer node `X`. -/
noncomputable def formOSG (X x : ℝ) : ℝ :=
  formOSSA X x * ((X - x) * log (X - x)) +
    formOSSB X x * ((X + x * (1 - X)) * log (X + x * (1 - X))) +
    formOSSD X x * ((x + setCKQ X) * log (x + setCKQ X)) + formOSSx X x * (x * log x) +
    formOSS1 X x * ((1 - x) * log (1 - x)) + formOST X x

/-- The node integrand in the variable `x`, with the five logarithms separated. -/
noncomputable def formOSFx (X x : ℝ) : ℝ :=
  formOSCv x (setCKQ X - setCKQ x) *
      (log (X - x) + log (X + x * (1 - X)) - log (1 - X) - log (1 - x) - log (x + setCKQ X)) +
    formOSCr x * (log x - log (1 - x) - log (x + setCKQ X)) + formOSC0 x (setCKQ X - setCKQ x)

section

variable {X x : ℝ}

theorem formOS_idA (hX : X ≠ 1) (hx : x ≠ 1) :
    -1 * formOSSA X x + (X - x) * formOSSA' X x = formOSCv x (setCKQ X - setCKQ x) := by
  have : X - 1 ≠ 0 := sub_ne_zero.2 hX
  have : -1 + X ≠ 0 := by intro h; apply hX; linarith
  have : 1 - X ≠ 0 := by intro h; apply hX; linarith
  have : 1 - x ≠ 0 := by intro h; apply hx; linarith
  unfold formOSSA formOSSA' formOSP6 formOSCv setCKQ
  field_simp
  ring

theorem formOS_idB (hX : X ≠ 1) (hx : x ≠ 1) :
    (1 - X) * formOSSB X x + (X + x * (1 - X)) * formOSSB' X x =
      formOSCv x (setCKQ X - setCKQ x) := by
  have : -1 + X ≠ 0 := by intro h; apply hX; linarith
  have : 1 - X ≠ 0 := by intro h; apply hX; linarith
  have : 1 - x ≠ 0 := by intro h; apply hx; linarith
  unfold formOSSB formOSSB' formOSP6 formOSCv setCKQ
  field_simp
  ring

theorem formOS_idD (hX : X ≠ 1) (hx : x ≠ 1) :
    1 * formOSSD X x + (x + setCKQ X) * formOSSD' X x =
      -formOSCv x (setCKQ X - setCKQ x) - formOSCr x := by
  have : -1 + X ≠ 0 := by intro h; apply hX; linarith
  have : 1 - X ≠ 0 := by intro h; apply hX; linarith
  have : 1 - x ≠ 0 := by intro h; apply hx; linarith
  unfold formOSSD formOSSD' formOSP6 formOSCv formOSCr setCKQ
  field_simp
  ring

theorem formOS_idx : 1 * formOSSx X x + x * formOSSx' X x = formOSCr x := by
  unfold formOSSx formOSSx' formOSP6 formOSCr
  ring

theorem formOS_id1 (hX : X ≠ 1) (hx : x ≠ 1) :
    -1 * formOSS1 X x + (1 - x) * formOSS1' X x =
      -formOSCv x (setCKQ X - setCKQ x) - formOSCr x := by
  have : -1 + X ≠ 0 := by intro h; apply hX; linarith
  have : 1 - X ≠ 0 := by intro h; apply hX; linarith
  have : 1 - x ≠ 0 := by intro h; apply hx; linarith
  unfold formOSS1 formOSS1' formOSP6 formOSCv formOSCr setCKQ
  field_simp
  ring

theorem formOS_idT (hX : X ≠ 1) (hx : x ≠ 1) :
    -1 * formOSSA X x + (1 - X) * formOSSB X x + 1 * formOSSD X x + 1 * formOSSx X x +
        -1 * formOSS1 X x + formOST' X x =
      formOSC0 x (setCKQ X - setCKQ x) - formOSCv x (setCKQ X - setCKQ x) * log (1 - X) := by
  have : -1 + X ≠ 0 := by intro h; apply hX; linarith
  have : 1 - X ≠ 0 := by intro h; apply hX; linarith
  have : 1 - x ≠ 0 := by intro h; apply hx; linarith
  unfold formOSSA formOSSB formOSSD formOSSx formOSS1 formOST' formOSP6 formOSCv formOSC0 setCKQ
  generalize log (1 - X) = L
  field_simp
  ring

/-- **The antiderivative**: `formOSG X` has derivative `formOSFx X` on `(0, X)`. -/
theorem hasDerivAt_formOSG (hX : X ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo 0 X) :
    HasDerivAt (formOSG X) (formOSFx X x) x := by
  have hX1 : X ≠ 1 := hX.2.ne
  have hx1 : x ≠ 1 := (hx.2.trans hX.2).ne
  have hQ := setCKQ_nonneg ⟨hX.1.le, hX.2.le⟩
  have pA := hasDerivAt_formOS_piece (hasDerivAt_formOSSA X x) (L := fun y => X - y) (a := -1)
    (by simpa using (hasDerivAt_id' x).const_sub X) (sub_pos.2 hx.2).ne'
  have pB := hasDerivAt_formOS_piece (hasDerivAt_formOSSB X x)
    (L := fun y => X + y * (1 - X)) (a := 1 - X)
    (by simpa using ((hasDerivAt_id' x).mul_const (1 - X)).const_add X)
    (add_pos hX.1 (mul_pos hx.1 (sub_pos.2 hX.2))).ne'
  have pD := hasDerivAt_formOS_piece (hasDerivAt_formOSSD X x)
    (L := fun y => y + setCKQ X) (a := 1) ((hasDerivAt_id' x).add_const _)
    (add_pos_of_pos_of_nonneg hx.1 hQ).ne'
  have px := hasDerivAt_formOS_piece (hasDerivAt_formOSSx X x) (L := fun y => y) (a := 1)
    (hasDerivAt_id' x) hx.1.ne'
  have p1 := hasDerivAt_formOS_piece (hasDerivAt_formOSS1 X x) (L := fun y => 1 - y) (a := -1)
    (by simpa using (hasDerivAt_id' x).const_sub 1)
    (sub_pos.2 (hx.2.trans hX.2)).ne'
  have h := ((((pA.add pB).add pD).add px).add p1).add (hasDerivAt_formOST X x)
  refine h.congr_deriv ?_
  have iA := formOS_idA hX1 hx1
  have iB := formOS_idB hX1 hx1
  have iD := formOS_idD hX1 hx1
  have ix := formOS_idx (X := X) (x := x)
  have i1 := formOS_id1 hX1 hx1
  have iT := formOS_idT hX1 hx1
  unfold formOSFx
  linear_combination log (X - x) * iA + log (X + x * (1 - X)) * iB +
    log (x + setCKQ X) * iD + log x * ix + log (1 - x) * i1 + iT

theorem continuous_formOSG (X : ℝ) : Continuous (formOSG X) := by
  have hm := continuous_mul_log
  have c : ∀ c₀ c₁ c₂ c₃ c₄ c₅ c₆ : ℝ, Continuous (formOSP6 c₀ c₁ c₂ c₃ c₄ c₅ c₆) :=
    continuous_formOSP6
  unfold formOSG formOSSA formOSSB formOSSD formOSSx formOSS1 formOST
  refine (((((c _ _ _ _ _ _ _).mul (hm.comp (by fun_prop))).add
    ((c _ _ _ _ _ _ _).mul (hm.comp (by fun_prop)))).add
    ((c _ _ _ _ _ _ _).mul (hm.comp (by fun_prop)))).add
    ((c _ _ _ _ _ _ _).mul hm)).add ((c _ _ _ _ _ _ _).mul (hm.comp (by fun_prop))) |>.add
    (c _ _ _ _ _ _ _)

end

end QED.ChainProof.SetCK

end
