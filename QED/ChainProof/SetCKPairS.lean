/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKPairX
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import QED.ChainProof.SetCKDensity

/-!
# Set (c), Stage K: the inner node integral of the pair kernel

Helper level (no frozen statement). For the outer node `X ∈ (0, 1)` the inner node integral
`S(X) = ∫₀^X σ_x(Q(X) - Q(x)) dx` of the discontinuity is elementary: with `v = Q(X) - Q(x)`,

`1 + x/((1-x) v) = (1-x)(X² - Xx + x)/((X - x)(X + x - Xx))`,

and `-α(x, -v)`, `-β(x, -v)`, `-γ(x, -v)` are rational in `x` (`sSigA`, `sSigB`, `sSigG`). The
`β` part is present for `x < Y₁(X) = X²/(1 - X + X²)` only. This file gives antiderivatives in
`x`: `pairW2` of the `α, γ` parts and `pairWB` of the `β` part (`hasDerivAt_pairW2`,
`hasDerivAt_pairWB`); polynomial coefficients in `x` are Horner lists (`hpoly`).
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set Filter Topology MeasureTheory

/-- A polynomial from its coefficient list (constant term first), in Horner form. -/
noncomputable def hpoly : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: l, x => a + x * hpoly l x

/-- The derivative of `hpoly`. -/
noncomputable def hpolyD : List ℝ → ℝ → ℝ
  | [], _ => 0
  | _ :: l, x => hpoly l x + x * hpolyD l x

theorem hasDerivAt_hpoly (l : List ℝ) (x : ℝ) : HasDerivAt (hpoly l) (hpolyD l x) x := by
  induction l with
  | nil =>
    have : hpoly [] = fun _ => (0 : ℝ) := by funext y; rfl
    rw [this]
    exact hasDerivAt_const x 0
  | cons a l ih =>
    have := ((hasDerivAt_id' x).mul ih).const_add a
    convert this using 1
    · funext y; rfl
    · simp only [hpolyD]; ring

@[fun_prop] theorem continuous_hpoly (l : List ℝ) : Continuous (hpoly l) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_hpoly l x).continuousAt

/-- Numerator coefficients in `x` of the `l1` term of `W₂`. -/
noncomputable def sW2c1L (X : ℝ) : List ℝ :=
  [2 - 9*X ^ 2 - 2*X, 3*(-2 + 2*X + 9*X ^ 2), -9*(-2 + 2*X + 3*X ^ 2), -22 + 9*X ^ 2 + 22*X,
    -9*(-1 + X)]

noncomputable def sW2c1 (X x : ℝ) : ℝ :=
  hpoly (sW2c1L X) x / (6*(-1 + X))

/-- Numerator coefficients in `x` of the `lw` term of `W₂`. -/
noncomputable def sW2cwL (X : ℝ) : List ℝ :=
  [-X ^ 2*(36 - 72*X - 27*X ^ 3 + 8*X ^ 4 + 63*X ^ 2), 6*(-1 + X) ^ 2*(-2 + 2*X + 9*X ^ 2),
    -18*(-1 + X) ^ 2*(-2 + 2*X + 3*X ^ 2), 2*(-1 + X) ^ 2*(-22 + 9*X ^ 2 + 22*X), -18*(-1 + X) ^
    3]

noncomputable def sW2cw (X x : ℝ) : ℝ :=
  hpoly (sW2cwL X) x / (12*(-1 + X) ^ 3)

/-- Numerator coefficients in `x` of the `ld` term of `W₂`. -/
noncomputable def sW2cdL (X : ℝ) : List ℝ :=
  [X*(-6 - 13*X ^ 2 + 4*X ^ 3 + 24*X), -3*(-2 + 2*X + 9*X ^ 2), 9*(-2 + 2*X + 3*X ^ 2), 22 - 22*X
    - 9*X ^ 2, 9*(-1 + X)]

noncomputable def sW2cd (X x : ℝ) : ℝ :=
  hpoly (sW2cdL X) x / (6*(-1 + X))

/-- Numerator coefficients in `x` of the `ls` term of `W₂`. -/
noncomputable def sW2csL (X : ℝ) : List ℝ :=
  [X*(6 - 17*X ^ 2 + 6*X + 9*X ^ 3), -3*(-1 + X) ^ 2*(-2 + 2*X + 9*X ^ 2), 9*(-1 + X) ^ 2*(-2 +
    2*X + 3*X ^ 2), -(-1 + X) ^ 2*(-22 + 9*X ^ 2 + 22*X), 9*(-1 + X) ^ 3]

noncomputable def sW2cs (X x : ℝ) : ℝ :=
  hpoly (sW2csL X) x / (6*(-1 + X) ^ 3)

noncomputable def sWx (X : ℝ) : ℝ :=
  -X ^ 2*(-4 + X ^ 2 + 4*X)/(12*(-1 + X) ^ 2)

noncomputable def sW2rL (X : ℝ) : List ℝ :=
  [-X ^ 2*(1 - X + 3*X ^ 2) ^ 2, -1 - 33*X ^ 3 + 3*X + 4*X ^ 5 + 9*X ^ 6 + 13*X ^ 4 + 14*X ^ 2,
    -(-1 + X)*(17 - 44*X ^ 2 - 34*X + 10*X ^ 4 + 61*X ^ 3), (-1 + X) ^ 2*(-51 + 51*X + 62*X ^ 2),
    -2*(-1 + X) ^ 2*(-26 + 9*X ^ 2 + 26*X), 18*(-1 + X) ^ 3]

noncomputable def sW2r (X x : ℝ) : ℝ :=
  hpoly (sW2rL X) x / (12*(-1 + X) ^ 2 * ((x - 1) * (X ^ 2 - X * x + x)))

noncomputable def sWBcd (X : ℝ) : ℝ :=
  -(-1 + X) ^ 2*(-4 + X ^ 4 - 12*X ^ 2 - 8*X + 2*X ^ 3)/(12*X*(-2 + X) ^ 3)

noncomputable def sWBcs (X : ℝ) : ℝ :=
  -(4 - 62*X ^ 3 - 24*X + 21*X ^ 4 + 60*X ^ 2)/(12*X*(-1 + X) ^ 2*(-2 + X) ^ 3)

noncomputable def sWBrL (X : ℝ) : List ℝ :=
  [X ^ 2*(6 - 106*X ^ 3 - 39*X ^ 5 - 18*X + 7*X ^ 6 + 68*X ^ 2 + 89*X ^ 4), -(2 + X ^ 2 -
    2*X)*(-2 - 57*X ^ 5 - 32*X ^ 3 + 6*X + 11*X ^ 2 + 14*X ^ 6 + 74*X ^ 4), -8 - 187*X ^ 5 - 46*X
    ^ 7 - 43*X ^ 3 - 23*X ^ 2 + 7*X ^ 8 + 32*X + 127*X ^ 6 + 148*X ^ 4]

noncomputable def sWBr (X x : ℝ) : ℝ :=
  hpoly (sWBrL X) x / (12*(-1 + X) ^ 2*(-2 + X) ^ 2 * ((x - X) * (x - 1) * (X * x - X - x)))

/-- Numerator of `sSigA`. -/
noncomputable def sSigAN (X x : ℝ) : ℝ :=
  -X ^ 8 - 287*x ^ 5 - 72*x ^ 7 - 24*x ^ 3 - 4*X ^ 7 + 4*X ^ 6 + 146*x ^ 4 + 238*x ^ 6 - X ^ 8*x
    ^ 2 - 1324*X ^ 2*x ^ 5 - 1024*X ^ 4*x ^ 4 - 952*X*x ^ 6 - 584*X*x ^ 4 - 574*X ^ 3*x ^ 6 -
    486*X ^ 3*x ^ 3 - 432*X ^ 2*x ^ 7 - 290*X ^ 5*x ^ 5 - 171*X ^ 6*x ^ 3 - 140*X ^ 4*x ^ 6 -
    88*X ^ 5*x ^ 2 - 72*X ^ 4*x ^ 7 - 54*X ^ 6*x ^ 5 - 46*X ^ 3*x ^ 5 - 20*X ^ 2*x ^ 2 - 20*X ^
    7*x ^ 2 - 14*x*X ^ 6 - 6*X ^ 4*x ^ 2 - 4*x*X ^ 5 + 2*x*X ^ 4 + 2*x*X ^ 8 + 8*X ^ 7*x ^ 3 +
    16*x*X ^ 7 + 50*X ^ 2*x ^ 3 + 60*X ^ 3*x ^ 2 + 74*X ^ 6*x ^ 2 + 96*X*x ^ 3 + 120*X ^ 5*x ^ 4
    + 126*X ^ 5*x ^ 6 + 132*X ^ 5*x ^ 3 + 162*X ^ 6*x ^ 4 + 288*X*x ^ 7 + 288*X ^ 3*x ^ 7 + 395*X
    ^ 4*x ^ 3 + 432*X ^ 2*x ^ 4 + 748*X ^ 3*x ^ 4 + 853*X ^ 4*x ^ 5 + 1148*X*x ^ 5 + 1302*X ^ 2*x
    ^ 6

noncomputable def sSigA (X x : ℝ) : ℝ :=
  sSigAN X x / (12*x*(-1 + X) ^ 2*(-1 + x) ^ 2*(-x - X ^ 2 + X*x) ^ 2)

/-- Numerator of `sSigB`. -/
noncomputable def sSigBN (X x : ℝ) : ℝ :=
  -(x - X ^ 2 + x*X ^ 2 - X*x) ^ 2*(x ^ 3 - X ^ 4 - 4*X ^ 3 - 2*x ^ 2 + 2*x + 4*X ^ 2 - X ^ 4*x ^
    2 - 20*X ^ 3*x ^ 2 - 14*x*X ^ 2 - 7*X ^ 2*x ^ 3 - 4*X*x - 2*X*x ^ 3 + 2*x*X ^ 4 + 4*X*x ^ 2 +
    8*X ^ 3*x ^ 3 + 16*x*X ^ 3 + 18*X ^ 2*x ^ 2)

noncomputable def sSigB (X x : ℝ) : ℝ :=
  sSigBN X x / (12*x*(-1 + X) ^ 2*(-1 + x) ^ 2*(x - X) ^ 2*(-X - x + X*x) ^ 2)

/-- Numerator of `sSigG`. -/
noncomputable def sSigGN (X x : ℝ) : ℝ :=
  -(-1 + x)*(-2 - 12*x ^ 2 + 2*X + 9*X ^ 2 + 10*x - 10*X*x - 9*x*X ^ 2 + 12*X*x ^ 2)

noncomputable def sSigG (X x : ℝ) : ℝ :=
  sSigGN X x / (2*(-1 + X))

/-- The numerator of `pairAl x (-(N/D))`, homogenized. -/
noncomputable def pairAlH (x N D : ℝ) : ℝ :=
  N*(-518*D ^ 3*x ^ 4 - 180*D ^ 3*x ^ 6 - 20*D ^ 3*x ^ 2 + 18*D ^ 3*x ^ 7 + 218*D ^ 3*x ^ 3 +
    480*D ^ 3*x ^ 5) + D ^ 4*(-237*x ^ 5 - 27*x ^ 7 - 24*x ^ 3 + 141*x ^ 6 + 150*x ^ 4) + N ^
    2*(-265*D ^ 2*x ^ 3 - 234*D ^ 2*x ^ 5 + 2*x*D ^ 2 + 54*D ^ 2*x ^ 6 + 64*D ^ 2*x ^ 2 + 379*D ^
    2*x ^ 4) + N ^ 3*(4*D - 20*D*x - 20*D*x ^ 3 + 4*D*x ^ 4 + 32*D*x ^ 2) + N ^ 4*(-1 + x ^ 3 -
    3*x ^ 2 + 3*x)

/-- The numerator of `pairBe x (-(N/D))`, homogenized. -/
noncomputable def pairBeH (x N D : ℝ) : ℝ :=
  N*(-20*D ^ 3*x ^ 4 + 20*D ^ 3*x ^ 3) + D ^ 4*(-4*x ^ 4 - 2*x ^ 3 + 7*x ^ 5) + N ^ 2*(-27*D ^
    2*x ^ 2 + 6*x*D ^ 2 + 18*D ^ 2*x ^ 3) + N ^ 3*(-4*D - 4*D*x ^ 2 + 10*D*x) + N ^ 4*(1 - x)

/-- The numerator of `pairGa x (-(N/D))`, homogenized. -/
noncomputable def pairGaH (x N D : ℝ) : ℝ :=
  D*(-2 - 13*x ^ 2 + 3*x ^ 3 + 12*x) + N*(9 - 18*x + 9*x ^ 2)

/-- `sW2cd X x = (X - x) * hpoly (sW2qdL X) x / (6 (X - 1))`: the coefficient of `log(X - x)`
vanishes at `x = X`. -/
noncomputable def sW2qdL (X : ℝ) : List ℝ :=
  [-6 - 13*X ^ 2 + 4*X ^ 3 + 24*X, 2*(9 - 20*X + 2*X ^ 2), -22 + 31*X, -9*(-1 + X)]

noncomputable def pairS0 (X : ℝ) : ℝ :=
  -(-4 - 354*X ^ 3 - 72*X ^ 5 - 56*X + 9*X ^ 6 + 231*X ^ 4 + 254*X ^ 2)/(12*(-1 + X)*(-2 + X) ^
    2)

noncomputable def pairSX (X : ℝ) : ℝ :=
  X*(6 - 21*X ^ 3 - 16*X + 8*X ^ 4 + 27*X ^ 2)/(6*(-1 + X) ^ 3)

noncomputable def pairS1 (X : ℝ) : ℝ :=
  (-1 + X) ^ 2*(2 - 16*X ^ 2 - 13*X ^ 4 + 2*X ^ 5 + 8*X + 26*X ^ 3)/(3*X*(-2 + X) ^ 3)

noncomputable def pairS2 (X : ℝ) : ℝ :=
  -X*(-2 + X)*(6 - 13*X ^ 3 - 12*X + 4*X ^ 4 + 19*X ^ 2)/(6*(-1 + X) ^ 3)

/-- The `β` threshold `Y₁(X) = X²/(1 - X + X²)`: `x < Q(X) - Q(x)` iff `x < Y₁(X)`. -/
noncomputable def pairY1 (X : ℝ) : ℝ := X ^ 2 / (1 - X + X ^ 2)

/-- **The inner node integral** `S(X) = ∫₀^X σ_x(Q(X) - Q(x)) dx` in closed form. -/
noncomputable def pairS (X : ℝ) : ℝ :=
  pairS0 X + pairSX X * log X + pairS1 X * log (1 - X) + pairS2 X * log (2 - X)

/-- `pairW2 + pairWB` with the cancelling `log x` terms removed. -/
noncomputable def pairG0 (X x : ℝ) : ℝ :=
  sW2c1 X x * log (1 - x) + sW2cw X x * log (X ^ 2 - X * x + x) + sW2cd X x * log (X - x) +
    sW2cs X x * log (X + x - X * x) + sW2r X x + (1 / 6 * log (1 - x) +
      sWBcd X * log (X - x) + sWBcs X * log (X + x - X * x) + sWBr X x)

/-- `pairW2` with its `log (X - x)` coefficient factored through `X - x`. -/
noncomputable def pairGX (X x : ℝ) : ℝ :=
  sW2c1 X x * log (1 - x) + sW2cw X x * log (X ^ 2 - X * x + x) +
    hpoly (sW2qdL X) x / (6 * (-1 + X)) * (-negMulLog (X - x)) +
    sW2cs X x * log (X + x - X * x) + sWx X * log x + sW2r X x

/-- The antiderivative in `x` of the `α` and `γ` parts of `σ_x(Q(X) - Q(x))`. -/
noncomputable def pairW2 (X x : ℝ) : ℝ :=
  sW2c1 X x * log (1 - x) + sW2cw X x * log (X ^ 2 - X * x + x) +
    sW2cd X x * log (X - x) + sW2cs X x * log (X + x - X * x) + sWx X * log x + sW2r X x

/-- The antiderivative in `x` of the `β` part of `σ_x(Q(X) - Q(x))`. -/
noncomputable def pairWB (X x : ℝ) : ℝ :=
  1 / 6 * log (1 - x) + sWBcd X * log (X - x) + sWBcs X * log (X + x - X * x) -
    sWx X * log x + sWBr X x

section

variable {X x : ℝ}

theorem pairS_atoms (hX : X ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) X) :
    0 < 1 - x ∧ 0 < X ^ 2 - X * x + x ∧ 0 < X - x ∧ 0 < X + x - X * x := by
  have h1 := hX.2
  have h0 := hx.1
  have h2 := hx.2
  refine ⟨by linarith, by nlinarith, by linarith, by nlinarith⟩

theorem pairW2_coeffs {X : ℝ} (hX : X - 1 ≠ 0) (x : ℝ) :
    hpolyD (sW2c1L X) x / (6 * (-1 + X)) = sSigG X x ∧
      hpolyD (sW2cwL X) x / (12 * (-1 + X) ^ 3) = sSigG X x ∧
      hpolyD (sW2cdL X) x / (6 * (-1 + X)) = -sSigG X x ∧
      hpolyD (sW2csL X) x / (6 * (-1 + X) ^ 3) = -sSigG X x := by
  have hX1 : -1 + X ≠ 0 := fun h => hX (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [sW2c1L, sW2cwL, sW2cdL, sW2csL, hpoly, hpolyD, sSigG, sSigGN]
    field_simp
    ring

theorem pairW2_rat (hX : X ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) X) :
    hpoly (sW2c1L X) x / (6 * (-1 + X)) * (-1 / (1 - x)) +
      hpoly (sW2cwL X) x / (12 * (-1 + X) ^ 3) * ((1 - X) / (X ^ 2 - X * x + x)) +
      hpoly (sW2cdL X) x / (6 * (-1 + X)) * (-1 / (X - x)) +
      hpoly (sW2csL X) x / (6 * (-1 + X) ^ 3) * ((1 - X) / (X + x - X * x)) +
      sWx X * (1 / x) +
      (hpolyD (sW2rL X) x * (12 * (-1 + X) ^ 2 * ((x - 1) * (X ^ 2 - X * x + x))) -
        hpoly (sW2rL X) x * (12 * (-1 + X) ^ 2 * (1 * (X ^ 2 - X * x + x) +
          (x - 1) * (-(X * 1) + 1)))) / (12 * (-1 + X) ^ 2 * ((x - 1) * (X ^ 2 - X * x + x))) ^ 2 =
      sSigA X x := by
  obtain ⟨a1, aw, ad, as⟩ := pairS_atoms hX hx
  have hx0 := hx.1
  unfold sSigA sWx
  have hx0' := hx0.ne'
  have a1' := a1.ne'
  have aw' := aw.ne'
  have ad' := ad.ne'
  have as' := as.ne'
  have h3 : x - 1 ≠ 0 := by linarith
  have h4 : -1 + x ≠ 0 := by linarith
  have h5 : -x - X ^ 2 + X * x ≠ 0 := by linarith
  have h6 : X - 1 ≠ 0 := by linarith [hX.2]
  have hX1 : -1 + X ≠ 0 := by linarith [hX.2]
  have h7 : X * (X - x) + x ≠ 0 := by nlinarith
  have h8 : X + x - x * X ≠ 0 := by nlinarith
  have h9 : -x - X ^ 2 + x * X ≠ 0 := by nlinarith
  field_simp
  simp only [sW2c1L, sW2cwL, sW2cdL, sW2csL, sW2rL, hpoly, hpolyD, sSigAN]
  ring

theorem hasDerivAt_pairW2 (hX : X ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) X) :
    HasDerivAt (pairW2 X) (sSigA X x + sSigG X x * (log (1 - x) + log (X ^ 2 - X * x + x) -
      log (X - x) - log (X + x - X * x))) x := by
  obtain ⟨a1, aw, ad, as⟩ := pairS_atoms hX hx
  have hx0 := hx.1
  have d1 : HasDerivAt (fun y => log (1 - y)) (-1 / (1 - x)) x := by
    simpa using ((hasDerivAt_id' x).const_sub 1).log a1.ne'
  have dw : HasDerivAt (fun y => log (X ^ 2 - X * y + y)) ((1 - X) / (X ^ 2 - X * x + x)) x := by
    have := ((((hasDerivAt_id' x).const_mul X).const_sub (X ^ 2)).add (hasDerivAt_id' x)).log
      aw.ne'
    convert this using 1
    simp only [Pi.add_apply]
    ring
  have dd : HasDerivAt (fun y => log (X - y)) (-1 / (X - x)) x := by
    simpa using ((hasDerivAt_id' x).const_sub X).log ad.ne'
  have ds : HasDerivAt (fun y => log (X + y - X * y)) ((1 - X) / (X + x - X * x)) x := by
    have := (((hasDerivAt_id' x).const_add X).sub ((hasDerivAt_id' x).const_mul X)).log as.ne'
    convert this using 1
    simp only [Pi.sub_apply]
    ring
  have dx : HasDerivAt log (1 / x) x := by simpa using hasDerivAt_log hx0.ne'
  have hX1 : -1 + X ≠ 0 := by linarith [hX.2]
  have hden : 12 * (-1 + X) ^ 2 * ((x - 1) * (X ^ 2 - X * x + x)) ≠ 0 := by
    have : x - 1 ≠ 0 := by linarith
    positivity
  have dD : HasDerivAt (fun y => 12 * (-1 + X) ^ 2 * ((y - 1) * (X ^ 2 - X * y + y)))
      (12 * (-1 + X) ^ 2 * (1 * (X ^ 2 - X * x + x) + (x - 1) * (-(X * 1) + 1))) x :=
    (((hasDerivAt_id' x).sub_const 1).mul
      (((hasDerivAt_id' x).const_mul X).const_sub (X ^ 2) |>.add (hasDerivAt_id' x))).const_mul _
  have dR := (hasDerivAt_hpoly (sW2rL X) x).div dD hden
  have p1 := (hasDerivAt_hpoly (sW2c1L X) x).div_const (6 * (-1 + X))
  have pw := (hasDerivAt_hpoly (sW2cwL X) x).div_const (12 * (-1 + X) ^ 3)
  have pd := (hasDerivAt_hpoly (sW2cdL X) x).div_const (6 * (-1 + X))
  have ps := (hasDerivAt_hpoly (sW2csL X) x).div_const (6 * (-1 + X) ^ 3)
  have H := ((((p1.mul d1).add (pw.mul dw)).add (pd.mul dd)).add (ps.mul ds)).add
    (dx.const_mul (sWx X)) |>.add dR
  refine H.congr_deriv ?_
  obtain ⟨c1, cw, cd, cs⟩ := pairW2_coeffs (by linarith [hX.2] : X - 1 ≠ 0) x
  have hr := pairW2_rat hX hx
  rw [c1, cw, cd, cs]
  linear_combination hr

theorem hasDerivAt_pairWB (hX : X ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) X) :
    HasDerivAt (pairWB X) (sSigB X x) x := by
  obtain ⟨a1, -, ad, as⟩ := pairS_atoms hX hx
  have hx0 := hx.1
  have hX0 := hX.1
  have d1 : HasDerivAt (fun y => log (1 - y)) (-1 / (1 - x)) x := by
    simpa using ((hasDerivAt_id' x).const_sub 1).log a1.ne'
  have dd : HasDerivAt (fun y => log (X - y)) (-1 / (X - x)) x := by
    simpa using ((hasDerivAt_id' x).const_sub X).log ad.ne'
  have ds : HasDerivAt (fun y => log (X + y - X * y)) ((1 - X) / (X + x - X * x)) x := by
    have := (((hasDerivAt_id' x).const_add X).sub ((hasDerivAt_id' x).const_mul X)).log as.ne'
    convert this using 1
    simp only [Pi.sub_apply]
    ring
  have dx : HasDerivAt log (1 / x) x := by simpa using hasDerivAt_log hx0.ne'
  have hX1 : -1 + X ≠ 0 := by linarith [hX.2]
  have hX2 : -2 + X ≠ 0 := by linarith [hX.2]
  have hden : 12 * (-1 + X) ^ 2 * (-2 + X) ^ 2 * ((x - X) * (x - 1) * (X * x - X - x)) ≠ 0 := by
    have : x - X ≠ 0 := by linarith
    have : x - 1 ≠ 0 := by linarith
    have : X * x - X - x ≠ 0 := by linarith
    positivity
  have dD : HasDerivAt
      (fun y => 12 * (-1 + X) ^ 2 * (-2 + X) ^ 2 * ((y - X) * (y - 1) * (X * y - X - y)))
      (12 * (-1 + X) ^ 2 * (-2 + X) ^ 2 * ((1 * (x - 1) + (x - X) * 1) * (X * x - X - x) +
        (x - X) * (x - 1) * (X * 1 - 1))) x :=
    ((((hasDerivAt_id' x).sub_const X).mul ((hasDerivAt_id' x).sub_const 1)).mul
      ((((hasDerivAt_id' x).const_mul X).sub_const X).sub (hasDerivAt_id' x))).const_mul _
  have dR := (hasDerivAt_hpoly (sWBrL X) x).div dD hden
  have H := ((((d1.const_mul (1 / 6)).add (dd.const_mul (sWBcd X))).add
    (ds.const_mul (sWBcs X))).sub (dx.const_mul (sWx X))).add dR
  refine H.congr_deriv ?_
  unfold sSigB sWBcd sWBcs sWx
  have hx0' := hx0.ne'
  have hX0' := hX0.ne'
  have a1' := a1.ne'
  have ad' := ad.ne'
  have as' := as.ne'
  have h3 : x - 1 ≠ 0 := by linarith
  have h4 : -1 + x ≠ 0 := by linarith
  have h5 : -X + x ≠ 0 := by linarith
  have h6 : X * x - X - x ≠ 0 := by linarith
  have h7 : x - X ≠ 0 := by linarith
  have h8 : X - 1 ≠ 0 := by linarith [hX.2]
  have h9 : X + x - x * X ≠ 0 := by nlinarith
  have h10 : -X - x + X * x ≠ 0 := by nlinarith
  have h11 : -X - x + x * X ≠ 0 := by nlinarith
  have h12 : X * (x - 1) - x ≠ 0 := by nlinarith
  field_simp
  simp only [sWBrL, hpoly, hpolyD, sSigBN]
  ring


theorem pairAl_neg_div {x N D : ℝ} (hx0 : x ≠ 0) (hx1 : x - 1 ≠ 0) (hD : D ≠ 0)
    (hND : N * (1 - x) + x * D ≠ 0) :
    pairAl x (-(N / D)) =
      pairAlH x N D / (12 * x * (x - 1) * D ^ 2 * (N * (1 - x) + x * D) ^ 2) := by
  have h1 : -1 + x ≠ 0 := fun h => hx1 (by linarith)
  have h2 : x * D + N - x * N ≠ 0 := fun h => hND (by linarith)
  have h3 : x * D - -N + -(x * N) ≠ 0 := fun h => hND (by linarith)
  unfold pairAl pairAlH
  field_simp
  ring

theorem pairBe_neg_div {x N D : ℝ} (hx0 : x ≠ 0) (hx1 : x - 1 ≠ 0) (hD : D ≠ 0) (hN : N ≠ 0) :
    pairBe x (-(N / D)) = pairBeH x N D / (12 * x * (x - 1) * N ^ 2 * D ^ 2) := by
  have h1 : -1 + x ≠ 0 := fun h => hx1 (by linarith)
  unfold pairBe pairBeH
  field_simp
  ring

theorem pairGa_neg_div {x N D : ℝ} (hD : D ≠ 0) :
    pairGa x (-(N / D)) = pairGaH x N D / (2 * D) := by
  unfold pairGa pairGaH
  field_simp
  ring

theorem pairH_spec (X x : ℝ) :
    pairAlH x ((X - x) * (x + X - x * X)) ((1 - x) * (1 - X)) = sSigAN X x * (1 - x) ^ 5 ∧
      pairBeH x ((X - x) * (x + X - x * X)) ((1 - x) * (1 - X)) = sSigBN X x * (1 - x) ∧
      pairGaH x ((X - x) * (x + X - x * X)) ((1 - x) * (1 - X)) = sSigGN X x * (1 - x) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold pairAlH sSigAN; ring
  · unfold pairBeH sSigBN; ring
  · unfold pairGaH sSigGN; ring

theorem sSig_pieces (hX : X ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) X) :
    -pairAl x (-(setCKQ X - setCKQ x)) = sSigA X x ∧
      -pairBe x (-(setCKQ X - setCKQ x)) = sSigB X x ∧
      -pairGa x (-(setCKQ X - setCKQ x)) = sSigG X x := by
  obtain ⟨a1, aw, ad, as⟩ := pairS_atoms hX hx
  have hx0 := hx.1
  have hX1 : 0 < 1 - X := by linarith [hX.2]
  rw [setCKQ_sub (a := x) (b := X) (by linarith [hx.2, hX.2]) hX.2]
  obtain ⟨eA, eB, eG⟩ := pairH_spec X x
  have hD : (1 - x) * (1 - X) ≠ 0 := by positivity
  have hN : (X - x) * (x + X - x * X) ≠ 0 := by
    have : 0 < x + X - x * X := by nlinarith
    positivity
  have hNDe : (X - x) * (x + X - x * X) * (1 - x) + x * ((1 - x) * (1 - X)) =
      (1 - x) ^ 2 * (X ^ 2 - X * x + x) := by ring
  have hND : (X - x) * (x + X - x * X) * (1 - x) + x * ((1 - x) * (1 - X)) ≠ 0 := by
    rw [hNDe]; positivity
  have hx1 : x - 1 ≠ 0 := by linarith
  have h4 : -1 + x ≠ 0 := by linarith
  have h5 : -x - X ^ 2 + X * x ≠ 0 := by linarith
  have h6 : -1 + X ≠ 0 := by linarith
  have h7 : x - X ≠ 0 := by linarith
  have h8 : -X - x + X * x ≠ 0 := by nlinarith
  have a1' := a1.ne'
  have hX1' := hX1.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [pairAl_neg_div hx0.ne' hx1 hD hND, eA, hNDe]
    unfold sSigA
    have aw' := aw.ne'
    field_simp
    ring
  · rw [pairBe_neg_div hx0.ne' hx1 hD hN, eB]
    unfold sSigB
    field_simp
    ring
  · rw [pairGa_neg_div hD, eG]
    unfold sSigG
    field_simp
    ring


theorem pairY1_spec (hX : X ∈ Ioo (0 : ℝ) 1) : 0 < pairY1 X ∧ pairY1 X < X := by
  have h0 := hX.1
  have h1 := hX.2
  have hw : 0 < 1 - X + X ^ 2 := by nlinarith
  refine ⟨div_pos (by positivity) hw, ?_⟩
  rw [pairY1, div_lt_iff₀ hw]
  nlinarith [mul_pos h0 (pow_pos (sub_pos.2 h1) 2)]

theorem lt_setCKQ_sub_iff (hX : X ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) X) :
    x < setCKQ X - setCKQ x ↔ x < pairY1 X := by
  have h0 := hX.1
  have h1 := hX.2
  have hx1 : x < 1 := hx.2.trans h1
  have hw : 0 < 1 - X + X ^ 2 := by nlinarith
  have e : setCKQ X - setCKQ x - x = (X ^ 2 * (1 - x) - x * (1 - X)) / ((1 - X) * (1 - x)) := by
    have := setCKQ_add_self hx1
    unfold setCKQ at this ⊢
    have a : 1 - X ≠ 0 := by linarith
    have b : 1 - x ≠ 0 := by linarith
    field_simp
    field_simp at this
    linear_combination (-(1 - X)) * this
  have hd : 0 < (1 - X) * (1 - x) := mul_pos (by linarith) (by linarith)
  rw [← sub_pos, e, div_pos_iff_of_pos_right hd, pairY1, lt_div_iff₀ hw]
  constructor <;> intro h <;> nlinarith

theorem dispSig_X (hX : X ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) X) :
    dispSig x (setCKQ X - setCKQ x) = sSigA X x + (if x < pairY1 X then sSigB X x else 0) +
      sSigG X x * (log (1 - x) + log (X ^ 2 - X * x + x) - log (X - x) -
        log (X + x - X * x)) := by
  obtain ⟨eA, eB, eG⟩ := sSig_pieces hX hx
  obtain ⟨a1, aw, ad, as⟩ := pairS_atoms hX hx
  have hx1 : x < 1 := hx.2.trans hX.2
  have hl : log (1 + x / (1 - x) / (setCKQ X - setCKQ x)) = log (1 - x) +
      log (X ^ 2 - X * x + x) - log (X - x) - log (X + x - X * x) := by
    rw [setCKQ_sub (a := x) (b := X) (by linarith) hX.2]
    have e : 1 + x / (1 - x) / ((X - x) * (x + X - x * X) / ((1 - x) * (1 - X))) =
        (1 - x) * (X ^ 2 - X * x + x) / ((X - x) * (X + x - X * x)) := by
      have a : 1 - X ≠ 0 := by linarith [hX.2]
      have b : x + X - x * X ≠ 0 := by nlinarith
      have c : X - X * x + x ≠ 0 := by nlinarith
      rw [eq_div_iff (by positivity)]
      field_simp
      ring
    rw [e, log_div (by positivity) (by positivity), log_mul a1.ne' aw.ne',
      log_mul ad.ne' as.ne']
    ring
  unfold dispSig
  rw [hl]
  by_cases h : x < pairY1 X
  · have h' := (lt_setCKQ_sub_iff hX hx).2 h
    simp only [h', h, ↓reduceIte]
    linear_combination eA + eB + eG * (log (1 - x) + log (X ^ 2 - X * x + x) - log (X - x) -
      log (X + x - X * x))
  · have h' : ¬ x < setCKQ X - setCKQ x := fun h'' => h ((lt_setCKQ_sub_iff hX hx).1 h'')
    simp only [h', h, ↓reduceIte]
    linear_combination eA + eG * (log (1 - x) + log (X ^ 2 - X * x + x) - log (X - x) -
      log (X + x - X * x))


theorem continuousAt_pairG0 (hX : X ∈ Ioo (0 : ℝ) 1) : ContinuousAt (pairG0 X) 0 := by
  have h0 := hX.1
  have h1 := hX.2
  have hX1 : -1 + X ≠ 0 := by linarith
  have hX2 : -2 + X ≠ 0 := by linarith
  have d1 : 12 * (-1 + X) ^ 2 * (-2 + X) ^ 2 * ((0 - X) * (0 - 1) * (X * 0 - X - 0)) ≠ 0 := by
    have : (0 - X) * (0 - 1) * (X * 0 - X - 0) = -X ^ 2 := by ring
    rw [this]; simp [hX1, hX2, h0.ne']
  have d2 : 12 * (-1 + X) ^ 2 * ((0 - 1) * (X ^ 2 - X * 0 + 0)) ≠ 0 := by
    have : (0 - 1) * (X ^ 2 - X * 0 + 0) = -X ^ 2 := by ring
    rw [this]; simp [hX1, h0.ne']
  have l1 : (1 : ℝ) - 0 ≠ 0 := by norm_num
  have l2 : X ^ 2 - X * 0 + 0 ≠ 0 := by simp; positivity
  have l3 : X - 0 ≠ 0 := by simp; positivity
  have l4 : X + 0 - X * 0 ≠ 0 := by simp; positivity
  unfold pairG0 sW2c1 sW2cw sW2cd sW2cs sW2r sWBr
  fun_prop (disch := assumption)

theorem continuousAt_pairGX (hX : X ∈ Ioo (0 : ℝ) 1) : ContinuousAt (pairGX X) X := by
  have h0 := hX.1
  have h1 := hX.2
  have hX1 : -1 + X ≠ 0 := by linarith
  have d2 : 12 * (-1 + X) ^ 2 * ((X - 1) * (X ^ 2 - X * X + X)) ≠ 0 := by
    have : (X - 1) * (X ^ 2 - X * X + X) = (X - 1) * X := by ring
    have hX1' : X - 1 ≠ 0 := by linarith
    rw [this]; simp [hX1, hX1', h0.ne']
  have l1 : 1 - X ≠ 0 := by linarith
  have l2 : X ^ 2 - X * X + X ≠ 0 := by ring_nf; positivity
  have l4 : X + X - X * X ≠ 0 := by nlinarith
  have l5 : X ≠ 0 := h0.ne'
  unfold pairGX sW2c1 sW2cw sW2cs sW2r
  fun_prop (disch := assumption)

theorem pairW2_add_pairWB (X x : ℝ) : pairW2 X x + pairWB X x = pairG0 X x := by
  unfold pairW2 pairWB pairG0
  ring

theorem pairW2_eq_pairGX (X x : ℝ) : pairW2 X x = pairGX X x := by
  have e : hpoly (sW2cdL X) x = (X - x) * hpoly (sW2qdL X) x := by
    simp only [sW2cdL, sW2qdL, hpoly]
    ring
  unfold pairW2 pairGX sW2cd negMulLog
  rw [e]
  ring

/-- The inner node integral as a difference of antiderivative values. -/
theorem integral_dispSig_X (hX : X ∈ Ioo (0 : ℝ) 1)
    (hint : IntervalIntegrable (fun x => dispSig x (setCKQ X - setCKQ x)) volume 0 X) :
    ∫ x in (0 : ℝ)..X, dispSig x (setCKQ X - setCKQ x) =
      pairGX X X + pairWB X (pairY1 X) - pairG0 X 0 := by
  obtain ⟨hY0, hYX⟩ := pairY1_spec hX
  set Y := pairY1 X with hYdef
  have hsub : ∀ c d : ℝ, 0 ≤ c → d ≤ X → c ≤ d →
      IntervalIntegrable (fun x => dispSig x (setCKQ X - setCKQ x)) volume c d :=
    fun c d hc hd hcd => hint.mono_set (by
      rw [uIcc_of_le hcd, uIcc_of_le hX.1.le]
      exact Icc_subset_Icc hc hd)
  have hd1 : ∀ x ∈ Ioo 0 Y, HasDerivAt (fun x => pairW2 X x + pairWB X x)
      (dispSig x (setCKQ X - setCKQ x)) x := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) X := ⟨hx.1, hx.2.trans hYX⟩
    refine ((hasDerivAt_pairW2 hX hx').add (hasDerivAt_pairWB hX hx')).congr_deriv ?_
    rw [dispSig_X hX hx']
    simp only [show x < pairY1 X from hx.2, ↓reduceIte]
    ring
  have hd2 : ∀ x ∈ Ioo Y X, HasDerivAt (pairW2 X) (dispSig x (setCKQ X - setCKQ x)) x := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) X := ⟨hY0.trans hx.1, hx.2⟩
    refine (hasDerivAt_pairW2 hX hx').congr_deriv ?_
    rw [dispSig_X hX hx']
    simp only [show ¬ x < pairY1 X from not_lt.2 hx.1.le, ↓reduceIte]
    ring
  have hYin : Y ∈ Ioo (0 : ℝ) X := ⟨hY0, hYX⟩
  have c2 : ContinuousAt (pairW2 X) Y := (hasDerivAt_pairW2 hX hYin).continuousAt
  have cB : ContinuousAt (pairWB X) Y := (hasDerivAt_pairWB hX hYin).continuousAt
  have h0 : Tendsto (fun x => pairW2 X x + pairWB X x) (𝓝[>] 0) (𝓝 (pairG0 X 0)) := by
    have := (continuousAt_pairG0 hX).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    exact this.congr fun x => (pairW2_add_pairWB X x).symm
  have hXl : Tendsto (pairW2 X) (𝓝[<] X) (𝓝 (pairGX X X)) := by
    have := (continuousAt_pairGX hX).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio X))
    exact this.congr fun x => (pairW2_eq_pairGX X x).symm
  have I1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hY0 hd1
    (hsub 0 Y le_rfl hYX.le hY0.le) h0 ((c2.add cB).tendsto.mono_left nhdsWithin_le_nhds)
  have I2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hYX hd2
    (hsub Y X hY0.le le_rfl hYX.le) (c2.tendsto.mono_left nhdsWithin_le_nhds) hXl
  rw [← intervalIntegral.integral_add_adjacent_intervals (hsub 0 Y le_rfl hYX.le hY0.le)
    (hsub Y X hY0.le le_rfl hYX.le), I1, I2]
  simp only [Pi.add_apply]
  ring


theorem sWBr_pairY1 (hX : X ∈ Ioo (0 : ℝ) 1) :
    sWBr X (pairY1 X) = -(1 + X ^ 2 - X) * (10 - 26 * X ^ 3 - 20 * X + 7 * X ^ 4 + 36 * X ^ 2) /
      (12 * (-1 + X) ^ 2 * (-2 + X) ^ 2) := by
  have h0 := hX.1.ne'
  have h1 : 1 - X ≠ 0 := by linarith [hX.2]
  have h1' : -1 + X ≠ 0 := by linarith [hX.2]
  have h2 : -2 + X ≠ 0 := by linarith [hX.2]
  have hw : 1 - X + X ^ 2 ≠ 0 := by nlinarith [hX.1, hX.2]
  have e1 : pairY1 X - X = -(X * (1 - X) ^ 2) / (1 - X + X ^ 2) := by
    unfold pairY1; field_simp; ring
  have e2 : pairY1 X - 1 = -(1 - X) / (1 - X + X ^ 2) := by
    unfold pairY1; field_simp; ring
  have e3 : X * pairY1 X - X - pairY1 X = -X / (1 - X + X ^ 2) := by
    unfold pairY1; field_simp; ring
  unfold sWBr
  rw [e1, e2, e3]
  simp only [sWBrL, hpoly]
  unfold pairY1
  field_simp
  ring

theorem pairS_coeffs (hX : X ∈ Ioo (0 : ℝ) 1) :
    sW2cw X X + sW2cs X X - sWx X - 2 * sW2cw X 0 - sW2cd X 0 - sW2cs X 0 = pairSX X ∧
      sW2c1 X X + 1 / 6 + 2 * sWBcd X = pairS1 X ∧ sW2cs X X = pairS2 X ∧
      -1 / 6 - sWBcd X - sWBcs X + sWx X = 0 ∧
      sW2r X X + sWBr X (pairY1 X) - sW2r X 0 - sWBr X 0 = pairS0 X := by
  have h0 := hX.1.ne'
  have h1 : -1 + X ≠ 0 := by linarith [hX.2]
  have h1' : X - 1 ≠ 0 := by linarith [hX.2]
  have h2 : -2 + X ≠ 0 := by linarith [hX.2]
  have h2' : X - 2 ≠ 0 := by linarith [hX.2]
  have hw : 1 - X + X ^ 2 ≠ 0 := by nlinarith [hX.1, hX.2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [sW2cw, sW2cs, sW2cd, sWx, sW2cwL, sW2csL, sW2cdL, hpoly, pairSX]
    field_simp
    ring
  · simp only [sW2c1, sWBcd, sW2c1L, hpoly, pairS1]
    field_simp
    ring
  · simp only [sW2cs, sW2csL, hpoly, pairS2]
    field_simp
    ring
  · simp only [sWBcd, sWBcs, sWx]
    field_simp
    ring
  · have e0 : sWBr X 0 = -hpoly (sWBrL X) 0 / (12 * (-1 + X) ^ 2 * (-2 + X) ^ 2 * X ^ 2) := by
      unfold sWBr
      rw [show 12 * (-1 + X) ^ 2 * (-2 + X) ^ 2 * ((0 - X) * (0 - 1) * (X * 0 - X - 0)) =
        -(12 * (-1 + X) ^ 2 * (-2 + X) ^ 2 * X ^ 2) by ring, div_neg, neg_div]
    rw [sWBr_pairY1 hX, e0]
    simp only [sW2r, sW2rL, sWBrL, hpoly, pairS0]
    field_simp
    ring

/-- **The inner node integral** in closed form, `S(X) = pairS X`. -/
theorem pairGX_add_pairWB_sub (hX : X ∈ Ioo (0 : ℝ) 1) :
    pairGX X X + pairWB X (pairY1 X) - pairG0 X 0 = pairS X := by
  have h0 := hX.1
  have h1 : 0 < 1 - X := by linarith [hX.2]
  have hw : 0 < 1 - X + X ^ 2 := by nlinarith [hX.2]
  have h2 : 0 < 2 - X := by linarith [hX.2]
  obtain ⟨cX, c1, c2, cW, c0⟩ := pairS_coeffs hX
  have eY1 : log (1 - pairY1 X) = log (1 - X) - log (1 - X + X ^ 2) := by
    rw [← log_div h1.ne' hw.ne']; congr 1; unfold pairY1; field_simp; ring
  have eY2 : log (X - pairY1 X) = log X + 2 * log (1 - X) - log (1 - X + X ^ 2) := by
    rw [show X - pairY1 X = X * (1 - X) ^ 2 / (1 - X + X ^ 2) by unfold pairY1; field_simp; ring,
      log_div (by positivity) hw.ne', log_mul h0.ne' (by positivity), log_pow]
    push_cast; ring
  have eY3 : log (X + pairY1 X - X * pairY1 X) = log X - log (1 - X + X ^ 2) := by
    rw [show X + pairY1 X - X * pairY1 X = X / (1 - X + X ^ 2) by unfold pairY1; field_simp; ring,
      log_div h0.ne' hw.ne']
  have eY4 : log (pairY1 X) = 2 * log X - log (1 - X + X ^ 2) := by
    rw [pairY1, log_div (by positivity) hw.ne', log_pow]; push_cast; ring
  have eX1 : log (X ^ 2 - X * X + X) = log X := by congr 1; ring
  have eX2 : log (X + X - X * X) = log X + log (2 - X) := by
    rw [← log_mul h0.ne' h2.ne']; congr 1; ring
  have e01 : log (X ^ 2 - X * 0 + 0) = 2 * log X := by
    rw [show X ^ 2 - X * 0 + 0 = X ^ 2 by ring, log_pow]; push_cast; ring
  unfold pairGX pairWB pairG0 pairS
  rw [eY1, eY2, eY3, eY4, eX1, eX2, e01]
  simp only [sub_self, negMulLog_zero, neg_zero, mul_zero, sub_zero, log_one, add_zero, zero_add,
    mul_zero]
  linear_combination log X * cX + log (1 - X) * c1 + log (2 - X) * c2 +
    log (1 - X + X ^ 2) * cW + c0

/-- **The density identity**: `ρ_L(X) Q(X) = e₁(X) + Q'(X) S(X)`. -/
theorem rhoL_mul_setCKQ (hX : X ∈ Ioo (0 : ℝ) 1) :
    rhoL X * setCKQ X = dispE1 X + setCKdQ X * pairS X := by
  have h0 := hX.1.ne'
  have h1 : 1 - X ≠ 0 := by linarith [hX.2]
  have h1' : X - 1 ≠ 0 := by linarith [hX.2]
  have h1'' : -1 + X ≠ 0 := by linarith [hX.2]
  have h2 : X - 2 ≠ 0 := by linarith [hX.2]
  have h2' : -2 + X ≠ 0 := by linarith [hX.2]
  rw [rhoL_eq hX]
  unfold setCKQ dispE1 setCKdQ pairS pairS0 pairSX pairS1 pairS2
  generalize log X = LX
  generalize log (1 - X) = L1
  generalize log (2 - X) = L2
  field_simp
  ring

end

end QED.ChainProof.SetCK
