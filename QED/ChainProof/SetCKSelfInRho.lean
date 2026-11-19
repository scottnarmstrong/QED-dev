/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKSelfInDisp

/-!
# Set (c), Stage K, group G1: the inner node integral and the density

Helper level (no frozen statement). For the outer node `X ∈ (0, 1)` the inner node integral
`S(X) = ∫₀^X σ_x(Q(X) - Q(x)) dx` of the G1 discontinuity is elementary: `σ_x(Q(X) - Q(x))` is
rational in `x`, given by `selfInSigB` for `x < Y₁(X) = X²/(1 - X + X²)` (where
`Q(X) - Q(x) > x`) and by `selfInSigA` above. With the antiderivatives `selfInIB` on `[0, Y₁]`
and `selfInIA` on `[Y₁, X]` (`integral_selfInSig_X`) the density

`ρ_S(X) = 2 (e₁(X) + Q'(X) S(X))/Q(X)`

is (`rhoSelfIn_mul_setCKQ`)

`ρ_S(X) = X(X-2)(X²-2X+2)/(6(X-1)³) log X - (X-1)(X⁴-4X³+3X²+4X+2)/(3X²(X-2)²) log(1-X)`
`  + (7X⁵ - 23X⁴ + 10X³ + 44X² - 60X + 20)/(12X(X-2)(X-1)²)`.

The logarithm of `1 - X + X²` cancels. Numerically `ρ_S(1⁻) = -7/18` and `ρ_S(X) ~ -1/X` at
`X → 0`; `∫₀¹ ρ_S Q/(Q + t) dX` reproduces `selfIn t` at `t = 1, 4` to 40 digits.
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set Filter Topology MeasureTheory

/-- **The G1 density** `ρ_S(X)`. -/
noncomputable def rhoSelfIn (X : ℝ) : ℝ :=
  X * (X - 2) * (X ^ 2 - 2 * X + 2) / (6 * (X - 1) ^ 3) * log X -
    (X - 1) * (X ^ 4 - 4 * X ^ 3 + 3 * X ^ 2 + 4 * X + 2) / (3 * X ^ 2 * (X - 2) ^ 2) *
      log (1 - X) +
    (7 * X ^ 5 - 23 * X ^ 4 + 10 * X ^ 3 + 44 * X ^ 2 - 60 * X + 20) /
      (12 * X * (X - 2) * (X - 1) ^ 2)

/-- The polynomial part common to both antiderivatives. -/
noncomputable def selfInW (X x : ℝ) : ℝ := -x ^ 2 / 8 - x * (2 * X ^ 2 - X + 1) / (12 * (X - 1))

/-- The `x`-antiderivative of `σ_x(Q(X) - Q(x))` on `[Y₁, X]` (`selfInSigA`). -/
noncomputable def selfInIA (X x : ℝ) : ℝ :=
  selfInW X x - X ^ 4 / (12 * (X - 1) ^ 2 * x) + log (1 - x) / 12 -
    X ^ 2 * (X ^ 2 - 2 * X + 2) / (12 * (X - 1) ^ 2) * log x

/-- The `x`-antiderivative of `σ_x(Q(X) - Q(x))` on `[0, Y₁]` (`selfInSigB`). -/
noncomputable def selfInIB (X x : ℝ) : ℝ :=
  selfInW X x + (2 * X - 1) / (12 * (X - 2) ^ 2 * (X - 1) ^ 2 * ((1 - X) * x + X)) +
    (X - 1) ^ 4 * (X + 1) / (12 * (X - 2) ^ 2 * (X - x)) +
    (6 * X ^ 4 - 22 * X ^ 3 + 27 * X ^ 2 - 12 * X + 2) / (12 * X * (X - 2) ^ 3 * (X - 1) ^ 2) *
      log ((1 - X) * x + X) -
    (X - 1) ^ 2 * (X ^ 4 - 4 * X ^ 3 + 3 * X ^ 2 + 4 * X + 2) / (12 * X * (X - 2) ^ 3) *
      log (X - x)

section

variable {x X : ℝ}

theorem hasDerivAt_selfInW (X x : ℝ) :
    HasDerivAt (selfInW X) (-x / 4 - (2 * X ^ 2 - X + 1) / (12 * (X - 1))) x := by
  have h := (((hasDerivAt_pow 2 x).neg).div_const 8).sub
    ((hasDerivAt_id' x).mul_const ((2 * X ^ 2 - X + 1)) |>.div_const (12 * (X - 1)))
  convert h using 1
  · funext y
    simp only [selfInW, Pi.sub_apply, Pi.neg_apply]
  · simp only [Nat.cast_ofNat]
    ring

theorem hasDerivAt_selfInIA (hX : X ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (selfInIA X) (selfInSigA x (setCKQ X - setCKQ x)) x := by
  have hx0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hX1 : X - 1 ≠ 0 := by linarith [hX.2]
  have hX1' : 1 - X ≠ 0 := by linarith [hX.2]
  have hl1 : HasDerivAt (fun x => log (1 - x)) (-1 / (1 - x)) x := by
    simpa using ((hasDerivAt_id' x).const_sub 1).log hx1
  have hl0 : HasDerivAt (fun x => log x) (1 / x) x := by
    simpa using (hasDerivAt_id' x).log hx0
  have hinv : HasDerivAt (fun x => X ^ 4 / (12 * (X - 1) ^ 2 * x))
      ((0 * (12 * (X - 1) ^ 2 * x) - X ^ 4 * (12 * (X - 1) ^ 2 * 1)) /
        (12 * (X - 1) ^ 2 * x) ^ 2) x :=
    (hasDerivAt_const x _).div ((hasDerivAt_id' x).const_mul _) (by positivity)
  have h := (((hasDerivAt_selfInW X x).sub hinv).add (hl1.div_const 12)).sub
    (hl0.const_mul (X ^ 2 * (X ^ 2 - 2 * X + 2) / (12 * (X - 1) ^ 2)))
  convert h using 1
  · funext y
    rfl
  rw [setCKQ_sub hx.2 hX.2]
  unfold selfInSigA
  field_simp
  ring

theorem hasDerivAt_selfInIB (hX : X ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ico (0 : ℝ) X) :
    HasDerivAt (selfInIB X) (selfInSigB x (setCKQ X - setCKQ x)) x := by
  have hX0 := hX.1.ne'
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2, hX.2]
  have hX1 : X - 1 ≠ 0 := by linarith [hX.2]
  have hX1' : 1 - X ≠ 0 := by linarith [hX.2]
  have hX2 : X - 2 ≠ 0 := by linarith [hX.2]
  have hXx : 0 < X - x := by linarith [hx.2]
  have hP : 0 < (1 - X) * x + X := by
    have : 0 ≤ (1 - X) * x := mul_nonneg (by linarith [hX.2]) hx.1
    linarith [hX.1]
  have hS : x + X - x * X ≠ 0 := by
    have : 0 ≤ x * (1 - X) := mul_nonneg hx.1 (by linarith [hX.2])
    linarith [hX.1]
  have hlP : HasDerivAt (fun x => log ((1 - X) * x + X)) ((1 - X) / ((1 - X) * x + X)) x := by
    simpa using (((hasDerivAt_id' x).const_mul (1 - X)).add_const X).log hP.ne'
  have hlX : HasDerivAt (fun x => log (X - x)) (-1 / (X - x)) x := by
    simpa using ((hasDerivAt_id' x).const_sub X).log hXx.ne'
  have hiP : HasDerivAt
      (fun x => (2 * X - 1) / (12 * (X - 2) ^ 2 * (X - 1) ^ 2 * ((1 - X) * x + X)))
      ((0 * (12 * (X - 2) ^ 2 * (X - 1) ^ 2 * ((1 - X) * x + X)) -
        (2 * X - 1) * (12 * (X - 2) ^ 2 * (X - 1) ^ 2 * ((1 - X) * 1))) /
          (12 * (X - 2) ^ 2 * (X - 1) ^ 2 * ((1 - X) * x + X)) ^ 2) x :=
    (hasDerivAt_const x _).div ((((hasDerivAt_id' x).const_mul (1 - X)).add_const X).const_mul
      _) (by positivity)
  have hiX : HasDerivAt (fun x => (X - 1) ^ 4 * (X + 1) / (12 * (X - 2) ^ 2 * (X - x)))
      ((0 * (12 * (X - 2) ^ 2 * (X - x)) - (X - 1) ^ 4 * (X + 1) * (12 * (X - 2) ^ 2 * (0 - 1))) /
        (12 * (X - 2) ^ 2 * (X - x)) ^ 2) x :=
    (hasDerivAt_const x _).div (((hasDerivAt_const x X).sub (hasDerivAt_id' x)).const_mul _)
      (by positivity)
  have h := ((((hasDerivAt_selfInW X x).add hiP).add hiX).add
    (hlP.const_mul ((6 * X ^ 4 - 22 * X ^ 3 + 27 * X ^ 2 - 12 * X + 2) /
      (12 * X * (X - 2) ^ 3 * (X - 1) ^ 2)))).sub
    (hlX.const_mul ((X - 1) ^ 2 * (X ^ 4 - 4 * X ^ 3 + 3 * X ^ 2 + 4 * X + 2) /
      (12 * X * (X - 2) ^ 3)))
  convert h using 1
  · funext y
    rfl
  rw [setCKQ_sub (hx.2.trans hX.2) hX.2]
  unfold selfInSigB
  have := hXx.ne'
  have hP0 := hP.ne'
  set P := (1 - X) * x + X with hPdef
  field_simp
  rw [hPdef]
  ring

theorem selfInSig_X (hX : X ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) X) :
    selfInSig x (setCKQ X - setCKQ x) = if x < pairY1 X then
      selfInSigB x (setCKQ X - setCKQ x) else selfInSigA x (setCKQ X - setCKQ x) := by
  unfold selfInSig
  simp only [lt_setCKQ_sub_iff hX hx]

/-- **The inner node integral** as a difference of antiderivative values. -/
theorem integral_selfInSig_X (hX : X ∈ Ioo (0 : ℝ) 1)
    (hint : IntervalIntegrable (fun x => selfInSig x (setCKQ X - setCKQ x)) volume 0 X) :
    ∫ x in (0 : ℝ)..X, selfInSig x (setCKQ X - setCKQ x) =
      (selfInIB X (pairY1 X) - selfInIB X 0) + (selfInIA X X - selfInIA X (pairY1 X)) := by
  obtain ⟨hY0, hYX⟩ := pairY1_spec hX
  set Y := pairY1 X with hYdef
  have hsub : ∀ c d : ℝ, 0 ≤ c → d ≤ X → c ≤ d →
      IntervalIntegrable (fun x => selfInSig x (setCKQ X - setCKQ x)) volume c d :=
    fun c d hc hd hcd => hint.mono_set (by
      rw [uIcc_of_le hcd, uIcc_of_le hX.1.le]
      exact Icc_subset_Icc hc hd)
  have hcB : ContinuousOn (selfInIB X) (Icc 0 Y) := fun x hx =>
    (hasDerivAt_selfInIB hX ⟨hx.1, hx.2.trans_lt hYX⟩).continuousAt.continuousWithinAt
  have hcA : ContinuousOn (selfInIA X) (Icc Y X) := fun x hx =>
    (hasDerivAt_selfInIA hX ⟨hY0.trans_le hx.1, hx.2.trans_lt hX.2⟩).continuousAt.continuousWithinAt
  have hd1 : ∀ x ∈ Ioo 0 Y, HasDerivAt (selfInIB X) (selfInSig x (setCKQ X - setCKQ x)) x := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) X := ⟨hx.1, hx.2.trans hYX⟩
    rw [selfInSig_X hX hx']
    simp only [show x < pairY1 X from hx.2, ↓reduceIte]
    exact hasDerivAt_selfInIB hX ⟨hx.1.le, hx'.2⟩
  have hd2 : ∀ x ∈ Ioo Y X, HasDerivAt (selfInIA X) (selfInSig x (setCKQ X - setCKQ x)) x := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) X := ⟨hY0.trans hx.1, hx.2⟩
    rw [selfInSig_X hX hx']
    simp only [show ¬ x < pairY1 X from not_lt.2 hx.1.le, ↓reduceIte]
    exact hasDerivAt_selfInIA hX ⟨hx'.1, hx.2.trans hX.2⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hsub 0 Y le_rfl hYX.le hY0.le)
    (hsub Y X hY0.le le_rfl hYX.le),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hY0.le hcB hd1
      (hsub 0 Y le_rfl hYX.le hY0.le),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hYX.le hcA hd2
      (hsub Y X hY0.le le_rfl hYX.le)]

/-- **The density identity**: `ρ_S(X) Q(X) = 2 (e₁(X) + Q'(X) S(X))`. -/
theorem rhoSelfIn_mul_setCKQ (hX : X ∈ Ioo (0 : ℝ) 1) :
    rhoSelfIn X * setCKQ X = 2 * (selfInE1 X + setCKdQ X *
      ((selfInIB X (pairY1 X) - selfInIB X 0) + (selfInIA X X - selfInIA X (pairY1 X)))) := by
  have h0 := hX.1
  have h1 : 0 < 1 - X := by linarith [hX.2]
  have hD : 0 < 1 - X + X ^ 2 := by nlinarith
  have hX1 : X - 1 ≠ 0 := by linarith
  have hX2 : X - 2 ≠ 0 := by linarith
  have lY : log (pairY1 X) = 2 * log X - log (1 - X + X ^ 2) := by
    rw [pairY1, log_div (by positivity) hD.ne', log_pow]
    push_cast
    ring
  have l1Y : log (1 - pairY1 X) = log (1 - X) - log (1 - X + X ^ 2) := by
    rw [show 1 - pairY1 X = (1 - X) / (1 - X + X ^ 2) by unfold pairY1; field_simp; ring,
      log_div h1.ne' hD.ne']
  have ePY : (1 - X) * pairY1 X + X = X / (1 - X + X ^ 2) := by
    unfold pairY1; field_simp; ring
  have eXY : X - pairY1 X = X * (1 - X) ^ 2 / (1 - X + X ^ 2) := by
    unfold pairY1; field_simp; ring
  have lPY : log ((1 - X) * pairY1 X + X) = log X - log (1 - X + X ^ 2) := by
    rw [ePY, log_div h0.ne' hD.ne']
  have lXY : log (X - pairY1 X) = log X + 2 * log (1 - X) - log (1 - X + X ^ 2) := by
    rw [eXY, log_div (by positivity) hD.ne', log_mul h0.ne' (by positivity), log_pow]
    push_cast
    ring
  have lP0 : log ((1 - X) * 0 + X) = log X := by rw [mul_zero, zero_add]
  have lX0 : log (X - 0) = log X := by rw [sub_zero]
  unfold rhoSelfIn selfInIA selfInIB selfInW selfInE1 setCKQ setCKdQ
  rw [lY, l1Y, lPY, lXY, lP0, lX0, ePY, eXY]
  unfold pairY1
  have := h1.ne'
  have := hD.ne'
  have : X ≠ 0 := h0.ne'
  field_simp
  ring

end

end QED.ChainProof.SetCK

end
