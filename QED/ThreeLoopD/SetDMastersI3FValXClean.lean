/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI3FValXAlpha
public import QED.ThreeLoopD.SetDMastersI3FValXInt

/-!
# Set (d), master `I₃`: the `e₃`-integral in the variables `(x, α)` and its `x`-derivative

Put `e₁ = c α` with `c = x (1 - x)`, `y = 1 - x`, `u = x α`, `v = y α` and
`Π = (1 + u)(1 + v) = 1 + α + c α²`. Then `q = c α/(1 + α)`, `p = 1/α`, `A = c Π`, and the
combination `c e₁ g(x, e₁) = L - P(0)` of `QED.ThreeLoopD.SetDMastersI3FValE3` becomes the clean
form `QED.ThreeLoopD.i3XH`, whose logarithms are those of the letters `x, y, α, 1 + α, 1 + u,
1 + v` and whose dilogarithm arguments are `-1/α`, `-v/(1 + u)`, `-u/(1 + v)`, `-c α/Π`,
`1/(1 + u)`, `1/(1 + v)`, `1/Π`, `(1 + α)/Π` (the three arguments below `-1` of the `F`-terms are
inverted by `QED.ThreeLoopD.i3E_dilogI_inv`).

In `x` at fixed `α`, `∂ₓ H = (1 - 2x) N(x α, y α)/(c Π)` with `N = QED.ThreeLoopD.i3XN`.

## Main results

* `QED.ThreeLoopD.i3XH_eq`: `L - P(0) = H(x, α)` at `e₁ = c α`.
* `QED.ThreeLoopD.hasDerivAt_i3XH`: `∂ₓ H = (1 - 2x) N(x α, y α)/(c Π)`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology
open QED.TwoLoop.UnitXClose

namespace QED.ThreeLoopD

/-- Inversion with the logarithm supplied. -/
theorem i3X_dilogI_neg_eq {X L : ℝ} (hX : 0 < X) (hL : log X = L) :
    dilogI (-X) = -π ^ 2 / 6 - L ^ 2 / 2 - dilogI (-(1 / X)) := by
  have := i3E_dilogI_inv hX
  rw [hL] at this
  linarith

/-- The clean form `H(x, α)` of `c e₁ g(x, e₁)` at `e₁ = c α`. -/
noncomputable def i3XH (x a : ℝ) : ℝ :=
  π ^ 2 / 6 - log x * log (1 - x) +
    ((log (1 + x * a) + log (1 + (1 - x) * a) - log a) ^ 2 +
      (log (1 + x * a) + log (1 + (1 - x) * a) - log a - log (1 + a)) ^ 2 -
      (log (1 + x * a) - log a) ^ 2 - (log (1 + (1 - x) * a) - log a) ^ 2) / 2 +
    (log x + log (1 - x) + log a - log (1 + a)) ^ 2 / 2 -
    (dilogI (-(1 / a)) + 2 * (π ^ 2 / 6) + (log (1 + x * a) - log (1 - x) - log a) ^ 2 / 2 +
      (log (1 + (1 - x) * a) - log x - log a) ^ 2 / 2 +
      dilogI (-((1 - x) * a / (1 + x * a))) + dilogI (-(x * a / (1 + (1 - x) * a)))) / (1 + a) +
    a / (1 + a) * (-(π ^ 2 / 6) -
      (log (1 + x * a) + log (1 + (1 - x) * a) - log x - log (1 - x) - log a) ^ 2 / 2 -
      dilogI (-(x * (1 - x) * a / ((1 + x * a) * (1 + (1 - x) * a))))) +
    (log (1 + a) - log (1 + x * a) - log (1 + (1 - x) * a)) *
      (log x + log (1 - x) + log a - log (1 + a)) -
    (dilogI (1 / (1 + x * a)) + dilogI (1 / (1 + (1 - x) * a)) -
      dilogI (1 / ((1 + x * a) * (1 + (1 - x) * a))) -
      dilogI ((1 + a) / ((1 + x * a) * (1 + (1 - x) * a))))

theorem i3XH_eq {x a : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    i3EL x (x * (1 - x) * a) - i3EP x (x * (1 - x) * a) 0 = i3XH x a := by
  obtain ⟨hx0, hx1⟩ := hx
  have hy0 : 0 < 1 - x := by linarith
  have hc0 : 0 < x * (1 - x) := mul_pos hx0 hy0
  have p1 : 0 < 1 + x * a := by positivity
  have p2 : 0 < 1 + (1 - x) * a := by positivity
  have p3 : 0 < 1 + a := by positivity
  have hP : 0 < (1 + x * a) * (1 + (1 - x) * a) := by positivity
  simp only [i3EL, i3EP, i3EF, i3EZ, i3EW, zero_div, neg_zero, dilogI_zero, neg_zero, sub_zero,
    zero_add]
  set c := x * (1 - x) with hc
  have hPc : (1 + x * a) * (1 + (1 - x) * a) = 1 + a + c * a ^ 2 := by rw [hc]; ring
  have r1 : log (c / (c * a) + (1 + c * a)) =
      log (1 + x * a) + log (1 + (1 - x) * a) - log a := by
    rw [← log_mul p1.ne' p2.ne', ← log_div hP.ne' ha.ne']; congr 1; rw [hPc]; field_simp; ring
  have r2 : log (c / (c * a) + c * (c * a) / (c + c * a)) =
      log (1 + x * a) + log (1 + (1 - x) * a) - log a - log (1 + a) := by
    rw [← log_mul p1.ne' p2.ne', ← log_div hP.ne' ha.ne', ← log_div (by positivity) p3.ne']
    congr 1; rw [hPc]; field_simp
  have r3 : log (c / (c * a) + x) = log (1 + x * a) - log a := by
    rw [← log_div p1.ne' ha.ne']; congr 1; rw [hc]; field_simp
  have r4 : log (c / (c * a) + (1 - x)) = log (1 + (1 - x) * a) - log a := by
    rw [← log_div p2.ne' ha.ne']; congr 1; rw [hc]; field_simp
  have r5 : log (c * (c * a) / (c + c * a)) = log x + log (1 - x) + log a - log (1 + a) := by
    rw [← log_mul hx0.ne' hy0.ne', ← log_mul (by positivity) ha.ne',
      ← log_div (by positivity) p3.ne']
    congr 1; rw [hc]; field_simp
  have r6 : (c * (c * a) / (c + c * a) - c) / (c * (c * a) / (c + c * a)) = -(1 / a) := by
    field_simp; ring
  have hX7 : 0 < (1 + x * a) / ((1 - x) * a) := by positivity
  have hL7 : log ((1 + x * a) / ((1 - x) * a)) = log (1 + x * a) - log (1 - x) - log a := by
    rw [log_div p1.ne' (by positivity), log_mul hy0.ne' ha.ne']; ring
  have e7 : (c * (c * a) / (c + c * a) - x) / (c * (c * a) / (c + c * a)) =
      -((1 + x * a) / ((1 - x) * a)) := by
    rw [hc]; field_simp; ring
  have r7 : dilogI ((c * (c * a) / (c + c * a) - x) / (c * (c * a) / (c + c * a))) =
      -π ^ 2 / 6 - (log (1 + x * a) - log (1 - x) - log a) ^ 2 / 2 -
        dilogI (-((1 - x) * a / (1 + x * a))) := by
    rw [e7, i3X_dilogI_neg_eq hX7 hL7, one_div_div]
  have hX8 : 0 < (1 + (1 - x) * a) / (x * a) := by positivity
  have hL8 : log ((1 + (1 - x) * a) / (x * a)) = log (1 + (1 - x) * a) - log x - log a := by
    rw [log_div p2.ne' (by positivity), log_mul hx0.ne' ha.ne']; ring
  have e8 : (c * (c * a) / (c + c * a) - (1 - x)) / (c * (c * a) / (c + c * a)) =
      -((1 + (1 - x) * a) / (x * a)) := by
    rw [hc]; field_simp; ring
  have r8 : dilogI ((c * (c * a) / (c + c * a) - (1 - x)) / (c * (c * a) / (c + c * a))) =
      -π ^ 2 / 6 - (log (1 + (1 - x) * a) - log x - log a) ^ 2 / 2 -
        dilogI (-(x * a / (1 + (1 - x) * a))) := by
    rw [e8, i3X_dilogI_neg_eq hX8 hL8, one_div_div]
  have hX9 : 0 < (1 + x * a) * (1 + (1 - x) * a) / (x * (1 - x) * a) := by positivity
  have hL9 : log ((1 + x * a) * (1 + (1 - x) * a) / (x * (1 - x) * a)) =
      log (1 + x * a) + log (1 + (1 - x) * a) - log x - log (1 - x) - log a := by
    rw [log_div hP.ne' (by positivity), log_mul p1.ne' p2.ne', log_mul (by positivity) ha.ne',
      log_mul hx0.ne' hy0.ne']
    ring
  have e9 : (c * (c * a) / (c + c * a) - (1 + c * a)) / (c * (c * a) / (c + c * a)) =
      -((1 + x * a) * (1 + (1 - x) * a) / (x * (1 - x) * a)) := by
    rw [hPc, ← hc]; field_simp; ring
  have r9 : dilogI ((c * (c * a) / (c + c * a) - (1 + c * a)) / (c * (c * a) / (c + c * a))) =
      -π ^ 2 / 6 -
        (log (1 + x * a) + log (1 + (1 - x) * a) - log x - log (1 - x) - log a) ^ 2 / 2 -
        dilogI (-(x * (1 - x) * a / ((1 + x * a) * (1 + (1 - x) * a)))) := by
    rw [e9, i3X_dilogI_neg_eq hX9 hL9, one_div_div]
  have r10 : log (c + c * a) - log (c + c * a + (c * a) ^ 2) =
      log (1 + a) - log (1 + x * a) - log (1 + (1 - x) * a) := by
    rw [show log (1 + a) - log (1 + x * a) - log (1 + (1 - x) * a) =
      log (1 + a) - (log (1 + x * a) + log (1 + (1 - x) * a)) by ring,
      ← log_div (by positivity) (by positivity), ← log_mul p1.ne' p2.ne',
      ← log_div p3.ne' hP.ne']
    congr 1; rw [hPc]; field_simp
  have r11 : c * (c * a) / (c + c * a) / (c * a) = 1 / (1 + a) := by field_simp
  have r12 : c * (c * a) / (c + c * a) / c = a / (1 + a) := by field_simp
  have w1 : c / (c * a) / (c / (c * a) + (1 + c * a)) =
      1 / ((1 + x * a) * (1 + (1 - x) * a)) := by rw [hPc]; field_simp; ring
  have w2 : c / (c * a) / (c / (c * a) + c * (c * a) / (c + c * a)) =
      (1 + a) / ((1 + x * a) * (1 + (1 - x) * a)) := by rw [hPc]; field_simp
  have w3 : c / (c * a) / (c / (c * a) + x) = 1 / (1 + x * a) := by rw [hc]; field_simp
  have w4 : c / (c * a) / (c / (c * a) + (1 - x)) = 1 / (1 + (1 - x) * a) := by
    rw [hc]; field_simp
  rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, w1, w2, w3, w4]
  simp only [i3XH]
  field_simp
  ring

/-- **The `x`-derivative of the clean form**: `∂ₓ H = (1 - 2x) N(x α, y α)/(c Π)`. -/
theorem hasDerivAt_i3XH {x a : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    HasDerivAt (fun x => i3XH x a) ((1 - 2 * x) * i3XN (x * a) ((1 - x) * a) /
      (x * (1 - x) * ((1 + x * a) * (1 + (1 - x) * a)))) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hy0 : 0 < 1 - x := by linarith
  have p1 : 0 < 1 + x * a := by positivity
  have p2 : 0 < 1 + (1 - x) * a := by positivity
  have p3 : 0 < 1 + a := by positivity
  have pc : 0 < 1 + x * (1 - x) * a := by positivity
  have hP : 0 < (1 + x * a) * (1 + (1 - x) * a) := by positivity
  have hPc : (1 + x * a) * (1 + (1 - x) * a) = 1 + a + x * (1 - x) * a ^ 2 := by ring
  have hlt : 1 + a < (1 + x * a) * (1 + (1 - x) * a) := by
    rw [hPc]; have : 0 < x * (1 - x) * a ^ 2 := by positivity
    linarith
  -- letters
  have e5 : HasDerivAt (fun x => 1 + x * a) a x := by
    simpa using ((hasDerivAt_id' x).mul_const a).const_add 1
  have e6 : HasDerivAt (fun x => 1 + (1 - x) * a) (-a) x := by
    simpa using (((hasDerivAt_id' x).const_sub 1).mul_const a).const_add 1
  have lx : HasDerivAt (fun x => log x) x⁻¹ x := hasDerivAt_log hx0.ne'
  have ly := ((hasDerivAt_id' x).const_sub 1).log hy0.ne'
  have l5 := e5.log p1.ne'
  have l6 := e6.log p2.ne'
  have la := hasDerivAt_const x (log a)
  have l1 := hasDerivAt_const x (log (1 + a))
  -- dilogarithm arguments
  have f1 : HasDerivAt (fun x => -((1 - x) * a / (1 + x * a))) (a * (1 + a) / (1 + x * a) ^ 2)
      x := by
    refine ((((hasDerivAt_id' x).const_sub 1).mul_const a).div e5 p1.ne').neg.congr_deriv ?_
    field_simp; ring
  have f2 : HasDerivAt (fun x => -(x * a / (1 + (1 - x) * a)))
      (-(a * (1 + a)) / (1 + (1 - x) * a) ^ 2) x := by
    refine (((hasDerivAt_id' x).mul_const a).div e6 p2.ne').neg.congr_deriv ?_
    field_simp; ring
  have f3 : HasDerivAt (fun x => -(x * (1 - x) * a / ((1 + x * a) * (1 + (1 - x) * a))))
      (-(a * (1 - 2 * x) * (1 + a)) / ((1 + x * a) * (1 + (1 - x) * a)) ^ 2) x := by
    refine ((((hasDerivAt_id' x).mul ((hasDerivAt_id' x).const_sub 1)).mul_const a).div
      (e5.mul e6) hP.ne').neg.congr_deriv ?_
    simp only [Pi.mul_apply]
    field_simp; ring
  have f4 : HasDerivAt (fun x => 1 / (1 + x * a)) (-a / (1 + x * a) ^ 2) x := by
    refine ((hasDerivAt_const x (1 : ℝ)).div e5 p1.ne').congr_deriv ?_
    field_simp; ring
  have f5 : HasDerivAt (fun x => 1 / (1 + (1 - x) * a)) (a / (1 + (1 - x) * a) ^ 2) x := by
    refine ((hasDerivAt_const x (1 : ℝ)).div e6 p2.ne').congr_deriv ?_
    field_simp; ring
  have f6 : HasDerivAt (fun x => 1 / ((1 + x * a) * (1 + (1 - x) * a)))
      (-(a ^ 2 * (1 - 2 * x)) / ((1 + x * a) * (1 + (1 - x) * a)) ^ 2) x := by
    refine ((hasDerivAt_const x (1 : ℝ)).div (e5.mul e6) hP.ne').congr_deriv ?_
    simp only [Pi.mul_apply]
    field_simp; ring
  have f7 : HasDerivAt (fun x => (1 + a) / ((1 + x * a) * (1 + (1 - x) * a)))
      (-((1 + a) * a ^ 2 * (1 - 2 * x)) / ((1 + x * a) * (1 + (1 - x) * a)) ^ 2) x := by
    refine ((hasDerivAt_const x (1 + a)).div (e5.mul e6) hP.ne').congr_deriv ?_
    simp only [Pi.mul_apply]
    field_simp; ring
  have g1 := i3X_hasDerivAt_dilogI f1
    (by have : 0 < (1 - x) * a / (1 + x * a) := by positivity
        linarith)
    (neg_ne_zero.2 (by positivity))
    (show log (1 - -((1 - x) * a / (1 + x * a))) = log (1 + a) - log (1 + x * a) by
      rw [← log_div p3.ne' p1.ne']; congr 1; field_simp; ring)
  have g2 := i3X_hasDerivAt_dilogI f2
    (by have : 0 < x * a / (1 + (1 - x) * a) := by positivity
        linarith)
    (neg_ne_zero.2 (by positivity))
    (show log (1 - -(x * a / (1 + (1 - x) * a))) = log (1 + a) - log (1 + (1 - x) * a) by
      rw [← log_div p3.ne' p2.ne']; congr 1; field_simp; ring)
  have g3 := i3X_hasDerivAt_dilogI f3
    (by have : 0 < x * (1 - x) * a / ((1 + x * a) * (1 + (1 - x) * a)) := by positivity
        linarith)
    (neg_ne_zero.2 (by positivity))
    (show log (1 - -(x * (1 - x) * a / ((1 + x * a) * (1 + (1 - x) * a)))) =
        log (1 + a) + log (1 + x * (1 - x) * a) - log (1 + x * a) - log (1 + (1 - x) * a) by
      rw [← log_mul p3.ne' pc.ne', show log ((1 + a) * (1 + x * (1 - x) * a)) - log (1 + x * a) -
        log (1 + (1 - x) * a) = log ((1 + a) * (1 + x * (1 - x) * a)) -
          (log (1 + x * a) + log (1 + (1 - x) * a)) by ring, ← log_mul p1.ne' p2.ne',
        ← log_div (by positivity) hP.ne']
      congr 1; field_simp; ring)
  have g4 := i3X_hasDerivAt_dilogI f4
    (by rw [div_lt_one p1]; nlinarith) (by positivity)
    (show log (1 - 1 / (1 + x * a)) = log x + log a - log (1 + x * a) by
      rw [← log_mul hx0.ne' ha.ne', ← log_div (by positivity) p1.ne']; congr 1; field_simp; ring)
  have g5 := i3X_hasDerivAt_dilogI f5
    (by rw [div_lt_one p2]; nlinarith) (by positivity)
    (show log (1 - 1 / (1 + (1 - x) * a)) = log (1 - x) + log a - log (1 + (1 - x) * a) by
      rw [← log_mul hy0.ne' ha.ne', ← log_div (by positivity) p2.ne']; congr 1; field_simp; ring)
  have g6 := i3X_hasDerivAt_dilogI f6
    (by rw [div_lt_one hP]; linarith) (by positivity)
    (show log (1 - 1 / ((1 + x * a) * (1 + (1 - x) * a))) =
        log a + log (1 + x * (1 - x) * a) - log (1 + x * a) - log (1 + (1 - x) * a) by
      rw [← log_mul ha.ne' pc.ne', show log (a * (1 + x * (1 - x) * a)) - log (1 + x * a) -
        log (1 + (1 - x) * a) = log (a * (1 + x * (1 - x) * a)) -
          (log (1 + x * a) + log (1 + (1 - x) * a)) by ring, ← log_mul p1.ne' p2.ne',
        ← log_div (by positivity) hP.ne']
      congr 1; field_simp; ring)
  have g7 := i3X_hasDerivAt_dilogI f7
    (by rw [div_lt_one hP]; linarith) (by positivity)
    (show log (1 - (1 + a) / ((1 + x * a) * (1 + (1 - x) * a))) =
        log x + log (1 - x) + 2 * log a - log (1 + x * a) - log (1 + (1 - x) * a) by
      rw [show log x + log (1 - x) + 2 * log a - log (1 + x * a) - log (1 + (1 - x) * a) =
        log (x * (1 - x) * a ^ 2) - (log (1 + x * a) + log (1 + (1 - x) * a)) by
          rw [log_mul (by positivity) (by positivity), log_mul hx0.ne' hy0.ne', log_pow]; ring,
        ← log_mul p1.ne' p2.ne', ← log_div (by positivity) hP.ne']
      congr 1; field_simp; ring)
  have dC := hasDerivAt_const x (dilogI (-(1 / a)))
  have t1 := (hasDerivAt_const x (π ^ 2 / 6)).sub (lx.mul ly)
  have t2 := (((((l5.add l6).sub la).pow 2).add ((((l5.add l6).sub la).sub l1).pow 2)).sub
    ((l5.sub la).pow 2) |>.sub ((l6.sub la).pow 2)).div_const 2
  have t3 := ((((lx.add ly).add la).sub l1).pow 2).div_const 2
  have t4 := (((((dC.add (hasDerivAt_const x (2 * (π ^ 2 / 6)))).add
    ((((l5.sub ly).sub la).pow 2).div_const 2)).add
    ((((l6.sub lx).sub la).pow 2).div_const 2)).add g1).add g2).div_const (1 + a)
  have t5 := (((hasDerivAt_const x (-(π ^ 2 / 6))).sub
    ((((((l5.add l6).sub lx).sub ly).sub la).pow 2).div_const 2)).sub g3).const_mul (a / (1 + a))
  have t6 := ((l1.sub l5).sub l6).mul (((lx.add ly).add la).sub l1)
  have t7 := ((g4.add g5).sub g6).sub g7
  have key := (((((t1.add t2).add t3).sub t4).add t5).add t6).sub t7
  refine key.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [i3XN_xa ⟨hx0, hx1⟩ ha]
  generalize log x = A1
  generalize log (1 - x) = A2
  generalize log a = A3
  generalize log (1 + a) = A4
  generalize log (1 + x * a) = A5
  generalize log (1 + (1 - x) * a) = A6
  generalize log (1 + x * (1 - x) * a) = A7
  have := hx0.ne'; have := hy0.ne'; have := ha.ne'; have := p1.ne'; have := p2.ne'
  have := p3.ne'
  field_simp
  ring

/-! ### Symmetry and the boundary value at `x = 0` -/

theorem i3XH_symm (x a : ℝ) : i3XH (1 - x) a = i3XH x a := by
  simp only [i3XH, sub_sub_cancel]
  rw [show (1 - x) * x * a = x * (1 - x) * a by ring,
    show (1 + (1 - x) * a) * (1 + x * a) = (1 + x * a) * (1 + (1 - x) * a) by ring]
  ring

theorem i3XH_zero {a : ℝ} (ha : 0 < a) : i3XH 0 a = 0 := by
  have hinv := i3E_dilogI_inv ha
  have h1 : (1 + a) / ((1 + 0 * a) * (1 + (1 - 0) * a)) = 1 := by
    rw [zero_mul, add_zero, one_mul, sub_zero, one_mul]; exact div_self (by positivity)
  simp only [i3XH, h1]
  simp only [log_zero, zero_mul, mul_zero, add_zero, sub_zero, one_mul, log_one, zero_div,
    neg_zero, dilogI_zero, div_one, zero_sub, sub_self]
  have h2 : dilogI (-(1 / a)) = -π ^ 2 / 6 - log a ^ 2 / 2 - dilogI (-a) := by linarith
  rw [h2]
  field_simp
  ring

/-- The part of `H` free of `log x` and of the two dilogarithms with argument tending to `1`. -/
noncomputable def i3XHQ (x a : ℝ) : ℝ :=

  π ^ 2 / 6 - 0 +
    ((log (1 + x * a) + log (1 + (1 - x) * a) - log a) ^ 2 +
      (log (1 + x * a) + log (1 + (1 - x) * a) - log a - log (1 + a)) ^ 2 -
      (log (1 + x * a) - log a) ^ 2 - (log (1 + (1 - x) * a) - log a) ^ 2) / 2 +
    (log (1 - x) + log a - log (1 + a)) ^ 2 / 2 -
    (dilogI (-(1 / a)) + 2 * (π ^ 2 / 6) + (log (1 + x * a) - log (1 - x) - log a) ^ 2 / 2 +
      (log (1 + (1 - x) * a) - log a) ^ 2 / 2 +
      dilogI (-((1 - x) * a / (1 + x * a))) + dilogI (-(x * a / (1 + (1 - x) * a)))) / (1 + a) +
    a / (1 + a) * (-(π ^ 2 / 6) -
      (log (1 + x * a) + log (1 + (1 - x) * a) - log (1 - x) - log a) ^ 2 / 2 -
      dilogI (-(x * (1 - x) * a / ((1 + x * a) * (1 + (1 - x) * a))))) +
    (log (1 + a) - log (1 + x * a) - log (1 + (1 - x) * a)) *
      (log (1 - x) + log a - log (1 + a)) -
    (dilogI (1 / (1 + (1 - x) * a)) - dilogI (1 / ((1 + x * a) * (1 + (1 - x) * a))))



theorem i3XH_split (x : ℝ) {a : ℝ} (ha : 0 < a) :
    i3XH x a = log x * (-(a * log (1 - x) + log (1 + x * a)) / (1 + a)) +
    i3XHQ x a - (dilogI (1 / (1 + x * a)) -
      dilogI ((1 + a) / ((1 + x * a) * (1 + (1 - x) * a)))) := by
  have : 1 + a ≠ 0 := by positivity
  simp only [i3XH, i3XHQ]
  field_simp
  ring

theorem i3X_tendsto_dilogI_one {f : ℝ → ℝ} (hf : Tendsto f (𝓝[>] 0) (𝓝 1))
    (hlt : ∀ᶠ x in 𝓝[>] (0 : ℝ), f x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => dilogI (f x)) (𝓝[>] 0) (𝓝 (QED.Polylog.Li₂ 1)) := by
  have hf' : Tendsto f (𝓝[>] 0) (𝓝[Icc (-1) 1] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨hf, hlt.mono fun x hx => ⟨by linarith [hx.1], hx.2.le⟩⟩
  have := ((QED.Polylog.continuousOn_Li₂ 1 (by norm_num)).tendsto).comp hf'
  refine this.congr' ?_
  filter_upwards [hlt] with x hx
  exact (dilogI_eq_Li₂ ⟨by linarith [hx.1], hx.2⟩).symm

theorem tendsto_i3XH_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x => i3XH x a) (𝓝[>] 0) (𝓝 0) := by
  have hc : ∀ {f : ℝ → ℝ}, ContinuousAt f 0 → f 0 < 1 →
      ContinuousAt (fun x => dilogI (f x)) 0 := fun hf h =>
    (hasDerivAt_dilogI h).continuousAt.comp (f := _) hf
  have c1 : ContinuousAt (fun x : ℝ => log (1 - x)) 0 :=
    (continuousAt_const.sub continuousAt_id).log (by norm_num)
  have c2 : ContinuousAt (fun x : ℝ => log (1 + x * a)) 0 :=
    (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).log (by norm_num)
  have c3 : ContinuousAt (fun x : ℝ => log (1 + (1 - x) * a)) 0 :=
    (continuousAt_const.add ((continuousAt_const.sub continuousAt_id).mul
      continuousAt_const)).log (by norm_num; positivity)
  have d1 : ContinuousAt (fun x : ℝ => dilogI (-((1 - x) * a / (1 + x * a)))) 0 :=
    hc (by fun_prop (disch := norm_num)) (by norm_num; linarith)
  have d2 : ContinuousAt (fun x : ℝ => dilogI (-(x * a / (1 + (1 - x) * a)))) 0 :=
    hc (by fun_prop (disch := (norm_num; positivity))) (by norm_num)
  have d3 : ContinuousAt (fun x : ℝ =>
      dilogI (-(x * (1 - x) * a / ((1 + x * a) * (1 + (1 - x) * a))))) 0 :=
    hc (by fun_prop (disch := (norm_num; positivity))) (by norm_num)
  have d4 : ContinuousAt (fun x : ℝ => dilogI (1 / (1 + (1 - x) * a))) 0 :=
    hc (by fun_prop (disch := (norm_num; positivity)))
      (by norm_num; exact inv_lt_one_of_one_lt₀ (by linarith))
  have d5 : ContinuousAt (fun x : ℝ => dilogI (1 / ((1 + x * a) * (1 + (1 - x) * a)))) 0 :=
    hc (by fun_prop (disch := (norm_num; positivity)))
      (by norm_num; exact inv_lt_one_of_one_lt₀ (by linarith))
  have hQ : ContinuousAt (fun x => i3XHQ x a) 0 := by
    simp only [i3XHQ]
    fun_prop (disch := (norm_num; try positivity))
  have hR : Tendsto (fun x => log x * (-(a * log (1 - x) + log (1 + x * a)) / (1 + a)))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 := i3X_tendsto_log_one_sub_mul_log
    have h2 : Tendsto (fun x : ℝ => log (1 + x * a) * log x) (𝓝[>] 0) (𝓝 0) := by
      have hm0 : Tendsto (fun x : ℝ => x * log x) (𝓝[>] 0) (𝓝 0) := by
        simpa using (continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      have hm := (hm0.abs).const_mul a
      simp only [mul_zero, abs_zero] at hm
      refine squeeze_zero_norm' ?_ hm
      filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      rw [Real.norm_eq_abs, abs_mul (log (1 + x * a))]
      have := QED.Polylog.abs_log_one_add_le (show 0 ≤ x * a by positivity)
      calc |log (1 + x * a)| * |log x| ≤ x * a * |log x| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = a * |x * log x| := by rw [abs_mul, abs_of_pos hx]; ring
    have := ((h1.const_mul a).add h2).neg.div_const (1 + a)
    simp only [mul_zero, add_zero, neg_zero, zero_div] at this
    refine this.congr' (Eventually.of_forall fun x => ?_)
    ring
  have hP1 : Tendsto (fun x : ℝ => 1 + x * a) (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun x : ℝ => 1 + x * a) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hPP : Tendsto (fun x : ℝ => (1 + x * a) * (1 + (1 - x) * a)) (𝓝[>] 0) (𝓝 (1 + a)) := by
    have hc : ContinuousAt (fun x : ℝ => (1 + x * a) * (1 + (1 - x) * a)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hI : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  have w1 := i3X_tendsto_dilogI_one (f := fun x => 1 / (1 + x * a))
    (by simpa using hP1.inv₀ (by norm_num))
    (by filter_upwards [hI] with x hx
        have : 0 < x * a := mul_pos hx.1 ha
        exact ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩)
  have w2 := i3X_tendsto_dilogI_one (f := fun x => (1 + a) / ((1 + x * a) * (1 + (1 - x) * a)))
    (by have := (tendsto_const_nhds (x := 1 + a)).div hPP (by positivity)
        rwa [div_self (show (1 + a) ≠ 0 by positivity)] at this)
    (by filter_upwards [hI] with x hx
        have hy : 0 < 1 - x := by linarith [hx.2]
        have : 0 < x * (1 - x) * a ^ 2 := mul_pos (mul_pos hx.1 hy) (pow_pos ha 2)
        have hp1 : 0 < 1 + x * a := by nlinarith [mul_pos hx.1 ha]
        have hp2 : 0 < 1 + (1 - x) * a := by nlinarith [mul_pos hy ha]
        refine ⟨div_pos (by linarith) (mul_pos hp1 hp2), ?_⟩
        rw [div_lt_one (mul_pos hp1 hp2)]; nlinarith)
  have hQ0 : i3XHQ 0 a = 0 := by
    have := i3XH_split 0 ha
    rw [i3XH_zero ha, log_zero, zero_mul, zero_add] at this
    have e : dilogI (1 / (1 + 0 * a)) - dilogI ((1 + a) / ((1 + 0 * a) * (1 + (1 - 0) * a))) =
        0 := by
      rw [zero_mul, add_zero, one_mul, sub_zero, one_mul, div_self (by positivity : (1 + a) ≠ 0),
        div_one, sub_self]
    linarith
  have := (hR.add (hQ.tendsto.mono_left nhdsWithin_le_nhds)).sub (w1.sub w2)
  rw [hQ0, sub_self, add_zero, sub_zero] at this
  refine this.congr' (Eventually.of_forall fun x => ?_)
  show _ = i3XH x a
  rw [i3XH_split x ha]

end QED.ThreeLoopD
