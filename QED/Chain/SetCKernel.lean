/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.VPChainPiHat
public import QED.Polylog.LiN
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Set (c): the space-like kernel and the integrand in atoms

Helper analysis for the sixth-order set (c) of `docs/HIGHER-LOOP-PLAN.md` (the second-order
vacuum-polarization insertion into the photon lines of the fourth-order vertex graphs). It is
**not** frozen.

## Source

E. Balzani, S. Laporta, M. Passera, *Hadronic vacuum polarization contributions to the muon g-2
in the space-like region*, Phys. Lett. B 834 (2022) 137462, arXiv:2112.05704v3
(`sources/cache/balzani-laporta-passera-2022.pdf`). Class (4a) of that paper is one vacuum
polarization (VP) insertion into a photon line of the two-loop vertex graphs; with the inserted
VP the one-loop electron VP and the external lepton the electron, it is set (c), up to the chain
graphs described below. In units of `(α/π)³`, with `t(x) = m² x²/(x-1)` (eq. (13)):

* eq. (21), (22): `F⁽⁴⁾(u) = R₁ + R₂ ln(-u) + R₃ ln(1+u) + R₄ ln(1-u)
  + R₅ [4 Li₂(u) + 2 Li₂(-u) + ln(-u) ln((1-u)²(1+u))]`, the imaginary part of the
  Barbieri–Remiddi fourth-order kernel `K⁽⁴⁾` on its cut (eq. (20)), here for `-1 < u < 0`;
* eq. (24): `κ⁽⁴⁾(x) = (2-x)/(x(x-1)) · 2 F⁽⁴⁾(x-1)`, so that class (4a) is
  `∫₀¹ κ⁽⁴⁾(x) Δα(t(x)) dx` (eq. (23));
* eq. (38): `λ⁽⁴⁾(x) = κ⁽⁴⁾(x) - 2 κ⁽²⁾(x) Δα_ℓ(t(x))` with `κ⁽²⁾(x) = 1 - x` (eq. (15)) and
  `Δα_ℓ` the one-loop VP of the external lepton, in units of `α/π`.

**The chain subtraction.** Class (4a) also contains the two graphs in which the inserted VP and
the external lepton's own one-loop VP sit in series on the photon line of the one-loop vertex
(the two orders of the two bubbles). With an inserted VP `Δα` they contribute
`2 ∫₀¹ κ⁽²⁾(x) Δα_ℓ(t(x)) Δα(t(x)) dx`, which eq. (38) removes. When the inserted VP is itself
the electron loop these are the set (b) chain counted twice, so set (c) is
`∫₀¹ λ⁽⁴⁾(x) Δα(t(x)) dx`; numerically the unsubtracted integral is `A_(c) + 2 A_(b)`.

`Δα(t(x))` is the renormalized one-loop VP at the Euclidean point `x²/(1-x)`, the repository's
`QED.Chain.piHat (x ^ 2 / (1 - x))` (`QED.Chain.piHat_photonVar` gives its closed form).

## Contents

* `setCF4`, `setCKappa`, `setCDeltaAlpha`, `setCLambda`: the literal kernel.
* `setCJ`: the integrand `λ⁽⁴⁾(1-s) Δα(1-s)` in the atoms
  `log s, log (1 - s), log (1 + s), Li 2 s, Li 2 (-s)` (`setCJ_eq`).
* `intervalIntegrable_setC_of_setCJ`, `integral_setC_eq_setCJ`: the substitution `x = 1 - s`.
-/

@[expose] public section

open Real Set MeasureTheory QED.Polylog

namespace QED.Chain

/-- `R₁(u)` of Balzani–Laporta–Passera 2022, eq. (22). -/
noncomputable def setCR1 (u : ℝ) : ℝ :=
  (23 * u ^ 6 - 37 * u ^ 5 + 124 * u ^ 4 - 86 * u ^ 3 - 57 * u ^ 2 + 99 * u + 78) /
    (72 * (u - 1) ^ 2 * u * (u + 1))

/-- `R₂(u)` of eq. (22). -/
noncomputable def setCR2 (u : ℝ) : ℝ :=
  (12 * u ^ 8 - 11 * u ^ 7 - 78 * u ^ 6 + 21 * u ^ 5 + 4 * u ^ 4 - 15 * u ^ 3 + 13 * u + 6) /
    (12 * (u - 1) ^ 3 * u * (u + 1) ^ 2)

/-- `R₃(u)` of eq. (22). -/
noncomputable def setCR3 (u : ℝ) : ℝ :=
  (u + 1) * (-u ^ 3 + 7 * u ^ 2 + 8 * u + 6) / (12 * u ^ 2)

/-- `R₄(u)` of eq. (22). -/
noncomputable def setCR4 (u : ℝ) : ℝ :=
  (-7 * u ^ 4 - 8 * u ^ 3 + 8 * u + 7) / (12 * u ^ 2)

/-- `R₅(u)` of eq. (22). -/
noncomputable def setCR5 (u : ℝ) : ℝ :=
  -(3 * u ^ 4 + 5 * u ^ 3 + 7 * u ^ 2 + 5 * u + 3) / (6 * u ^ 2)

/-- `F⁽⁴⁾(u)` of eq. (21) (`Im K⁽⁴⁾/π` on the cut, eq. (20)); used for `-1 < u < 0`. -/
noncomputable def setCF4 (u : ℝ) : ℝ :=
  setCR1 u + setCR2 u * log (-u) + setCR3 u * log (1 + u) + setCR4 u * log (1 - u) +
    setCR5 u * (4 * Li 2 u + 2 * Li 2 (-u) + log (-u) * log ((1 - u) ^ 2 * (1 + u)))

/-- The space-like class-(4a) kernel `κ⁽⁴⁾(x) = (2-x)/(x(x-1)) · 2F⁽⁴⁾(x-1)`, eq. (24). -/
noncomputable def setCKappa (x : ℝ) : ℝ :=
  (2 - x) / (x * (x - 1)) * (2 * setCF4 (x - 1))

/-- The one-loop VP `Δα(t(x))` in units of `α/π`: `Π̂` at the Euclidean point `x²/(1-x)`. -/
noncomputable def setCDeltaAlpha (x : ℝ) : ℝ :=
  piHat (x ^ 2 / (1 - x))

/-- The chain-subtracted kernel `λ⁽⁴⁾(x) = κ⁽⁴⁾(x) - 2 (1-x) Δα(t(x))`, eq. (38) with the
external lepton's VP equal to the inserted one. -/
noncomputable def setCLambda (x : ℝ) : ℝ :=
  setCKappa x - 2 * (1 - x) * setCDeltaAlpha x

namespace SetCKernel

/-- Coefficient of the monomial `21000` of `setCJ`. -/
noncomputable def j21000 (x : ℝ) : ℝ :=
  (-3 + 11 * x + x ^ 2 - 5 * x ^ 3 + 16 * x ^ 4 - 5 * x ^ 5 + x ^ 6 + 11 * x ^ 7 - 3 * x ^ 8) /
      (9 * x ^ 3 * (1 - x) ^ 4)

/-- Coefficient of the monomial `20100` of `setCJ`. -/
noncomputable def j20100 (x : ℝ) : ℝ :=
  (-6 + 22 * x + 2 * x ^ 2 - 10 * x ^ 3 + 32 * x ^ 4 - 10 * x ^ 5 + 2 * x ^ 6 + 22 * x ^ 7 - 6
      * x ^ 8) / (9 * x ^ 3 * (1 - x) ^ 4)

/-- Coefficient of the monomial `20000` of `setCJ`. -/
noncomputable def j20000 (x : ℝ) : ℝ :=
  (6 - 25 * x + 2 * x ^ 2 + 27 * x ^ 3 + 16 * x ^ 4 - 5 * x ^ 5 - 108 * x ^ 6 - x ^ 7 + 8
      * x ^ 8) / (18 * x ^ 2 * (1 + x) * (1 - x) ^ 4)

/-- Coefficient of the monomial `11000` of `setCJ`. -/
noncomputable def j11000 (x : ℝ) : ℝ :=
  (-12 + 68 * x - 29 * x ^ 2 + 31 * x ^ 3 + 113 * x ^ 4 - 27 * x ^ 5) / (54 * x ^ 3 * (1 - x))

/-- Coefficient of the monomial `10100` of `setCJ`. -/
noncomputable def j10100 (x : ℝ) : ℝ :=
  (-39 + 181 * x + 2 * x ^ 2 + 2 * x ^ 3 + 181 * x ^ 4 - 39 * x ^ 5) / (54 * x ^ 3 * (1 - x))

/-- Coefficient of the monomial `10010` of `setCJ`. -/
noncomputable def j10010 (x : ℝ) : ℝ :=
  (-6 + 22 * x + 2 * x ^ 2 - 10 * x ^ 3 + 32 * x ^ 4 - 10 * x ^ 5 + 2 * x ^ 6 + 22 * x ^ 7 - 6
      * x ^ 8) / (9 * x ^ 3 * (1 - x) ^ 4)

/-- Coefficient of the monomial `10001` of `setCJ`. -/
noncomputable def j10001 (x : ℝ) : ℝ :=
  (-12 + 44 * x + 4 * x ^ 2 - 20 * x ^ 3 + 64 * x ^ 4 - 20 * x ^ 5 + 4 * x ^ 6 + 44 * x ^ 7 - 12
      * x ^ 8) / (9 * x ^ 3 * (1 - x) ^ 4)

/-- Coefficient of the monomial `10000` of `setCJ`. -/
noncomputable def j10000 (x : ℝ) : ℝ :=
  (-18 - 175 * x + 627 * x ^ 2 + 731 * x ^ 3 + 77 * x ^ 4 + 107 * x ^ 5 - 751 * x ^ 6 + 57
      * x ^ 7 + 17 * x ^ 8) / (108 * x ^ 2 * (1 + x) ^ 2 * (1 - x) ^ 3)

/-- Coefficient of the monomial `01000` of `setCJ`. -/
noncomputable def j01000 (x : ℝ) : ℝ :=
  (30 - 142 * x + 69 * x ^ 2 + 52 * x ^ 3 - 176 * x ^ 4 + 18 * x ^ 5 + 5 * x ^ 6) / (54 * x ^ 3 *
      (1 - x) ^ 2)

/-- Coefficient of the monomial `00100` of `setCJ`. -/
noncomputable def j00100 (x : ℝ) : ℝ :=
  (35 - 124 * x - 107 * x ^ 2 + 104 * x ^ 3 - 107 * x ^ 4 - 124 * x ^ 5 + 35 * x ^ 6) / (54
      * x ^ 3 * (1 - x) ^ 2)

/-- Coefficient of the monomial `00010` of `setCJ`. -/
noncomputable def j00010 (x : ℝ) : ℝ :=
  (-30 + 152 * x - 138 * x ^ 2 + 88 * x ^ 3 + 88 * x ^ 4 - 138 * x ^ 5 + 152 * x ^ 6 - 30
      * x ^ 7) / (27 * x ^ 3 * (1 - x) ^ 3)

/-- Coefficient of the monomial `00001` of `setCJ`. -/
noncomputable def j00001 (x : ℝ) : ℝ :=
  (-60 + 304 * x - 276 * x ^ 2 + 176 * x ^ 3 + 176 * x ^ 4 - 276 * x ^ 5 + 304 * x ^ 6 - 60
      * x ^ 7) / (27 * x ^ 3 * (1 - x) ^ 3)

/-- Coefficient of the monomial `00000` of `setCJ`. -/
noncomputable def j00000 (x : ℝ) : ℝ :=
  (-130 + 477 * x + 323 * x ^ 2 - 294 * x ^ 3 + 128 * x ^ 4 + 417 * x ^ 5 - 105 * x ^ 6) / (108
      * x ^ 2 * (1 + x) * (1 - x) ^ 2)

end SetCKernel

open SetCKernel

/-- **The set (c) integrand in `s = 1 - x`**, in the atoms
`log s, log (1 - s), log (1 + s), Li 2 s, Li 2 (-s)` (exponents in the coefficient names). -/
noncomputable def setCJ (x : ℝ) : ℝ :=
  j21000 x * (log x ^ 2 * log (1 - x)) +
    j20100 x * (log x ^ 2 * log (1 + x)) +
    j20000 x * (log x ^ 2) +
    j11000 x * (log x * log (1 - x)) +
    j10100 x * (log x * log (1 + x)) +
    j10010 x * (log x * Li 2 x) +
    j10001 x * (log x * Li 2 (-x)) +
    j10000 x * (log x) +
    j01000 x * (log (1 - x)) +
    j00100 x * (log (1 + x)) +
    j00010 x * (Li 2 x) +
    j00001 x * (Li 2 (-x)) +
    j00000 x


/-- The set (c) integrand at `x = 1 - s` in atoms, for `0 < s < 1`. -/
theorem setCJ_eq {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    setCLambda (1 - s) * setCDeltaAlpha (1 - s) = setCJ s := by
  obtain ⟨h0, h1⟩ := hs
  have hx : 1 - s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hz : s ≠ 0 := h0.ne'
  have hm : 1 - s ≠ 0 := by linarith
  have hp : 1 + s ≠ 0 := by linarith
  have hm' : 0 < 1 - s := by linarith
  have hp' : 0 < 1 + s := by linarith
  have hn : -s ≠ 0 := neg_ne_zero.2 hz
  have hn1 : -s - 1 ≠ 0 := by linarith
  have hn2 : -s + 1 ≠ 0 := by linarith
  have eu : 1 - s - 1 = -s := by ring
  have e1 : 1 - (1 - s) = s := by ring
  have l1 : log ((1 - -s) ^ 2 * (1 + -s)) = 2 * log (1 + s) + log (1 - s) := by
    rw [sub_neg_eq_add, ← sub_eq_add_neg, log_mul (by positivity) hm, log_pow]
    push_cast; ring
  unfold setCLambda setCDeltaAlpha setCKappa setCF4
  rw [piHat_photonVar hx, eu, l1, neg_neg, ← sub_eq_add_neg]
  unfold piHatX setCR1 setCR2 setCR3 setCR4 setCR5 setCJ
  rw [e1]
  simp only [sub_neg_eq_add]
  generalize log s = A0 at *
  generalize log (1 - s) = A1 at *
  generalize log (1 + s) = A2 at *
  generalize Li 2 s = A3 at *
  generalize Li 2 (-s) = A4 at *
  simp only [j21000, j20100, j20000, j11000, j10100, j10010, j10001, j10000, j01000, j00100,
    j00010, j00001, j00000]
  field_simp
  ring

/-- The substitution `x = 1 - s` transfers integrability. -/
theorem intervalIntegrable_setC_of_setCJ (h : IntervalIntegrable setCJ volume 0 1) :
    IntervalIntegrable (fun x => setCLambda x * setCDeltaAlpha x) volume 0 1 := by
  have h1 : IntervalIntegrable (fun s => setCLambda (1 - s) * setCDeltaAlpha (1 - s))
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h ⊢
    exact h.congr_fun (fun s hs => (setCJ_eq hs).symm) measurableSet_Ioo
  have h2 := h1.comp_sub_left 1
  simp only [sub_sub_cancel, sub_zero, sub_self] at h2
  exact h2.symm

/-- **The set (c) integral in the variable `s = 1 - x`.** -/
theorem integral_setC_eq_setCJ :
    ∫ x in (0 : ℝ)..1, setCLambda x * setCDeltaAlpha x = ∫ s in (0 : ℝ)..1, setCJ s := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun x => setCLambda x * setCDeltaAlpha x) (a := 0) (b := 1) (1 : ℝ)
  simp only [sub_zero, sub_self] at h
  rw [← h, intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le
    zero_le_one, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun s hs => setCJ_eq hs

end QED.Chain
