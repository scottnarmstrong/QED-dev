/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemA1
public import QED.ThreeLoopD.SetDMastersI9RemA2Fub

/-!
# Set (d), master `I₉`: the density of `∫ F₂` in the variables `(p, s)`

`QED.ThreeLoopD.integral_i9RemF2_eq` writes `∫ F₂` as the integral over the `(x, w)`-square of
`QED.ThreeLoopD.i9A2Dens`. Split off the part `-12 log (1 - w) Y₁/(c w)`
(`= 4 log (1 - w) · QED.ThreeLoopD.i9A1Dens`), whose `(p, s)`-form contains `log M`,
`M = p + s² (1 - p)`. The rest, `Dens' = i9A2Dens + 4 log (1 - w) i9A1Dens`, is

  `Dens' = |det Ψ'| · Θ ∘ Ψ`,
  `Θ(p, s) = k(s, p) ((-6 log p - 6 log (1 - p) - 3 log (s (1 - s)/E)) g(p) + h(p))`,

in the variables `Ψ(x, w) = (p, s)` of `QED.ThreeLoopD.SetDMastersI9RemA1`, with `k`, `g` from
`QED.ThreeLoopD.SetDMastersI9RemA1Kernel` and `h` an explicit weight-3 function of `p`
(`QED.ThreeLoopD.i9A2h`). Two facts make this work: `(P₀ A + w B)/(c w) = |det Ψ'| k (B/p +
A/(1 - p))` for any `A, B` (the algebra of `QED.ThreeLoopD.i9A1Dens_eq`), and
`s (1 - s)/E = P₁` at `Ψ(x, w)`. The `y`-closed forms are homogeneous: with `P₀ = p P₁`,
`w = (1 - p) P₁`, every logarithm is `log p`, `log (1 - p)`, `log P₁` or `log (1 - w)`.

## Main results

* `QED.ThreeLoopD.i9A2_transfer`: the generic transfer identity.
* `QED.ThreeLoopD.i9A2DensP_eq`: `Dens' = |det Ψ'| · Θ ∘ Ψ`.
-/

@[expose] public section

open MeasureTheory Set Real QED.Polylog

namespace QED.ThreeLoopD

/-! ### The weight-3 functions of `p` -/

/-- `A_L = 2F + 4ζ(3) + 2 log p Li₂ (1 - p) + log³ p / 6`, `F = logOneSubSqPrim (1 - p)`. -/
noncomputable def i9A2AL (p : ℝ) : ℝ :=
  2 * logOneSubSqPrim (1 - p) + 4 * zeta3 + 2 * Real.log p * Li₂ (1 - p) + Real.log p ^ 3 / 6

/-- `B_L = -2ζ(3) + 2 Li₃ (1 - p) + F/2`. -/
noncomputable def i9A2BL (p : ℝ) : ℝ := -2 * zeta3 + 2 * Li₃ (1 - p) + logOneSubSqPrim (1 - p) / 2

/-- `A₂ = 2F + 2/3 log³ p + 2 log p Li₂ (1 - p) + 4 ζ(3)`. -/
noncomputable def i9A2A2 (p : ℝ) : ℝ :=
  2 * logOneSubSqPrim (1 - p) + 2 / 3 * Real.log p ^ 3 + 2 * Real.log p * Li₂ (1 - p) + 4 * zeta3

/-- `B₂ = F + π²/3 log (1 - p)`. -/
noncomputable def i9A2B2 (p : ℝ) : ℝ := logOneSubSqPrim (1 - p) + π ^ 2 / 3 * Real.log (1 - p)

/-- `h(p) = (-3 B_L + 9/2 B₂)/p + (-3 A_L + 9/2 A₂)/(1 - p)`. -/
noncomputable def i9A2h (p : ℝ) : ℝ :=
  (-3 * i9A2BL p + 9 / 2 * i9A2B2 p) / p + (-3 * i9A2AL p + 9 / 2 * i9A2A2 p) / (1 - p)

/-- The coefficient of `P₀` (the `a`-part), with `ℓ = log P₁` as a parameter. -/
noncomputable def i9A2cA (p ℓ : ℝ) : ℝ :=
  (-6 * Real.log p - 6 * Real.log (1 - p) - 3 * ℓ) * (Real.log p ^ 2 / 2) +
    (-3 * i9A2AL p + 9 / 2 * i9A2A2 p)

/-- The coefficient of `w` (the `w`-part), with `ℓ = log P₁` as a parameter. -/
noncomputable def i9A2cB (p ℓ : ℝ) : ℝ :=
  (-6 * Real.log p - 6 * Real.log (1 - p) - 3 * ℓ) * (π ^ 2 / 6 - Li₂ (1 - p)) +
    (-3 * i9A2BL p + 9 / 2 * i9A2B2 p)

/-- **The `(p, s)`-density** `Θ(p, s)` of `Dens'`. -/
noncomputable def i9A2Theta (q : ℝ × ℝ) : ℝ :=
  i9A1k q.2 q.1 * ((-6 * Real.log q.1 - 6 * Real.log (1 - q.1) -
      3 * Real.log (q.2 * (1 - q.2) / (q.2 + q.1 * (1 - q.2)))) * i9A1g q.1 + i9A2h q.1)

/-- `Dens' = i9A2Dens + 4 log (1 - w) i9A1Dens`. -/
noncomputable def i9A2DensP (z : ℝ × ℝ) : ℝ :=
  i9A2Dens z.1 z.2 + 4 * Real.log (1 - z.2) * i9A1Dens z

/-! ### The identities -/

theorem i9A2Theta_eq (p s : ℝ) :
    i9A2Theta (p, s) = i9A1k s p * (i9A2cB p (Real.log (s * (1 - s) / (s + p * (1 - s)))) / p +
      i9A2cA p (Real.log (s * (1 - s) / (s + p * (1 - s)))) / (1 - p)) := by
  simp only [i9A2Theta, i9A1g, i9A2h, i9A2cA, i9A2cB, div_eq_mul_inv, mul_inv]
  ring

/-- **The transfer identity**: `(P₀ A + w B)/(c w) = |det Ψ'| k(s, p) (B/p + A/(1 - p))`. -/
theorem i9A2_transfer {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) (A B : ℝ) :
    (i9Poly z.1 z.2 0 * A + z.2 * B) / (z.1 * (1 - z.1) * z.2) =
      |(i9A1Deriv z).det| * (i9A1k (i9A1Map z).2 (i9A1Map z).1 *
        (B / (i9A1Map z).1 + A / (1 - (i9A1Map z).1))) := by
  rw [abs_det_i9A1Deriv hz]
  have hP := i9A1P_pos hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  obtain ⟨x, w⟩ := z
  simp only at h1 h2 h3 h4
  unfold i9A1P at hP
  have hP' : x * (1 - x) * (1 - w) ^ 2 + w ≠ 0 := hP.ne'
  have ha : 0 < 1 - x * (1 - w) := by nlinarith
  have hu : 0 < 1 - w := by linarith
  have hx1 : 0 < 1 - x := by linarith
  have hN : 0 < x * (1 - x) * (1 - w) ^ 2 := by positivity
  have hE : x * (1 - w) + x * (1 - x) * (1 - w) ^ 2 / (x * (1 - x) * (1 - w) ^ 2 + w) *
      (1 - x * (1 - w)) =
      x * (1 - w) * (1 - x * (1 - w)) / (x * (1 - x) * (1 - w) ^ 2 + w) := by
    field_simp
    ring
  have h1p : 1 - x * (1 - x) * (1 - w) ^ 2 / (x * (1 - x) * (1 - w) ^ 2 + w) =
      w / (x * (1 - x) * (1 - w) ^ 2 + w) := by
    field_simp
    ring
  simp only [i9A1Map, i9A1k, i9Poly, i9A1P, mul_zero, add_zero]
  rw [hE, h1p]
  field_simp
  ring

theorem i9A1Map_fst_eq (z : ℝ × ℝ) :
    (i9A1Map z).1 = i9Poly z.1 z.2 0 / i9Poly z.1 z.2 1 := by
  simp [i9A1Map, i9Poly]

/-- `s (1 - s)/E = P₁` at `Ψ(x, w)`. -/
theorem i9A2_b_eq {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    (i9A1Map z).2 * (1 - (i9A1Map z).2) /
        ((i9A1Map z).2 + (i9A1Map z).1 * (1 - (i9A1Map z).2)) = i9Poly z.1 z.2 1 := by
  have hP := i9A1P_pos hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  obtain ⟨x, w⟩ := z
  simp only at h1 h2 h3 h4
  unfold i9A1P at hP
  have hP' : x * (1 - x) * (1 - w) ^ 2 + w ≠ 0 := hP.ne'
  have ha : 0 < 1 - x * (1 - w) := by nlinarith
  have hu : 0 < 1 - w := by linarith
  simp only [i9A1Map, i9Poly, mul_one]
  field_simp
  ring

/-- **The algebra of `Dens'`**: `Dens' = (P₀ A + w B)/(c w)` with `A = i9A2cA p (log P₁)`,
`B = i9A2cB p (log P₁)`, `p = P₀/P₁`. -/
theorem i9A2DensP_eq_div {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i9A2DensP z = (i9Poly z.1 z.2 0 *
        i9A2cA (i9Poly z.1 z.2 0 / i9Poly z.1 z.2 1) (Real.log (i9Poly z.1 z.2 1)) +
      z.2 * i9A2cB (i9Poly z.1 z.2 0 / i9Poly z.1 z.2 1) (Real.log (i9Poly z.1 z.2 1))) /
        (z.1 * (1 - z.1) * z.2) := by
  obtain ⟨hx, hw⟩ := hz
  obtain ⟨x, w⟩ := z
  simp only at hx hw ⊢
  have hc := i9_c_pos hx
  have hw0 := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have ha := i9Poly_zero_pos hx hw
  have hb : 0 < i9Poly x w 1 := by rw [i9Poly_eq_add x w 1]; positivity
  have e1 : i9Poly x w 0 + w = i9Poly x w 1 := by rw [i9Poly_eq_add x w 1, mul_one]
  have hq : w / i9Poly x w 1 = 1 - i9Poly x w 0 / i9Poly x w 1 := by
    field_simp; linarith
  have hlK : Real.log (i9Poly x w 1 / i9Poly x w 0) =
      -Real.log (i9Poly x w 0 / i9Poly x w 1) := by
    rw [← Real.log_inv, inv_div]
  have hla : Real.log (i9Poly x w 0) =
      Real.log (i9Poly x w 0 / i9Poly x w 1) + Real.log (i9Poly x w 1) := by
    rw [Real.log_div ha.ne' hb.ne']; ring
  have hlw : Real.log w = Real.log (1 - i9Poly x w 0 / i9Poly x w 1) + Real.log (i9Poly x w 1) := by
    rw [← hq, Real.log_div hw0.ne' hb.ne']; ring
  have hlc : Real.log (x * (1 - x)) = Real.log (i9Poly x w 0 / i9Poly x w 1) +
      Real.log (i9Poly x w 1) - 2 * Real.log (1 - w) := by
    rw [← hla]
    have : i9Poly x w 0 = x * (1 - x) * (1 - w) ^ 2 := by unfold i9Poly; ring
    rw [this, Real.log_mul hc.ne' (by positivity), Real.log_pow]
    push_cast; ring
  simp only [i9A2DensP, i9A2Dens, i9A1Dens, i9A2YL, i9A2Y2, i9A2cA, i9A2cB, i9A2AL, i9A2BL,
    i9A2A2, i9A2B2]
  rw [e1, hq, hlK]
  rw [hla, hlw, hlc]
  generalize Real.log (i9Poly x w 0 / i9Poly x w 1) = Lp
  generalize Real.log (1 - i9Poly x w 0 / i9Poly x w 1) = Lq
  generalize Real.log (i9Poly x w 1) = Lb
  generalize Real.log (1 - w) = Lu
  generalize Li₂ (1 - i9Poly x w 0 / i9Poly x w 1) = L2
  generalize Li₃ (1 - i9Poly x w 0 / i9Poly x w 1) = L3
  generalize logOneSubSqPrim (1 - i9Poly x w 0 / i9Poly x w 1) = F
  have e2 : i9Poly x w 1 = i9Poly x w 0 + w := e1.symm
  rw [e2]
  field_simp
  ring

/-- **`Dens' = |det Ψ'| · Θ ∘ Ψ`.** -/
theorem i9A2DensP_eq {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    i9A2DensP z = |(i9A1Deriv z).det| • i9A2Theta (i9A1Map z) := by
  rw [i9A2DensP_eq_div hz, i9A2_transfer hz, smul_eq_mul]
  congr 1
  rw [show i9A2Theta (i9A1Map z) = i9A2Theta ((i9A1Map z).1, (i9A1Map z).2) from rfl,
    i9A2Theta_eq, i9A2_b_eq hz, i9A1Map_fst_eq]

end QED.ThreeLoopD
