/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Numerics.BoxQuadrature
public import QED.OneLoop.PauliLimit
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An interval extension of the one-loop Pauli integrand (milestone NUM.CERTIFICATE)

Decision D-34 encloses the regulated one-loop Pauli coefficient at fixed regulator points. On
shell it is `(e²/8π²) ∫ pauliIntegrand m (m_γ, Λ, q²)` over `QED.Integration.feynmanMeasure`
(`QED.OneLoop.VertexLimit.formFactorB_eq`). This module rewrites the integrand in a form whose
interval evaluation on a box is nearly exact, and proves the soundness of that evaluation.

Write `y = z.2`, `x = z.1`, `Q = 1 + x(1 - x)c` and `D_K = (1 - y)K + y²Q`. With `m_γ = m a`,
`Λ = m b` and `q² = m² c` the factor `m²` cancels, and

`pauliIntegrand m (m a, m b, m² c) = 2(1 - y) - 2(1 - y)(1 - T_{a²} + T_{b²})`,
`T_K = y² / D_K`.

The first term has integral `1` (`QED.OneLoop.VertexLimit.integral_two_mul_one_sub`); the second,
the *remainder*, is nonnegative and concentrated near `y = 0` (on the scale `a`), and is the part
that is certified.
For `y > 0`, `T_K = 1/((1 - y) y⁻² K + Q)`: each of `(1 - y)`, `y⁻²` decreases in `y`, so the
interval evaluation of this form gives the exact range of `T_K` up to outward rounding. On boxes
touching `y = 0`, where `y⁻²` is unbounded, the extension evaluates `y² / D_K` directly. The
factor `x(1 - x)` is evaluated as `1/4 - (x - 1/2)²`, whose interval evaluation is also exact.

## Main definitions

* `QED.Numerics.Pauli.remainder A B c`: the remainder `2(1 - y)(1 - T_A + T_B)`, with `A = a²`,
  `B = b²`.
* `QED.Numerics.Pauli.remExt KA KB C`: its interval extension on a box, for interval constants
  `KA ∋ A`, `KB ∋ B`, `C ∋ c`.

## Main statements

* `QED.Numerics.Pauli.pauliIntegrand_eq`: the algebraic identity above.
* `QED.Numerics.Pauli.remExt_sound`: soundness of the extension on every box of `(0, 1]²`.
* `QED.Numerics.Pauli.integral_pauliIntegrand_mem_of_check`: if the box-partition checker
  accepts `remExt` with claimed bounds `[lo, hi]`, then
  `∫ pauliIntegrand m (m a, m b, m² c) ∈ [1 - hi, 1 - lo]`.
-/

@[expose] public section

open MeasureTheory Set QED.Integration QED.OneLoop.VertexLimit

namespace QED.Numerics.Pauli

/-! ### The remainder -/

/-- The denominator `D_K = (1 - y)K + y²(1 + x(1 - x)c)` at `z = (x, y)`. -/
noncomputable def denom (K c : ℝ) (z : ℝ × ℝ) : ℝ :=
  (1 - z.2) * K + z.2 ^ 2 * (1 + z.1 * (1 - z.1) * c)

/-- `T_K = y² / D_K`. -/
noncomputable def pauliT (K c : ℝ) (z : ℝ × ℝ) : ℝ := z.2 ^ 2 * (denom K c z)⁻¹

/-- The remainder `2(1 - y)(1 - T_A + T_B)`. -/
noncomputable def remainder (A B c : ℝ) (z : ℝ × ℝ) : ℝ :=
  2 * (1 - z.2) * (1 - pauliT A c z + pauliT B c z)

/-- The Pauli integrand at `m_γ = m a`, `Λ = m b`, `q² = m² c` is `2(1 - y)` minus the
remainder at `A = a²`, `B = b²`. -/
theorem pauliIntegrand_eq {m : ℝ} (hm : m ≠ 0) (a b c : ℝ) (z : ℝ × ℝ) :
    pauliIntegrand m (m * a, m * b, m ^ 2 * c) z
      = 2 * (1 - z.2) - remainder (a ^ 2) (b ^ 2) c z := by
  have hm2 : m ^ 2 * (m ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hm)
  have e : ∀ k : ℝ, (1 - z.2) * (m * k) ^ 2 + z.2 ^ 2 * (m ^ 2 + z.1 * (1 - z.1) * (m ^ 2 * c))
      = m ^ 2 * denom (k ^ 2) c z := fun k => by simp only [denom]; ring
  simp only [pauliIntegrand, remainder, pauliT]
  rw [e a, e b, mul_inv, mul_inv]
  linear_combination (2 * z.2 * ((1 - z.2) - (1 - z.2) ^ 2) *
    ((denom (a ^ 2) c z)⁻¹ - (denom (b ^ 2) c z)⁻¹)) * hm2

theorem denom_pos {K c : ℝ} (hK : 0 < K) (hc : 0 ≤ c) {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) : 0 < denom K c z := by
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
  have hQ : 0 < 1 + z.1 * (1 - z.1) * c := by
    have : 0 ≤ z.1 * (1 - z.1) * c := mul_nonneg (mul_nonneg hx0 (by linarith)) hc
    linarith
  have h1 : 0 ≤ (1 - z.2) * K := mul_nonneg (by linarith) hK.le
  rcases eq_or_lt_of_le hy0 with h | h
  · rw [denom, ← h]
    linarith
  · have : 0 < z.2 ^ 2 * (1 + z.1 * (1 - z.1) * c) := by positivity
    rw [denom]
    linarith

theorem continuousOn_inv_denom {K c : ℝ} (hK : 0 < K) (hc : 0 ≤ c) :
    ContinuousOn (fun z => (denom K c z)⁻¹) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
  ContinuousOn.inv₀ (by unfold denom; fun_prop) fun _ hz => (denom_pos hK hc hz).ne'

theorem continuousOn_remainder {A B c : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 ≤ c) :
    ContinuousOn (remainder A B c) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  have hTA : ContinuousOn (pauliT A c) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    (continuous_snd.pow 2).continuousOn.mul (continuousOn_inv_denom hA hc)
  have hTB : ContinuousOn (pauliT B c) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    (continuous_snd.pow 2).continuousOn.mul (continuousOn_inv_denom hB hc)
  have h2 : ContinuousOn (fun z : ℝ × ℝ => 2 * (1 - z.2)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    fun_prop
  exact h2.mul ((continuousOn_const.sub hTA).add hTB)

/-- The integral of the Pauli integrand at `m_γ = m a`, `Λ = m b`, `q² = m² c` is `1` minus the
integral of the remainder. -/
theorem integral_pauliIntegrand_eq {m a b c : ℝ} (hm : m ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : 0 ≤ c) :
    ∫ z, pauliIntegrand m (m * a, m * b, m ^ 2 * c) z ∂feynmanMeasure
      = 1 - ∫ z, remainder (a ^ 2) (b ^ 2) c z ∂feynmanMeasure := by
  have h1 : Integrable (fun z : ℝ × ℝ => 2 * (1 - z.2)) feynmanMeasure :=
    integrable_feynmanMeasure_of_continuousOn (by fun_prop)
  have h2 : Integrable (remainder (a ^ 2) (b ^ 2) c) feynmanMeasure :=
    integrable_feynmanMeasure_of_continuousOn
      (continuousOn_remainder (sq_pos_of_ne_zero ha) (sq_pos_of_ne_zero hb) hc)
  simp only [pauliIntegrand_eq hm]
  rw [integral_sub h1 h2, integral_two_mul_one_sub]

/-! ### The interval extension -/

variable {S : ℕ}

/-- Interval extension of `1 + x(1 - x)c`, through `x(1 - x) = 1/4 - (x - 1/2)²`. -/
def qExt (C : Interval S) (B : Box S) : Interval S :=
  1 + C * (Interval.ofRat (1 / 4) - Interval.sq (B.X - Interval.ofRat (1 / 2)))

/-- Interval extension of `T_K`: `y² / D_K` on boxes touching `y = 0`, and
`1/((1 - y) y⁻² K + Q)` elsewhere. -/
def tExt (K C : Interval S) (B : Box S) : Interval S :=
  bif Nat.beq B.y₀ 0 then
    Interval.sq B.Y * ((1 - B.Y) * K + Interval.sq B.Y * qExt C B)⁻¹
  else ((1 - B.Y) * (Interval.sq B.Y)⁻¹ * K + qExt C B)⁻¹

/-- Interval extension of the remainder `2(1 - y)(1 - T_A + T_B)`. -/
def remExt (KA KB C : Interval S) (B : Box S) : Interval S :=
  2 * (1 - B.Y) * (1 - tExt KA C B + tExt KB C B)

/-- For `y ≠ 0`, `T_K = 1/((1 - y) y⁻² K + Q)`. -/
theorem pauliT_eq_inv {K c : ℝ} {z : ℝ × ℝ} (hy : z.2 ≠ 0) :
    pauliT K c z = ((1 - z.2) * (z.2 ^ 2)⁻¹ * K + (1 + z.1 * (1 - z.1) * c))⁻¹ := by
  have hy2 : z.2 ^ 2 * (z.2 ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hy)
  have e : (1 - z.2) * (z.2 ^ 2)⁻¹ * K + (1 + z.1 * (1 - z.1) * c)
      = denom K c z * (z.2 ^ 2)⁻¹ := by
    simp only [denom]
    linear_combination (-(1 + z.1 * (1 - z.1) * c)) * hy2
  rw [e, mul_inv, inv_inv, pauliT, mul_comm]

variable [NeZero S]

theorem mem_qExt {c : ℝ} {C : Interval S} (hc : c ∈ C) {B : Box S} {z : ℝ × ℝ}
    (hz : z ∈ B.toSet) : 1 + z.1 * (1 - z.1) * c ∈ qExt C B := by
  have hx := Box.fst_mem_X hz
  have e : 1 + z.1 * (1 - z.1) * c = 1 + c * (1 / 4 - (z.1 - 1 / 2) ^ 2) := by ring
  rw [e, qExt]
  interval_mem

theorem mem_tExt {K c : ℝ} {KI C : Interval S} (hK : K ∈ KI) (hc : c ∈ C) {B : Box S}
    {z : ℝ × ℝ} (hz : z ∈ B.toSet) (hy : z.2 ≠ 0) : pauliT K c z ∈ tExt KI C B := by
  have hy' := Box.snd_mem_Y hz
  have hq := mem_qExt hc hz
  unfold tExt
  cases Nat.beq B.y₀ 0
  · rw [Bool.cond_false, pauliT_eq_inv hy]
    interval_mem
  · rw [Bool.cond_true, pauliT, denom]
    interval_mem

/-- **Soundness of the interval extension of the remainder** on every box, at points of
`(0, 1]²`. -/
theorem remExt_sound {A B c : ℝ} {KA KB C : Interval S} (hA : A ∈ KA) (hB : B ∈ KB)
    (hc : c ∈ C) :
    ∀ Bx : Box S, ∀ z ∈ Bx.toSet, z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 →
      remainder A B c z ∈ remExt KA KB C Bx := by
  intro Bx z hz hz'
  have hy0 : z.2 ≠ 0 := hz'.2.1.ne'
  have hy := Box.snd_mem_Y hz
  have hTA := mem_tExt hA hc hz hy0
  have hTB := mem_tExt hB hc hz hy0
  rw [remainder, remExt]
  interval_mem

/-- **The certified enclosure.** If the box-partition checker accepts the extension `remExt`
of the remainder with claimed bounds `[lo, hi]`, then the integral of the Pauli integrand at
`m_γ = m a`, `Λ = m b`, `q² = m² c` lies in `[1 - hi, 1 - lo]`. -/
theorem integral_pauliIntegrand_mem_of_check {m a b c : ℝ} {KA KB C : Interval S}
    {P : List Strip} {lo hi : ℚ} (hm : m ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc0 : 0 ≤ c)
    (hA : a ^ 2 ∈ KA) (hB : b ^ 2 ∈ KB) (hc : c ∈ C)
    (h : Quadrature.check (remExt KA KB C) P lo hi = true) :
    ∫ z, pauliIntegrand m (m * a, m * b, m ^ 2 * c) z ∂feynmanMeasure
      ∈ Icc (1 - (hi : ℝ)) (1 - (lo : ℝ)) := by
  obtain ⟨h1, h2⟩ := Quadrature.integral_bounds_of_check_of_continuousOn
    (continuousOn_remainder (sq_pos_of_ne_zero ha) (sq_pos_of_ne_zero hb) hc0)
    (remExt_sound hA hB hc) h
  rw [integral_pauliIntegrand_eq hm ha hb hc0]
  exact ⟨by linarith, by linarith⟩

end QED.Numerics.Pauli

end
