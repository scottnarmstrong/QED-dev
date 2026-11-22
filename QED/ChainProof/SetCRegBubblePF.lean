/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellKer

/-!
# Set (c): partial fractions of the bubble-line photon and the outer-line factors of the share

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, the regulator
limit `hReg` (Stage L). In the frozen model the photon line carrying the bubble is the
Pauli–Villars photon `D(s) = 1/(s + a) - 1/(s + b)` (`a = m_γ²`, `b = Λ²`) on both sides of the
inserted loop. By the spectral form of the bubble, a photon of spectral mass² `c = T m²` enters
through `R_T(s) = s² D(s)²/(s + c)`
(`QED.ChainProof.SetCRegDisp.vpPhotonT`). The same `R_T` enters the VP-share counterterms of
(Sc₂) through the shell kernels `shellKer₀`, `shellKer₁C`. Both the graphs and the counterterms
are linear in `R_T`. So the finite-regulator form of an inner-massive placement is fixed by the
exact partial fractions of `R_T`, which this file proves:

`R_T = C/(s+c) + A/(s+a) + B/(s+b) + A₂/(s+a)² + B₂/(s+b)²`, with `C + A + B = 0`.

At `a = 0` this is `κ (1/(s+c) - 1/(s+b)) - (b²/(b-c))/(s+b)²` with `κ = b²/(b-c)²`. The
Λ-partner has relative coefficient exactly `-1`, under a common factor `κ → 1`. There is a
double-pole (`∂/∂Λ²`) partner, and at `a > 0` there are further terms of order `a`. So the
bubble line is **not** a plain Pauli–Villars difference with unit coefficient at finite
regulators.

The outer line of every VP-share class is the plain Pauli–Villars photon. Its factors are
differences with unit coefficient: `dVk`, `dVm` by definition and `sPauliB0` by
`sPauliB0_eq`.

## Main statements

* `bubCoefC`, `bubCoefA`, `bubCoefB`, `bubCoefA2`, `bubCoefB2`: the five coefficients;
* **`bubble_partialFractions`**, **`vpPhotonT_partialFractions`**: the identity;
* `bubCoef_simple_sum`: `C + A + B = 0`;
* `bubCoefB_zero`, `bubCoefA_zero`, `bubCoefA2_zero`: the form at `a = 0`;
* **`sPauliB0_eq`**: `B(0) = 2 (F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ))` for the share vertex classes.
-/

@[expose] public section

open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegBubble

open QED.ChainProof.SetCRegDisp QED.TwoLoop.UnitVPLink

/-! ### The coefficients -/

/-- The coefficient of `1/(s + c)`: `c²(a-b)²/((a-c)²(b-c)²)`. -/
noncomputable def bubCoefC (a b c : ℝ) : ℝ :=
  c ^ 2 * (a - b) ^ 2 / ((a - c) ^ 2 * (b - c) ^ 2)

/-- The coefficient of `1/(s + a)`: `-a(a² + ab - 2bc)/((a-b)(a-c)²)`. -/
noncomputable def bubCoefA (a b c : ℝ) : ℝ :=
  -(a * (a ^ 2 + a * b - 2 * b * c)) / ((a - b) * (a - c) ^ 2)

/-- The coefficient of `1/(s + b)`: `b(ab - 2ac + b²)/((a-b)(b-c)²)`. -/
noncomputable def bubCoefB (a b c : ℝ) : ℝ :=
  b * (a * b - 2 * a * c + b ^ 2) / ((a - b) * (b - c) ^ 2)

/-- The coefficient of `1/(s + a)²`: `-a²/(a-c)`. -/
noncomputable def bubCoefA2 (a c : ℝ) : ℝ := -a ^ 2 / (a - c)

/-- The coefficient of `1/(s + b)²`: `-b²/(b-c)`. -/
noncomputable def bubCoefB2 (b c : ℝ) : ℝ := -b ^ 2 / (b - c)

/-! ### The identity -/

/-- **Partial fractions of the bubble-line photon** `s² D(s)²/(s + c)`, `D = 1/(s+a) - 1/(s+b)`,
for distinct `a, b, c`. -/
theorem bubble_partialFractions {a b c s : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : s + a ≠ 0) (hb : s + b ≠ 0) (hc : s + c ≠ 0) :
    s ^ 2 * (1 / (s + a) - 1 / (s + b)) ^ 2 / (s + c) =
      bubCoefC a b c / (s + c) + bubCoefA a b c / (s + a) + bubCoefB a b c / (s + b) +
        bubCoefA2 a c / (s + a) ^ 2 + bubCoefB2 b c / (s + b) ^ 2 := by
  have h1 : a - b ≠ 0 := sub_ne_zero.2 hab
  have h2 : a - c ≠ 0 := sub_ne_zero.2 hac
  have h3 : b - c ≠ 0 := sub_ne_zero.2 hbc
  unfold bubCoefC bubCoefA bubCoefB bubCoefA2 bubCoefB2
  field_simp
  ring

/-- **The bubble-line photon `R_T` in partial fractions** (`a = m_γ²`, `b = Λ²`, `c = T m²`). -/
theorem vpPhotonT_partialFractions {m mγ Λ T s : ℝ} (hab : mγ ^ 2 ≠ Λ ^ 2)
    (hac : mγ ^ 2 ≠ T * m ^ 2) (hbc : Λ ^ 2 ≠ T * m ^ 2) (ha : s + mγ ^ 2 ≠ 0)
    (hb : s + Λ ^ 2 ≠ 0) (hc : s + T * m ^ 2 ≠ 0) :
    vpPhotonT m mγ Λ T s =
      bubCoefC (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) / (s + T * m ^ 2) +
        bubCoefA (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) / (s + mγ ^ 2) +
        bubCoefB (mγ ^ 2) (Λ ^ 2) (T * m ^ 2) / (s + Λ ^ 2) +
        bubCoefA2 (mγ ^ 2) (T * m ^ 2) / (s + mγ ^ 2) ^ 2 +
        bubCoefB2 (Λ ^ 2) (T * m ^ 2) / (s + Λ ^ 2) ^ 2 := by
  rw [← bubble_partialFractions hab hac hbc ha hb hc]
  unfold vpPhotonT photonD
  ring

/-- **The simple-pole coefficients sum to zero** (`R_T = O(s⁻³)`), so the tail of `R_T` is a
finite combination of logarithms. -/
theorem bubCoef_simple_sum {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    bubCoefC a b c + bubCoefA a b c + bubCoefB a b c = 0 := by
  have h1 : a - b ≠ 0 := sub_ne_zero.2 hab
  have h2 : a - c ≠ 0 := sub_ne_zero.2 hac
  have h3 : b - c ≠ 0 := sub_ne_zero.2 hbc
  unfold bubCoefC bubCoefA bubCoefB
  field_simp
  ring

/-! ### The form at zero photon mass -/

/-- At `a = 0` the Λ-partner has relative coefficient exactly `-1`. -/
theorem bubCoefB_zero {b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) :
    bubCoefB 0 b c = -bubCoefC 0 b c := by
  unfold bubCoefB bubCoefC
  field_simp
  ring

theorem bubCoefC_zero {b c : ℝ} (hc : c ≠ 0) : bubCoefC 0 b c = b ^ 2 / (b - c) ^ 2 := by
  unfold bubCoefC
  field_simp
  ring

theorem bubCoefA_zero (b c : ℝ) : bubCoefA 0 b c = 0 := by
  simp [bubCoefA]

theorem bubCoefA2_zero (c : ℝ) : bubCoefA2 0 c = 0 := by
  simp [bubCoefA2]

/-! ### The outer-line factor of the share vertex classes -/

/-- **The Pauli factor of the share vertex classes is a plain Pauli–Villars difference**:
`B(0) = 2 (F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ))`. -/
theorem sPauliB0_eq (P₀ : Params) {mγ Λ : ℝ} (hm : 0 < P₀.m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    sPauliB0 P₀ mγ Λ =
      2 * (QED.TwoLoop.UnitLLink.oneLoopF2 P₀.m mγ - QED.TwoLoop.UnitLLink.oneLoopF2 P₀.m Λ) :=
  QED.TwoLoop.UnitLLink.oneLoopPauliZero_eq { P₀ with mγ := mγ, Λ := Λ } hm hmγ hΛ

end QED.ChainProof.SetCRegBubble

end
