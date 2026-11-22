/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersLaurent
public import QED.ThreeLoopD.SetDMastersI2Wire
public import QED.ThreeLoopD.SetDMastersI9KTaylor
import QED.ThreeLoopD.SetDMastersI12RestWire
import QED.ThreeLoopD.SetDMastersI2Analytic
import QED.ThreeLoopD.SetDMastersI2P0Val
import QED.TwoLoop.UnitXGraphChengWuSet
import QED.Integration.ChengWu
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Set (e) master I₄

In the pinned Laporta–Remiddi (1996) source (`sources/manifest.json`, eq. (9) and the list
before eq. (14)), I₄ has unit powers of D₂, D₃, D₄, D₆, D₇, D₈. Put Schwinger parameters
`a, b, c, l, m, n` on these lines in that order. The electron edges are AB, BC, CE and the
photon edges are AC, AE, BE, with external momentum between A and E. In units with mass 1,
the electron momenta are `p-k₁-k₂`, `p-k₁-k₂-k₃`, `p-k₂-k₃`; the photons carry `k₁,k₂,k₃`.

The coefficient matrix of the loop quadratic form has diagonal
`a+b+l, a+b+c+m, b+c+n` and upper off-diagonal `a+b, b, b+c` in lexicographic order.
The mixed term is `-2 p · (v₁ k₁ + v₂ k₂ + v₃ k₃)` with `v = (a+b,a+b+c,b+c)`.
For `S = a+b+c`, the constant is `S(1+p²)`. Completing the square gives
`U = det M` and `F = S(1+p²) U - p² vᵀ adj(M) v`, so on shell `p² = -1` the second
polynomial is `vᵀ adj(M) v`. The positive monomial expansions below collect terms
with the same square. These conventions agree with `QED.DimReg.LR96Family`.

The Gaussian integrals in measure `dᵈk/π^(d/2)` give `U^(-d/2) exp(-F/U)`.
Rescaling all parameters by their sum `r` gives the radial integral of
`r^(3ε-1) exp(-r F/U)`, where `d = 4 - 2ε` and the polynomials now use simplex
coordinates. Thus `I₄ = π^(3ε) Γ(3ε) P(ε)` with `P = ∫ U^(-2+4ε) F^(-3ε)`
on the simplex. The simplex measure is Lebesgue measure in `(a,b,c,l,m)` with
`n = 1-a-b-c-l-m`, as obtained by eliminating the delta function with unit Jacobian.
The Wick rotation and dimensionally continued Gaussian formula are the conventions of
`QED.DimReg.LR96Family`. The LR96 loop measure contributes `π^ε` per loop.

To see convergence near zero, on the simplex write the integrand as
`U^(-2+ε) (F/U)^(-3ε)`. The ratio `F/U` is `S - R`, where `R` is the effective
resistance between A and E with edge resistances given by the parameters. Indeed the
energy of the flow along ABCE is S, and minimizing over cycle flows subtracts
`vᵀ M⁻¹ v`. The direct edge AE in parallel with ABCE gives a trial flow of energy
`Sm/(S+m)`, hence `S² ≤ F/U ≤ S ≤ 1`.

Order the six parameters from largest to smallest. In each projective sector the
unnormalized parameters are `1,t₁,t₁t₂,…,t₁⋯t₅`, divided by their sum `H ∈ [1,6]`.
The Jacobian is `H⁻⁶ ∏ tⱼ^(5-j)`. The leading monomial of U has exponent
`j ↦ h(Gⱼ)`, the cycle rank of the subgraph of the smallest `6-j` edges.
Indeed the greedy spanning tree takes the smallest edges first, and its complement
simultaneously minimizes the number of chosen edges from each such subgraph.
For `6-j = 1,2,3,4,5` the maximum ranks are `0,0,1,1,2`, respectively.
At zero regulator the Jacobian times `U⁻²` therefore has all exponents nonnegative.
The bounds on `F/U`, with `S ≥ t₁⋯t₅/6`, and the leading monomial of U bound
the integrands uniformly for `|re ε| < 1/16` by integrable products of powers,
even with any fixed power of the logarithms for differentiation. Thus the only
subtraction needed for the master near zero is the explicit overall Gamma pole.
The Lean integrability proof below uses a direct simplex bound. For each choice of
coordinate at least 1/6, five monomials of U contain that coordinate, and every other
coordinate occurs twice among them. Their product gives
`U ≥ (1/6) (a b c l m n)^(2/5)`. Also `F ≥ a²bc ≥ (a b c l m n)²`.
For `‖ε‖ < 1/100` the absolute integrand is bounded by a constant times the product of
all six coordinates to power −9/10, which is integrable on the simplex. The
source-to-parametric derivation above is a mathematical argument accompanying the definition.

The numerical photon integration in `scripts/numerics/three_loop_masters/i4photon.py`
eliminates the coordinate m analytically and evaluates the first three coefficients.

The wire below uses `K₀ = Γ(1+3ε)/Γ(1+ε)³ = 1 + π² ε²/2 + O(ε³)`. The value `P(0) = 6ζ₃` is
proved below (`i4PInt_zero_eq`). It remains to prove `P'(0) = i4P1` and `P''(0)/2 = i4P2`, the
hypotheses of `hasTruncLaurent_setEMasterI4_of_coeffs`; the targets include Laporta's 2001
corrections as recorded in `QED.ThreeLoopE.SetEMastersLaurent`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology Real QED.Polylog QED.ThreeLoopD

namespace QED.ThreeLoopE

/-- The first Symanzik polynomial, in parameter order D₂, D₃, D₄, D₆, D₇, D₈. -/
def i4U (a b c l m n : ℝ) : ℝ :=
  a * b * (c + l + m) + a * c * (l + m + n) + a * n * (l + m) +
    b * c * (m + n) + b * (l * m + l * n + m * n) + c * l * (m + n) + l * m * n

/-- The second Symanzik polynomial on shell in the same parameter order. -/
def i4F (a b c l m n : ℝ) : ℝ :=
  a * b * c * (a + b + c + 2 * (l + m + n)) + a * b * (a + b) * (l + m) +
    a * c * (a + c) * (l + m + n) + a * n * (a * (l + m) + 2 * (b * (l + m) + c * l)) +
    b * c * (b + c) * (m + n) + b ^ 2 * (l * m + l * n + m * n) +
    c * l * (2 * b + c) * (m + n)

/-- The open simplex in five independent coordinates. -/
def i4Dom : Set (ℝ × ℝ × ℝ × ℝ × ℝ) :=
  {x | 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2.1 ∧ 0 < x.2.2.2.2 ∧
    x.1 + x.2.1 + x.2.2.1 + x.2.2.2.1 + x.2.2.2.2 < 1}

/-- The projective factor P of I₄. -/
noncomputable def i4PInt (ε : ℂ) : ℂ :=
  ∫ x in i4Dom,
    let (a, b, c, l, m) := x
    let n := 1 - (a + b + c + l + m)
    (i4U a b c l m n : ℂ) ^ (-2 + 4 * ε) * (i4F a b c l m n : ℂ) ^ (-3 * ε)

/-- I₄ in the LR96 normalization. -/
noncomputable def lr96I4 (ε : ℂ) : ℂ :=
  QED.DimReg.lr96LoopFactor (4 - 2 * ε) ^ 3 * (Gamma (3 * ε) * i4PInt ε)

/-- The set (e) master I₄ divided by C. -/
noncomputable def setEMasterI4 (ε : ℂ) : ℂ := lr96I4 ε / lr96C ε

/-- The constant term of the target expansion of P. -/
noncomputable def i4P0 : ℂ := 6 * (zeta3 : ℂ)

/-- The linear coefficient of the target expansion of P. -/
noncomputable def i4P1 : ℂ :=
  -7 / 30 * (π : ℂ) ^ 4 + 6 * (zeta3 : ℂ) + (π : ℂ) ^ 2

/-- The quadratic coefficient of the target expansion of P. -/
noncomputable def i4P2 : ℂ :=
  -12 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ) - 91 / 2 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    - 7 / 5 * (π : ℂ) ^ 4 + 12 * laportaC2 - 6 * laportaC1 + 1155 / 2 * (zeta5 : ℂ)
    - 246 * (zeta3 : ℂ) + 48 * (π : ℂ) ^ 2

/-- The target of the projective factor through quadratic order. -/
noncomputable def i4PLaurent (ε : ℂ) : ℂ := i4P0 + i4P1 * ε + i4P2 * ε ^ 2

/-! ### The master in terms of `P` -/

/-- **`I₄ C⁻¹ = K₀ P / (3ε)`**, `K₀ = Γ(1 + 3ε) / Γ(1 + ε)³`. -/
theorem setEMasterI4_eq {ε : ℂ} (h0 : ε ≠ 0) (hε : ‖ε‖ < 1 / 8) :
    setEMasterI4 ε = i12K0 ε * i4PInt ε / (3 * ε) := by
  have h3 : 3 * ε ≠ 0 := setDGamma_mul_ne_zero h0 3 (by norm_num) rfl
  have hG1 := Gamma_one_add_ne_zero (setDGamma_norm_mul_lt_one hε 1 (by norm_num))
  have hpi : (π : ℂ) ^ ε ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  simp only [setEMasterI4, lr96I4, lr96C, QED.DimReg.lr96LoopFactor_four_sub, i12K0]
  rw [Gamma_eq_div_one (s := 3 * ε) (t := 1 + 3 * ε) (p := 3 * ε) h3 (by ring) rfl,
    show (1 : ℂ) + ε = 1 + 1 * ε by ring]
  generalize Gamma (1 + 1 * ε) = A at *
  generalize Gamma (1 + 3 * ε) = B at *
  generalize (π : ℂ) ^ ε = Q at *
  field_simp

/-! ### The expansion -/

/-- The polynomial `Q` with `(1 + ε² X₀ + ε⁴ X₀²/2) P_L - 3ε L₄ = ε³ Q`. -/
noncomputable def i4Q (ε : ℂ) : ℂ :=
  (π : ℂ) ^ 2 / 2 * (i4P1 + i4P2 * ε) +
    (-8 * (zeta3 : ℂ) + 13 / 60 * (π : ℂ) ^ 4 * ε - 48 * (zeta5 : ℂ) * ε ^ 2) * i4PLaurent ε +
    ε * i2X ε ^ 2 * i4PLaurent ε / 2

/-- The remainder `R₄` with `I₄ C⁻¹ = L₄ + ε² R₄`, given `P = P_L + ε³ R`. -/
noncomputable def i4R (ε R : ℂ) : ℂ :=
  (i4Q ε + ε ^ 3 * i2T ε * i4PLaurent ε + (i12PolyKH (i2X ε) ε + ε ^ 6 * i2T ε) * R) / 3

/-- The remainder `R₄` is analytic at `0` whenever `R` is. -/
theorem analyticAt_i4R {R : ℂ → ℂ} (hR : AnalyticAt ℂ R 0) :
    AnalyticAt ℂ (fun ε => i4R ε (R ε)) 0 := by
  have hX : AnalyticAt ℂ i2X 0 := by unfold i2X i12PolyX0; fun_prop
  have hV : AnalyticAt ℂ i12V0 0 := by
    have h1 := analyticAt_i12_logGammaRem 3
    have h2 := analyticAt_i12_logGammaRem 1
    unfold i12V0
    fun_prop
  have hT : AnalyticAt ℂ i2T 0 := analyticAt_i12ExpT hX hV
  have hL : AnalyticAt ℂ i4PLaurent 0 := by unfold i4PLaurent; fun_prop
  have hQ : AnalyticAt ℂ i4Q 0 := by unfold i4Q; fun_prop
  unfold i4R i12PolyKH
  fun_prop

/-- **The set (e) input for `I₄` from the expansion of `P`**: if `P = P_L + ε³ R` with `R`
analytic at `0`, then `I₄ C⁻¹ = L₄ + ε² R₄` with `R₄` analytic at `0`. -/
theorem hasTruncLaurent_setEMasterI4_of_P (hP : HasTruncLaurent i4PInt i4PLaurent 3) :
    HasTruncLaurent setEMasterI4 setELaurentI4 2 := by
  obtain ⟨RR, hRR, hRe⟩ := hP
  refine ⟨fun ε => i4R ε (RR ε), analyticAt_i4R hRR, ?_⟩
  filter_upwards [setDGamma_eventually_small, hRe, self_mem_nhdsWithin] with ε hε hRε h0
  have h0 : ε ≠ 0 := h0
  have hK : i12K0 ε = i12PolyKH (i2X ε) ε + ε ^ 6 * i2T ε := by
    rw [i12K0_eq hε, exp_eq_i12ExpT]
    rfl
  rw [setEMasterI4_eq h0 hε, hRε, hK, i4R, i4Q]
  simp only [setELaurentI4, i4PLaurent, i4P0, i4P1, i4P2, i12PolyKH, i2X, i12PolyX0]
  generalize i2T ε = T
  generalize RR ε = R
  generalize laportaC1 = C1
  generalize laportaC2 = C2
  field_simp
  ring


/-! ### Polynomial bounds for convergence -/

private theorem i4U_lower_pow {a b c l m n : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l) (hm : 0 < m) (hn : 0 < n)
    (hs : a + b + c + l + m + n = 1) :
    (a * b * c * l * m * n) ^ 2 ≤ 216 * i4U a b c l m n ^ 5 := by
  set U := i4U a b c l m n with hU
  have hU0 : 0 ≤ U := by rw [hU]; unfold i4U; positivity
  have mul5 {p q r s t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
      (hs : 0 ≤ s) (ht : 0 ≤ t) (h1 : p ≤ U) (h2 : q ≤ U) (h3 : r ≤ U)
      (h4 : s ≤ U) (h5 : t ≤ U) : p * q * r * s * t ≤ U ^ 5 := by
    simpa only [pow_succ, pow_zero, one_mul] using
      mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h1 h2 hq hU0) h3 hr (by positivity))
        h4 hs (by positivity)) h5 ht (by positivity)
  have finish {x : ℝ} (hx : 1 / 6 ≤ x)
      (h : x ^ 3 * (a * b * c * l * m * n) ^ 2 ≤ U ^ 5) :
      (a * b * c * l * m * n) ^ 2 ≤ 216 * U ^ 5 := by
    have h3 : (1 / 6 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx _
    have := mul_le_mul_of_nonneg_right h3 (sq_nonneg (a * b * c * l * m * n))
    norm_num at this
    linarith
  have largest : 1 / 6 ≤ a ∨ 1 / 6 ≤ b ∨ 1 / 6 ≤ c ∨ 1 / 6 ≤ l ∨
      1 / 6 ≤ m ∨ 1 / 6 ≤ n := by
    by_contra! h
    linarith only [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, hs]
  rcases largest with h | h | h | h | h | h
  · apply finish h
    convert mul5 (p := a * b * c)
      (q := a * b * l) (r := a * c * m) (s := a * l * n) (t := a * m * n)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      ?_ ?_ ?_ ?_ ?_ using 1
    · ring
    all_goals rw [hU]; unfold i4U
    · have he : 0 ≤ a * b * l + a * b * m + a * c * l + a * c * m + a * c * n + a * l * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * m + a * c * l + a * c * m + a * c * n + a * l * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * n + a * l * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
  · apply finish h
    convert mul5 (p := a * b * c)
      (q := a * b * l) (r := b * c * m) (s := b * l * n) (t := b * m * n)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      ?_ ?_ ?_ ?_ ?_ using 1
    · ring
    all_goals rw [hU]; unfold i4U
    · have he : 0 ≤ a * b * l + a * b * m + a * c * l + a * c * m + a * c * n + a * l * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * m + a * c * l + a * c * m + a * c * n + a * l * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * c * n + b * l * m + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * c * n + b * l * m + b * l * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
  · apply finish h
    convert mul5 (p := a * b * c)
      (q := a * c * m) (r := b * c * n) (s := c * l * m) (t := c * l * n)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      ?_ ?_ ?_ ?_ ?_ using 1
    · ring
    all_goals rw [hU]; unfold i4U
    · have he : 0 ≤ a * b * l + a * b * m + a * c * l + a * c * m + a * c * n + a * l * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * n + a * l * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * c * n + b * l * m + b * l * n +
          b * m * n + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * c * n + b * l * m + b * l * n +
          b * m * n + c * l * m + l * m * n := by positivity
      linarith only [he]
  · apply finish h
    convert mul5 (p := a * b * l)
      (q := a * c * l) (r := b * l * m) (s := c * l * n) (t := l * m * n)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      ?_ ?_ ?_ ?_ ?_ using 1
    · ring
    all_goals rw [hU]; unfold i4U
    · have he : 0 ≤ a * b * c + a * b * m + a * c * l + a * c * m + a * c * n + a * l * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * m + a * c * n + a * l * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * c * n + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * c * n + b * l * m + b * l * n +
          b * m * n + c * l * m + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * c * n + b * l * m + b * l * n +
          b * m * n + c * l * m + c * l * n := by positivity
      linarith only [he]
  · apply finish h
    convert mul5 (p := a * b * m)
      (q := a * c * m) (r := b * m * n) (s := c * l * m) (t := l * m * n)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      ?_ ?_ ?_ ?_ ?_ using 1
    · ring
    all_goals rw [hU]; unfold i4U
    · have he : 0 ≤ a * b * c + a * b * l + a * c * l + a * c * m + a * c * n + a * l * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * n + a * l * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * c * n + b * l * m + b * l * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * c * n + b * l * m + b * l * n +
          b * m * n + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * c * n + b * l * m + b * l * n +
          b * m * n + c * l * m + c * l * n := by positivity
      linarith only [he]
  · apply finish h
    convert mul5 (p := a * c * n)
      (q := a * l * n) (r := b * c * n) (s := b * m * n) (t := l * m * n)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      ?_ ?_ ?_ ?_ ?_ using 1
    · ring
    all_goals rw [hU]; unfold i4U
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * l * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * m * n + b * c * m + b * c * n + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * l * m + b * l * n + b * m * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * c * n + b * l * m + b * l * n +
          c * l * m + c * l * n + l * m * n := by positivity
      linarith only [he]
    · have he : 0 ≤ a * b * c + a * b * l + a * b * m + a * c * l + a * c * m + a * c * n +
          a * l * n + a * m * n + b * c * m + b * c * n + b * l * m + b * l * n +
          b * m * n + c * l * m + c * l * n := by positivity
      linarith only [he]


/-- Five independent real coordinates on the projective simplex. -/
abbrev I4Coords := ℝ × ℝ × ℝ × ℝ × ℝ

private def i4CoordsEquiv : (Fin 5 → ℝ) ≃ᵐ I4Coords :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
        ((MeasurableEquiv.refl ℝ).prodCongr
          ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
            ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ => ℝ)))))))

private theorem measurePreserving_i4CoordsEquiv : MeasurePreserving i4CoordsEquiv := by
  unfold i4CoordsEquiv
  exact ((((MeasurePreserving.id volume).prod
    ((((MeasurePreserving.id volume).prod
      ((((MeasurePreserving.id volume).prod (volume_preserving_piFinTwo (fun _ => ℝ)))).comp
        (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0)))).comp
      (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0)))).comp
    (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0))

private theorem i4CoordsEquiv_apply (x : Fin 5 → ℝ) :
    i4CoordsEquiv x = (x 0, x 1, x 2, x 3, x 4) := by
  rfl

private theorem preimage_i4Dom :
    i4CoordsEquiv ⁻¹' i4Dom = QED.Integration.ChengWu.openSimplex 5 := by
  ext x
  simp [i4CoordsEquiv_apply, i4Dom, QED.Integration.ChengWu.mem_openSimplex,
    Fin.forall_fin_succ, Fin.sum_univ_succ, add_assoc, and_assoc]

private theorem measurableSet_i4Dom : MeasurableSet i4Dom := by
  unfold i4Dom
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const (by fun_prop)).inter
    ((measurableSet_lt measurable_const (by fun_prop)).inter
      ((measurableSet_lt measurable_const (by fun_prop)).inter
        ((measurableSet_lt measurable_const (by fun_prop)).inter
          ((measurableSet_lt measurable_const (by fun_prop)).inter
            (measurableSet_lt (by fun_prop) measurable_const)))))

/-- The sixth coordinate obtained from the simplex constraint. -/
def i4Last (x : I4Coords) : ℝ :=
  1 - (x.1 + x.2.1 + x.2.2.1 + x.2.2.2.1 + x.2.2.2.2)

/-- The first Symanzik polynomial evaluated in the simplex chart. -/
def i4SimplexU (x : I4Coords) : ℝ :=
  i4U x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 (i4Last x)

/-- The second Symanzik polynomial evaluated in the simplex chart. -/
def i4SimplexF (x : I4Coords) : ℝ :=
  i4F x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 (i4Last x)

private def i4Product (x : I4Coords) : ℝ :=
  x.1 * x.2.1 * x.2.2.1 * x.2.2.2.1 * x.2.2.2.2 * i4Last x



private theorem integrableOn_i4Product :
    IntegrableOn (fun x => i4Product x ^ (-(9 / 10) : ℝ)) i4Dom := by
  open QED.Integration Feynman TwoLoop ChengWu in
  have h := integrableOn_prod_simplexPoint_rpow (m := 5) Finset.univ
    (s := 9 / 10) (by norm_num) (by norm_num)
  have hset : QED.Integration.Feynman.simplexSet 5 =ᵐ[volume]
      QED.Integration.ChengWu.openSimplex 5 :=
    QED.Integration.ChengWu.simplexSet_ae_eq_openSimplex (0 : Fin 5)
  rw [IntegrableOn, Measure.restrict_congr_set hset] at h
  rw [← measurePreserving_i4CoordsEquiv.integrableOn_comp_preimage
    i4CoordsEquiv.measurableEmbedding, preimage_i4Dom]
  change IntegrableOn _ (QED.Integration.ChengWu.openSimplex 5) at h
  refine h.congr_fun (fun x hx => ?_) (preimage_i4Dom ▸
    i4CoordsEquiv.measurable measurableSet_i4Dom)
  open QED.Integration Feynman TwoLoop ChengWu in
  obtain ⟨hx, hs⟩ := mem_openSimplex.mp hx
  dsimp only [Function.comp_apply]
  rw [Fin.prod_univ_castSucc]
  simp only [simplexPoint_castSucc, simplexPoint_last, Fin.prod_univ_succ,
    Fin.sum_univ_succ, i4Product, i4Last, i4CoordsEquiv_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change x 0 + (x 1 + (x 2 + (x 3 + x 4))) < 1 at hs
  have hlast : 0 ≤ 1 - (x 0 + x 1 + x 2 + x 3 + x 4) := by linarith
  simp only [add_assoc] at hlast ⊢
  have h0 := (hx 0).le
  have h1 := (hx 1).le
  have h2 := (hx 2).le
  have h3 := (hx 3).le
  have h4 := (hx 4).le
  rw [Real.mul_rpow (by positivity) hlast, Real.mul_rpow (by positivity) h4,
    Real.mul_rpow (by positivity) h3, Real.mul_rpow (by positivity) h2,
    Real.mul_rpow h0 h1]
  ring_nf; rfl

private theorem i4U_ge {a b c l m n : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l) (hm : 0 < m) (hn : 0 < n)
    (hs : a + b + c + l + m + n = 1) :
    1 / 6 * (a * b * c * l * m * n) ^ (2 / 5 : ℝ) ≤ i4U a b c l m n := by
  have hp : 0 ≤ a * b * c * l * m * n := by positivity
  apply le_of_pow_le_pow_left₀ (n := 5) (by norm_num) (by unfold i4U; positivity)
  rw [mul_pow, ← Real.rpow_natCast ((a * b * c * l * m * n) ^ (2 / 5 : ℝ)),
    ← Real.rpow_mul hp]
  norm_num
  have h := i4U_lower_pow ha hb hc hl hm hn hs
  have hu : 0 ≤ i4U a b c l m n ^ 5 := by unfold i4U; positivity
  linarith

private theorem i4F_ge {a b c l m n : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hl : 0 < l) (hm : 0 < m) (hn : 0 < n)
    (hs : a + b + c + l + m + n = 1) :
    (a * b * c * l * m * n) ^ 2 ≤ i4F a b c l m n := by
  have h1 : b * c * l ^ 2 * m ^ 2 * n ^ 2 ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) * 1 * 1 ^ 2 * 1 ^ 2 * 1 ^ 2 := by
        gcongr <;> linarith
      _ = _ := by norm_num
  calc
    _ = (a * b * c * a) * (b * c * l ^ 2 * m ^ 2 * n ^ 2) := by ring
    _ ≤ a * b * c * a * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ _ := by
      have hlead : a * b * c * a ≤ a * b * c * (a + b + c + 2 * (l + m + n)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      unfold i4F
      have htail : 0 ≤
          a * b * (a + b) * (l + m) + a * c * (a + c) * (l + m + n) +
          a * n * (a * (l + m) + 2 * (b * (l + m) + c * l)) +
          b * c * (b + c) * (m + n) + b ^ 2 * (l * m + l * n + m * n) +
          c * l * (2 * b + c) * (m + n) := by positivity
      linarith only [hlead, htail]


/-! ### Uniform majorant and differentiation -/

private theorem i4_coordinates_pos {x : I4Coords} (hx : x ∈ i4Dom) :
    0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2.1 ∧ 0 < x.2.2.2.2 ∧
      0 < i4Last x := by
  obtain ⟨ha, hb, hc, hl, hm, hs⟩ := hx
  exact ⟨ha, hb, hc, hl, hm, sub_pos.mpr hs⟩

private theorem i4UF_pos {x : I4Coords} (hx : x ∈ i4Dom) :
    0 < i4SimplexU x ∧ 0 < i4SimplexF x := by
  obtain ⟨ha, hb, hc, hl, hm, hn⟩ := i4_coordinates_pos hx
  unfold i4SimplexU i4SimplexF i4U i4F
  exact ⟨by positivity, by positivity⟩

private noncomputable def i4Integrand (ε : ℂ) (x : I4Coords) : ℂ :=
  (i4SimplexU x : ℂ) ^ (-2 + 4 * ε) * (i4SimplexF x : ℂ) ^ (-3 * ε)

private theorem measurable_i4Integrand (ε : ℂ) : Measurable (i4Integrand ε) := by
  unfold i4Integrand i4SimplexU i4SimplexF i4Last i4U i4F
  fun_prop

private noncomputable def i4Majorant (x : I4Coords) : ℝ :=
  (10000 * (1 / 6 : ℝ) ^ (-(51 / 25) : ℝ)) * i4Product x ^ (-(9 / 10) : ℝ)

private theorem integrableOn_i4Majorant : IntegrableOn i4Majorant i4Dom :=
  integrableOn_i4Product.const_mul _

private theorem rpow_le_hundred_mul {u r s : ℝ} (hu : 0 < u) (hu' : u ≤ 100)
    (hlo : r ≤ s) (hhi : s - r ≤ 1) : u ^ s ≤ 100 * u ^ r := by
  have h : u ^ (s - r) ≤ 100 := by
    by_cases h1 : u ≤ 1
    · exact (Real.rpow_le_one hu.le h1 (by linarith)).trans (by norm_num)
    · calc
        _ ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h1) hhi
        _ ≤ 100 := by simpa
  rw [show s = r + (s - r) by ring, Real.rpow_add hu, mul_comm]
  exact mul_le_mul_of_nonneg_right h (by positivity)

private theorem norm_i4Integrand_le {ε : ℂ} (hε : ‖ε‖ < 1 / 100)
    {x : I4Coords} (hx : x ∈ i4Dom) : ‖i4Integrand ε x‖ ≤ i4Majorant x := by
  obtain ⟨hu, hf⟩ := i4UF_pos hx
  obtain ⟨ha, hb, hc, hl, hm, hn⟩ := i4_coordinates_pos hx
  have hs : x.1 + x.2.1 + x.2.2.1 + x.2.2.2.1 + x.2.2.2.2 + i4Last x = 1 := by
    unfold i4Last
    ring
  have hp : 0 < i4Product x := by unfold i4Product; positivity
  have hp1 : i4Product x ≤ 1 := by
    unfold i4Product
    calc
      _ ≤ (1 : ℝ) * 1 * 1 * 1 * 1 * 1 := by gcongr <;> linarith
      _ = _ := by norm_num
  have hu1 : i4SimplexU x ≤ 100 := by
    calc
      _ ≤ i4U 1 1 1 1 1 1 := by unfold i4SimplexU i4U; gcongr <;> linarith
      _ ≤ _ := by norm_num [i4U]
  have hf1 : i4SimplexF x ≤ 100 := by
    calc
      _ ≤ i4F 1 1 1 1 1 1 := by unfold i4SimplexF i4F; gcongr <;> linarith
      _ ≤ _ := by norm_num [i4F]
  have hU := i4U_ge ha hb hc hl hm hn hs
  have hF := i4F_ge ha hb hc hl hm hn hs
  have hre := abs_le.mp ((abs_re_le_norm ε).trans hε.le)
  rw [i4Integrand, norm_mul, norm_cpow_eq_rpow_re_of_pos hu,
    norm_cpow_eq_rpow_re_of_pos hf]
  simp only [add_re, mul_re, neg_re, re_ofNat, im_ofNat, zero_mul, sub_zero, neg_im,
    neg_zero]
  have huB := rpow_le_hundred_mul hu hu1 (r := -(51 / 25)) (s := -2 + 4 * ε.re)
    (by linarith [hre.1]) (by linarith [hre.2])
  have hfB := rpow_le_hundred_mul hf hf1 (r := -(3 / 100)) (s := -3 * ε.re)
    (by linarith [hre.2]) (by linarith [hre.1])
  have huP : i4SimplexU x ^ (-(51 / 25) : ℝ) ≤
      (1 / 6 * i4Product x ^ (2 / 5 : ℝ)) ^ (-(51 / 25) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hU (by norm_num)
  have hfP : i4SimplexF x ^ (-(3 / 100) : ℝ) ≤
      (i4Product x ^ 2) ^ (-(3 / 100) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hF (by norm_num)
  refine (mul_le_mul huB hfB (by positivity) (by positivity)).trans ?_
  refine (mul_le_mul (mul_le_mul_of_nonneg_left huP (by norm_num))
    (mul_le_mul_of_nonneg_left hfP (by norm_num)) (by positivity) (by positivity)).trans ?_
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 6) (by positivity),
    ← Real.rpow_mul hp.le, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  unfold i4Majorant
  calc
    _ = (10000 * (1 / 6 : ℝ) ^ (-(51 / 25) : ℝ)) *
        i4Product x ^ (-(219 / 250) : ℝ) := by
      rw [show -(219 / 250 : ℝ) = 2 / 5 * -(51 / 25) + (2 : ℕ) * -(3 / 100) by norm_num,
        Real.rpow_add hp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hp hp1 (by norm_num)) (by positivity)

/-- The projective integrand is integrable for a disk about zero regulator. -/
theorem integrableOn_i4Integrand {ε : ℂ} (hε : ‖ε‖ < 1 / 100) :
    IntegrableOn (fun x =>
      (i4SimplexU x : ℂ) ^ (-2 + 4 * ε) * (i4SimplexF x : ℂ) ^ (-3 * ε)) i4Dom :=
  integrableOn_i4Majorant.mono' (measurable_i4Integrand ε).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_i4Dom fun _ hx => norm_i4Integrand_le hε hx)

private theorem differentiableAt_i4PInt {ε₀ : ℂ} (h0 : ‖ε₀‖ < 1 / 200) :
    DifferentiableAt ℂ i4PInt ε₀ := by
  change DifferentiableAt ℂ (fun ε => ∫ x in i4Dom, i4Integrand ε x) ε₀
  refine QED.DimReg.differentiableAt_integral_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 200)
    integrableOn_i4Majorant (fun ε _ => (measurable_i4Integrand ε).aestronglyMeasurable) ?_ ?_
  · refine ae_restrict_of_forall_mem measurableSet_i4Dom fun x hx ε hε => ?_
    apply norm_i4Integrand_le _ hx
    have h := norm_sub_norm_le ε ε₀
    rw [Metric.mem_ball, dist_eq_norm] at hε
    linarith
  · refine ae_restrict_of_forall_mem measurableSet_i4Dom fun x hx ε _ => ?_
    obtain ⟨hu, hf⟩ := i4UF_pos hx
    apply DifferentiableAt.differentiableWithinAt
    unfold i4Integrand
    exact ((by fun_prop : DifferentiableAt ℂ (fun ε : ℂ => -2 + 4 * ε) ε).const_cpow
      (Or.inl (ofReal_ne_zero.mpr hu.ne'))).mul
      ((by fun_prop : DifferentiableAt ℂ (fun ε : ℂ => -3 * ε) ε).const_cpow
      (Or.inl (ofReal_ne_zero.mpr hf.ne')))

/-- The projective integral is analytic at zero regulator. -/
theorem analyticAt_i4PInt : AnalyticAt ℂ i4PInt 0 := by
  refine DifferentiableOn.analyticAt (s := Metric.ball 0 (1 / 200)) ?_
    (Metric.ball_mem_nhds _ (by norm_num))
  exact fun _ hε => (differentiableAt_i4PInt (by simpa using hε)).differentiableWithinAt


/-- The logarithmic factor in each regulator derivative of the integrand. -/
noncomputable def i4LogWeight (x : I4Coords) : ℝ :=
  4 * Real.log (i4SimplexU x) - 3 * Real.log (i4SimplexF x)

private noncomputable def i4DerivIntegrand (k : ℕ) (ε : ℂ) (x : I4Coords) : ℂ :=
  i9KExp k (-2 * Real.log (i4SimplexU x)) (i4LogWeight x) ε

private theorem i4DerivIntegrand_zero {x : I4Coords} (hx : x ∈ i4Dom) (ε : ℂ) :
    i4DerivIntegrand 0 ε x = i4Integrand ε x := by
  obtain ⟨hu, hf⟩ := i4UF_pos hx
  unfold i4DerivIntegrand i9KExp i4Integrand i4LogWeight
  rw [i9_cpow_eq_exp hu, i9_cpow_eq_exp hf, pow_zero, one_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem i4DerivIntegrand_at_zero {x : I4Coords} (hx : x ∈ i4Dom) (k : ℕ) :
    i4DerivIntegrand k 0 x = ((i4LogWeight x ^ k / i4SimplexU x ^ 2 : ℝ) : ℂ) := by
  obtain ⟨hu, -⟩ := i4UF_pos hx
  have he : Real.exp (-2 * Real.log (i4SimplexU x)) = (i4SimplexU x ^ 2)⁻¹ := by
    rw [show -2 * Real.log (i4SimplexU x) = Real.log ((i4SimplexU x ^ 2)⁻¹) by
      rw [Real.log_inv, Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  unfold i4DerivIntegrand i9KExp
  rw [zero_mul, add_zero, ← ofReal_exp, he]
  push_cast
  rw [div_eq_mul_inv]

/-- The first three regulator derivatives at zero are integrals of powers of the log weight
against the tetrahedron period density. Divide the second derivative by two for the Taylor
coefficient. -/
theorem iteratedDeriv_i4PInt {k : ℕ} (hk : k ≤ 2) :
    iteratedDeriv k i4PInt 0 =
      ((∫ x in i4Dom, i4LogWeight x ^ k / i4SimplexU x ^ 2 : ℝ) : ℂ) := by
  have e : i4PInt = fun ε => ∫ x in i4Dom, i4DerivIntegrand 0 ε x := funext fun ε =>
    setIntegral_congr_fun measurableSet_i4Dom fun x hx => (i4DerivIntegrand_zero hx ε).symm
  have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
  rw [e, iteratedDeriv_integral_of_chain
    (D := i4DerivIntegrand) (R := 1 / 100) (ρ := 1 / 300) (b := i4Majorant)
    (by norm_num) (Filter.Eventually.of_forall fun x k ε => hasDerivAt_i9KExp k _ _ ε)
    (ae_restrict_of_forall_mem measurableSet_i4Dom fun x hx ε hε => by
      rw [i4DerivIntegrand_zero hx]; exact norm_i4Integrand_le hε hx)
    integrableOn_i4Majorant (fun k ε => by
      have hm : Measurable (i4DerivIntegrand k ε) := by
        unfold i4DerivIntegrand i9KExp i4LogWeight i4SimplexU i4SimplexF i4Last i4U i4F
        fun_prop
      exact hm.aestronglyMeasurable) k 0 (by simp; linarith),
    ← integral_complex_ofReal]
  exact setIntegral_congr_fun measurableSet_i4Dom fun x hx => i4DerivIntegrand_at_zero hx k

/-- Values of the first three derivatives suffice for the normalized master expansion. -/
theorem hasTruncLaurent_setEMasterI4_of_coeffs (h0 : i4PInt 0 = i4P0)
    (h1 : iteratedDeriv 1 i4PInt 0 = i4P1) (h2 : iteratedDeriv 2 i4PInt 0 / 2 = i4P2) :
    HasTruncLaurent setEMasterI4 setELaurentI4 2 := by
  refine hasTruncLaurent_setEMasterI4_of_P ?_
  obtain ⟨R, hR, hev⟩ := hasTruncLaurent_of_analyticAt_zero analyticAt_i4PInt 3
  refine ⟨R, hR, hev.mono fun ε hε => ?_⟩
  rw [hε, i4PLaurent, ← h0, ← h1, ← h2]
  simp [Finset.sum_range_succ]


/-! ### The common tetrahedron period -/

private noncomputable def i4Period (z : Fin 6 → ℝ) : ℝ :=
  (i4U (z 0) (z 1) (z 4) (z 5) (z 2) (z 3) ^ 2)⁻¹

private theorem i4Period_smul (z : Fin 6 → ℝ) (t : ℝ) :
    i4Period (t • z) = (t ^ 6)⁻¹ • i4Period z := by
  have h : i4U (t * z 0) (t * z 1) (t * z 4) (t * z 5) (t * z 2) (t * z 3) =
      t ^ 3 * i4U (z 0) (z 1) (z 4) (z 5) (z 2) (z 3) := by unfold i4U; ring
  simp only [i4Period, Pi.smul_apply, smul_eq_mul, h, mul_pow, ← pow_mul, mul_inv_rev]
  ring

private theorem i4_gauge_polynomial {a b l y₄ y₇ y₈ : ℝ} (h : a + b + l = 1) :
    i4U a b y₈ l y₄ y₇ =
      (y₇ + a * b) * (y₈ + b * l) + (y₈ + b * l) * (y₄ + a * l) +
        (y₄ + a * l) * (y₇ + a * b) := by
  have hh : l = 1 - a - b := by linarith
  rw [hh]
  unfold i4U
  ring

open QED.Integration Feynman TwoLoop ChengWu in
private theorem i4Period_simplex :
    ∫ x in i4Dom, (i4SimplexU x ^ 2)⁻¹ =
      ∫ x in simplexSet 5, i4Period (simplexPoint x) := by
  classical
  let σ : Equiv.Perm (Fin 5) := Equiv.swap 2 4
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin 5 => ℝ) σ
  have he := volume_measurePreserving_piCongrLeft (fun _ : Fin 5 => ℝ) σ
  have he_apply (x : Fin 5 → ℝ) (i : Fin 5) : e x i = x (σ.symm i) := by
    simpa [e] using MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) σ x (σ.symm i)
  have hep : e ⁻¹' simplexSet 5 = simplexSet 5 := by
    ext x
    simp only [mem_preimage]
    rw [mem_simplexSet_iff (by decide), mem_simplexSet_iff (by decide)]
    have hlast : simplexPoint (e x) (Fin.last 5) = simplexPoint x (Fin.last 5) := by
      simp only [simplexPoint_last, he_apply, Equiv.sum_comp]
    constructor
    · intro h i
      induction i using Fin.lastCases with
      | last => rw [← hlast]; exact h _
      | cast j =>
        simpa only [simplexPoint_castSucc, he_apply, Equiv.symm_apply_apply] using h (σ j).castSucc
    · intro h i
      induction i using Fin.lastCases with
      | last => rw [hlast]; exact h _
      | cast j =>
        simpa only [simplexPoint_castSucc, he_apply] using h (σ.symm j).castSucc
  rw [← measurePreserving_i4CoordsEquiv.setIntegral_preimage_emb
    i4CoordsEquiv.measurableEmbedding, preimage_i4Dom,
    ← setIntegral_congr_set (simplexSet_ae_eq_openSimplex (0 : Fin 5)),
    ← (measurePreserving_simplexSwap (3 : Fin 5)).setIntegral_preimage_emb
      (simplexSwapEquiv 3).measurableEmbedding, preimage_simplexSwap,
    ← he.setIntegral_preimage_emb e.measurableEmbedding, hep]
  refine setIntegral_congr_fun (measurableSet_simplexSet _) fun x _ => ?_
  have hu (z : Fin 5 → ℝ) : i4SimplexU (i4CoordsEquiv z) =
      i4U (simplexPoint z 0) (simplexPoint z 1) (simplexPoint z 2)
        (simplexPoint z 3) (simplexPoint z 4) (simplexPoint z 5) := by
    have hsum : ∑ i, z i = z 0 + (z 1 + (z 2 + (z 3 + z 4))) := by
      simp [Fin.sum_univ_succ]
    simp only [i4SimplexU, i4Last, i4CoordsEquiv_apply,
      show (0 : Fin 6) = (0 : Fin 5).castSucc from rfl,
      show (1 : Fin 6) = (1 : Fin 5).castSucc from rfl,
      show (2 : Fin 6) = (2 : Fin 5).castSucc from rfl,
      show (3 : Fin 6) = (3 : Fin 5).castSucc from rfl,
      show (4 : Fin 6) = (4 : Fin 5).castSucc from rfl,
      show (5 : Fin 6) = Fin.last 5 from rfl,
      simplexPoint_castSucc, simplexPoint_last, hsum, add_assoc]
  rw [hu]
  unfold i4Period
  simp only [simplexPoint_simplexSwap]
  have hlast : simplexPoint (e x) 5 = simplexPoint x 5 := by
    change simplexPoint (e x) (Fin.last 5) = simplexPoint x (Fin.last 5)
    simp only [simplexPoint_last, he_apply, Equiv.sum_comp]
  have shift :
      ∀ i : Fin 6, simplexPoint (e x) i =
        simplexPoint x (Equiv.swap (2 : Fin 6) 4 i) := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      rw [show Equiv.swap (2 : Fin 6) 4 (Fin.last 5) = Fin.last 5 from by decide]
      exact hlast
    | cast j =>
      have hj : Equiv.swap (2 : Fin 6) 4 j.castSucc = (σ.symm j).castSucc := by
        fin_cases j <;> decide
      rw [hj, simplexPoint_castSucc, simplexPoint_castSucc, he_apply]
  simp only [e] at shift
  simp only [shift]
  rfl

private def i4TriangleBox : Set (Fin 5 → ℝ) :=
  {z | (∀ i, 0 < z i) ∧ z 0 < 1 ∧ z 1 < 1}

private def i4TriangleMap (z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  z - (z 1 * z 0) • Pi.single 0 1

private theorem i4TriangleMap_apply (z : Fin 5 → ℝ) (i : Fin 5) :
    i4TriangleMap z i = if i = 0 then (1 - z 1) * z 0 else z i := by
  by_cases h : i = 0
  · subst i
    simp [i4TriangleMap]; ring
  · simp [i4TriangleMap, h]

private noncomputable def i4TriangleDeriv (z : Fin 5 → ℝ) :
    (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ) :=
  ContinuousLinearMap.id ℝ _ -
    (z 1 • (ContinuousLinearMap.proj 0 : (Fin 5 → ℝ) →L[ℝ] ℝ) +
      z 0 • (ContinuousLinearMap.proj 1 : (Fin 5 → ℝ) →L[ℝ] ℝ)).smulRight
      (Pi.single 0 1)

private theorem hasFDerivAt_i4TriangleMap (z : Fin 5 → ℝ) :
    HasFDerivAt i4TriangleMap (i4TriangleDeriv z) z := by
  have h₁ := (ContinuousLinearMap.proj 1 : (Fin 5 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h₀ := (ContinuousLinearMap.proj 0 : (Fin 5 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h := (hasFDerivAt_id z).sub ((h₁.mul h₀).smul_const
    (Pi.single (M := fun _ : Fin 5 => ℝ) 0 1))
  have he : i4TriangleMap = id -
      fun y : Fin 5 → ℝ => (y 1 * y 0) • Pi.single (M := fun _ : Fin 5 => ℝ) 0 1 := by
    funext x i
    rfl
  rw [he]
  simpa only [i4TriangleDeriv, ContinuousLinearMap.proj_apply, Pi.mul_apply] using h

private theorem det_i4TriangleDeriv (z : Fin 5 → ℝ) :
    (i4TriangleDeriv z).det = 1 - z 1 := by
  let u : Fin 5 → ℝ := Pi.single 0 1
  let v : Fin 5 → ℝ := fun j => -(z 1 * u j + z 0 * Pi.single (M := fun _ : Fin 5 => ℝ) 1 1 j)
  have hM : LinearMap.toMatrix' (i4TriangleDeriv z : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ)) =
      1 + Matrix.replicateCol (Fin 1) u * Matrix.replicateRow (Fin 1) v := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    simp only [i4TriangleDeriv, ContinuousLinearMap.coe_coe]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> by_cases hj' : j = 1 <;>
      simp_all [u, v, Pi.single_apply, Matrix.mul_apply, Matrix.one_apply, eq_comm] <;> ring
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', hM,
    Matrix.det_one_add_mul_comm, Matrix.det_fin_one]
  simp [u, v, Matrix.replicateRow_mul_replicateCol_apply, sub_eq_add_neg]

private theorem preimage_i4TriangleBox : i4CoordsEquiv ⁻¹' i2Dom = i4TriangleBox := by
  ext z
  simp [i4CoordsEquiv_apply, i2Dom, i4TriangleBox, Fin.forall_fin_succ]
  tauto

open QED.TwoLoop.UnitXGraph in
private theorem image_i4TriangleMap :
    i4TriangleMap '' i4TriangleBox = cwSet ({0, 1} : Finset (Fin 5)) := by
  ext z
  simp only [mem_cwSet, Finset.sum_insert (by decide : (0 : Fin 5) ∉ ({1} : Finset (Fin 5))),
    Finset.sum_singleton]
  constructor
  · rintro ⟨w, ⟨hw, hx, hy⟩, rfl⟩
    have hy' := sub_pos.mpr hy
    refine ⟨fun i => ?_, ?_⟩
    · rw [i4TriangleMap_apply]
      split
      · exact mul_pos hy' (hw 0)
      · exact hw i
    · simp only [i4TriangleMap_apply, ite_true,
        ite_eq_right (by decide : (1 : Fin 5) ≠ 0)]
      linarith [mul_pos hy' (sub_pos.mpr hx)]
  · rintro ⟨hz, hs⟩
    have hz1 : z 1 < 1 := by linarith [hz 0]
    have hpos := sub_pos.mpr hz1
    refine ⟨Function.update z 0 (z 0 / (1 - z 1)), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i
      by_cases hi : i = 0
      · subst i; simpa using div_pos (hz 0) hpos
      · simpa [Function.update_of_ne hi] using hz i
    · rw [Function.update_self, div_lt_one hpos]
      linarith
    · simpa using hz1
    · ext i
      by_cases hi : i = 0
      · subst i
        simp [i4TriangleMap_apply, hpos.ne', mul_div_cancel₀]
      · simp [i4TriangleMap_apply, hi]

private theorem injOn_i4TriangleMap : InjOn i4TriangleMap i4TriangleBox := by
  intro x hx y _ h
  have hn (i : Fin 5) (hi : i ≠ 0) : x i = y i := by
    simpa only [i4TriangleMap_apply, ite_eq_right hi] using congrFun h i
  ext i
  by_cases hi : i = 0
  · subst i
    have h1 := hn 1 (by decide)
    have h0 := congrFun h 0
    simp only [i4TriangleMap_apply, ite_true, ← h1] at h0
    exact mul_left_cancel₀ (sub_pos.mpr hx.2.2).ne' h0
  · exact hn i hi

open QED.Integration.Feynman QED.TwoLoop.UnitXGraph in
private theorem i4Period_eq_i2Period :
    ∫ x in i4Dom, (i4SimplexU x ^ 2)⁻¹ =
      ∫ x in i2Dom, (1 - x.2.1) * (i2U x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ^ 2)⁻¹ := by
  rw [i4Period_simplex, integral_simplex_chengWuSet (by decide : 0 < 5)
    ({0, 1} : Finset (Fin 5)) i4Period (fun z _ t _ => i4Period_smul z t),
    ← image_i4TriangleMap]
  have hm : MeasurableSet i4TriangleBox := preimage_i4TriangleBox ▸
    i4CoordsEquiv.measurable (measurableSet_Ioo.prod (measurableSet_Ioo.prod
      (measurableSet_Ioi.prod (measurableSet_Ioi.prod measurableSet_Ioi))))
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hm
    (fun z _ => (hasFDerivAt_i4TriangleMap z).hasFDerivWithinAt) injOn_i4TriangleMap,
    ← measurePreserving_i4CoordsEquiv.setIntegral_preimage_emb
      i4CoordsEquiv.measurableEmbedding, preimage_i4TriangleBox]
  refine setIntegral_congr_fun hm fun x hx => ?_
  rw [det_i4TriangleDeriv, abs_of_pos (sub_pos.mpr hx.2.2), smul_eq_mul, i4CoordsEquiv_apply]
  congr 1
  simp only [i4Period]
  have hsnoc (w : Fin 5 → ℝ) (t : ℝ) (i : Fin 5) :
      Fin.snoc (α := fun _ : Fin 6 => ℝ) w t i.castSucc = w i :=
    Fin.snoc_castSucc (α := fun _ : Fin 6 => ℝ) t w i
  simp only [show (5 : Fin 6) = Fin.last 5 from rfl, Fin.snoc_last,
    show (0 : Fin 6) = (0 : Fin 5).castSucc from rfl,
    show (1 : Fin 6) = (1 : Fin 5).castSucc from rfl,
    show (2 : Fin 6) = (2 : Fin 5).castSucc from rfl,
    show (3 : Fin 6) = (3 : Fin 5).castSucc from rfl,
    show (4 : Fin 6) = (4 : Fin 5).castSucc from rfl, hsnoc,
    Finset.sum_insert (by decide : (0 : Fin 5) ∉ ({1} : Finset (Fin 5))), Finset.sum_singleton]
  simp only [i4TriangleMap_apply, ite_true,
        ite_eq_right (by decide : (1 : Fin 5) ≠ 0),
    ite_eq_right (by decide : (2 : Fin 5) ≠ 0), ite_eq_right (by decide : (3 : Fin 5) ≠ 0),
    ite_eq_right (by decide : (4 : Fin 5) ≠ 0)]
  rw [i4_gauge_polynomial (by ring)]
  unfold i2U i2LineA i2LineB i2LineC
  ring

/-- The value at zero is the common tetrahedron period evaluated for set (d). -/
theorem i4PInt_zero_eq : i4PInt 0 = i4P0 := by
  have h : i4PInt 0 = i2PInt 0 := by
    rw [← iteratedDeriv_zero (f := i4PInt), iteratedDeriv_i4PInt (by decide : 0 ≤ 2)]
    simp only [pow_zero, one_div]
    rw [i4Period_eq_i2Period, ← integral_complex_ofReal, i2PInt_eq]
    refine setIntegral_congr_fun (measurableSet_Ioo.prod (measurableSet_Ioo.prod
      (measurableSet_Ioi.prod (measurableSet_Ioi.prod measurableSet_Ioi)))) fun x hx => ?_
    obtain ⟨hu, hf⟩ := i2UF_pos hx
    unfold i2Integrand
    simp only [mul_zero, add_zero, cpow_zero, mul_one, ofReal_mul, ofReal_inv, ofReal_pow]
    rw [show (-2 : ℂ) = ((-2 : ℤ) : ℂ) by norm_num, Complex.cpow_intCast]
    simp
  rw [h, i2PInt_zero_eq]
  rfl

end QED.ThreeLoopE
