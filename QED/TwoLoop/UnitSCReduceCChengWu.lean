/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCReduceC
public import QED.TwoLoop.UnitXGraphReduceChengWu
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner pair in the hierarchical variables of section 2.2

Section 8 of `docs/TWO-LOOP-UNITS.md`, the `S + C` link, reductions for the corner classes (the
analogue of `QED/TwoLoop/UnitXGraphReduceChengWu.lean`). The merged integrand `cornerF4`
(`QED/TwoLoop/UnitSCReduceC.lean`) is homogeneous of degree `-5` in the group sums
`(z_o, y₃, y₄, z_a, z_b)` (`cornerF4_smul`), so the Cheng–Wu theorem with the constraint on the
inner vertex simplex `y₃ + y₄ + z_b = 1` (`T = {y₃, y₄}`) turns the integral over `Δ₄` into one
over `z_o, z_a ∈ (0, ∞)` and `(y₃, y₄)` in the open triangle:

* `sixteen_pi_pow_four_mul_openZero_Cp_eq_chengWu`, `…_eq_iterated`: for `m = e = 1` and
  `0 < m_γ < Λ`,
  `16π⁴ (1/(64 m⁵)) (1/i) openZero C₊ = ∫_{y₃, y₄ > 0, y₃ + y₄ < 1} ∫₀^∞ dz_o ∫₀^∞ dz_a
    cornerF4(z_o, y₃, y₄, z_a, 1 - y₃ - y₄)`, with integrability;
* `sixteen_pi_pow_four_mul_openZero_C_eq_iterated`: **the corner pair**
  `16π⁴ (1/(64 m⁵)) (1/i) (openZero C₊ + openZero C₋)` is twice that (the mirror identity
  `openZero_Cm_eq_Cp`), the factor `2` of eq. (6.3) of the document.

In this frame the **splitting identity (2.1)** holds (`gCU_frame`, `gCE_frame`): with
`Y = y₃ + y₄`, `b = z_o + g`, `w = z_a + e`, `g = y₃ z_b`, `e = y₃ y₄` (the row `C₊` of the
table of section 2.2), `U = b + w` and `E = Y² + b²/(b + w)`, so
`V_{μ_a μ_b} = Y² + (1 - Y) μ_b + b²/(b + w) + μ_a (w - e)`. After `w = b(1-x)/x` (Jacobian
`b/x²`), `cornerTerm` is the integrand `A₂/D² + A₁/D` of eq. (6.2) of the document, with its
polynomials `p₁, p₂` (`cornerTerm_subst`), `D = Y² + (1-Y) μ_b - μ_a e + b h(x)`,
`h(x) = (x² + (1-x) μ_a)/x`; the constraint `z_a > 0` is `b > e x/(1-x)` (the lower limit
`β(x) = max(g, e x/(1-x))` of section 2.2).
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.TwoLoop.UnitSCReduce

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitSCGraph
open QED.TwoLoop.UnitLGraphReduce QED.TwoLoop.UnitXGraph
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### Homogeneity -/

theorem gCU_smul (t o y3 y4 a b : ℝ) :
    gCU (t * o) (t * y3) (t * y4) (t * a) (t * b) = t ^ 2 * gCU o y3 y4 a b := by
  unfold gCU; ring

theorem gCEn_smul (t o y3 y4 a b : ℝ) :
    gCEn (t * o) (t * y3) (t * y4) (t * a) (t * b) = t ^ 3 * gCEn o y3 y4 a b := by
  unfold gCEn; ring

theorem gCW_smul (t o y3 y4 b : ℝ) :
    gCW (t * o) (t * y3) (t * y4) (t * b) = t ^ 2 * gCW o y3 y4 b := by
  unfold gCW; ring

theorem gCM1_smul (t o s y3 y4 a b : ℝ) :
    gCM1 (t * o) (t * s) (t * y3) (t * y4) (t * a) (t * b) = t ^ 6 * gCM1 o s y3 y4 a b := by
  simp only [gCM1, cpM1pa, cpM1pb, cpM1pc, cpM1pd]; ring

theorem gCM2_smul (t o s y3 y4 a b : ℝ) :
    gCM2 (t * o) (t * s) (t * y3) (t * y4) (t * a) (t * b) = t ^ 5 * gCM2 o s y3 y4 a b := by
  simp only [gCM2, cpM2pa, cpM2pb, cpM2pc, cpM2pd]; ring

theorem gCE_pos {o y3 y4 a b : ℝ} (ho : 0 < o) (h3 : 0 < y3) (h4 : 0 < y4) (ha : 0 < a)
    (hb : 0 < b) : 0 < gCE o y3 y4 a b := by
  have := gCU_pos ho h3 h4 ha hb
  unfold gCE gCEn
  positivity

theorem cornerTerm_smul {μa μb o y3 y4 a b t : ℝ} (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) (ho : 0 < o)
    (h3 : 0 < y3) (h4 : 0 < y4) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    cornerTerm μa μb (t * o) (t * y3) (t * y4) (t * a) (t * b) =
      (t ^ 5)⁻¹ * cornerTerm μa μb o y3 y4 a b := by
  have hU := gCU_pos ho h3 h4 ha hb
  have hE := gCE_pos ho h3 h4 ha hb
  have hV : 0 < gCE o y3 y4 a b + μa * a + μb * b := by positivity
  have eE : gCE (t * o) (t * y3) (t * y4) (t * a) (t * b) = t * gCE o y3 y4 a b := by
    unfold gCE
    rw [gCEn_smul, gCU_smul]
    field_simp
  have eV : gCE (t * o) (t * y3) (t * y4) (t * a) (t * b) + μa * (t * a) + μb * (t * b) =
      t * (gCE o y3 y4 a b + μa * a + μb * b) := by rw [eE]; ring
  unfold cornerTerm
  rw [eV, gCU_smul, show t * o / 2 = t * (o / 2) by ring, gCW_smul, gCM1_smul, gCM2_smul]
  field_simp

theorem cornerF4_smul (P : Params) {z : Fin 5 → ℝ} (hz : ∀ i, 0 < z i) {t : ℝ} (ht : 0 < t) :
    cornerF4 P (t • z) = (t ^ 5)⁻¹ * cornerF4 P z := by
  have h0 : 0 ≤ P.mγ ^ 2 := sq_nonneg _
  have hΛ : 0 ≤ P.Λ ^ 2 := sq_nonneg _
  simp only [cornerF4, Pi.smul_apply, smul_eq_mul]
  rw [cornerTerm_smul h0 h0 (hz 0) (hz 1) (hz 2) (hz 3) (hz 4) ht,
    cornerTerm_smul h0 hΛ (hz 0) (hz 1) (hz 2) (hz 3) (hz 4) ht,
    cornerTerm_smul hΛ h0 (hz 0) (hz 1) (hz 2) (hz 3) (hz 4) ht,
    cornerTerm_smul hΛ hΛ (hz 0) (hz 1) (hz 2) (hz 3) (hz 4) ht]
  ring

/-! ### The splitting identity (2.1) in the frame `y₃ + y₄ + z_b = 1` -/

/-- **The splitting identity, `U`**: `U = b + w` with `b = z_o + y₃ z_b`, `w = z_a + y₃ y₄`. -/
theorem gCU_frame (o y3 y4 a : ℝ) :
    gCU o y3 y4 a (1 - y3 - y4) = (o + y3 * (1 - y3 - y4)) + (a + y3 * y4) := by
  unfold gCU; ring

/-- **The splitting identity, `E`**: `E = Y² + b²/(b + w)`. -/
theorem gCE_frame {o y3 y4 a : ℝ} (hU : gCU o y3 y4 a (1 - y3 - y4) ≠ 0) :
    gCE o y3 y4 a (1 - y3 - y4) =
      (y3 + y4) ^ 2 + (o + y3 * (1 - y3 - y4)) ^ 2 /
        ((o + y3 * (1 - y3 - y4)) + (a + y3 * y4)) := by
  rw [gCU_frame] at hU
  unfold gCE
  rw [gCU_frame]
  field_simp
  unfold gCEn
  ring

/-- The polynomial `p₁` of eq. (6.2) of the document. -/
def cornerP1 (x y3 y4 : ℝ) : ℝ :=
  2 * x ^ 3 * y3 ^ 2 - 2 * x ^ 3 * y3 - 6 * x ^ 2 * y3 ^ 2 - 4 * x ^ 2 * y3 * y4 + 6 * x ^ 2 * y3 +
    2 * x ^ 2 * y4 - x ^ 2 + 6 * x * y3 ^ 2 + 8 * x * y3 * y4 - 6 * x * y3 + 2 * x * y4 ^ 2 -
    6 * x * y4 - 2 * y3 ^ 2 - 4 * y3 * y4 + 4 * y3 - 2 * y4 ^ 2 + 4 * y4

/-- The polynomial `p₂` of eq. (6.2) of the document. -/
def cornerP2 (x y3 y4 : ℝ) : ℝ :=
  8 * x ^ 2 * y3 ^ 2 - 8 * x ^ 2 * y3 - 10 * x * y3 ^ 2 - 4 * x * y3 * y4 + 2 * x * y3 -
    2 * x * y4 + 5 * x + 2 * y3 ^ 2 + 4 * y3 - 2 * y4 ^ 2 + 4 * y4 - 4

/-- **After `w = b(1-x)/x`** (with the Jacobian `b/x²`), `cornerTerm` in the frame
`y₃ + y₄ + z_b = 1` is the integrand `A₂/D² + A₁/D` of eq. (6.2) of the document:
`A₂ = x(b-g)[p₁ b + x(2-x)(1-2y₃) g]/(4b²)`, `A₁ = -x(b-g)[2(x-1)b² + p₂ b - 3x(1-2y₃) g]/(4b³)`,
`D = Y² + (1-Y) μ_b - μ_a e + b (x² + (1-x) μ_a)/x`, `g = y₃(1-Y)`, `e = y₃ y₄`. -/
theorem cornerTerm_subst {μa μb y3 y4 b x : ℝ} (hb : 0 < b) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hD : 0 < (y3 + y4) ^ 2 + (1 - (y3 + y4)) * μb - μa * (y3 * y4) +
      b * ((x ^ 2 + (1 - x) * μa) / x)) :
    cornerTerm μa μb (b - y3 * (1 - y3 - y4)) y3 y4 (b * (1 - x) / x - y3 * y4) (1 - y3 - y4) *
        (b / x ^ 2) =
      x * (b - y3 * (1 - y3 - y4)) * (cornerP1 x y3 y4 * b +
          x * (2 - x) * (1 - 2 * y3) * (y3 * (1 - y3 - y4))) / (4 * b ^ 2) /
        ((y3 + y4) ^ 2 + (1 - (y3 + y4)) * μb - μa * (y3 * y4) +
          b * ((x ^ 2 + (1 - x) * μa) / x)) ^ 2 +
      -(x * (b - y3 * (1 - y3 - y4)) * (2 * (x - 1) * b ^ 2 + cornerP2 x y3 y4 * b -
          3 * x * (1 - 2 * y3) * (y3 * (1 - y3 - y4)))) / (4 * b ^ 3) /
        ((y3 + y4) ^ 2 + (1 - (y3 + y4)) * μb - μa * (y3 * y4) +
          b * ((x ^ 2 + (1 - x) * μa) / x)) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hU : gCU (b - y3 * (1 - y3 - y4)) y3 y4 (b * (1 - x) / x - y3 * y4) (1 - y3 - y4) =
      b / x := by
    rw [gCU_frame]; field_simp; ring
  have hU0 : gCU (b - y3 * (1 - y3 - y4)) y3 y4 (b * (1 - x) / x - y3 * y4) (1 - y3 - y4) ≠ 0 := by
    rw [hU]; positivity
  have hV : gCE (b - y3 * (1 - y3 - y4)) y3 y4 (b * (1 - x) / x - y3 * y4) (1 - y3 - y4) +
      μa * (b * (1 - x) / x - y3 * y4) + μb * (1 - y3 - y4) =
      (y3 + y4) ^ 2 + (1 - (y3 + y4)) * μb - μa * (y3 * y4) +
        b * ((x ^ 2 + (1 - x) * μa) / x) := by
    rw [gCE_frame hU0]
    have := hb.ne'
    have := hx0.ne'
    have hbx : b - y3 * (1 - y3 - y4) + y3 * (1 - y3 - y4) +
        (b * (1 - x) / x - y3 * y4 + y3 * y4) = b / x := by field_simp; ring
    rw [hbx]
    field_simp
    ring
  unfold cornerTerm
  rw [hV, hU]
  have := hD.ne'
  simp only [gCW, gCM1, gCM2, cornerP1, cornerP2, cpM1pa, cpM1pb, cpM1pc, cpM1pd, cpM2pa, cpM2pb,
    cpM2pc, cpM2pd]
  field_simp
  ring

/-! ### The theorem -/

/-- **The class `C₊` in the hierarchical Cheng–Wu variables** (`m = e = 1`, `0 < m_γ < Λ`):
`16π⁴ (1/(64 m⁵)) (1/i) openZero C₊ = ∫_D cornerF4(z_o, y₃, y₄, z_a, 1 - y₃ - y₄)` over
`D = {z_o, y₃, y₄, z_a > 0, y₃ + y₄ < 1}`, and the integrand is integrable on `D`. -/
theorem sixteen_pi_pow_four_mul_openZero_Cp_eq_chengWu {P : Params} (hm : P.m = 1)
    (he : P.e = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    IntegrableOn (fun w : Fin 4 → ℝ => cornerF4 P (Fin.snoc w (1 - (w 1 + w 2))))
      (cwSet innerSet) ∧
    16 * (π : ℂ) ^ 4 * (1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * openZero .Cp P)) =
      ((∫ w in cwSet innerSet, cornerF4 P (Fin.snoc w (1 - (w 1 + w 2))) : ℝ) : ℂ) := by
  obtain ⟨hI, hEq⟩ := sixteen_pi_pow_four_mul_openZero_Cp_eq_simplex hm he hmγ hΛ
  have hF : ∀ z : Fin 5 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      cornerF4 P (t • z) = (t ^ 5)⁻¹ • cornerF4 P z := fun z hz t ht => by
    rw [smul_eq_mul]; exact cornerF4_smul P hz ht
  have hCW := integral_simplex_chengWuSet (by norm_num) innerSet (cornerF4 P) hF
  have hCWi := (integrableOn_simplex_chengWuSet_iff (by norm_num) innerSet (cornerF4 P) hF).mp hI
  simp only [sum_innerSet] at hCW hCWi
  exact ⟨hCWi, by rw [hEq, hCW]⟩

/-- **The class `C₊` as an iterated integral in the hierarchical variables** (`m = e = 1`,
`0 < m_γ < Λ`). -/
theorem sixteen_pi_pow_four_mul_openZero_Cp_eq_iterated {P : Params} (hm : P.m = 1)
    (he : P.e = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    16 * (π : ℂ) ^ 4 * (1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * openZero .Cp P)) =
      ((∫ p in innerTriangle, ∫ zo in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
        cornerF4 P ![zo, p.1, p.2, za, 1 - (p.1 + p.2)] : ℝ) : ℂ) := by
  obtain ⟨hI, hEq⟩ := sixteen_pi_pow_four_mul_openZero_Cp_eq_chengWu hm he hmγ hΛ
  rw [hEq, integral_cwSet_innerSet hI]
  rfl

/-- **The corner pair `C₊ + C₋` as twice the iterated integral** (`m = e = 1`, `0 < m_γ < Λ`):
the factor `2` of eq. (6.3) of the document. -/
theorem sixteen_pi_pow_four_mul_openZero_C_eq_iterated {P : Params} (hm : P.m = 1)
    (he : P.e = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    16 * (π : ℂ) ^ 4 * (1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * (openZero .Cp P + openZero .Cm P))) =
      ((2 * ∫ p in innerTriangle, ∫ zo in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
        cornerF4 P ![zo, p.1, p.2, za, 1 - (p.1 + p.2)] : ℝ) : ℂ) := by
  have h := sixteen_pi_pow_four_mul_openZero_Cp_eq_iterated hm he hmγ hΛ
  rw [openZero_Cm_eq_Cp hm he]
  push_cast
  rw [← h]
  ring

end QED.TwoLoop.UnitSCReduce

end
