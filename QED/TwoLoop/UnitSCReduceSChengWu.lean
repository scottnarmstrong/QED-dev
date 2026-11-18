/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCReduceS
public import QED.TwoLoop.UnitLGraphReduceChengWu
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The self-energy pair in the variables of eq. (5.1) of the document

Section 8 of `docs/TWO-LOOP-UNITS.md`, the `S + C` link, reductions for the self-energy classes
(the analogue of `QED/TwoLoop/UnitLGraphReduceChengWu.lean`). The merged integrand `selfF4`
(`QED/TwoLoop/UnitSCReduceS.lean`) is homogeneous of degree `-4` in the group sums
`(z_o, Y, z_a, z_b)` (`selfF4_smul`), so the Cheng–Wu theorem with the constraint on the inner
self-energy loop `Y + z_b = 1` turns the integral over `Δ₃` into one over `Y ∈ (0, 1)`,
`z_o, z_a ∈ (0, ∞)`. There `s = 1`, `c = Y(1-Y)`, `a = z_o + c` (the document's outer electron
parameter `b` of section 2.2, `b ≥ c`), `U = a + z_a`, and the integrand is
`f_S(Y, a, z_a; μ_a, μ_b) = ((a - c)²/2) z_a [-a²(2U + z_a(1-Y))/(2U⁶ D²) + (3YU + 2z_a(1-Y))/(U⁵ D)]`
(`selfDocF`), `D = Y² + (1-Y) μ_b + a²/U + μ_a z_a` (eq. (2.1)), summed over the photon masses
`μ_a, μ_b ∈ {m_γ², Λ²}` with the Pauli–Villars signs (`selfDocSum`). After the substitution
`z_a = a(1-x)/x` (Jacobian `a/x²`) this is the document's eq. (5.1),
`A₂/D² + A₁/D` with `A₂ = x²(x-1)(a-c)²(Yx-Y-x+3)/(4a)`, `A₁ = -x(x-1)(a-c)²(2Yx+Y-2x+2)/(2a²)`
(`selfDocF_subst`).

* `sixteen_pi_pow_four_mul_openZero_Sp_eq_doc`: for `m = e = 1` and `0 < m_γ < Λ`,
  `16π⁴ (1/(64 m⁵)) (1/i) openZero S₊ = ∫_{(z_o, Y, z_a) ∈ D} selfDocSum(Y, z_o, z_a)`,
  `D = {z_o > 0, 0 < Y < 1, z_a > 0}`, and the integrand is integrable on `D`;
* `sixteen_pi_pow_four_mul_openZero_Sp_eq_doc_iterated`: the same as the iterated integral
  `∫₀¹ dY ∫₀^∞ dz_o ∫₀^∞ dz_a`;
* `sixteen_pi_pow_four_mul_openZero_S_eq_doc_iterated`: **the self-energy pair**,
  `16π⁴ (1/(64 m⁵)) (1/i) (openZero S₊ + openZero S₋) = 2 ∫₀¹ dY ∫₀^∞ dz_o ∫₀^∞ dz_a selfDocSum`
  (with the mirror identity `QED.TwoLoop.UnitSCReduce.openZero_Sm_eq_Sp`): the factor `2` of
  eq. (5.3) of the document.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.TwoLoop.UnitSCReduce

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitSCGraph
open QED.TwoLoop.UnitLGraphReduce
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.ChengWu (chengWuSet integral_simplex_chengWu integrableOn_simplex_chengWu_iff)

/-! ### Homogeneity -/

/-- **`selfTerm` is homogeneous of degree `-4`.** -/
theorem selfTerm_smul {μa μb A B a b t : ℝ} (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) (hA : 0 < A)
    (hB : 0 < B) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    selfTerm μa μb (t * A) (t * B) (t * a) (t * b) = (t ^ 4)⁻¹ * selfTerm μa μb A B a b := by
  have hU := gU_pos hA hB ha hb
  have hV : 0 < gE A B a b + μa * a + μb * b := by
    have : 0 < gE A B a b := by
      unfold gE; have := hU; unfold ga gS gc; positivity
    positivity
  have eU : gU (t * A) (t * B) (t * a) (t * b) = t ^ 2 * gU A B a b := by
    unfold gU ga gS gc; ring
  have e1 : selfN1 (t * A) (t * B) (t * a) (t * b) = t ^ 8 * selfN1 A B a b := by
    unfold selfN1 gU ga gS gc; ring
  have e2 : selfN2 (t * A) (t * B) (t * a) (t * b) = t ^ 5 * selfN2 A B a b := by
    unfold selfN2 gU ga gS gc; ring
  have eV : gE (t * A) (t * B) (t * a) (t * b) + μa * (t * a) + μb * (t * b) =
      t * (gE A B a b + μa * a + μb * b) := by
    rw [gE_smul ht hU.ne']; ring
  unfold selfTerm
  rw [eU, e1, e2, eV]
  have := hU.ne'
  have := hV.ne'
  field_simp

/-- **`selfF4` is homogeneous of degree `-4`** on the positive orthant. -/
theorem selfF4_smul (P : Params) {z : Fin 4 → ℝ} (hz : ∀ i, 0 < z i) {t : ℝ} (ht : 0 < t) :
    selfF4 P (t • z) = (t ^ 4)⁻¹ * selfF4 P z := by
  have h0 : 0 ≤ P.mγ ^ 2 := sq_nonneg _
  have h1 : 0 ≤ P.Λ ^ 2 := sq_nonneg _
  simp only [selfF4, Pi.smul_apply, smul_eq_mul]
  rw [selfTerm_smul h0 h0 (hz 0) (hz 1) (hz 2) (hz 3) ht,
    selfTerm_smul h0 h1 (hz 0) (hz 1) (hz 2) (hz 3) ht,
    selfTerm_smul h1 h0 (hz 0) (hz 1) (hz 2) (hz 3) ht,
    selfTerm_smul h1 h1 (hz 0) (hz 1) (hz 2) (hz 3) ht]
  ring

/-! ### The variables of eq. (5.1) -/

/-- **The integrand of the self-energy class in the frame `Y + z_b = 1`** at photon masses
`μ_a` (outer), `μ_b` (inner), as a function of `Y`, `a = z_o + Y(1-Y)` and `z_a`:
`((a - c)²/2) z_a [-a²(2U + z_a(1-Y))/(2U⁶ D²) + (3YU + 2z_a(1-Y))/(U⁵ D)]`, `U = a + z_a`,
`D = Y² + (1-Y) μ_b + a²/U + μ_a z_a`. -/
noncomputable def selfDocF (Y a za μa μb : ℝ) : ℝ :=
  (a - Y * (1 - Y)) ^ 2 / 2 * za *
    (-(a ^ 2 * (2 * (a + za) + za * (1 - Y))) /
        (2 * (a + za) ^ 6 * (Y ^ 2 + (1 - Y) * μb + a ^ 2 / (a + za) + μa * za) ^ 2) +
      (3 * Y * (a + za) + 2 * za * (1 - Y)) /
        ((a + za) ^ 5 * (Y ^ 2 + (1 - Y) * μb + a ^ 2 / (a + za) + μa * za)))

/-- The Pauli–Villars-signed sum over the photon masses, at `a = z_o + Y(1-Y)`. -/
noncomputable def selfDocSum (P : Params) (Y zo za : ℝ) : ℝ :=
  selfDocF Y (zo + Y * (1 - Y)) za (P.mγ ^ 2) (P.mγ ^ 2) -
    selfDocF Y (zo + Y * (1 - Y)) za (P.mγ ^ 2) (P.Λ ^ 2) -
    selfDocF Y (zo + Y * (1 - Y)) za (P.Λ ^ 2) (P.mγ ^ 2) +
    selfDocF Y (zo + Y * (1 - Y)) za (P.Λ ^ 2) (P.Λ ^ 2)

/-- In the frame `Y + z_b = 1`, `selfTerm` is `selfDocF`. -/
theorem selfTerm_frame {μa μb zo Y za : ℝ} (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) (hA : 0 < zo)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (ha : 0 < za) :
    selfTerm μa μb zo Y za (1 - Y) = selfDocF Y (zo + Y * (1 - Y)) za μa μb := by
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hU := gU_pos hA hY.1 ha hY1
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 hY1
  have eU : gU zo Y za (1 - Y) = zo + Y * (1 - Y) + za := by unfold gU ga gS gc; ring
  have eE : gE zo Y za (1 - Y) = Y ^ 2 + (zo + Y * (1 - Y)) ^ 2 / (zo + Y * (1 - Y) + za) := by
    unfold gE; rw [eU]
    have : 0 < zo + Y * (1 - Y) + za := by positivity
    field_simp
    unfold ga gS gc
    ring
  have hD : 0 < Y ^ 2 + (1 - Y) * μb + (zo + Y * (1 - Y)) ^ 2 / (zo + Y * (1 - Y) + za) +
      μa * za := by positivity
  have eV : gE zo Y za (1 - Y) + μa * za + μb * (1 - Y) =
      Y ^ 2 + (1 - Y) * μb + (zo + Y * (1 - Y)) ^ 2 / (zo + Y * (1 - Y) + za) + μa * za := by
    rw [eE]; ring
  have e1 : selfN1 zo Y za (1 - Y) =
      -(3 * za * (zo + Y * (1 - Y)) ^ 2 * (2 * (zo + Y * (1 - Y) + za) + za * (1 - Y))) := by
    unfold selfN1 gU ga gS gc; ring
  have e2 : selfN2 zo Y za (1 - Y) =
      2 * za * (3 * Y * (zo + Y * (1 - Y) + za) + 2 * za * (1 - Y)) := by
    unfold selfN2 gU ga gS gc; ring
  unfold selfTerm selfDocF
  rw [eV, eU, e1, e2]
  have := hD.ne'
  have hUa : (zo + Y * (1 - Y) + za) ≠ 0 := by positivity
  rw [show zo + Y * (1 - Y) - Y * (1 - Y) = zo by ring,
    show zo + Y * (1 - Y) + za = zo + Y * (1 - Y) + za by rfl]
  field_simp
  ring

theorem selfF4_frame (P : Params) {w : Fin 3 → ℝ} (hw : w ∈ chengWuSet (1 : Fin 3)) :
    selfF4 P (Fin.snoc w (1 - w 1)) = selfDocSum P (w 1) (w 0) (w 2) := by
  obtain ⟨hpos, h1⟩ := QED.Integration.ChengWu.mem_chengWuSet.mp hw
  have hY : w 1 ∈ Ioo (0 : ℝ) 1 := ⟨hpos 1, h1⟩
  have h0 : 0 ≤ P.mγ ^ 2 := sq_nonneg _
  have hΛ : 0 ≤ P.Λ ^ 2 := sq_nonneg _
  have s0 : (Fin.snoc w (1 - w 1) : Fin 4 → ℝ) 0 = w 0 := rfl
  have s1 : (Fin.snoc w (1 - w 1) : Fin 4 → ℝ) 1 = w 1 := rfl
  have s2 : (Fin.snoc w (1 - w 1) : Fin 4 → ℝ) 2 = w 2 := rfl
  have s3 : (Fin.snoc w (1 - w 1) : Fin 4 → ℝ) 3 = 1 - w 1 := rfl
  simp only [selfF4, selfDocSum, s0, s1, s2, s3]
  rw [selfTerm_frame h0 h0 (hpos 0) hY (hpos 2), selfTerm_frame h0 hΛ (hpos 0) hY (hpos 2),
    selfTerm_frame hΛ h0 (hpos 0) hY (hpos 2), selfTerm_frame hΛ hΛ (hpos 0) hY (hpos 2)]

/-- **After the substitution `z_a = a(1-x)/x`** (with the Jacobian `a/x²`), `selfDocF` is the
integrand `A₂/D² + A₁/D` of eq. (5.1) of the document, `D = M + a h(x)` with
`M = Y² + (1-Y) μ_b`, `h(x) = (x² + (1-x) μ_a)/x` (eq. (2.2)). -/
theorem selfDocF_subst {Y a x μa μb : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (ha : 0 < a)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) :
    selfDocF Y a (a * (1 - x) / x) μa μb * (a / x ^ 2) =
      x ^ 2 * (x - 1) * (a - Y * (1 - Y)) ^ 2 * (Y * x - Y - x + 3) / (4 * a) /
          (Y ^ 2 + (1 - Y) * μb + a * ((x ^ 2 + (1 - x) * μa) / x)) ^ 2 +
        -(x * (x - 1) * (a - Y * (1 - Y)) ^ 2 * (2 * Y * x + Y - 2 * x + 2)) / (2 * a ^ 2) /
          (Y ^ 2 + (1 - Y) * μb + a * ((x ^ 2 + (1 - x) * μa) / x)) := by
  obtain ⟨hx0, hx1⟩ := hx
  have h1x : 0 < 1 - x := by linarith
  have h1Y : 0 < 1 - Y := by linarith [hY.2]
  have hU : a + a * (1 - x) / x = a / x := by field_simp; ring
  have hD : Y ^ 2 + (1 - Y) * μb + a ^ 2 / (a + a * (1 - x) / x) + μa * (a * (1 - x) / x) =
      Y ^ 2 + (1 - Y) * μb + a * ((x ^ 2 + (1 - x) * μa) / x) := by
    rw [hU]; field_simp; ring
  have hDpos : 0 < Y ^ 2 + (1 - Y) * μb + a * ((x ^ 2 + (1 - x) * μa) / x) := by
    have := hY.1; positivity
  unfold selfDocF
  rw [hD, hU]
  have := hDpos.ne'
  field_simp
  ring

/-! ### The theorem -/

/-- **The class `S₊` in the variables of eq. (5.1)** (`m = e = 1`, `0 < m_γ < Λ`):
`16π⁴ (1/(64 m⁵)) (1/i) openZero S₊ = ∫_{z_o > 0, 0 < Y < 1, z_a > 0} selfDocSum(Y, z_o, z_a)`,
and the integrand is integrable on that domain. -/
theorem sixteen_pi_pow_four_mul_openZero_Sp_eq_doc {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    IntegrableOn (fun w : Fin 3 → ℝ => selfDocSum P (w 1) (w 0) (w 2)) (chengWuSet 1) ∧
    16 * (π : ℂ) ^ 4 * (1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * openZero .Sp P)) =
      ((∫ w in chengWuSet (1 : Fin 3), selfDocSum P (w 1) (w 0) (w 2) : ℝ) : ℂ) := by
  obtain ⟨hI, hEq⟩ := sixteen_pi_pow_four_mul_openZero_Sp_eq_simplex hm he hmγ hΛ
  have hF : ∀ z : Fin 4 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      selfF4 P (t • z) = (t ^ 4)⁻¹ • selfF4 P z := fun z hz t ht => by
    rw [smul_eq_mul]; exact selfF4_smul P hz ht
  have hCW := integral_simplex_chengWu (1 : Fin 3) (selfF4 P) hF
  have hCWi := (integrableOn_simplex_chengWu_iff (1 : Fin 3) (selfF4 P) hF).mp hI
  have hframe : ∫ w in chengWuSet (1 : Fin 3), selfF4 P (Fin.snoc w (1 - w 1)) =
      ∫ w in chengWuSet (1 : Fin 3), selfDocSum P (w 1) (w 0) (w 2) :=
    setIntegral_congr_fun (QED.Integration.ChengWu.measurableSet_chengWuSet 1)
      fun w hw => selfF4_frame P hw
  refine ⟨hCWi.congr_fun (fun w hw => selfF4_frame P hw)
    (QED.Integration.ChengWu.measurableSet_chengWuSet 1), ?_⟩
  rw [hEq, hCW, hframe]

/-- **The class `S₊` as the iterated integral of eq. (5.1)** (`m = e = 1`, `0 < m_γ < Λ`). -/
theorem sixteen_pi_pow_four_mul_openZero_Sp_eq_doc_iterated {P : Params} (hm : P.m = 1)
    (he : P.e = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    16 * (π : ℂ) ^ 4 * (1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * openZero .Sp P)) =
      ((∫ Y in Ioo (0 : ℝ) 1, ∫ zo in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
        selfDocSum P Y zo za : ℝ) : ℂ) := by
  obtain ⟨hI, hEq⟩ := sixteen_pi_pow_four_mul_openZero_Sp_eq_doc hm he hmγ hΛ
  rw [hEq, QED.Integration.ChengWu.integral_chengWuSet_one hI]
  rfl

/-- **The self-energy pair `S₊ + S₋` as twice the iterated integral of eq. (5.1)**
(`m = e = 1`, `0 < m_γ < Λ`): the factor `2` of eq. (5.3) of the document. -/
theorem sixteen_pi_pow_four_mul_openZero_S_eq_doc_iterated {P : Params} (hm : P.m = 1)
    (he : P.e = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    16 * (π : ℂ) ^ 4 * (1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * (openZero .Sp P + openZero .Sm P))) =
      ((2 * ∫ Y in Ioo (0 : ℝ) 1, ∫ zo in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
        selfDocSum P Y zo za : ℝ) : ℂ) := by
  have h := sixteen_pi_pow_four_mul_openZero_Sp_eq_doc_iterated hm he hmγ hΛ
  rw [openZero_Sm_eq_Sp hm he]
  push_cast
  rw [← h]
  ring

end QED.TwoLoop.UnitSCReduce

end
