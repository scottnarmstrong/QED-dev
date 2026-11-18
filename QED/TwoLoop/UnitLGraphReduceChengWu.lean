/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLGraphReduce
public import QED.Integration.ChengWu
public import QED.Integration.ChengWuFubini
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The ladder graph half in the variables of eq. (3.1) of the document

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the L link, graph half, items (ii) and (iii).
The merged integrand `ladderF4` (`QED/TwoLoop/UnitLGraphReduce.lean`) is homogeneous of degree
`-4` in the group sums `(z_A, z_B, z_a, z_b)` (`ladderF4_smul`), so the Cheng–Wu theorem
(`QED.Integration.ChengWu.integral_simplex_chengWu`, constraint on the inner loop
`z_B + z_b = 1`, `z_B = Y`) turns the integral over `Δ₃` into one over
`Y ∈ (0, 1)`, `z_A, z_a ∈ (0, ∞)`. There the integrand is the document's eq. (3.1),
`f_L(Y, a, z_a; μ_a, μ_b) = Y z_a (a - c)/(2U⁴) [(9c + a)/D + Q₀/(U D²)]` (`ladderDocF`, as in
`ladder_f` of `scripts/numerics/two_loop_unit_integrals.py`), with `c = Y(1-Y)`, `a = z_A + c`,
`U = a + z_a`, `D = Y² + (1-Y) μ_b + a²/U + μ_a z_a`,
`Q₀ = (3Y-2)a² + (4Y-Y²-2) a z_a - 2c z_a²`, summed over the photon masses
`μ_a, μ_b ∈ {m_γ², Λ²}` with the Pauli–Villars signs (`ladderDocSum`):

* `sixteen_pi_pow_four_mul_graphHalf_eq_doc`: for `m = e = 1` and `0 < m_γ < Λ`,
  `16π⁴ · graphHalf P = ∫_{(z_A, Y, z_a) ∈ D} ladderDocSum(Y, z_A, z_a)`, with
  `D = {z_A > 0, 0 < Y < 1, z_a > 0}` (`QED.Integration.ChengWu.chengWuSet 1`), and the integrand
  is integrable on `D`;
* `sixteen_pi_pow_four_mul_graphHalf_eq_doc_iterated`: the same as the iterated integral
  `∫₀¹ dY ∫₀^∞ dz_A ∫₀^∞ dz_a`, the measure of eq. (3.1).

The document's (3.1) displays the term with the outer photon at mass `λ = m_γ`; the terms with
the outer photon at `Λ` are kept here (finite `Λ`).
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace QED.TwoLoop.UnitLGraphReduce

open QED.WickModel
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.ChengWu (chengWuSet integral_simplex_chengWu integrableOn_simplex_chengWu_iff)

/-! ### Homogeneity -/

theorem gE_smul {A B a b t : ℝ} (ht : 0 < t) (hU : gU A B a b ≠ 0) :
    gE (t * A) (t * B) (t * a) (t * b) = t * gE A B a b := by
  have hU' : gU (t * A) (t * B) (t * a) (t * b) = t ^ 2 * gU A B a b := by
    unfold gU ga gS gc; ring
  unfold gE
  rw [hU']
  unfold gU ga gS gc at hU ⊢
  field_simp

/-- **`ladderTerm` is homogeneous of degree `-4`.** -/
theorem ladderTerm_smul {μa μb A B a b t : ℝ} (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) (hA : 0 < A)
    (hB : 0 < B) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    ladderTerm μa μb (t * A) (t * B) (t * a) (t * b) = (t ^ 4)⁻¹ * ladderTerm μa μb A B a b := by
  have hU := gU_pos hA hB ha hb
  have hE := gE_nonneg hA hB ha hb
  have hV : 0 < gE A B a b + μa * a + μb * b := by
    have : 0 < gE A B a b := by
      unfold gE; have := hU; unfold ga gS gc; positivity
    positivity
  have eU : gU (t * A) (t * B) (t * a) (t * b) = t ^ 2 * gU A B a b := by
    unfold gU ga gS gc; ring
  have eQ : gQ (t * A) (t * B) (t * a) (t * b) = t ^ 5 * gQ A B a b := by
    unfold gQ ga gS gc; ring
  have ec : gc (t * B) (t * b) = t ^ 2 * gc B b := by unfold gc; ring
  have ea : ga (t * A) (t * B) (t * b) = t ^ 2 * ga A B b := by unfold ga gS gc; ring
  have eV : gE (t * A) (t * B) (t * a) (t * b) + μa * (t * a) + μb * (t * b) =
      t * (gE A B a b + μa * a + μb * b) := by
    rw [gE_smul ht hU.ne']; ring
  unfold ladderTerm
  rw [eU, eQ, ec, ea, eV]
  have := hU.ne'
  have := hV.ne'
  field_simp

/-- **`ladderF4` is homogeneous of degree `-4`** on the positive orthant. -/
theorem ladderF4_smul (P : Params) {z : Fin 4 → ℝ} (hz : ∀ i, 0 < z i) {t : ℝ} (ht : 0 < t) :
    ladderF4 P (t • z) = (t ^ 4)⁻¹ * ladderF4 P z := by
  have h0 : 0 ≤ P.mγ ^ 2 := sq_nonneg _
  have h1 : 0 ≤ P.Λ ^ 2 := sq_nonneg _
  simp only [ladderF4, Pi.smul_apply, smul_eq_mul]
  rw [ladderTerm_smul h0 h0 (hz 0) (hz 1) (hz 2) (hz 3) ht,
    ladderTerm_smul h0 h1 (hz 0) (hz 1) (hz 2) (hz 3) ht,
    ladderTerm_smul h1 h0 (hz 0) (hz 1) (hz 2) (hz 3) ht,
    ladderTerm_smul h1 h1 (hz 0) (hz 1) (hz 2) (hz 3) ht]
  ring

/-! ### The variables of eq. (3.1) -/

/-- **The integrand of eq. (3.1) of the document** at photon masses `μ_a` (outer), `μ_b` (inner):
`f_L = Y z_a (a - c)/(2U⁴) [(9c + a)/D + Q₀/(U D²)]`. -/
noncomputable def ladderDocF (Y a za μa μb : ℝ) : ℝ :=
  Y * za * (a - Y * (1 - Y)) / (2 * (a + za) ^ 4) *
    ((9 * (Y * (1 - Y)) + a) / (Y ^ 2 + (1 - Y) * μb + a ^ 2 / (a + za) + μa * za) +
      ((3 * Y - 2) * a ^ 2 + (4 * Y - Y ^ 2 - 2) * a * za - 2 * (Y * (1 - Y)) * za ^ 2) /
        ((a + za) * (Y ^ 2 + (1 - Y) * μb + a ^ 2 / (a + za) + μa * za) ^ 2))

/-- The Pauli–Villars-signed sum of eq. (3.1) over the photon masses, at `a = z_A + Y(1-Y)`. -/
noncomputable def ladderDocSum (P : Params) (Y zA za : ℝ) : ℝ :=
  ladderDocF Y (zA + Y * (1 - Y)) za (P.mγ ^ 2) (P.mγ ^ 2) -
    ladderDocF Y (zA + Y * (1 - Y)) za (P.mγ ^ 2) (P.Λ ^ 2) -
    ladderDocF Y (zA + Y * (1 - Y)) za (P.Λ ^ 2) (P.mγ ^ 2) +
    ladderDocF Y (zA + Y * (1 - Y)) za (P.Λ ^ 2) (P.Λ ^ 2)

/-- In the frame `z_B + z_b = 1`, `ladderTerm` is the integrand of eq. (3.1). -/
theorem ladderTerm_frame {μa μb zA Y za : ℝ} (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) (hA : 0 < zA)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (ha : 0 < za) :
    ladderTerm μa μb zA Y za (1 - Y) = ladderDocF Y (zA + Y * (1 - Y)) za μa μb := by
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hU := gU_pos hA hY.1 ha hY1
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 hY1
  have eU : gU zA Y za (1 - Y) = zA + Y * (1 - Y) + za := by unfold gU ga gS gc; ring
  have eE : gE zA Y za (1 - Y) = Y ^ 2 + (zA + Y * (1 - Y)) ^ 2 / (zA + Y * (1 - Y) + za) := by
    unfold gE; rw [eU]
    have : 0 < zA + Y * (1 - Y) + za := by positivity
    field_simp
    unfold ga gS gc
    ring
  have hD : 0 < Y ^ 2 + (1 - Y) * μb + (zA + Y * (1 - Y)) ^ 2 / (zA + Y * (1 - Y) + za) +
      μa * za := by positivity
  have eV : gE zA Y za (1 - Y) + μa * za + μb * (1 - Y) =
      Y ^ 2 + (1 - Y) * μb + (zA + Y * (1 - Y)) ^ 2 / (zA + Y * (1 - Y) + za) + μa * za := by
    rw [eE]; ring
  unfold ladderTerm ladderDocF
  rw [eV, eU]
  have eQ : gQ zA Y za (1 - Y) = (3 * Y - 2) * (zA + Y * (1 - Y)) ^ 2 +
      (4 * Y - Y ^ 2 - 2) * (zA + Y * (1 - Y)) * za - 2 * (Y * (1 - Y)) * za ^ 2 := by
    unfold gQ ga gS gc; ring
  have ec : gc Y (1 - Y) = Y * (1 - Y) := rfl
  have ea : ga zA Y (1 - Y) = zA + Y * (1 - Y) := by unfold ga gS gc; ring
  rw [eQ, ec, ea]
  have := hD.ne'
  have hUa : (zA + Y * (1 - Y) + za) ≠ 0 := by positivity
  field_simp
  ring

theorem ladderF4_frame (P : Params) {w : Fin 3 → ℝ} (hw : w ∈ chengWuSet (1 : Fin 3)) :
    ladderF4 P (Fin.snoc w (1 - w 1)) = ladderDocSum P (w 1) (w 0) (w 2) := by
  obtain ⟨hpos, h1⟩ := QED.Integration.ChengWu.mem_chengWuSet.mp hw
  have hY : w 1 ∈ Ioo (0 : ℝ) 1 := ⟨hpos 1, h1⟩
  have h0 : 0 ≤ P.mγ ^ 2 := sq_nonneg _
  have hΛ : 0 ≤ P.Λ ^ 2 := sq_nonneg _
  have s0 : (Fin.snoc w (1 - w 1) : Fin 4 → ℝ) 0 = w 0 := rfl
  have s1 : (Fin.snoc w (1 - w 1) : Fin 4 → ℝ) 1 = w 1 := rfl
  have s2 : (Fin.snoc w (1 - w 1) : Fin 4 → ℝ) 2 = w 2 := rfl
  have s3 : (Fin.snoc w (1 - w 1) : Fin 4 → ℝ) 3 = 1 - w 1 := rfl
  simp only [ladderF4, ladderDocSum, s0, s1, s2, s3]
  rw [ladderTerm_frame h0 h0 (hpos 0) hY (hpos 2), ladderTerm_frame h0 hΛ (hpos 0) hY (hpos 2),
    ladderTerm_frame hΛ h0 (hpos 0) hY (hpos 2), ladderTerm_frame hΛ hΛ (hpos 0) hY (hpos 2)]

/-! ### The theorem -/

/-- **The ladder graph half in the variables of eq. (3.1)** (`m = e = 1`, `0 < m_γ < Λ`):
`16π⁴ · graphHalf P = ∫_{z_A > 0, 0 < Y < 1, z_a > 0} ∑_{μ_a, μ_b} ± f_L(Y, z_A + Y(1-Y), z_a)`,
and the integrand is integrable on that domain. -/
theorem sixteen_pi_pow_four_mul_graphHalf_eq_doc {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    IntegrableOn (fun w : Fin 3 → ℝ => ladderDocSum P (w 1) (w 0) (w 2)) (chengWuSet 1) ∧
    16 * (π : ℂ) ^ 4 * QED.TwoLoop.UnitLLink.graphHalf P =
      ((∫ w in chengWuSet (1 : Fin 3), ladderDocSum P (w 1) (w 0) (w 2) : ℝ) : ℂ) := by
  obtain ⟨hI, hEq⟩ := sixteen_pi_pow_four_mul_graphHalf_eq_simplex hm he hmγ hΛ
  have hF : ∀ z : Fin 4 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      ladderF4 P (t • z) = (t ^ 4)⁻¹ • ladderF4 P z := fun z hz t ht => by
    rw [smul_eq_mul]; exact ladderF4_smul P hz ht
  have hCW := integral_simplex_chengWu (1 : Fin 3) (ladderF4 P) hF
  have hCWi := (integrableOn_simplex_chengWu_iff (1 : Fin 3) (ladderF4 P) hF).mp hI
  have hframe : ∫ w in chengWuSet (1 : Fin 3), ladderF4 P (Fin.snoc w (1 - w 1)) =
      ∫ w in chengWuSet (1 : Fin 3), ladderDocSum P (w 1) (w 0) (w 2) :=
    setIntegral_congr_fun (QED.Integration.ChengWu.measurableSet_chengWuSet 1)
      fun w hw => ladderF4_frame P hw
  refine ⟨hCWi.congr_fun (fun w hw => ladderF4_frame P hw)
    (QED.Integration.ChengWu.measurableSet_chengWuSet 1), ?_⟩
  rw [hEq, hCW, hframe]

/-- **The ladder graph half as the iterated integral of eq. (3.1)** (`m = e = 1`,
`0 < m_γ < Λ`): `16π⁴ · graphHalf P = ∫₀¹ dY ∫₀^∞ dz_A ∫₀^∞ dz_a ∑_{μ_a, μ_b} ± f_L`. -/
theorem sixteen_pi_pow_four_mul_graphHalf_eq_doc_iterated {P : Params} (hm : P.m = 1)
    (he : P.e = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    16 * (π : ℂ) ^ 4 * QED.TwoLoop.UnitLLink.graphHalf P =
      ((∫ Y in Ioo (0 : ℝ) 1, ∫ zA in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
        ladderDocSum P Y zA za : ℝ) : ℂ) := by
  obtain ⟨hI, hEq⟩ := sixteen_pi_pow_four_mul_graphHalf_eq_doc hm he hmγ hΛ
  rw [hEq, QED.Integration.ChengWu.integral_chengWuSet_one hI]
  rfl

end QED.TwoLoop.UnitLGraphReduce

end
