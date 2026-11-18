/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraphReduce
public import QED.TwoLoop.UnitXGraphChengWuSet
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The crossed-ladder unit in the hierarchical variables of section 2.2

Section 8 of `docs/TWO-LOOP-UNITS.md`, the graph half of the X unit, items (ii) and (iii) (the
analogue of `QED/TwoLoop/UnitLGraphReduceChengWu.lean`). The merged integrand `crossedF4`
(`QED/TwoLoop/UnitXGraphReduce.lean`) is homogeneous of degree `-5` in the group sums
`(z_A, z_M, z_c, z_a, z_b)` (`crossedF4_smul`), so the Cheng–Wu theorem with the constraint on
the inner simplex `z_M + z_c + z_b = 1` (`integral_simplex_chengWuSet`, `T = {z_M, z_c}`) turns
the integral over `Δ₄` into one over `z_A, z_a ∈ (0, ∞)` and `(z_M, z_c)` in the open triangle
`z_M, z_c > 0`, `z_M + z_c < 1`, with `z_b = 1 - z_M - z_c`:

* `sixteen_pi_pow_four_mul_unitF2_X_eq_chengWu`: for `m = e = 1` and `0 < m_γ < Λ`,
  `16π⁴ · unitF2 X P = ∫_{D} crossedF4(z_A, z_M, z_c, z_a, 1 - z_M - z_c)`,
  `D = {w ∈ ℝ⁴ : wᵢ > 0, w₁ + w₂ < 1}`, and the integrand is integrable on `D`.

In this frame the document's labels are `z₁ = z_A` (the single outer electron line `0`),
`z₂ = z_M` (the merged electron pair), `z₃ = z_c` (line `3`), `Y = z₂ + z₃`, and the **splitting
identity (2.1)** holds (`gXU_frame`, `gXE_frame`): with `b = z_A + z₂ z_b` and `w = z_a + z₂ z₃`
(the shifts `g = z₂ z_b`, `e = z₂ z₃` of the table of section 2.2),
`U = b + w` and `E = Y² + b²/(b + w)`, so
`V_{μ_a μ_b} = Y² + (1 - Y) μ_b + b²/(b + w) + μ_a (w - e)`, the `D` of eq. (2.1).
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace QED.TwoLoop.UnitXGraph

open QED.WickModel
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### Homogeneity -/

theorem gXan_smul (t A M c a b : ℝ) (k : Fin 4) :
    gXan (t * A) (t * M) (t * c) (t * a) (t * b) k = t ^ 2 * gXan A M c a b k := by
  fin_cases k <;> simp [gXan] <;> ring

theorem gXbn_smul (t A s M c a b : ℝ) (k : Fin 4) :
    gXbn (t * A) (t * s) (t * M) (t * c) (t * a) (t * b) k = t ^ 2 * gXbn A s M c a b k := by
  fin_cases k <;> simp [gXbn] <;> ring

theorem gXU_smul (t A M c a b : ℝ) :
    gXU (t * A) (t * M) (t * c) (t * a) (t * b) = t ^ 2 * gXU A M c a b := by
  unfold gXU; ring

theorem gXEn_smul (t A M c a b : ℝ) :
    gXEn (t * A) (t * M) (t * c) (t * a) (t * b) = t ^ 3 * gXEn A M c a b := by
  unfold gXEn; ring

theorem gPsi1_smul (t A s M c a b : ℝ) :
    gPsi1 (t * A) (t * s) (t * M) (t * c) (t * a) (t * b) = t ^ 8 * gPsi1 A s M c a b := by
  unfold gPsi1
  simp only [gXan_smul, gXbn_smul, gXU_smul, psiT1h_smul]
  ring

theorem psiT2h_smul₂ (s r a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u : ℝ) :
    psiT2h (s * a0) (s * a1) (s * a2) (s * a3) (s * b0) (s * b1) (s * b2) (s * b3) (r * c01)
        (r * c02) (r * c03) (r * c12) (r * c13) (r * c23) (s * u) =
      s ^ 2 * r * psiT2h a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u := by
  simp only [psiT2h]; ring

theorem gPsi2_smul (t A s M c a b : ℝ) :
    gPsi2 (t * A) (t * s) (t * M) (t * c) (t * a) (t * b) = t ^ 5 * gPsi2 A s M c a b := by
  unfold gPsi2
  have h := psiT2h_smul₂ (t ^ 2) t (gXan A M c a b 0) (gXan A M c a b 1) (gXan A M c a b 2)
    (gXan A M c a b 3) (gXbn A s M c a b 0) (gXbn A s M c a b 1) (gXbn A s M c a b 2)
    (gXbn A s M c a b 3) (A + a) (A + a) (-M) (A + c + a + b) (c + b) (c + b) (gXU A M c a b)
  simp only [gXan_smul, gXbn_smul, gXU_smul]
  rw [show t * A + t * a = t * (A + a) by ring, show -(t * M) = t * -M by ring,
    show t * A + t * c + t * a + t * b = t * (A + c + a + b) by ring,
    show t * c + t * b = t * (c + b) by ring, h]
  ring

theorem gXE_pos {A M c a b : ℝ} (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a)
    (hb : 0 < b) : 0 < gXE A M c a b := by
  have := gXU_pos hA hM hc ha hb
  unfold gXE gXEn at *; positivity

theorem crossedTerm_smul {μa μb A M c a b t : ℝ} (hμa : 0 ≤ μa) (hμb : 0 ≤ μb) (hA : 0 < A)
    (hM : 0 < M) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    crossedTerm μa μb (t * A) (t * M) (t * c) (t * a) (t * b) =
      (t ^ 5)⁻¹ * crossedTerm μa μb A M c a b := by
  have hU := gXU_pos hA hM hc ha hb
  have hE := gXE_pos hA hM hc ha hb
  have hV : 0 < gXE A M c a b + μa * a + μb * b := by positivity
  have eE : gXE (t * A) (t * M) (t * c) (t * a) (t * b) = t * gXE A M c a b := by
    unfold gXE
    rw [gXEn_smul, gXU_smul]
    field_simp
  have eV : gXE (t * A) (t * M) (t * c) (t * a) (t * b) + μa * (t * a) + μb * (t * b) =
      t * (gXE A M c a b + μa * a + μb * b) := by rw [eE]; ring
  unfold crossedTerm
  rw [eV, gXU_smul, show t * M / 2 = t * (M / 2) by ring, gPsi1_smul, gPsi2_smul]
  field_simp

theorem crossedF4_smul (P : Params) {z : Fin 5 → ℝ} (hz : ∀ i, 0 < z i) {t : ℝ} (ht : 0 < t) :
    crossedF4 P (t • z) = (t ^ 5)⁻¹ * crossedF4 P z := by
  have h0 : 0 ≤ P.mγ ^ 2 := sq_nonneg _
  have hΛ : 0 ≤ P.Λ ^ 2 := sq_nonneg _
  simp only [crossedF4, Pi.smul_apply, smul_eq_mul]
  rw [crossedTerm_smul h0 h0 (hz 0) (hz 1) (hz 2) (hz 3) (hz 4) ht,
    crossedTerm_smul h0 hΛ (hz 0) (hz 1) (hz 2) (hz 3) (hz 4) ht,
    crossedTerm_smul hΛ h0 (hz 0) (hz 1) (hz 2) (hz 3) (hz 4) ht,
    crossedTerm_smul hΛ hΛ (hz 0) (hz 1) (hz 2) (hz 3) (hz 4) ht]
  ring

/-! ### The splitting identity (2.1) in the frame `z_M + z_c + z_b = 1` -/

/-- **The splitting identity, `U`**: `U = b + w` with `b = z_A + z₂ z_b`, `w = z_a + z₂ z₃`. -/
theorem gXU_frame (A M c a : ℝ) :
    gXU A M c a (1 - M - c) = (A + M * (1 - M - c)) + (a + M * c) := by
  unfold gXU; ring

/-- **The splitting identity, `E`**: `E = Y² + b²/(b + w)`. -/
theorem gXE_frame {A M c a : ℝ} (hU : gXU A M c a (1 - M - c) ≠ 0) :
    gXE A M c a (1 - M - c) =
      (M + c) ^ 2 + (A + M * (1 - M - c)) ^ 2 / ((A + M * (1 - M - c)) + (a + M * c)) := by
  rw [← gXU_frame] at *
  unfold gXE
  field_simp
  unfold gXU gXEn
  ring

/-! ### The theorem -/

/-- The inner coordinates `{z_M, z_c}` of the Cheng–Wu constraint. -/
def innerSet : Finset (Fin 4) := {1, 2}

theorem sum_innerSet (w : Fin 4 → ℝ) : ∑ i ∈ innerSet, w i = w 1 + w 2 := by
  simp [innerSet]

/-- **The crossed-ladder unit in the hierarchical Cheng–Wu variables** (`m = e = 1`,
`0 < m_γ < Λ`): `16π⁴ · unitF2 X P = ∫_D crossedF4(z_A, z_M, z_c, z_a, 1 - z_M - z_c)` over
`D = {z_A, z_M, z_c, z_a > 0, z_M + z_c < 1}`, and the integrand is integrable on `D`. -/
theorem sixteen_pi_pow_four_mul_unitF2_X_eq_chengWu {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    IntegrableOn (fun w : Fin 4 → ℝ => crossedF4 P (Fin.snoc w (1 - (w 1 + w 2))))
      (cwSet innerSet) ∧
    16 * (π : ℂ) ^ 4 * QED.TwoLoop.UnitsRegulated.unitF2 .X P =
      ((∫ w in cwSet innerSet, crossedF4 P (Fin.snoc w (1 - (w 1 + w 2))) : ℝ) : ℂ) := by
  obtain ⟨hI, hEq⟩ := sixteen_pi_pow_four_mul_unitF2_X_eq_simplex hm he hmγ hΛ
  have hF : ∀ z : Fin 5 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      crossedF4 P (t • z) = (t ^ 5)⁻¹ • crossedF4 P z := fun z hz t ht => by
    rw [smul_eq_mul]; exact crossedF4_smul P hz ht
  have hCW := integral_simplex_chengWuSet (by norm_num) innerSet (crossedF4 P) hF
  have hCWi := (integrableOn_simplex_chengWuSet_iff (by norm_num) innerSet (crossedF4 P) hF).mp hI
  simp only [sum_innerSet] at hCW hCWi
  exact ⟨hCWi, by rw [hEq, hCW]⟩

/-! ### Fubini on the Cheng–Wu domain -/

/-- The index map `Fin 2 ⊕ Fin 2 ≃ Fin 4`: the inner pair `(z_M, z_c)` first, then `(z_A, z_a)`. -/
def innerIdx : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv.trans
  { toFun := ![1, 2, 0, 3], invFun := ![2, 0, 1, 3], left_inv := by decide,
    right_inv := by decide }

/-- The measurable equivalence `w ↦ ((w₁, w₂), (w₀, w₃))`. -/
noncomputable def splitInner : (Fin 4 → ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) innerIdx).symm.trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).trans
      (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow))

theorem measurePreserving_splitInner :
    MeasurePreserving splitInner volume ((volume : Measure (ℝ × ℝ)).prod (volume.prod volume)) := by
  refine ((volume_measurePreserving_piCongrLeft (fun _ => ℝ) innerIdx).symm _).trans ?_
  refine (volume_measurePreserving_sumPiEquivProdPi _).trans ?_
  exact (volume_preserving_finTwoArrow ℝ).prod (volume_preserving_finTwoArrow ℝ)

theorem splitInner_symm_apply (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    splitInner.symm q = ![q.2.1, q.1.1, q.1.2, q.2.2] := by
  funext i
  fin_cases i <;> rfl

/-- The open triangle `{(z₂, z₃) : z₂, z₃ > 0, z₂ + z₃ < 1}`. -/
def innerTriangle : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}

theorem measurableSet_innerTriangle : MeasurableSet innerTriangle := by
  have e : innerTriangle = {p : ℝ × ℝ | 0 < p.1} ∩ {p | 0 < p.2} ∩ {p | p.1 + p.2 < 1} := by
    ext p; simp [innerTriangle, and_assoc]
  rw [e]
  exact ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_const measurable_snd)).inter
    (measurableSet_lt (by fun_prop) measurable_const)

theorem preimage_splitInner_symm :
    splitInner.symm ⁻¹' cwSet innerSet = innerTriangle ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  ext q
  simp only [Set.mem_preimage, splitInner_symm_apply, mem_cwSet, sum_innerSet, Fin.forall_fin_succ,
    Set.mem_prod, Set.mem_Ioi, innerTriangle, Set.mem_ofPred_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  constructor
  · rintro ⟨⟨h0, h1, h2, h3, -⟩, h4⟩
    exact ⟨⟨h1, h2, by simpa using h4⟩, h0, by simpa using h3⟩
  · rintro ⟨⟨h1, h2, h4⟩, h0, h3⟩
    refine ⟨⟨h0, h1, h2, by simpa using h3, fun i => i.elim0⟩, by simpa using h4⟩

/-- **Fubini on the Cheng–Wu domain of the crossed ladder**:
`∫_D g = ∫_{(z₂, z₃) ∈ triangle} ∫₀^∞ dz_A ∫₀^∞ dz_a g(z_A, z₂, z₃, z_a)` for `g` integrable. -/
theorem integral_cwSet_innerSet {g : (Fin 4 → ℝ) → ℝ} (hg : IntegrableOn g (cwSet innerSet)) :
    ∫ w in cwSet innerSet, g w =
      ∫ p in innerTriangle, ∫ zA in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ), g ![zA, p.1, p.2, za] := by
  have he := measurePreserving_splitInner.symm
  have h1 := he.setIntegral_preimage_emb splitInner.symm.measurableEmbedding g (cwSet innerSet)
  have hint := (he.integrableOn_comp_preimage splitInner.symm.measurableEmbedding).mpr hg
  rw [preimage_splitInner_symm] at h1 hint
  rw [← h1, setIntegral_prod (fun q => g (splitInner.symm q)) hint]
  have hint' : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => g (splitInner.symm q))
      ((volume.restrict innerTriangle).prod
        ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict]; exact hint
  refine integral_congr_ae ?_
  filter_upwards [hint'.prod_right_ae] with p hp
  rw [setIntegral_prod _ hp]
  simp only [splitInner_symm_apply]

/-- **The crossed-ladder unit as an iterated integral in the hierarchical variables**
(`m = e = 1`, `0 < m_γ < Λ`):
`16π⁴ · unitF2 X P = ∫_{z₂, z₃ > 0, z₂ + z₃ < 1} ∫₀^∞ dz_A ∫₀^∞ dz_a
  crossedF4(z_A, z₂, z₃, z_a, 1 - z₂ - z₃)`. -/
theorem sixteen_pi_pow_four_mul_unitF2_X_eq_iterated {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    16 * (π : ℂ) ^ 4 * QED.TwoLoop.UnitsRegulated.unitF2 .X P =
      ((∫ p in innerTriangle, ∫ zA in Ioi (0 : ℝ), ∫ za in Ioi (0 : ℝ),
        crossedF4 P ![zA, p.1, p.2, za, 1 - (p.1 + p.2)] : ℝ) : ℂ) := by
  obtain ⟨hI, hEq⟩ := sixteen_pi_pow_four_mul_unitF2_X_eq_chengWu hm he hmγ hΛ
  rw [hEq, integral_cwSet_innerSet hI]
  rfl

end QED.TwoLoop.UnitXGraph

end
