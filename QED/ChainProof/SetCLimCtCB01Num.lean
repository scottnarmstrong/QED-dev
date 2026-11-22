/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLimCtCB01Amp
public import QED.ChainProof.SetCLimCtCB01Shape
public import QED.ChainProof.SetCLimCtCDNum

/-!
# Set (c): the integrands of `CB0`, `CB1` in shape form

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. From the T1
values of `QED/ChainProof/SetCLimCtCB01Amp.lean`, at `ε ≠ 0` and under the two Pauli–Villars
conditions:

* `cbNum P M X₁ X₀`: the numerator of the bubble vertex with arbitrary open-line matrices
  (`X₁` outgoing, `X₀` incoming), `= cbNum P 0 + M² cbNum2` (`cbNum_eq`);
* `cbAmp_eq`: the merge of the inserted line (`QED.ChainProof.SetCPauli.electronInsertion_merge`),
  `S̃ X S̃ = D⁻¹ Y + D⁻² (c A) + iε D⁻² Y`, gives numerators over denominators;
* `flavourSum_cb`: the divided difference over the loop flavours (`flavourSum_propDenom`) onto
  the four ten-line shapes of `VP`;
* **`contractionValue₂_cb0_shapes`, `contractionValue₂_cb1_shapes`**: the value is the joint
  integral of `(2π)⁻⁸ cbIntegrand`, the once-merged numerator `(cbEa0, cbEa2)` over the shapes `t`
  plus `c (cbEv0, cbEv2) + iε (cbEa0, cbEa2)` over the doubled eleven-line shapes `(d, t)`
  (`cbDenom`, the open line `d` repeated as line `10`).
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCPauli.CB01

open QED.WickModel QED.TwoLoop.Bridge
open QED.ChainProof.SetCPauli (mergeY mergeC)
open QED.Integration.TwoLoop (lineDenom castLoopMatrix)
open QED.ChainProof.SetCLink (repCB0 repCB1)

/-- **The numerator of the bubble vertex with open-line matrices `X₁` (outgoing), `X₀`
(incoming)**, loop mass `M`, in the class loop momenta `λ` (`q = λ₀`, `k = -λ₁`). -/
noncomputable def cbNum (P : Params) (M : ℝ) (X1 X0 : Matrix (Fin 4) (Fin 4) ℂ) (α β μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (I * P.e) ^ 5 * (1 / I) ^ 6 * ∑ l0 : Fin 4, ∑ l3 : Fin 4, ∑ l4 : Fin 4, ∑ l5 : Fin 4,
    (Dirac.gamma l0 * X1 * Dirac.gamma μ * X0 * Dirac.gamma l3) α β *
      ((Minkowski.metric l0 l4 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) *
      ((Minkowski.metric l3 l5 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) *
      loopTrace M (ℓ 0) (-ℓ 1) l5 l4

theorem trace_loop_eq (M ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (l4 l5 : Fin 4) :
    Matrix.trace (Dirac.gamma l4 * QED.OneLoop.electronPropagator M ε (ℓ 0 - ℓ 1) *
        Dirac.gamma l5 * QED.OneLoop.electronPropagator M ε (ℓ 0)) =
      (propDenom M ε (ℓ 0 - ℓ 1))⁻¹ * (propDenom M ε (ℓ 0))⁻¹ *
        loopTrace M (ℓ 0) (-ℓ 1) l5 l4 := by
  have ht : (Dirac.gamma l4 * electronNumerator M (ℓ 0 - ℓ 1) * Dirac.gamma l5 *
      electronNumerator M (ℓ 0)).trace = (Dirac.gamma l5 * electronNumerator M (ℓ 0) *
      Dirac.gamma l4 * electronNumerator M (ℓ 0 - ℓ 1)).trace := by
    rw [show Dirac.gamma l4 * electronNumerator M (ℓ 0 - ℓ 1) * Dirac.gamma l5 *
        electronNumerator M (ℓ 0) = (Dirac.gamma l4 * electronNumerator M (ℓ 0 - ℓ 1)) *
          (Dirac.gamma l5 * electronNumerator M (ℓ 0)) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [QED.TwoLoop.Bridge.electronPropagator_eq_smul,
    QED.TwoLoop.Bridge.electronPropagator_eq_smul, loopTrace, ← sub_eq_add_neg]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ht]
  ring

/-- The open line `d` with the merged insertion, at `ε ≠ 0`:
`S̃ X S̃ = D⁻¹ Y + D⁻² (c A) + iε D⁻² Y`. -/
theorem cbLine_self (P : Params) (hε : P.ε ≠ 0) (d : Fin 2) (q : Fin 4 → ℝ) :
    cbLine P d d q = (propDenom P.m P.ε q)⁻¹ • mergeY P.m P.δ₂ P.δm q +
      ((propDenom P.m P.ε q)⁻¹ * (propDenom P.m P.ε q)⁻¹) •
        (mergeC P.m P.δ₂ P.δm • electronNumerator P.m q) +
      ((P.ε : ℂ) * I * ((propDenom P.m P.ε q)⁻¹ * (propDenom P.m P.ε q)⁻¹)) •
        mergeY P.m P.δ₂ P.δm q := by
  have h := QED.ChainProof.SetCPauli.electronInsertion_merge P.m P.ε P.δ₂ P.δm hε q
  rw [QED.TwoLoop.Insertion.electronInsertion] at h
  simp only [cbLine, ↓reduceIte]
  rw [← neg_neg (_ * _ * _), h]
  simp only [smul_neg, neg_add, neg_neg]

theorem cbLine_ne (P : Params) {d i : Fin 2} (h : i ≠ d) (q : Fin 4 → ℝ) :
    cbLine P d i q = (propDenom P.m P.ε q)⁻¹ • electronNumerator P.m q := by
  simp only [cbLine, h, ↓reduceIte, QED.TwoLoop.Bridge.electronPropagator_eq_smul]

/-! ### The amplitude as numerators over denominators -/

/-- The open-line momenta `p + λ₁` (line `0`, incoming), `p' + λ₁` (line `1`, outgoing). -/
def cbMom (p' p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ := ![p + ℓ 1, p' + ℓ 1]

/-- The open-line matrices of the once-merged term: `Y` on the line `d`, `A` on the other. -/
noncomputable def cbXa (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (i : Fin 2) : Matrix (Fin 4) (Fin 4) ℂ :=
  if i = d then mergeY P.m P.δ₂ P.δm (cbMom p' p ℓ i) else electronNumerator P.m (cbMom p' p ℓ i)

/-- The photon and loop denominators of flavour `f`. -/
noncomputable def cbRest (P : Params) (f : Fin 3) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  (propDenom P.mγ P.ε (ℓ 1))⁻¹ * (propDenom P.Λ P.ε (ℓ 1))⁻¹ *
    ((propDenom P.mγ P.ε (-ℓ 1))⁻¹ * (propDenom P.Λ P.ε (-ℓ 1))⁻¹) *
    ((propDenom (P.mass f) P.ε (ℓ 0 - ℓ 1))⁻¹ * (propDenom (P.mass f) P.ε (ℓ 0))⁻¹)

/-- **The amplitude at `ε ≠ 0` as numerators over denominators**: with `D_i` the open-line
denominators, `-[N_a D_d⁻¹ D_o⁻¹ + (c N + iε N_a) D_d⁻² D_o⁻¹] × (photons, loop)`. -/
theorem cbAmp_eq (P : Params) (hε : P.ε ≠ 0) (f : Fin 3) (d : Fin 2) (p' p : Fin 4 → ℝ)
    (α β μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbAmp P f d p' p α β μ ℓ =
      -((cbNum P (P.mass f) (cbXa P d p' p ℓ 1) (cbXa P d p' p ℓ 0) α β μ ℓ *
            ((propDenom P.m P.ε (cbMom p' p ℓ 0))⁻¹ * (propDenom P.m P.ε (cbMom p' p ℓ 1))⁻¹) +
          (mergeC P.m P.δ₂ P.δm * cbNum P (P.mass f) (electronNumerator P.m (cbMom p' p ℓ 1))
              (electronNumerator P.m (cbMom p' p ℓ 0)) α β μ ℓ +
            (P.ε : ℂ) * I * cbNum P (P.mass f) (cbXa P d p' p ℓ 1) (cbXa P d p' p ℓ 0) α β μ ℓ) *
            ((propDenom P.m P.ε (cbMom p' p ℓ 0))⁻¹ * (propDenom P.m P.ε (cbMom p' p ℓ 1))⁻¹ *
              (propDenom P.m P.ε (cbMom p' p ℓ d))⁻¹)) *
        cbRest P f ℓ) := by
  have hK : (I * P.e) ^ 5 * (-I) * (1 / I) ^ 7 = -((I * P.e) ^ 5 * (1 / I) ^ 6) := by
    have h : -I * (1 / I) = -1 := by rw [one_div, neg_mul, mul_inv_cancel₀ I_ne_zero]
    calc (I * P.e) ^ 5 * (-I) * (1 / I) ^ 7 = (I * P.e) ^ 5 * (1 / I) ^ 6 * (-I * (1 / I)) := by
          ring
      _ = _ := by rw [h]; ring
  unfold cbAmp cbRest
  rw [hK]
  simp only [trace_loop_eq, photonPropagator_eq_mul _ _ hε]
  fin_cases d
  · simp only [Fin.zero_eta, cbLine_self P hε, cbLine_ne P (show (1 : Fin 2) ≠ 0 by decide),
      cbXa, cbMom, Fin.isValue, ↓reduceIte, Fin.reduceEq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    unfold cbNum
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  · simp only [Fin.mk_one, cbLine_self P hε, cbLine_ne P (show (0 : Fin 2) ≠ 1 by decide),
      cbXa, cbMom, Fin.isValue, ↓reduceIte, Fin.reduceEq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    unfold cbNum
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring

/-! ### The divided difference over the loop flavours -/

/-- The coefficient of `M²` in `cbNum`. -/
noncomputable def cbNum2 (P : Params) (X1 X0 : Matrix (Fin 4) (Fin 4) ℂ) (α β μ : Fin 4) : ℂ :=
  (I * P.e) ^ 5 * (1 / I) ^ 6 * ∑ l0 : Fin 4, ∑ l3 : Fin 4, ∑ l4 : Fin 4, ∑ l5 : Fin 4,
    (Dirac.gamma l0 * X1 * Dirac.gamma μ * X0 * Dirac.gamma l3) α β *
      ((Minkowski.metric l0 l4 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) *
      ((Minkowski.metric l3 l5 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) *
      (Dirac.gamma l5 * Dirac.gamma l4).trace

theorem cbNum_eq (P : Params) (M : ℝ) (X1 X0 : Matrix (Fin 4) (Fin 4) ℂ) (α β μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbNum P M X1 X0 α β μ ℓ =
      cbNum P 0 X1 X0 α β μ ℓ + ((M ^ 2 : ℝ) : ℂ) * cbNum2 P X1 X0 α β μ := by
  rw [cbNum, cbNum, cbNum2]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [loopTrace_eq]
  ring

/-- The numerator of the divided-difference term `t` for the numerator `E₀ + M² E₂`, as in
`vpTermNumer`. -/
noncomputable def cbTermNumer (P : Params) (p p' : Fin 4 → ℝ) (E0 E2 : ℂ) (t : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  if t = 3 then -(vpBubbleCoeff P * E2 * (vpDenom P 3 p p' 8 ℓ + vpDenom P 3 p p' 3 ℓ))
  else vpBubbleCoeff P * (E0 + ((P.m ^ 2 : ℝ) : ℂ) * E2)

theorem cbLineVP_rows (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    classLineVP p p' 0 ℓ = p + ℓ 1 ∧ classLineVP p p' 1 ℓ = p' + ℓ 1 ∧
      classLineVP p p' 2 ℓ = ℓ 0 - ℓ 1 ∧ classLineVP p p' 3 ℓ = ℓ 0 ∧
      classLineVP p p' 4 ℓ = -ℓ 1 ∧ classLineVP p p' 5 ℓ = ℓ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext μ <;>
    simp [classLineVP, QED.Integration.TwoLoop.lineMomentum,
      QED.Integration.TwoLoop.castLoopMatrix, QED.Integration.TwoLoop.class5LoopMatrix,
      QED.Integration.TwoLoop.classVPMomenta, Fin.sum_univ_two] <;> ring

/-- **The flavour sum in divided-difference form**: for `ε ≠ 0` and the two Pauli–Villars
conditions, the flavour sum of `(E₀ + M_f² E₂)` over the open-line, photon and loop denominators
is the sum over the four shapes `t` of `cbTermNumer t` over the ten denominators `vpDenom t`. -/
theorem flavourSum_cb (P : Params) (hε : P.ε ≠ 0) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (p' p : Fin 4 → ℝ) (E0 E2 : ℂ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ f : Fin 3, (P.loopCoeff f : ℂ) * ((E0 + ((P.mass f ^ 2 : ℝ) : ℂ) * E2) *
        ((propDenom P.m P.ε (cbMom p' p ℓ 0))⁻¹ * (propDenom P.m P.ε (cbMom p' p ℓ 1))⁻¹) *
        cbRest P f ℓ) =
      ∑ t : Fin 4, cbTermNumer P p p' E0 E2 t ℓ * ∏ i : Fin 10, (vpDenom P t p p' i ℓ)⁻¹ := by
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := cbLineVP_rows p p' ℓ
  simp only [Fin.sum_univ_three, Fin.sum_univ_four, prod_univ_ten, vpDenom_eq, cbTermNumer, cbRest,
    cbMom]
  simp only [Params.loopCoeff, Params.mass, vpShapeMasses, vpShapeLines, Matrix.cons_val,
    Fin.isValue, Fin.reduceEq, ↓reduceIte, Complex.ofReal_one, vpBubbleCoeff, r0, r1, r2, r3, r4,
    r5]
  have key := flavourSum_propDenom hε (ℓ 0 - ℓ 1) (ℓ 0) hc₁ hc₂ E0 E2
  linear_combination
    ((propDenom P.m P.ε (p + ℓ 1))⁻¹ * (propDenom P.m P.ε (p' + ℓ 1))⁻¹ *
      (propDenom P.mγ P.ε (-ℓ 1))⁻¹ * (propDenom P.mγ P.ε (ℓ 1))⁻¹ *
      (propDenom P.Λ P.ε (-ℓ 1))⁻¹ * (propDenom P.Λ P.ε (ℓ 1))⁻¹) * key

/-! ### The integrand in shape form -/

/-- The line denominators of the doubled shape `(d, t)` at prescription `ε`. -/
noncomputable def cbDenom (P : Params) (d : Fin 2) (t : Fin 4) (p p' : Fin 4 → ℝ) (ε : ℝ)
    (i : Fin 11) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  lineDenom (castLoopMatrix (cbShapeMatrix d t)) (cbShapeMomenta d t p p') (cbShapeMasses P t) ε i ℓ

theorem cbDenom_castSucc (P : Params) (d : Fin 2) (t : Fin 4) (p p' : Fin 4 → ℝ) (ε : ℝ)
    (i : Fin 10) (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbDenom P d t p p' ε i.castSucc ℓ =
      lineDenom (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t p p') (vpShapeMasses P t) ε i
        ℓ := by
  have hl : QED.Integration.TwoLoop.lineMomentum (castLoopMatrix (cbShapeMatrix d t))
      (cbShapeMomenta d t p p') i.castSucc ℓ = QED.Integration.TwoLoop.lineMomentum
        (castLoopMatrix (vpShapeMatrix t)) (vpShapeMomenta t p p') i ℓ := by
    funext μ
    simp only [QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, cbShapeMatrix_castSucc,
      cbShapeMomenta_castSucc]
  simp only [cbDenom, lineDenom, hl, cbShapeMasses_castSucc]

theorem cbDenom_last (P : Params) (d : Fin 2) (t : Fin 4) (p p' : Fin 4 → ℝ) (ε : ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbDenom P d t p p' ε (Fin.last 10) ℓ = propDenom P.m ε (cbMom p' p ℓ d) := by
  have hl : ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      QED.Integration.TwoLoop.lineMomentum (castLoopMatrix (cbShapeMatrix d t))
      (cbShapeMomenta d t p p') (Fin.last 10) ℓ = cbMom p' p ℓ d := fun ℓ => by
    funext μ
    simp only [QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, cbShapeMatrix_last,
      cbShapeMomenta, cbShapeLines_last]
    fin_cases d <;> fin_cases t <;>
      simp [vpShapeMatrix, vpShapeLines, QED.Integration.TwoLoop.class5LoopMatrix,
        QED.Integration.TwoLoop.classVPMomenta, cbMom, Fin.sum_univ_two] <;> ring
  simp only [cbDenom, lineDenom, hl, cbShapeMasses_last, propDenom]

/-- The `ε`-independent numerator pair of the once-merged term: `(E₀, E₂)` of
`cbNum (cbXa 1) (cbXa 0)`. -/
noncomputable def cbEa0 (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ) (α β μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  cbNum P 0 (cbXa P d p' p ℓ 1) (cbXa P d p' p ℓ 0) α β μ ℓ

noncomputable def cbEa2 (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ) (α β μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  cbNum2 P (cbXa P d p' p ℓ 1) (cbXa P d p' p ℓ 0) α β μ

/-- The pair `(E₀, E₂)` of the bare numerator `cbNum A₁ A₀` (that of `VP`). -/
noncomputable def cbEv0 (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  cbNum P 0 (electronNumerator P.m (cbMom p' p ℓ 1)) (electronNumerator P.m (cbMom p' p ℓ 0)) α β
    μ ℓ

noncomputable def cbEv2 (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  cbNum2 P (electronNumerator P.m (cbMom p' p ℓ 1)) (electronNumerator P.m (cbMom p' p ℓ 0)) α β μ

/-- **The flavour sum of the amplitudes in shape form** (`ε ≠ 0`, Pauli–Villars conditions):
the once-merged numerator over the ten-line shapes `t`, and `c N + iε N_a` over the doubled
eleven-line shapes `(d, t)`. -/
theorem flavourSum_cbAmp (P : Params) (hε : P.ε ≠ 0) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (d : Fin 2) (p' p : Fin 4 → ℝ)
    (α β μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ f : Fin 3, (P.loopCoeff f : ℂ) * cbAmp P f d p' p α β μ ℓ =
      -(∑ t : Fin 4, cbTermNumer P p p' (cbEa0 P d p' p α β μ ℓ) (cbEa2 P d p' p α β μ ℓ) t ℓ *
          ∏ i : Fin 10, (vpDenom P t p p' i ℓ)⁻¹ +
        ∑ t : Fin 4, cbTermNumer P p p'
            (mergeC P.m P.δ₂ P.δm * cbEv0 P p' p α β μ ℓ +
              (P.ε : ℂ) * I * cbEa0 P d p' p α β μ ℓ)
            (mergeC P.m P.δ₂ P.δm * cbEv2 P p' p α β μ ℓ +
              (P.ε : ℂ) * I * cbEa2 P d p' p α β μ ℓ) t ℓ *
          ∏ i : Fin 11, (cbDenom P d t p p' P.ε i ℓ)⁻¹) := by
  have hprod : ∀ t : Fin 4, ∏ i : Fin 11, (cbDenom P d t p p' P.ε i ℓ)⁻¹ =
      (∏ i : Fin 10, (vpDenom P t p p' i ℓ)⁻¹) * (propDenom P.m P.ε (cbMom p' p ℓ d))⁻¹ :=
    fun t => by
      rw [Fin.prod_univ_castSucc, cbDenom_last]
      simp only [cbDenom_castSucc]
      rfl
  simp only [hprod, ← mul_assoc]
  rw [← Finset.sum_mul, ← flavourSum_cb P hε hc₁ hc₂, ← flavourSum_cb P hε hc₁ hc₂,
    Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [cbAmp_eq P hε, cbNum_eq P (P.mass f), cbNum_eq P (P.mass f) (electronNumerator P.m _)]
  unfold cbEa0 cbEa2 cbEv0 cbEv2
  ring

/-- The integrand of `CB0` (`d = 1`), `CB1` (`d = 0`) in shape form, at the prescription `P.ε`. -/
noncomputable def cbIntegrand (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ) (α β μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  -(∑ t : Fin 4, cbTermNumer P p p' (cbEa0 P d p' p α β μ ℓ) (cbEa2 P d p' p α β μ ℓ) t ℓ *
      ∏ i : Fin 10, (vpDenom P t p p' i ℓ)⁻¹ +
    ∑ t : Fin 4, cbTermNumer P p p'
        (mergeC P.m P.δ₂ P.δm * cbEv0 P p' p α β μ ℓ + (P.ε : ℂ) * I * cbEa0 P d p' p α β μ ℓ)
        (mergeC P.m P.δ₂ P.δm * cbEv2 P p' p α β μ ℓ +
          (P.ε : ℂ) * I * cbEa2 P d p' p α β μ ℓ) t ℓ *
      ∏ i : Fin 11, (cbDenom P d t p p' P.ε i ℓ)⁻¹)

/-- **The value of `CB0` in shape form** (`ε ≠ 0`, Pauli–Villars conditions). -/
theorem contractionValue₂_cb0_shapes (P : Params) (hε : P.ε ≠ 0) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    contractionValue₂ P repCB0 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
        (fun _ => β) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * cbIntegrand P 1 p' p α β μ ℓ := by
  rw [contractionValue₂_cb0]
  simp only [flavourSum_cbAmp P hε hc₁ hc₂, cbIntegrand]

/-- **The value of `CB1` in shape form** (`ε ≠ 0`, Pauli–Villars conditions). -/
theorem contractionValue₂_cb1_shapes (P : Params) (hε : P.ε ≠ 0) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    contractionValue₂ P repCB1 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
        (fun _ => β) (fun _ => μ) =
      QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * cbIntegrand P 0 p' p α β μ ℓ := by
  rw [contractionValue₂_cb1]
  simp only [flavourSum_cbAmp P hε hc₁ hc₂, cbIntegrand]

end QED.ChainProof.SetCPauli.CB01

end
