/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZero
public import QED.TwoLoop.PauliZeroLimitParam
public import QED.TwoLoop.ParametricBridgeVPFlavour
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The curve of pairs and the Pauli numerator along it

Part of obligation O2-22 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4).

* `curveMomentum m u = m((1+u²)/(1-u²), 2u/(1-u²), 0, 0)`: on shell, positive energy for
  `|u| < 1`, with `q² = 4m²u²/(1-u²)` against `restMomentum m` (`dot_curveMomentum_sub`); it is
  `boostMomentum m (q²)` for `0 ≤ u < 1` (`boostMomentum_curveQ`), the reflection in the first
  spatial axis maps it to `curveMomentum m (-u)` and fixes the rest momentum, and
  `(1 - u²) curveMomentum m u` is polynomial of degree `2` (`isUPoly_curveMomentum`).
* `pauliNum m p' p V = m D T₁ + (q² - 2m²) T₂`, the numerator of the Pauli projector
  (`formFactorProj₂_eq_pauliNum`). It is the linear form `∑ pauliWt μ i j V^μ_ij`
  (`pauliNum_eq_sum`) whose weights are polynomials of degree `4` in `p'`
  (`isLoopPoly_pauliWt`), vanishes identically at `p' = p` (`pauliNum_self`), and is invariant under
  Lorentz maps with spinor lifts (`pauliNum_map`).
* `pauliNum_vertexLimit_neg`: the Pauli numerator of the order-`e⁵` vertex limit along the curve is
  even in `u`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set

namespace QED.TwoLoop.PauliZeroLimit

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Bridge (IsLoopPoly IsLoopAffine IsLoopPolyMat electronNumerator propDenom)

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The curve -/

/-- `p'(u) = m((1+u²)/(1-u²), 2u/(1-u²), 0, 0)`. -/
noncomputable def curveMomentum (m u : ℝ) : Fin 4 → ℝ :=
  ![m * (1 + u ^ 2) / (1 - u ^ 2), 2 * m * u / (1 - u ^ 2), 0, 0]

/-- `q² = 4m²u²/(1-u²)` along the curve. -/
noncomputable def curveQ (m u : ℝ) : ℝ := 4 * m ^ 2 * u ^ 2 / (1 - u ^ 2)

theorem one_sub_sq_pos {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) : 0 < 1 - u ^ 2 := by
  nlinarith [hu.1, hu.2]

theorem dot_curveMomentum (m : ℝ) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    Minkowski.dot (curveMomentum m u) (curveMomentum m u) = -m ^ 2 := by
  have h := (one_sub_sq_pos hu).ne'
  simp only [Minkowski.dot_eq, curveMomentum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring

theorem curveMomentum_pos {m : ℝ} (hm : 0 < m) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    0 < curveMomentum m u 0 := by
  have h := one_sub_sq_pos hu
  simp only [curveMomentum, Matrix.cons_val_zero]
  positivity

theorem curveQ_nonneg (m : ℝ) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) : 0 ≤ curveQ m u := by
  have h := one_sub_sq_pos hu
  unfold curveQ
  positivity

theorem curveQ_neg (m u : ℝ) : curveQ m (-u) = curveQ m u := by simp [curveQ]

theorem dot_curveMomentum_sub (m : ℝ) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    Minkowski.dot (curveMomentum m u - restMomentum m) (curveMomentum m u - restMomentum m) =
      curveQ m u := by
  have h := (one_sub_sq_pos hu).ne'
  simp only [Minkowski.dot_eq, curveMomentum, restMomentum, curveQ, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring

theorem curveMomentum_zero (m : ℝ) : curveMomentum m 0 = restMomentum m := by
  funext μ
  fin_cases μ <;> simp [curveMomentum, restMomentum]

/-- **The curve is the canonical boost**: `p'(u) = boostMomentum m (q²)` for `0 ≤ u < 1`. -/
theorem boostMomentum_curveQ {m : ℝ} (hm : 0 < m) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    boostMomentum m (curveQ m u) = curveMomentum m u := by
  have hu : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hu1⟩
  have h := one_sub_sq_pos hu
  have hm' := hm.ne'
  have hsq : curveQ m u + curveQ m u ^ 2 / (4 * m ^ 2) = (2 * m * u / (1 - u ^ 2)) ^ 2 := by
    unfold curveQ
    field_simp
    ring
  funext μ
  fin_cases μ
  · simp only [boostMomentum, curveMomentum, curveQ, Matrix.cons_val_zero, Fin.zero_eta]
    field_simp
    ring
  · simp only [boostMomentum, curveMomentum, Matrix.cons_val_one, Fin.mk_one]
    rw [hsq, Real.sqrt_sq (by positivity)]
  · rfl
  · rfl

/-- The first spatial unit vector. -/
def axisOne : Fin 4 → ℝ := ![0, 1, 0, 0]

theorem dot_axisOne : Minkowski.dot axisOne axisOne = 1 := by
  simp [Minkowski.dot_eq, axisOne]

theorem reflectMatrix_curveMomentum (m u : ℝ) :
    reflectMatrix axisOne *ᵥ curveMomentum m u = curveMomentum m (-u) := by
  rw [reflectMatrix_mulVec]
  funext μ
  fin_cases μ <;> simp [reflect, axisOne, curveMomentum, Minkowski.dot_eq]
  ring

theorem reflectMatrix_restMomentum (m : ℝ) :
    reflectMatrix axisOne *ᵥ restMomentum m = restMomentum m := by
  rw [reflectMatrix_mulVec]
  funext μ
  fin_cases μ <;> simp [reflect, axisOne, restMomentum, Minkowski.dot_eq]

/-- `(1 - u²) p'(u)` is polynomial of degree at most `2`. -/
theorem isUPoly_curveMomentum {ι : Type*} (m : ℝ) (μ : Fin 4) :
    IsUPoly (ι := ι) 2 fun _ u => wt u * ((curveMomentum m u μ : ℝ) : ℂ) := by
  have key : ∀ (P : Polynomial ℂ), P.natDegree ≤ 2 →
      (∀ u ∈ Ioo (-1 : ℝ) 1, wt u * ((curveMomentum m u μ : ℝ) : ℂ) = P.eval (u : ℂ)) →
      IsUPoly (ι := ι) 2 fun _ u => wt u * ((curveMomentum m u μ : ℝ) : ℂ) :=
    fun P hP h _ => ⟨P, hP, h⟩
  have hw : ∀ u ∈ Ioo (-1 : ℝ) 1, wt u = ((1 - u ^ 2 : ℝ) : ℂ) := fun u _ => by simp [wt]
  fin_cases μ
  · refine key (Polynomial.C (m : ℂ) * (1 + Polynomial.X ^ 2)) ?_ fun u hu => ?_
    · refine Polynomial.natDegree_mul_le.trans ?_
      rw [Polynomial.natDegree_C, zero_add]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (Polynomial.natDegree_X_pow_le 2))
      rw [Polynomial.natDegree_one]; exact Nat.zero_le _
    · have h := (one_sub_sq_pos hu).ne'
      rw [hw u hu]
      simp only [curveMomentum, Fin.zero_eta, Matrix.cons_val_zero]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_one,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [← ofReal_mul, mul_div_cancel₀ _ h]
      push_cast
      ring
  · refine key (Polynomial.C (2 * m : ℂ) * Polynomial.X) ?_ fun u hu => ?_
    · refine Polynomial.natDegree_mul_le.trans ?_
      rw [Polynomial.natDegree_C, zero_add]
      exact Polynomial.natDegree_X_le.trans (by norm_num)
    · have h := (one_sub_sq_pos hu).ne'
      rw [hw u hu]
      simp only [curveMomentum, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [← ofReal_mul, mul_div_cancel₀ _ h]
      push_cast
      ring
  · exact (IsUPoly.const (fun _ => 0)).congr fun _ u _ => by simp [curveMomentum]
  · exact (IsUPoly.const (fun _ => 0)).congr fun _ u _ => by simp [curveMomentum]

/-! ### The Pauli numerator -/

/-- The numerator `m D T₁ + (q² - 2m²) T₂` of the Pauli projector. -/
noncomputable def pauliNum (m : ℝ) (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ℂ :=
  (m : ℂ) * (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) * traceGammaProj m p' p V +
    ((Minkowski.dot (p' - p) (p' - p) : ℂ) - 2 * (m : ℂ) ^ 2) * traceVecProj m p' p (p' + p) V

theorem formFactorProj₂_eq_pauliNum (e m : ℝ) (p' p : Fin 4 → ℝ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    QED.OneLoop.formFactorProj₂ e m p' p V = (m : ℂ) * pauliNum m p' p V /
      ((e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
        (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2) := rfl

theorem pauliNum_self (m : ℝ) (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -m ^ 2)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : pauliNum m p p V = 0 :=
  formFactorProj₂_numerator_self m p hp V

/-- The weights of the Pauli numerator as a linear form in the entries of `V`. -/
noncomputable def pauliWt (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) : ℂ :=
  (m : ℂ) * (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) *
      (electronNumerator m p * gammaLower μ * electronNumerator m p') j i +
    ((Minkowski.dot (p' - p) (p' - p) : ℂ) - 2 * (m : ℂ) ^ 2) *
      ((Minkowski.lower (p' + p) μ : ℝ) : ℂ) * (electronNumerator m p * electronNumerator m p') j i

theorem trace_mul_mul_eq_sum (A V B : Matrix (Fin 4) (Fin 4) ℂ) :
    trace (A * V * B) = ∑ i, ∑ j, V i j * (B * A) j i := by
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  rfl

/-- **The Pauli numerator as a linear form.** -/
theorem pauliNum_eq_sum (m : ℝ) (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pauliNum m p' p V = ∑ μ, ∑ i, ∑ j, pauliWt m p' p μ i j * V μ i j := by
  have h1 : traceGammaProj m p' p V = ∑ μ, ∑ i, ∑ j, V μ i j *
      (electronNumerator m p * gammaLower μ * electronNumerator m p') j i := by
    unfold traceGammaProj
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [show ((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p) * gammaLower μ =
        electronNumerator m p' * V μ * (electronNumerator m p * gammaLower μ) by
      simp only [electronNumerator, Matrix.mul_assoc], trace_mul_mul_eq_sum]
  have h2 : traceVecProj m p' p (p' + p) V = ∑ μ, ((Minkowski.lower (p' + p) μ : ℝ) : ℂ) *
      ∑ i, ∑ j, V μ i j * (electronNumerator m p * electronNumerator m p') j i := by
    unfold traceVecProj
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [show ((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p) =
        electronNumerator m p' * V μ * electronNumerator m p from rfl, trace_mul_mul_eq_sum]
  rw [pauliNum, h1, h2]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  unfold pauliWt
  ring

/-- **The weights are polynomials of degree at most `4` in `p'`.** -/
theorem isLoopPoly_pauliWt (m : ℝ) (p : Fin 4 → ℝ) (μ i j : Fin 4) :
    IsLoopPoly 1 4 fun y => pauliWt m (y 0) p μ i j := by
  have hy : IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ => y 0 :=
    ⟨![1], 0, fun y => by funext ν; simp⟩
  have hys : IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ => y 0 - p :=
    ⟨![1], -p, fun y => by funext ν; simp [sub_eq_add_neg]⟩
  have hya : IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ => y 0 + p :=
    ⟨![1], p, fun y => by funext ν; simp⟩
  have hQ : IsLoopPoly 1 2 fun y : Fin 1 → Fin 4 → ℝ =>
      ((Minkowski.dot (y 0 - p) (y 0 - p) : ℝ) : ℂ) := by
    have h := hys.isLoopPoly_propDenom 0 0
    refine (congrArg (IsLoopPoly 1 2) (funext fun y => ?_)).mp h
    simp [propDenom]
  have hlow : IsLoopPoly 1 1 fun y : Fin 1 → Fin 4 → ℝ =>
      ((Minkowski.lower (y 0 + p) μ : ℝ) : ℂ) := by
    have e : ∀ y : Fin 1 → Fin 4 → ℝ, ((Minkowski.lower (y 0 + p) μ : ℝ) : ℂ) =
        ∑ ν ∈ Finset.univ, ((Minkowski.metric μ ν : ℝ) : ℂ) * (((y 0 + p) ν : ℝ) : ℂ) := by
      intro y
      simp [Minkowski.lower]
    simp only [e]
    exact IsLoopPoly.sum _ fun ν _ => (hya.isLoopPoly_coord ν).const_mul _
  have hE1 : IsLoopPolyMat 1 1 fun y : Fin 1 → Fin 4 → ℝ =>
      electronNumerator m p * gammaLower μ * electronNumerator m (y 0) := by
    simpa using ((IsLoopPolyMat.const (L := 1) (electronNumerator m p * gammaLower μ)).mul
      (hy.isLoopPolyMat_electronNumerator m))
  have hE2 : IsLoopPolyMat 1 1 fun y : Fin 1 → Fin 4 → ℝ =>
      electronNumerator m p * electronNumerator m (y 0) := by
    simpa using ((IsLoopPolyMat.const (L := 1) (electronNumerator m p)).mul
      (hy.isLoopPolyMat_electronNumerator m))
  unfold pauliWt
  have h1 := (((IsLoopPoly.const (n := 0) (4 * (m : ℂ) ^ 2)).mono (Nat.zero_le 2)).add
    hQ).const_mul (m : ℂ) |>.mul (hE1 j i)
  have h2 := ((hQ.sub ((IsLoopPoly.const (n := 0) (2 * (m : ℂ) ^ 2)).mono (Nat.zero_le 2))).mul
    hlow).mul (hE2 j i)
  have h := (h1.mono (by norm_num : 2 + 1 ≤ 4)).add h2
  refine (congrArg (IsLoopPoly 1 4) (funext fun y => ?_)).mp h
  ring

/-- **The Pauli numerator is invariant** under a Lorentz map with a spinor lift. -/
theorem pauliNum_map {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S T) (m : ℝ) (p' p : Fin 4 → ℝ) {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hW : ∀ μ, S * W μ * T = vecAct L V μ) :
    pauliNum m (L *ᵥ p') (L *ᵥ p) W = pauliNum m p' p V := by
  have hK : L *ᵥ p' + L *ᵥ p = L *ᵥ (p' + p) := (Matrix.mulVec_add _ _ _).symm
  have hq : Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) =
      Minkowski.dot (p' - p) (p' - p) := by
    rw [← Matrix.mulVec_sub, h.dot_mulVec]
  unfold pauliNum
  rw [hK, hq, traceGammaProj_map h m p' p hW, traceVecProj_map h m p' p (p' + p) hW]

section Vertex

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁)
  (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
  (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
include hm hmγ hΛ hM₁ hM₂ hc₁ hc₂

theorem isVertexOrderFiveLimit_curve {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    IsVertexOrderFiveLimit P (curveMomentum P.m u) (restMomentum P.m)
      (vertexLimitAt P (curveMomentum P.m u) (restMomentum P.m)) :=
  isVertexOrderFiveLimit_vertexLimitAt P (VertexLimit.exists_isVertexOrderFiveLimit P hm hmγ hΛ
    hM₁ hM₂ hc₁ hc₂ (dot_restMomentum (m := P.m)) (dot_curveMomentum P.m hu)
    (restMomentum_pos hm) (curveMomentum_pos hm hu)
    ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu))

/-- **The Pauli numerator of the vertex limit along the curve is even in `u`.** -/
theorem pauliNum_vertexLimit_neg {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    pauliNum P.m (curveMomentum P.m (-u)) (restMomentum P.m)
        (vertexLimitAt P (curveMomentum P.m (-u)) (restMomentum P.m)) =
      pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
        (vertexLimitAt P (curveMomentum P.m u) (restMomentum P.m)) := by
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
    (by rw [dot_axisOne]; exact one_ne_zero)
  have hW := isVertexOrderFiveLimit_curve P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hu'
  have e1 := reflectMatrix_curveMomentum P.m u
  have e2 := reflectMatrix_restMomentum P.m
  rw [← e1, ← e2] at hW
  have key : pauliNum P.m (reflectMatrix axisOne *ᵥ curveMomentum P.m u)
      (reflectMatrix axisOne *ᵥ restMomentum P.m)
      (vertexLimitAt P (reflectMatrix axisOne *ᵥ curveMomentum P.m u)
        (reflectMatrix axisOne *ᵥ restMomentum P.m)) =
      pauliNum P.m (curveMomentum P.m u) (restMomentum P.m)
        (vertexLimitAt P (curveMomentum P.m u) (restMomentum P.m)) := by
    refine pauliNum_map h P.m _ _ fun μ => ?_
    refine conj_vertexLimit_map P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ h (dot_restMomentum (m := P.m))
      (dot_curveMomentum P.m hu) (restMomentum_pos hm) (curveMomentum_pos hm hu) ?_ ?_
      ((dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu)
      (isVertexOrderFiveLimit_curve P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hu) hW μ
    · rw [e2]; exact restMomentum_pos hm
    · rw [e1]; exact curveMomentum_pos hm hu'
  rw [e1, e2] at key
  exact key

end Vertex

end QED.TwoLoop.PauliZeroLimit

end
