/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.CountertermMirrorVertex
public import QED.TwoLoop.LimitMirrorVP

/-!
# The mirror identity of the counterterm part

Part of obligation O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). The counterterm part
`QED.TwoLoop.LimitMirror.ctPart` of the order-`e⁵` limit is the sum of the limits of the seven
counterterm classes. Grouped by charge conjugation:

* `δ₂` on the incoming line `↔` `δ₂` on the outgoing line
  (`QED.TwoLoop.CountertermMirror.isCtChargeConjPair_d2In_d2Out`);
* each `δ₃` class to itself (`isCtChargeConjPair_d3Slot0`), and the two have the same limit
  (`ctLimit_d3Slot1`);
* the three `δ₁` classes are `δ₁` times the one-loop vertex, whose limit is mirror symmetric by its
  closed form, with no covariance hypothesis (`isMirrorSymmetric_ctLimit_d1`).

The `δ₂` and `δ₃` limits are mirror symmetric given their covariance under the reflection `R_K`
(`IsReflCovariantAt`, as for the classes of five gauge vertices). Charge conjugation transports
covariance within a pair (`isReflCovariantAt_of_pair`, using `C S_Kᵀ C = S_K`), so the covariance
of `δ₂ in` gives that of `δ₂ out`.

## Main statements

* `isReflCovariantAt_of_pair`: covariance passes along a charge-conjugate pair.
* `isMirrorSymmetric_ctPart`: **the counterterm part is mirror symmetric**, given the `R_K`
  covariance of the limits of the classes `δ₂ in` and `δ₃` (slot `0`).
* `isMirrorSymmetric_headline_of_cov_ct`: the mirror identity of the order-`e⁵` limit in the shape
  of the headline (HV₃), from the `R_K` covariance of the seven class limits of five gauge vertices
  and of those two counterterm class limits; the hypothesis `hct` of
  `QED.TwoLoop.LimitMirror.isMirrorSymmetric_headline_of_cov` is discharged.
-/

@[expose] public section

open Matrix Complex Filter Topology

namespace QED.TwoLoop.CountertermMirror

open QED.WickModel QED.TwoLoop.Relabel QED.TwoLoop.LimitMirror QED.OneLoop QED.Dirac

/-- The counterterm part, grouped by charge conjugation. -/
theorem ctPart_eq (P : Params) (p' p : Fin 4 → ℝ) :
    ctPart P p' p = (ctLimit .d2In P p' p + ctLimit .d2Out P p' p) + ctLimit .d3Slot0 P p' p +
      ctLimit .d3Slot1 P p' p + ctLimit .d1At1 P p' p + ctLimit .d1At2 P p' p +
      ctLimit .d1At3 P p' p := by
  rw [ctPart, show (Finset.univ : Finset CtClass) =
    {.d2In, .d2Out, .d3Slot0, .d3Slot1, .d1At1, .d1At2, .d1At3} from rfl]
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton]
  abel

/-! ### Covariance transported by charge conjugation -/

/-- The chirality matrix `Γ = diag(-1, -1, 1, 1)` is charge-conjugation invariant. -/
theorem ccT_chirality :
    ccT (Matrix.diagonal ![(-1 : ℂ), -1, 1, 1]) = Matrix.diagonal ![(-1 : ℂ), -1, 1, 1] := by
  ext a b
  rw [ccT_apply]
  fin_cases a <;> fin_cases b <;> simp [ccIdx, ccSign, Matrix.diagonal]

theorem ccT_ccT (X : Matrix (Fin 4) (Fin 4) ℂ) : ccT (ccT X) = X :=
  chargeConj_transpose_involutive X

/-- The spinor representative `S_K = K̸ Γ` of `R_K` is charge-conjugation invariant. -/
theorem ccT_reflSpin (K : Fin 4 → ℝ) : ccT (reflSpin K) = reflSpin K := by
  rw [reflSpin, ccT_mul, ccT_chirality, ccT_slash, Matrix.mul_neg, Dirac.chirality_mul_slash,
    neg_neg]

theorem ccT_conj (K : Fin 4 → ℝ) (c : ℂ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    ccT (reflSpin K * X * (c • reflSpin K)) = reflSpin K * ccT X * (c • reflSpin K) := by
  rw [ccT_mul, ccT_mul, ccT_smul, ccT_reflSpin]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

theorem ccT_vecAct (L : Matrix (Fin 4) (Fin 4) ℝ) (W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ : Fin 4) : ccT (vecAct L W μ) = vecAct L (fun ν => ccT (W ν)) μ := by
  simp only [vecAct, ccT_sum, ccT_smul]

theorem vecAct_neg' (L : Matrix (Fin 4) (Fin 4) ℝ) (W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ : Fin 4) : vecAct L (fun ν => -W ν) μ = -vecAct L W μ := by
  simp only [vecAct, smul_neg, Finset.sum_neg_distrib]

theorem vecAct_vecAct (L L' : Matrix (Fin 4) (Fin 4) ℝ) (W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ : Fin 4) : vecAct L (fun ν => vecAct L' W ν) μ = vecAct (L * L') W μ := by
  simp only [vecAct, Finset.smul_sum, smul_smul, Matrix.mul_apply, ofReal_sum, ofReal_mul,
    Finset.sum_smul]
  exact Finset.sum_comm

theorem vecAct_one (W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) : vecAct 1 W μ = W μ := by
  simp [vecAct, Matrix.one_apply]

theorem reflectMatrix_mul_self {K : Fin 4 → ℝ} (hK : Minkowski.dot K K ≠ 0) :
    reflectMatrix K * reflectMatrix K = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, reflectMatrix_mulVec,
    reflectMatrix_mulVec, reflect_reflect hK, Matrix.one_mulVec]

/-- **Charge conjugation transports covariance**: for a charge-conjugate pair `(c, c')` with
limits at `(p', p)`, the `R_K` covariance of the limit of `c` gives that of `c'`. -/
theorem isReflCovariantAt_of_pair {c c' : CtClass} (hcc : IsCtChargeConjPair c c') (P : Params)
    {m : ℝ} {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    (h : HasCtLimit c P p' p) (h' : HasCtLimit c' P p' p)
    (hcov : IsReflCovariantAt (ctLimit c P) p' p) : IsReflCovariantAt (ctLimit c' P) p' p := by
  obtain ⟨hRp, hRp', -⟩ := reflect_add_self hp' hp hq
  have hK := dot_add_self_ne_zero hp' hp hq
  set d : ℂ := ((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ) with hd
  have hd0 : d ≠ 0 := by rw [hd]; exact_mod_cast hK
  set S := reflSpin (p' + p) with hS
  set R := reflectMatrix (p' + p) with hR
  have hA : ∀ μ, ctLimit c' P (-p) (-p') μ = -ccT (ctLimit c P p' p μ) := fun μ => by
    rw [ccT, chargeConj_ctLimit_of_pair hcc P h μ, neg_neg]
  have hB : ∀ μ, ctLimit c' P p' p μ = -ccT (ctLimit c P (-p) (-p') μ) := fun μ => by
    have e : ccT (ctLimit c' P p' p μ) = -ctLimit c P (-p) (-p') μ :=
      chargeConj_ctLimit_of_pair hcc.symm P h' μ
    rw [show ctLimit c P (-p) (-p') μ = -ccT (ctLimit c' P p' p μ) by rw [e, neg_neg], ccT_neg,
      ccT_ccT, neg_neg]
  have hC : ∀ μ, S * ctLimit c P (-p) (-p') μ * (d⁻¹ • S) = vecAct R (ctLimit c P p' p) μ :=
    fun μ => by
      have e := hcov μ
      rwa [hRp, hRp'] at e
  have hSS : ∀ X : Matrix (Fin 4) (Fin 4) ℂ, S * (S * X * (d⁻¹ • S)) * (d⁻¹ • S) = X := fun X => by
    have e1 : S * S = d • 1 := reflSpin_mul_reflSpin _
    calc S * (S * X * (d⁻¹ • S)) * (d⁻¹ • S) = (d⁻¹ * d⁻¹) • ((S * S) * X * (S * S)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
      _ = X := by
          rw [e1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
            smul_smul]
          rw [show d⁻¹ * d⁻¹ * d * d = 1 by field_simp, one_smul]
  have hD : ∀ μ, S * ctLimit c P p' p μ * (d⁻¹ • S) = vecAct R (ctLimit c P (-p) (-p')) μ :=
    fun μ => by
      calc S * ctLimit c P p' p μ * (d⁻¹ • S)
          = S * vecAct R (fun ν => vecAct R (ctLimit c P p' p) ν) μ * (d⁻¹ • S) := by
            rw [vecAct_vecAct, hR, reflectMatrix_mul_self hK, vecAct_one]
        _ = S * vecAct R (fun ν => S * ctLimit c P (-p) (-p') ν * (d⁻¹ • S)) μ * (d⁻¹ • S) := by
            simp only [hC]
        _ = vecAct R (ctLimit c P (-p) (-p')) μ := by
            rw [← mul_vecAct_mul, hSS]
  intro μ
  rw [hRp, hRp', hA μ, show ctLimit c' P p' p = fun ν => -ccT (ctLimit c P (-p) (-p') ν) from
    funext hB, vecAct_neg', ← ccT_vecAct, ← hD μ, Matrix.mul_neg, Matrix.neg_mul, ccT_conj]

/-- **The counterterm part of the order-`e⁵` limit is mirror symmetric**, for `m, m_γ, Λ > 0`,
on-shell positive-energy `p, p'` with `q² > 0` and every value of the counterterms, given the
covariance under the reflection `R_K` of the limits of the counterterm classes `δ₂ in` and `δ₃`
(slot `0`). The covariance of `δ₂ out` follows by charge conjugation
(`isReflCovariantAt_of_pair`), and the three `δ₁` classes need no covariance hypothesis. -/
theorem isMirrorSymmetric_ctPart (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
    (hD2In : IsReflCovariantAt (ctLimit .d2In P) p' p)
    (hD3 : IsReflCovariantAt (ctLimit .d3Slot0 P) p' p) :
    IsMirrorSymmetric p' p (ctPart P p' p) := by
  have hl := fun c => hasCtLimit c P hm hmγ hΛ hp hp' hp0 hp0' hq.le
  have h3 := isMirrorSymmetric_ctLimit_self P hp' hp hq isCtChargeConjPair_d3Slot0 (hl _) hD3
  have hd1 := fun c (hc : IsD1 c) =>
    isMirrorSymmetric_ctLimit_d1 hc P hm hmγ hΛ hp hp' hp0 hp0' hq
  rw [ctPart_eq]
  refine isMirrorSymmetric_add (isMirrorSymmetric_add (isMirrorSymmetric_add
    (isMirrorSymmetric_add (isMirrorSymmetric_add
      (isMirrorSymmetric_ctLimit_pair P hp' hp hq isCtChargeConjPair_d2In_d2Out (hl _) (hl _)
        hD2In (isReflCovariantAt_of_pair isCtChargeConjPair_d2In_d2Out P hp' hp hq (hl _) (hl _)
          hD2In)) h3) ?_) (hd1 _ (Or.inl rfl))) (hd1 _ (Or.inr (Or.inl rfl))))
    (hd1 _ (Or.inr (Or.inr rfl)))
  rw [ctLimit_d3Slot1]
  exact h3

/-- **The mirror identity of the order-`e⁵` limit, with the counterterm part discharged.** In the
shape of the headline (HV₃): for the parameters of
`QED.TwoLoop.VertexLimit.exists_isVertexOrderFiveLimit_headline`, an on-shell positive-energy pair
with `q² > 0` and the limit `V`, if the limits of the seven classes `L, X, C₊, C₋, S₊, S₋, VP` and
of the two counterterm classes `δ₂ in`, `δ₃` (slot `0`) are covariant under the reflection
`R_K` in `K = p + p'`, then `V` is mirror symmetric. -/
theorem isMirrorSymmetric_headline_of_cov_ct (P₀ : Params) (hm : 0 < P₀.m) (M₁ M₂ c₁ c₂ : ℝ)
    (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) (hPV₁ : 1 + c₁ + c₂ = 0)
    (hPV₂ : P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (mγ Λ : ℝ) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (d₁ d₂ dm d₃ : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P₀.m ^ 2)
    (hp : Minkowski.dot p p = -P₀.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hV : IsVertexOrderFiveLimit
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } p' p V)
    (hcov : ∀ c ∈ Furry.nonFurry, IsReflCovariantAt (classLimit c
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ }) p' p)
    (hcovCt : ∀ c ∈ ({.d2In, .d3Slot0} : Finset CtClass), IsReflCovariantAt (ctLimit c
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ }) p' p) :
    IsMirrorSymmetric p' p V :=
  isMirrorSymmetric_headline_of_cov P₀ hm M₁ M₂ c₁ c₂ hM₁ hM₂ hPV₁ hPV₂ mγ Λ hmγ hΛ d₁ d₂ dm d₃
    p' p hp' hp hp0' hp0 hq V hV hcov
    (isMirrorSymmetric_ctPart
      { P₀ with
        M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, δ₁ := d₁, δ₂ := d₂,
        δm := dm, δ₃ := d₃ } hm hmγ hΛ hp hp' hp0 hp0' hq (hcovCt _ (by decide))
      (hcovCt _ (by decide)))

end QED.TwoLoop.CountertermMirror

end
