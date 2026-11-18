/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.CountertermMirror
public import QED.OneLoop.VertexFormFactors

/-!
# The mirror identity of the `δ₁` counterterm classes

Part of obligation O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). Each of the three `δ₁`
classes is `δ₁` times the one-loop vertex at every prescription `ε`
(`QED.TwoLoop.Insertion.contractionValue₂_d1At1`, …), so its `ε → 0⁺` limit at on-shell
positive-energy `(p', p)` is `δ₁` times the one-loop vertex limit. That limit has the closed form
(`QED.OneLoop.VertexLimit.vertexLimit_entry_eq`)

`V₁^μ = i (e³/16π²) ∫ dF [log(D_Λ/D_γ) γ^μ + (1/2)(1/D_γ - 1/D_Λ) Ñ^μ(-K_z)]`,

a full `4 × 4` matrix identity, with `Ñ^μ(ℓ) = γ_ν (m - (p' + ℓ)̸) γ^μ (m - (p + ℓ)̸) γ^ν` and the
Feynman shift `K_z = y (x p' + (1 - x) p)`. This file proves that `V₁` is mirror symmetric,
**with no covariance hypothesis**, from the closed form:

* the mirror map `𝓜(X) = S_K C Xᵀ C S_K⁻¹` (`mirrorMap`) reverses products, sends `γ^μ` to
  `-(R_K)^μ_ν γ^ν` and `v̸` to `-(R_K v)̸`;
* on shell, `R_K` maps `p' - K_z ↦ -(p - K_{z̃})` and `p - K_z ↦ -(p' - K_{z̃})` with
  `z̃ = (1 - x, y)`, so `𝓜(Ñ^μ(-K_z)) = -(R_K)^μ_ν Ñ^ν(-K_{z̃})`
  (`mirrorMap_vertexNumeratorMatrix`), and the denominators are symmetric under `x ↦ 1 - x`
  (`QED.OneLoop.VertexLimit.feynmanMass_reflect`);
* the Feynman measure is invariant under `x ↦ 1 - x`
  (`QED.OneLoop.VertexLimit.integral_feynman_reflect`).

This route does not use the limits at the negative-energy point `(-p, -p')`, at which the one-loop
vertex limit is not proved.

## Main statements

* `isMirrorSymmetric_closedForm`: the closed-form integral is mirror symmetric.
* `ctLimit_d1_eq`: the `δ₁` class limits in closed form.
* `isMirrorSymmetric_ctLimit_d1`: **each `δ₁` class limit is mirror symmetric.**
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory

namespace QED.TwoLoop.CountertermMirror

open QED.WickModel QED.TwoLoop.Relabel QED.TwoLoop.Insertion QED.TwoLoop.LimitMirror QED.Dirac
  QED.OneLoop QED.OneLoop.VertexLimit QED.Integration

/-! ### The mirror map -/

/-- The mirror map `X ↦ S_K C Xᵀ C S_K⁻¹`. -/
noncomputable def mirrorMap (K : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  reflSpin K * ccT X * (((Minkowski.dot K K : ℝ) : ℂ)⁻¹ • reflSpin K)

theorem isMirrorSymmetric_iff (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    IsMirrorSymmetric p' p V ↔
      ∀ μ, mirrorMap (p' + p) (V μ) = -vecAct (reflectMatrix (p' + p)) V μ :=
  Iff.rfl

section Map

variable {K : Fin 4 → ℝ}

theorem mirrorMap_add (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    mirrorMap K (X + Y) = mirrorMap K X + mirrorMap K Y := by
  simp only [mirrorMap, ccT_add, Matrix.mul_add, Matrix.add_mul]

theorem mirrorMap_sub (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    mirrorMap K (X - Y) = mirrorMap K X - mirrorMap K Y := by
  simp only [mirrorMap, ccT_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem mirrorMap_smul (c : ℂ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    mirrorMap K (c • X) = c • mirrorMap K X := by
  simp only [mirrorMap, ccT_smul, Matrix.mul_smul, Matrix.smul_mul]
  rw [smul_comm]

theorem reflect_neg' (v : Fin 4 → ℝ) : reflect K (-v) = -reflect K v := by
  rw [← reflectMatrix_mulVec, ← reflectMatrix_mulVec, Matrix.mulVec_neg]

variable (hK : Minkowski.dot K K ≠ 0)
include hK

theorem mirrorMap_mul (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    mirrorMap K (X * Y) = mirrorMap K Y * mirrorMap K X := by
  simp only [mirrorMap, ccT_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ (reflSpin K) (ccT X * _), inv_mul_reflSpin hK, Matrix.one_mul]

theorem mirrorMap_one : mirrorMap K (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
  rw [mirrorMap, ccT_one, Matrix.mul_one, reflSpin_mul_inv hK]

theorem mirrorMap_gamma (μ : Fin 4) :
    mirrorMap K (gamma μ) = -vecAct (reflectMatrix K) gamma μ := by
  rw [mirrorMap, ccT_gamma, Matrix.mul_neg, Matrix.neg_mul, isCovariantUnder_reflect_gamma hK μ]

theorem mirrorMap_slash (v : Fin 4 → ℝ) : mirrorMap K (slash v) = -slash (reflect K v) := by
  rw [mirrorMap, ccT_slash, Matrix.mul_neg, Matrix.neg_mul, reflSpin_mul_slash_mul_inv hK]

end Map

/-! ### Linear combinations under `vecAct` -/

theorem vecAct_sub' (L : Matrix (Fin 4) (Fin 4) ℝ) (A B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ : Fin 4) : vecAct L (fun ν => A ν - B ν) μ = vecAct L A μ - vecAct L B μ := by
  simp only [vecAct, smul_sub, Finset.sum_sub_distrib]

/-- `vecAct` of the shape of the contracted numerator. -/
theorem vecAct_numeratorShape (L : Matrix (Fin 4) (Fin 4) ℝ) (α β : ℂ) (f : Fin 4 → ℝ)
    (X Y : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    vecAct L (fun ν => α • gamma ν - ((f ν : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
        β • (X * gamma ν * Y)) μ =
      α • vecAct L gamma μ - (((L *ᵥ f) μ : ℝ) : ℂ) • 1 + β • (X * vecAct L gamma μ * Y) := by
  rw [vecAct_add L (fun ν => α • gamma ν - ((f ν : ℝ) : ℂ) • 1) (fun ν => β • (X * gamma ν * Y)),
    vecAct_sub' L (fun ν => α • gamma ν) (fun ν => ((f ν : ℝ) : ℂ) • 1),
    vecAct_smul, vecAct_smul, vecAct_apply_smul_one, vecAct_mulVec_apply, mul_vecAct_mul]

/-! ### The numerator -/

/-- **The mirror map on the one-loop numerator**: if `R_K (p' + ℓ) = -(p + ℓ')` and
`R_K (p + ℓ) = -(p' + ℓ')`, then `𝓜(Ñ^μ(ℓ)) = -(R_K)^μ_ν Ñ^ν(ℓ')`. -/
theorem mirrorMap_vertexNumeratorMatrix {K : Fin 4 → ℝ} (hK : Minkowski.dot K K ≠ 0) (m : ℝ)
    {p' p ℓ ℓ' : Fin 4 → ℝ} (h1 : reflect K (p' + ℓ) = -(p + ℓ'))
    (h2 : reflect K (p + ℓ) = -(p' + ℓ')) (μ : Fin 4) :
    mirrorMap K (vertexNumeratorMatrix m p' p μ ℓ) =
      -vecAct (reflectMatrix K) (fun ν => vertexNumeratorMatrix m p' p ν ℓ') μ := by
  have h1' : reflect K (p' + ℓ') = -(p + ℓ) := by
    rw [← neg_neg (p' + ℓ'), ← h2, reflect_neg', reflect_reflect hK]
  have h2' : reflect K (p + ℓ') = -(p' + ℓ) := by
    rw [← neg_neg (p + ℓ'), ← h1, reflect_neg', reflect_reflect hK]
  have hf : (fun ν => 4 * m * ((p' + ℓ') ν + (p + ℓ') ν)) = (4 * m) • ((p' + ℓ') + (p + ℓ')) := by
    funext ν
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hRf : (reflectMatrix K *ᵥ fun ν => 4 * m * ((p' + ℓ') ν + (p + ℓ') ν)) μ =
      -(4 * m * ((p' + ℓ) μ + (p + ℓ) μ)) := by
    rw [hf, Matrix.mulVec_smul, reflectMatrix_mulVec, reflect_add, h1', h2']
    simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
    ring
  simp only [vertexNumeratorMatrix_eq]
  rw [vecAct_numeratorShape, hRf]
  simp only [mirrorMap_add, mirrorMap_sub, mirrorMap_smul, mirrorMap_one hK, mirrorMap_mul hK,
    mirrorMap_slash hK, mirrorMap_gamma hK, h1, h2, slash_neg]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, smul_neg, ofReal_neg, neg_smul,
    Matrix.mul_assoc]
  abel

/-! ### The closed-form integrand -/

section OnShell

variable {m mγ Λ : ℝ} {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
  (hp : Minkowski.dot p p = -m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p))
include hp' hp hq

theorem reflect_add_shift (z : ℝ × ℝ) :
    reflect (p' + p) (p' + -shiftK p' p z) = -(p + -shiftK p' p (1 - z.1, z.2)) ∧
      reflect (p' + p) (p + -shiftK p' p z) = -(p' + -shiftK p' p (1 - z.1, z.2)) := by
  obtain ⟨hRp, hRp', -⟩ := reflect_add_self hp' hp hq
  have hlin : ∀ a b : ℝ, reflect (p' + p) (a • p' + b • p) = -(a • p + b • p') := by
    intro a b
    rw [← reflectMatrix_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      reflectMatrix_mulVec, reflectMatrix_mulVec, hRp, hRp', smul_neg, smul_neg, neg_add,
      add_comm]
  have e1 : p' + -shiftK p' p z = (1 - z.2 * z.1) • p' + (-(z.2 * (1 - z.1))) • p := by
    funext i
    simp only [shiftK, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : p + -shiftK p' p z = (-(z.2 * z.1)) • p' + (1 - z.2 * (1 - z.1)) • p := by
    funext i
    simp only [shiftK, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨?_, ?_⟩
  · rw [e1, hlin]
    funext i
    simp only [shiftK, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [e2, hlin]
    funext i
    simp only [shiftK, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- **The mirror map on the closed-form integrand**: `𝓜(F^μ(z)) = -(R_K)^μ_ν F^ν(1 - x, y)`. -/
theorem mirrorMap_closedFormMatrix (μ : Fin 4) (z : ℝ × ℝ) :
    mirrorMap (p' + p) (closedFormMatrix m mγ Λ p' p μ z) =
      -vecAct (reflectMatrix (p' + p)) (fun ν => closedFormMatrix m mγ Λ p' p ν (1 - z.1, z.2))
        μ := by
  have hK := dot_add_self_ne_zero hp' hp hq
  obtain ⟨h1, h2⟩ := reflect_add_shift hp' hp hq z
  simp only [closedFormMatrix, feynmanMass_reflect hp' hp]
  rw [vecAct_smul, vecAct_add, vecAct_smul, vecAct_smul, mirrorMap_smul, mirrorMap_add,
    mirrorMap_smul, mirrorMap_smul, mirrorMap_gamma hK,
    mirrorMap_vertexNumeratorMatrix hK m h1 h2]
  simp only [smul_neg, smul_add, neg_add]

end OnShell

/-! ### Entrywise integrals -/

section Integral

variable {η : Measure (ℝ × ℝ)}

theorem mul_of_integral_mul (A B : Matrix (Fin 4) (Fin 4) ℂ) (f : ℝ × ℝ → Matrix (Fin 4) (Fin 4) ℂ)
    (hf : ∀ i j, Integrable (fun z => f z i j) η) :
    A * Matrix.of (fun i j => ∫ z, f z i j ∂η) * B =
      Matrix.of fun i j => ∫ z, (A * f z * B) i j ∂η := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const, integral_finsetSum Finset.univ fun k _ => (hf k l).const_mul (A i k)]
    simp only [integral_const_mul]
  · intro l _
    exact (integrable_finsetSum _ fun k _ => (hf k l).const_mul _).mul_const _

theorem vecAct_of_integral (L : Matrix (Fin 4) (Fin 4) ℝ)
    (F : Fin 4 → ℝ × ℝ → Matrix (Fin 4) (Fin 4) ℂ) (hF : ∀ μ i j, Integrable (fun z => F μ z i j) η)
    (μ : Fin 4) :
    vecAct L (fun ν => Matrix.of fun i j => ∫ z, F ν z i j ∂η) μ =
      Matrix.of fun i j => ∫ z, vecAct L (fun ν => F ν z) μ i j ∂η := by
  ext i j
  simp only [vecAct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro ν _
    exact (hF ν i j).const_mul _

/-- **The mirror identity passes to entrywise integrals**: if `𝓜(F^μ(z)) = -(R_K)^μ_ν F^ν(σ z)`
pointwise, with `σ` preserving the integral, then `∫ F` is mirror symmetric. -/
theorem isMirrorSymmetric_integral {p' p : Fin 4 → ℝ}
    (F : Fin 4 → ℝ × ℝ → Matrix (Fin 4) (Fin 4) ℂ) (hF : ∀ μ i j, Integrable (fun z => F μ z i j) η)
    (σ : ℝ × ℝ → ℝ × ℝ) (hσ : ∀ g : ℝ × ℝ → ℂ, ∫ z, g (σ z) ∂η = ∫ z, g z ∂η)
    (hpt : ∀ μ z, mirrorMap (p' + p) (F μ z) =
      -vecAct (reflectMatrix (p' + p)) (fun ν => F ν (σ z)) μ) :
    IsMirrorSymmetric p' p (fun μ => Matrix.of fun i j => ∫ z, F μ z i j ∂η) := by
  intro μ
  change mirrorMap (p' + p) (Matrix.of fun i j => ∫ z, F μ z i j ∂η) = _
  have e1 : mirrorMap (p' + p) (Matrix.of fun i j => ∫ z, F μ z i j ∂η) =
      Matrix.of fun i j => ∫ z, mirrorMap (p' + p) (F μ z) i j ∂η := by
    have eT : (Matrix.of fun i j => ∫ z, F μ z i j ∂η)ᵀ =
        Matrix.of fun i j => ∫ z, (F μ z)ᵀ i j ∂η := by
      ext i j
      rfl
    unfold mirrorMap ccT
    rw [eT, show ∀ X : Matrix (Fin 4) (Fin 4) ℂ, reflSpin (p' + p) * (chargeConj * X * chargeConj) *
        (((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ)⁻¹ • reflSpin (p' + p)) =
        (reflSpin (p' + p) * chargeConj) * X *
          (chargeConj * (((Minkowski.dot (p' + p) (p' + p) : ℝ) : ℂ)⁻¹ • reflSpin (p' + p))) from
        fun X => by simp only [Matrix.mul_assoc]]
    rw [mul_of_integral_mul _ _ (fun z => (F μ z)ᵀ) fun i j => hF μ j i]
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_assoc]
  rw [e1, vecAct_of_integral _ _ hF]
  ext i j
  simp only [hpt μ, Matrix.neg_apply, Matrix.of_apply, integral_neg]
  exact congrArg Neg.neg (hσ fun z => vecAct (reflectMatrix (p' + p)) (fun ν => F ν z) μ i j)

end Integral

/-! ### The one-loop vertex limit and the `δ₁` classes -/

/-- **The closed form of the one-loop vertex limit is mirror symmetric**, for `m, m_γ, Λ > 0` and
on-shell positive-energy `p, p'` with `q² > 0`. -/
theorem isMirrorSymmetric_closedForm {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    IsMirrorSymmetric p' p
      (fun μ => Matrix.of fun i j => ∫ z, closedFormMatrix m mγ Λ p' p μ z i j ∂feynmanMeasure) :=
  isMirrorSymmetric_integral (fun μ z => closedFormMatrix m mγ Λ p' p μ z)
    (integrable_closedFormMatrix hm hmγ hΛ hp' hp hp0' hp0) (fun z => (1 - z.1, z.2))
    (fun g => integral_feynman_reflect g) (mirrorMap_closedFormMatrix hp' hp hq)

/-- The `δ₁` classes. -/
def IsD1 (c : CtClass) : Prop := c = .d1At1 ∨ c = .d1At2 ∨ c = .d1At3

/-- Each `δ₁` class value is `δ₁` times the one-loop vertex, at every `ε`. -/
theorem ctValue_d1 {c : CtClass} (hc : IsD1 c) (P : Params) (p' p : Fin 4 → ℝ) (μ a b : Fin 4)
    (ε : ℝ) :
    ctValue c P p' p μ a b ε = (P.δ₁ : ℂ) * vertexValue { P with ε := ε } p' p μ a b := by
  rcases hc with rfl | rfl | rfl
  · exact contractionValue₂_d1At1 { P with ε := ε } (hmom_pos p' p) (fun _ => a) (fun _ => b)
      (fun _ => μ)
  · exact contractionValue₂_d1At2 { P with ε := ε } (hmom_pos p' p) (fun _ => a) (fun _ => b)
      (fun _ => μ)
  · exact contractionValue₂_d1At3 { P with ε := ε } (hmom_pos p' p) (fun _ => a) (fun _ => b)
      (fun _ => μ)

/-- **The `δ₁` class limits in closed form**: `W_{δ₁}(p', p) = δ₁ i (e³/16π²) ∫ dF F(z)`. -/
theorem ctLimit_d1_eq {c : CtClass} (hc : IsD1 c) (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0) :
    ctLimit c P p' p = fun μ => ((P.δ₁ : ℂ) * (I * ((P.e ^ 3 / (16 * Real.pi ^ 2) : ℝ) : ℂ))) •
      Matrix.of fun i j => ∫ z, closedFormMatrix P.m P.mγ P.Λ p' p μ z i j ∂feynmanMeasure := by
  funext μ
  ext a b
  have ht : Tendsto (ctValue c P p' p μ a b) (𝓝[>] 0)
      (𝓝 ((P.δ₁ : ℂ) * ∫ v, spatialG P.e P.m P.mγ P.Λ 0 p' p μ a b v)) :=
    ((CountertermLimit.tendsto_vertexValue P hm hmγ hΛ (pOut := fun _ => p') (pIn := fun _ => p)
      hp hp' hp0 hp0' (fun _ => a) (fun _ => b) (fun _ => μ)).const_mul (P.δ₁ : ℂ)).congr
      fun ε => (ctValue_d1 hc P p' p μ a b ε).symm
  have hv := vertexLimit_entry_eq (e := P.e) hm hmγ hΛ hp' hp hp0' hp0 μ a b
  have hv' : ∫ v, spatialG P.e P.m P.mγ P.Λ 0 p' p μ a b v =
      I * (((P.e ^ 3 / (16 * Real.pi ^ 2) : ℝ) : ℂ) *
        ∫ z, closedFormMatrix P.m P.mγ P.Λ p' p μ z a b ∂feynmanMeasure) := by
    rw [← hv]
    field_simp
  simp only [ctLimit, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [ht.limUnder_eq, hv']
  ring

/-- **Each `δ₁` class limit is mirror symmetric**, with no covariance hypothesis: for
`m, m_γ, Λ > 0`, on-shell positive-energy `p, p'` with `q² > 0` and every value of the
counterterms. -/
theorem isMirrorSymmetric_ctLimit_d1 {c : CtClass} (hc : IsD1 c) (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    IsMirrorSymmetric p' p (ctLimit c P p' p) := by
  rw [ctLimit_d1_eq hc P hm hmγ hΛ hp hp' hp0 hp0']
  exact isMirrorSymmetric_smul _ (isMirrorSymmetric_closedForm hm hmγ hΛ hp' hp hp0' hp0 hq)

end QED.TwoLoop.CountertermMirror

end
