/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroExplicitPiece
public import QED.TwoLoop.PauliZeroLimitCurve
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Mass scaling: the parametric toolkit

Infrastructure for the mass scaling of the regulated `F₂⁽⁴⁾(0)`: multiplying all masses
`m, m_γ, Λ, M₁, M₂` by `s > 0` multiplies each explicit class value by `s⁵`, so the Pauli
coefficient `(1/(64 m⁵)) (1/i) ∑ Z` is unchanged.

* `massScale s P`: the parameters with all five masses multiplied by `s`.
* Homogeneity of the elementary pieces: `Minkowski.dot`, `slash`, the electron numerator
  `m - p̸`, the curve `p'(u)`, the rest momentum and the Pauli weights `pauliWt` (degree `5`).
* `dilateQ a s Q`: the quartic whose degree-`k` coefficients are multiplied by `a sᵏ`;
  `(dilateQ a s Q).eval ℓ = a Q.eval (s ℓ)`.
* `paramNum_dilateQ`, `paramNumOf_smul`: the parametric numerator `T₁ + T₂ V + T₃ V²` of
  `ℓ ↦ a F(ℓ/t)` at momenta `t p` and masses `t M` is `a` times that of `F` at `(p, M)`
  (with `symanzikV_smul`: `V(t p, t M) = t² V(p, M)`).
* `secondCoeff_const_mul_projNum`: the second-order coefficient of a projected parametric
  numerator along a curve exists, so a constant factor comes out of it.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.MassScaling

open QED.WickModel QED.Dirac QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.ClassLimit
open QED.Integration.TwoLoop (LoopQuartic LoopIndex loopComp loopShift symanzikV symanzikU
  symanzikMatrix symanzikVector energyShift spatialShift coefVec loopMomenta)
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (electronNumerator)

/-! ### Scaling the masses -/

/-- **The parameters with all masses multiplied by `s`**: `m, m_γ, Λ, M₁, M₂ ↦ s m, s m_γ, s Λ,
s M₁, s M₂`; the charge, the counterterms, `ε` and the loop coefficients are unchanged. -/
def massScale (s : ℝ) (P : Params) : Params :=
  { P with m := s * P.m, mγ := s * P.mγ, Λ := s * P.Λ, M₁ := s * P.M₁, M₂ := s * P.M₂ }

@[simp] theorem massScale_m (s : ℝ) (P : Params) : (massScale s P).m = s * P.m := rfl
@[simp] theorem massScale_mγ (s : ℝ) (P : Params) : (massScale s P).mγ = s * P.mγ := rfl
@[simp] theorem massScale_Λ (s : ℝ) (P : Params) : (massScale s P).Λ = s * P.Λ := rfl
@[simp] theorem massScale_M₁ (s : ℝ) (P : Params) : (massScale s P).M₁ = s * P.M₁ := rfl
@[simp] theorem massScale_M₂ (s : ℝ) (P : Params) : (massScale s P).M₂ = s * P.M₂ := rfl
@[simp] theorem massScale_e (s : ℝ) (P : Params) : (massScale s P).e = P.e := rfl
@[simp] theorem massScale_δ₁ (s : ℝ) (P : Params) : (massScale s P).δ₁ = P.δ₁ := rfl
@[simp] theorem massScale_δ₂ (s : ℝ) (P : Params) : (massScale s P).δ₂ = P.δ₂ := rfl
@[simp] theorem massScale_δm (s : ℝ) (P : Params) : (massScale s P).δm = P.δm := rfl
@[simp] theorem massScale_δ₃ (s : ℝ) (P : Params) : (massScale s P).δ₃ = P.δ₃ := rfl
@[simp] theorem massScale_ε (s : ℝ) (P : Params) : (massScale s P).ε = P.ε := rfl
@[simp] theorem massScale_c₁ (s : ℝ) (P : Params) : (massScale s P).c₁ = P.c₁ := rfl
@[simp] theorem massScale_c₂ (s : ℝ) (P : Params) : (massScale s P).c₂ = P.c₂ := rfl

/-! ### Homogeneity of the elementary pieces -/

theorem dot_smul (s : ℝ) (p k : Fin 4 → ℝ) :
    Minkowski.dot (s • p) (s • k) = s ^ 2 * Minkowski.dot p k := by
  simp only [Minkowski.dot_eq, Pi.smul_apply, smul_eq_mul]
  ring

theorem lower_smul (s : ℝ) (p : Fin 4 → ℝ) (μ : Fin 4) :
    Minkowski.lower (s • p) μ = s * Minkowski.lower p μ := by
  simp only [Minkowski.lower, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem slash_smul (s : ℝ) (p : Fin 4 → ℝ) : slash (s • p) = (s : ℂ) • slash p := by
  simp only [slash, lower_smul, Finset.smul_sum, smul_smul, ofReal_mul]

theorem electronNumerator_smul (s M : ℝ) (k : Fin 4 → ℝ) :
    electronNumerator (s * M) (s • k) = (s : ℂ) • electronNumerator M k := by
  simp only [electronNumerator, slash_smul, smul_sub, smul_smul, ofReal_mul]

theorem restMomentum_smul (s m : ℝ) : restMomentum (s * m) = s • restMomentum m := by
  funext μ
  fin_cases μ <;> simp [restMomentum]

theorem curveMomentum_smul (s m u : ℝ) : curveMomentum (s * m) u = s • curveMomentum m u := by
  funext μ
  fin_cases μ <;> simp [curveMomentum] <;> ring

/-- **The Pauli weights are homogeneous of degree `5`.** -/
theorem pauliWt_smul (s m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    pauliWt (s * m) (s • p') (s • p) μ i j = (s : ℂ) ^ 5 * pauliWt m p' p μ i j := by
  have h1 : s • p' - s • p = s • (p' - p) := (smul_sub s p' p).symm
  have h2 : s • p' + s • p = s • (p' + p) := (smul_add s p' p).symm
  simp only [pauliWt, h1, h2, dot_smul, lower_smul, electronNumerator_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, ofReal_mul, ofReal_pow]
  ring

/-! ### Dilated quartics -/

/-- The quartic whose coefficients of degree `k` are multiplied by `a sᵏ`. -/
def dilateQ (a s : ℂ) (Q : LoopQuartic) : LoopQuartic where
  const := a * Q.const
  lin i := a * s * Q.lin i
  quad i j := a * s ^ 2 * Q.quad i j
  cub i j k := a * s ^ 3 * Q.cub i j k
  quart i j k l := a * s ^ 4 * Q.quart i j k l

theorem evalC_dilateQ (a s : ℂ) (Q : LoopQuartic) (X : LoopIndex → ℂ) :
    (dilateQ a s Q).evalC X = a * Q.evalC (fun i => s * X i) := by
  have h1 : ∀ i, a * s * Q.lin i * X i = a * (Q.lin i * (s * X i)) := fun i => by ring
  have h2 : ∀ i j, a * s ^ 2 * Q.quad i j * (X i * X j) =
      a * (Q.quad i j * (s * X i * (s * X j))) := fun i j => by ring
  have h3 : ∀ i j k, a * s ^ 3 * Q.cub i j k * (X i * X j * X k) =
      a * (Q.cub i j k * (s * X i * (s * X j) * (s * X k))) := fun i j k => by ring
  have h4 : ∀ i j k l, a * s ^ 4 * Q.quart i j k l * (X i * X j * X k * X l) =
      a * (Q.quart i j k l * (s * X i * (s * X j) * (s * X k) * (s * X l))) :=
    fun i j k l => by ring
  simp only [LoopQuartic.evalC, dilateQ, h1, h2, h3, h4, mul_add, Finset.mul_sum]

theorem loopComp_smul (t : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    loopComp (t • ℓ) = fun i => (t : ℂ) * loopComp ℓ i := by
  funext i
  simp [loopComp]

theorem eval_dilateQ (a : ℂ) (t : ℝ) (Q : LoopQuartic) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (dilateQ a (t : ℂ) Q).eval ℓ = a * Q.eval (t • ℓ) := by
  simp only [LoopQuartic.eval, evalC_dilateQ, loopComp_smul]

theorem quartSym_dilateQ (a s : ℂ) (Q : LoopQuartic) (i j k l : LoopIndex) :
    (dilateQ a s Q).quartSym i j k l = a * s ^ 4 * Q.quartSym i j k l := by
  simp only [LoopQuartic.quartSym, dilateQ]
  ring

theorem hess_dilateQ (a s : ℂ) (Q : LoopQuartic) (X : LoopIndex → ℂ) (i j : LoopIndex) :
    (dilateQ a s Q).hess X i j = a * s ^ 2 * Q.hess (fun k => s * X k) i j := by
  have h3 : ∀ k, (a * s ^ 3 * Q.cub i j k + a * s ^ 3 * Q.cub i k j + a * s ^ 3 * Q.cub k i j) *
      X k = a * s ^ 2 * ((Q.cub i j k + Q.cub i k j + Q.cub k i j) * (s * X k)) :=
    fun k => by ring
  have h4 : ∀ k l, a * s ^ 4 * Q.quartSym i j k l * (X k * X l) =
      a * s ^ 2 * (Q.quartSym i j k l * (s * X k * (s * X l))) := fun k l => by ring
  simp only [LoopQuartic.hess, quartSym_dilateQ, h4]
  simp only [dilateQ, h3, mul_add, Finset.mul_sum]

theorem contractTwo_dilateQ (a s : ℂ) (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X : LoopIndex → ℂ) :
    (dilateQ a s Q).contractTwo A X = a * s ^ 2 * Q.contractTwo A (fun k => s * X k) := by
  simp only [LoopQuartic.contractTwo, hess_dilateQ, Finset.mul_sum, mul_assoc]

theorem contractFour_dilateQ (a s : ℂ) (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (dilateQ a s Q).contractFour A = a * s ^ 4 * Q.contractFour A := by
  simp only [LoopQuartic.contractFour, dilateQ, Finset.mul_sum, mul_assoc]

/-! ### The shift and the second Symanzik function -/

section Symanzik

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ) (t : ℝ)

theorem coefVec_smul (q : Fin (m + 1) → ℝ) :
    coefVec α z (fun i => t * q i) = t • coefVec α z q := by
  funext s
  simp only [coefVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem energyShift_smul : energyShift α (t • p) z = t • energyShift α p z := by
  simp only [energyShift, Pi.smul_apply, smul_eq_mul, coefVec_smul, Matrix.mulVec_smul]

theorem spatialShift_smul : spatialShift α (t • p) z = t • spatialShift α p z := by
  funext s c
  simp only [spatialShift, Pi.smul_apply, smul_eq_mul, coefVec_smul, Matrix.mulVec_smul]

theorem loopShift_smul : loopShift α (t • p) z = t • loopShift α p z := by
  funext s μ
  simp only [loopShift, energyShift_smul, spatialShift_smul, Pi.smul_apply]
  refine Fin.cases ?_ (fun j => ?_) μ <;> simp [loopMomenta]

theorem symanzikVector_smul : symanzikVector α (t • p) z = t • symanzikVector α p z := by
  funext s μ
  simp only [symanzikVector, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **`V(t p, t M) = t² V(p, M)`.** -/
theorem symanzikV_smul : symanzikV α (t • p) (t • M) z = t ^ 2 * symanzikV α p M z := by
  simp only [symanzikV, symanzikVector_smul, dot_smul, Pi.smul_apply, smul_eq_mul, mul_sub,
    Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun _ _ => by ring
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Symanzik

/-! ### The parametric numerator -/

theorem loopComp_neg_smul (t : ℝ) (S : Fin 2 → Fin 4 → ℝ) :
    loopComp (-(t • S)) = fun i => (t : ℂ) * loopComp (-S) i := by
  funext i
  simp [loopComp]

/-- **The parametric numerator of a dilated quartic**: for `t ≠ 0`, the parametric numerator of
`ℓ ↦ a Q(ℓ/t)` at momenta `t p` and masses `t M` is `a` times that of `Q` at `(p, M)`. -/
theorem paramNum_dilateQ (Q : LoopQuartic) (a : ℂ) {t : ℝ} (ht : t ≠ 0) {m : ℕ}
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (x : Fin m → ℝ) :
    paramNum (dilateQ a ((t⁻¹ : ℝ) : ℂ) Q) α (t • p) (t • M) x = a * paramNum Q α p M x := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
  have key : (fun i => ((t⁻¹ : ℝ) : ℂ) * loopComp (-loopShift α (t • p) (simplexPoint x)) i) =
      loopComp (-loopShift α p (simplexPoint x)) := by
    funext i
    rw [loopShift_smul, loopComp_neg_smul]
    push_cast
    field_simp
  have key' : t⁻¹ • -loopShift α (t • p) (simplexPoint x) = -loopShift α p (simplexPoint x) := by
    rw [loopShift_smul, smul_neg, smul_smul, inv_mul_cancel₀ ht, one_smul]
  simp only [paramNum, coeffOne, coeffTwo, coeffThree, eval_dilateQ, contractTwo_dilateQ,
    contractFour_dilateQ, key, key', symanzikV_smul]
  push_cast
  field_simp

/-- **The parametric numerator of a dilated numerator function**: for `t ≠ 0` and `F`
represented by a quartic, `paramNumOf (ℓ ↦ a F(t⁻¹ ℓ))` at momenta `t p` and masses `t M` is `a`
times `paramNumOf F` at `(p, M)`. -/
theorem paramNumOf_smul {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hF : ∃ Q : LoopQuartic, Q.eval = F)
    (a : ℂ) {t : ℝ} (ht : t ≠ 0) {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (x : Fin m → ℝ) :
    paramNumOf (fun ℓ => a * F (t⁻¹ • ℓ)) α (t • p) (t • M) x = a * paramNumOf F α p M x := by
  obtain ⟨Q, hQ⟩ := hF
  have hQ' : (dilateQ a ((t⁻¹ : ℝ) : ℂ) Q).eval = fun ℓ => a * F (t⁻¹ • ℓ) := by
    funext ℓ
    rw [eval_dilateQ, hQ]
  rw [paramNumOf_eq hQ', paramNumOf_eq hQ, paramNum_dilateQ Q a ht]

/-! ### Constants out of the second-order coefficient -/

theorem secondCoeff_const_mul_of_tendsto {g : ℝ → ℂ} {L : ℂ}
    (hg : Tendsto (fun u => (g u + g (-u) - 2 * g 0) / (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0) (𝓝 L))
    (c : ℂ) : secondCoeff (fun u => c * g u) = c * secondCoeff g := by
  have h1 : secondCoeff g = L := hg.limUnder_eq
  have h2 : Tendsto (fun u => (c * g u + c * g (-u) - 2 * (c * g 0)) / (2 * (u : ℂ) ^ 2))
      (𝓝[≠] 0) (𝓝 (c * L)) :=
    (hg.const_mul c).congr fun u => by ring
  rw [h1]
  exact h2.limUnder_eq

/-- **The second-order quotient of a projected parametric numerator converges** at every `x`,
under the polynomial hypotheses of `QED.TwoLoop.PauliZeroExplicit.tendsto_piece_explicit`. -/
theorem exists_tendsto_secondQuot_projNum (C : CurveData) {J : Type*} [Fintype J] {D n r Dω : ℕ}
    (F : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hFpoly : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * F u j ℓ)
    (hFq : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, ∃ Q : LoopQuartic, Q.eval = F u j)
    (ω : ℝ → J → ℂ) (hω : ∀ j, IsUPoly (ι := Fin C.m → ℝ) Dω fun _ u => wt u ^ r * ω u j)
    (hω0 : ∀ Y : J → ℂ, ∑ j, ω 0 j * Y j = 0) (x : Fin C.m → ℝ) :
    ∃ L, Tendsto (fun u => (projNum C F ω x u + projNum C F ω x (-u) - 2 * projNum C F ω x 0) /
      (2 * (u : ℂ) ^ 2)) (𝓝[≠] 0) (𝓝 L) := by
  classical
  have hnode : ∀ k : Fin (D + 1), node D k ∈ Ioo (-1 : ℝ) 1 := node_mem D
  choose Qk hQk using fun j k => hFq (node D k) (hnode k) j
  set A : (Fin C.m → ℝ) → ℝ → ℂ := fun x u => ∑ j, (wt u ^ r * ω u j) * (-((π : ℂ) ^ 4) *
    ∑ k, (wt (node D k) ^ n * (lbasis D k).eval (u : ℂ)) *
      (wt u ^ 4 * paramNum (Qk j k) C.α (C.mom u) C.M x)) with hA_def
  have hA : IsUPoly (Dω + (D + 8)) A :=
    IsUPoly.sum _ fun j _ => (hω j).mul (IsUPoly.const_mul _ (IsUPoly.sum _ fun k _ =>
      ((isUPoly_lbasis D k).const_mul _).mul (isUPoly_paramNum (Qk j k) C.α C.M C.mom C.hmom)))
  have hA0 : ∀ x, A x 0 = 0 := fun x => by
    simp only [hA_def, wt_zero, one_pow, one_mul]
    exact hω0 _
  have hAN : ∀ x, ∀ u ∈ Ioo (-1 : ℝ) 1, A x u = wt u ^ (r + n + 4) * projNum C F ω x u := by
    intro x u hu
    have hw : wt u ^ n ≠ 0 := pow_ne_zero n (wt_ne_zero hu)
    simp only [hA_def, projNum]
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [paramNumOf_eq (eval_jointQuartic (hFpoly j) (hQk j) hu), jointQuartic, paramNum_qsum]
    have e1 : ∑ k, wt (node D k) ^ n * (lbasis D k).eval (u : ℂ) *
        (wt u ^ 4 * paramNum (Qk j k) C.α (C.mom u) C.M x) =
        wt u ^ 4 * ∑ k, wt (node D k) ^ n * (lbasis D k).eval (u : ℂ) *
          paramNum (Qk j k) C.α (C.mom u) C.M x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k, lam D n u k * paramNum (Qk j k) C.α (C.mom u) C.M x =
        (wt u ^ n)⁻¹ * ∑ k, wt (node D k) ^ n * (lbasis D k).eval (u : ℂ) *
          paramNum (Qk j k) C.α (C.mom u) C.M x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp only [lam]; ring
    rw [e1, e2]
    field_simp
    ring
  have h0 : (interp (Dω + (D + 8)) A x).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, ← ofReal_zero, ← hA.eq_interp x 0 ⟨by norm_num, by norm_num⟩,
      hA0, ofReal_zero]
  have hg : ∀ u ∈ Ioo (-1 : ℝ) 1, wt u ^ (r + n + 4) * projNum C F ω x u =
      (interp (Dω + (D + 8)) A x).eval (u : ℂ) := fun u hu => by
    rw [← hAN x u hu, hA.eq_interp x u hu]
  exact ⟨_, tendsto_secondCoeff_of_poly hg h0⟩

/-- **A constant comes out of the second-order coefficient of a projected parametric
numerator.** -/
theorem secondCoeff_const_mul_projNum (C : CurveData) {J : Type*} [Fintype J] {D n r Dω : ℕ}
    (F : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hFpoly : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * F u j ℓ)
    (hFq : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, ∃ Q : LoopQuartic, Q.eval = F u j)
    (ω : ℝ → J → ℂ) (hω : ∀ j, IsUPoly (ι := Fin C.m → ℝ) Dω fun _ u => wt u ^ r * ω u j)
    (hω0 : ∀ Y : J → ℂ, ∑ j, ω 0 j * Y j = 0) (x : Fin C.m → ℝ) (c : ℂ) :
    secondCoeff (fun u => c * projNum C F ω x u) = c * secondCoeff (projNum C F ω x) := by
  obtain ⟨L, hL⟩ := exists_tendsto_secondQuot_projNum C F hFpoly hFq ω hω hω0 x
  exact secondCoeff_const_mul_of_tendsto hL c

end QED.TwoLoop.MassScaling

end
