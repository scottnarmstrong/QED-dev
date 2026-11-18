/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LimitCovarianceQuartic

/-!
# Lorentz maps that move the external momenta: the parametric side

Part of obligations O2-20 and O2-21 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). The
little-group covariance of `QED/TwoLoop/LimitCovariance*.lean` uses Lorentz maps that fix the
external momenta. The mirror identity needs the reflection `R_K` in `K = p + p'`, which moves them
(`R_K p = -p'`, `R_K p' = -p` on shell). This file gives the parametric half of covariance under
an arbitrary real `L` with a spinor lift `(S, T)` (`QED.TwoLoop.LimitCovariance.IsSpinLift`),
proper or not, time-reversing or not; only `L g Lᵀ = g` and `Lᵀ g L = g` are used.

* `isSpinLift_reflect`: `(S_K, S_K/(K·K))` with `S_K = K̸Γ` is a spinor lift of `R_K`.
* `paramIntegrand_map`: **the parametric integrand at the external data `L pᵢ`** with numerator
  `Q` equals the integrand at the data `pᵢ` with numerator `ℓ ↦ Q(L ℓ)` (`lmap (blockL L) Q`):
  the Symanzik remainder `V` depends on the external momenta only through Minkowski products, the
  loop shift moves to `L S`, and `G = g ⊗ A⁻¹` is invariant.
* `conj_eq_vecAct_of_paramValue`: if `W^μ_{ij}` are the parametric values of numerators
  `N^μ_{ij}` at data `pᵢ`, `W₂^μ_{ij}` those of `N₂^μ_{ij}` at data `L pᵢ`, and
  `S N₂^μ(L ℓ) T = L^μ_ν N^ν(ℓ)`, then `S W₂^μ T = L^μ_ν W^ν`.
-/

@[expose] public section

open Complex Matrix MeasureTheory
open scoped Real

namespace QED.TwoLoop.ReflCovariance

open QED.Dirac QED.TwoLoop.LimitCovariance QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-- **The spinor lift of a reflection**: `(S_K, S_K/(K·K))`, `S_K = K̸Γ`, lifts `R_K`. -/
theorem isSpinLift_reflect {K : Fin 4 → ℝ} (hK : Minkowski.dot K K ≠ 0) :
    IsSpinLift (reflectMatrix K) (reflSpin K) (((Minkowski.dot K K : ℝ) : ℂ)⁻¹ • reflSpin K) :=
  ⟨reflSpin_mul_inv hK, isCovariantUnder_reflect_gamma hK⟩

/-! ### The parametric data under `L` -/

section Data

variable {m : ℕ}

theorem lineMomentum_map (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → Fin 4 → ℝ)
    (i : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum α (fun j => L *ᵥ q j) i (loopAct L ℓ) = L *ᵥ lineMomentum α q i ℓ := by
  funext μ
  simp only [lineMomentum, loopAct, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem lineDenom_map (h : IsSpinLift L S T) (α : Fin (m + 1) → Fin 2 → ℝ)
    (q : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (ε : ℝ) (i : Fin (m + 1))
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom α (fun j => L *ᵥ q j) M ε i (loopAct L ℓ) = lineDenom α q M ε i ℓ := by
  simp only [lineDenom, lineMomentum_map, h.dot_mulVec]

theorem symanzikVector_map (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) (s : Fin 2) :
    symanzikVector α (fun i => L *ᵥ p i) z s = L *ᵥ symanzikVector α p z s := by
  funext μ
  simp only [symanzikVector, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem symanzikV_map (h : IsSpinLift L S T) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ) :
    symanzikV α (fun i => L *ᵥ p i) M z = symanzikV α p M z := by
  simp only [symanzikV, symanzikVector_map, h.dot_mulVec]

theorem loopShift_map (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) :
    loopShift α (fun i => L *ᵥ p i) z = loopAct L (loopShift α p z) := by
  funext s μ
  simp only [loopAct, loopShift_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  calc _ = ∑ t, ∑ ν, ∑ i, (symanzikMatrix α z)⁻¹ s t * (z i * α i t * (L μ ν * p i ν)) :=
        Finset.sum_congr rfl fun t _ => Finset.sum_comm
    _ = ∑ ν, ∑ t, ∑ i, (symanzikMatrix α z)⁻¹ s t * (z i * α i t * (L μ ν * p i ν)) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring

/-- **The parametric integrand under a Lorentz map of the external data.** -/
theorem paramIntegrand_map (h : IsSpinLift L S T) (Q : LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (ε : ℝ)
    (x : Fin m → ℝ) :
    ClassLimit.paramIntegrand Q α (fun i => L *ᵥ p i) M ε x =
      ClassLimit.paramIntegrand (lmap (blockL L) Q) α p M ε x := by
  have hX : actC (blockL L) (loopComp (-loopShift α p (simplexPoint x))) =
      loopComp (-loopShift α (fun i => L *ᵥ p i) (simplexPoint x)) := by
    rw [actC_blockL_loopComp, loopAct_neg, loopShift_map]
  have h1 : (lmap (blockL L) Q).eval (-loopShift α p (simplexPoint x)) =
      Q.eval (-loopShift α (fun i => L *ᵥ p i) (simplexPoint x)) := by
    rw [LoopQuartic.eval, evalC_lmap, hX]
    rfl
  have h2 : (lmap (blockL L) Q).contractTwo (symanzikMatrix α (simplexPoint x))
      (loopComp (-loopShift α p (simplexPoint x))) =
      Q.contractTwo (symanzikMatrix α (simplexPoint x))
        (loopComp (-loopShift α (fun i => L *ᵥ p i) (simplexPoint x))) := by
    rw [contractTwo_lmap _ _ (symanzikMatrix_transpose _ _), hX,
      blockL_conj_loopMetricInv h.lorentz_left]
    rfl
  have h3 : (lmap (blockL L) Q).contractFour (symanzikMatrix α (simplexPoint x)) =
      Q.contractFour (symanzikMatrix α (simplexPoint x)) := by
    rw [contractFour_lmap, blockL_conj_loopMetricInv h.lorentz_left]
    rfl
  simp only [ClassLimit.paramIntegrand, h1, h2, h3, symanzikV_map h]

end Data

/-! ### Parametric values under `L` -/

theorem IsParamValue.exists_integrableOn {D : ParamData} {F : (Fin 2 → Fin 4 → ℝ) → ℂ} {v : ℂ}
    (h : IsParamValue D F v) :
    ∃ Q : LoopQuartic, Q.eval = F ∧
      IntegrableOn (ClassLimit.paramIntegrand Q D.α D.p D.M 0) (simplexSet D.m) ∧
      v = -((π : ℂ) ^ 4) * ∫ x in simplexSet D.m, ClassLimit.paramIntegrand Q D.α D.p D.M 0 x := by
  obtain ⟨Q, hQ, hB, hv⟩ := h
  exact ⟨Q, hQ, IsParamValue.integrableOn (hQ ▸ hB), hv⟩

/-- **Covariance of parametric values between two external data related by `L`.** The values
`W` at the data `D.p` and `W₂` at the data `p₂ = L D.p` (with the same loop matrix, masses and
simplex), of numerators with `S N₂^μ(L ℓ) T = L^μ_ν N^ν(ℓ)`, satisfy `S W₂^μ T = L^μ_ν W^ν`. -/
theorem conj_eq_vecAct_of_paramValue (D : ParamData) (h : IsSpinLift L S T)
    (p₂ : Fin (D.m + 1) → Fin 4 → ℝ) (hp₂ : p₂ = fun i => L *ᵥ D.p i)
    (N N₂ : Fin 4 → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hN : ∀ μ ℓ, S * N₂ μ (loopAct L ℓ) * T = vecAct L (fun ν => N ν ℓ) μ)
    (W W₂ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hW : ∀ μ i j, IsParamValue D (fun ℓ => N μ ℓ i j) (W μ i j))
    (hW₂ : ∀ μ i j, ∃ Q : LoopQuartic, Q.eval = (fun ℓ => N₂ μ ℓ i j) ∧
      IntegrableOn (ClassLimit.paramIntegrand Q D.α p₂ D.M 0) (simplexSet D.m) ∧
      W₂ μ i j = -((π : ℂ) ^ 4) *
        ∫ x in simplexSet D.m, ClassLimit.paramIntegrand Q D.α p₂ D.M 0 x)
    (μ : Fin 4) : S * W₂ μ * T = vecAct L W μ := by
  subst hp₂
  choose Q hQ hI hv using hW₂
  ext i j
  have hr : IsParamValue D (fun ℓ => ∑ ν, ((L μ ν : ℝ) : ℂ) * N ν ℓ i j)
      (∑ ν, ((L μ ν : ℝ) : ℂ) * W ν i j) :=
    IsParamValue.sum _ _ fun ν _ => hW ν i j
  obtain ⟨-, -, hB, -⟩ := id hr
  have hl : IsParamValue D (fun ℓ => ∑ ν, ((L μ ν : ℝ) : ℂ) * N ν ℓ i j)
      (-((π : ℂ) ^ 4) * ∫ x in simplexSet D.m, ClassLimit.paramIntegrand
        (qsum Finset.univ (fun kl : Fin 4 × Fin 4 => S i kl.2 * T kl.1 j)
          (fun kl => lmap (blockL L) (Q μ kl.2 kl.1))) D.α D.p D.M 0 x) := by
    refine ⟨_, funext fun ℓ => ?_, hB, rfl⟩
    rw [eval_qsum]
    have := congrFun (congrFun (hN μ ℓ) i) j
    simp only [Matrix.mul_apply, vecAct, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul] at this
    rw [← this]
    simp only [eval_lmap_blockL, hQ]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hR : ∀ kl : Fin 4 × Fin 4,
      ClassLimit.paramIntegrand (lmap (blockL L) (Q μ kl.2 kl.1)) D.α D.p D.M 0 =
        ClassLimit.paramIntegrand (Q μ kl.2 kl.1) D.α (fun i => L *ᵥ D.p i) D.M 0 := fun kl =>
    funext fun x => (paramIntegrand_map h _ _ _ _ _ x).symm
  have hval : -((π : ℂ) ^ 4) * ∫ x in simplexSet D.m, ClassLimit.paramIntegrand
        (qsum Finset.univ (fun kl : Fin 4 × Fin 4 => S i kl.2 * T kl.1 j)
          (fun kl => lmap (blockL L) (Q μ kl.2 kl.1))) D.α D.p D.M 0 x =
      ∑ kl : Fin 4 × Fin 4, S i kl.2 * T kl.1 j * W₂ μ kl.2 kl.1 := by
    simp only [paramIntegrand_qsum]
    rw [integral_finsetSum _ fun kl _ => ?_]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun kl _ => ?_
      rw [integral_const_mul, hR, hv]
      ring
    · rw [hR]
      exact (hI μ kl.2 kl.1).const_mul _
  rw [show vecAct L W μ i j = ∑ ν, ((L μ ν : ℝ) : ℂ) * W ν i j by
    simp only [vecAct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]]
  rw [← IsParamValue.unique hl hr, hval]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- The same for values divided by a constant `a`, with numerators depending on `ℓ₀` only (the
counterterm classes). -/
theorem conj_eq_vecAct_of_paramValue_div (D : ParamData) (h : IsSpinLift L S T)
    (p₂ : Fin (D.m + 1) → Fin 4 → ℝ) (hp₂ : p₂ = fun i => L *ᵥ D.p i)
    (N N₂ : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hN : ∀ μ k, S * N₂ μ (L *ᵥ k) * T = vecAct L (fun ν => N ν k) μ)
    (V V₂ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (a : ℂ)
    (hV : ∀ μ i j, ∃ v, IsParamValue D (fun ℓ => N μ (ℓ 0) i j) v ∧ V μ i j = v / a)
    (hV₂ : ∀ μ i j, ∃ Q : LoopQuartic, Q.eval = (fun ℓ => N₂ μ (ℓ 0) i j) ∧
      IntegrableOn (ClassLimit.paramIntegrand Q D.α p₂ D.M 0) (simplexSet D.m) ∧
      V₂ μ i j = (-((π : ℂ) ^ 4) *
        ∫ x in simplexSet D.m, ClassLimit.paramIntegrand Q D.α p₂ D.M 0 x) / a)
    (μ : Fin 4) : S * V₂ μ * T = vecAct L V μ := by
  choose v hv hVv using hV
  choose Q hQ hI hV₂v using hV₂
  have key := conj_eq_vecAct_of_paramValue D h p₂ hp₂ (fun μ ℓ => N μ (ℓ 0))
    (fun μ ℓ => N₂ μ (ℓ 0)) (fun μ ℓ => hN μ (ℓ 0)) (fun μ => Matrix.of (v μ))
    (fun μ => Matrix.of fun i j => -((π : ℂ) ^ 4) *
      ∫ x in simplexSet D.m, ClassLimit.paramIntegrand (Q μ i j) D.α p₂ D.M 0 x)
    (fun μ i j => hv μ i j) (fun μ i j => ⟨Q μ i j, hQ μ i j, hI μ i j, rfl⟩) μ
  have eV : V = fun μ => a⁻¹ • Matrix.of (v μ) := by
    funext μ
    ext i j
    simp only [hVv, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have eV₂ : V₂ μ = a⁻¹ • Matrix.of fun i j => -((π : ℂ) ^ 4) *
      ∫ x in simplexSet D.m, ClassLimit.paramIntegrand (Q μ i j) D.α p₂ D.M 0 x := by
    ext i j
    simp only [hV₂v, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [eV₂, Matrix.mul_smul, Matrix.smul_mul, key, eV, vecAct_smul]

end QED.TwoLoop.ReflCovariance

end
