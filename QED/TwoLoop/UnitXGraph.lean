/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLGraph
import Mathlib.Tactic.Ring

/-!
# The crossed ladder: its projected parametric numerator by Wick's rule

Section 8 of `docs/TWO-LOOP-UNITS.md`, the graph half of the X unit, first step (the analogue of
`QED/TwoLoop/UnitLGraph.lean` for the ladder). The X value is
`openZero .X P = ∫_{Δ₇} c₂[N(x, ·)] / V(x)⁴` with
`N(x, u) = ∑ⱼ wⱼ(u) (-π⁴) paramNumOf (F_{u,j}) α p(u) M x` (`openNum`). With the Pauli weights
written as a trace (`QED.TwoLoop.UnitLGraph.sum_pauliWt_mul`):

* `sum_pauliWt_openF_X`: the projected crossed numerator is a combination of electron chains,
  `∑ⱼ wⱼ F_{u,j}(ℓ) = κ ∑_μ ∑_l c_{μ,l} tr(B_{μ,l,0} E₃ B_{μ,l,1} E₂ B_{μ,l,2} E₁ B_{μ,l,3} E₀)`,
  `κ = (2π)⁻⁸ (ie)⁵ (1/i)⁴` (`QED.TwoLoop.UnitLGraph.ladderConst`), with `c_{μ,l}` the photon
  weights of the pairing of `X` (photons `0–3` and `1–4`, `crossedWeight`) and
  `B_{μ,l} = (γ^{l₀} P_μ γ^{l₄}, γ^{l₃}, γ^{l₂}, γ^{l₁})` (`crossedB`);
* `openNum_X_eq`: hence
  `N(x, u) = -π⁴ κ ∑_μ ∑_l c_{μ,l} paramNumOf (chain_{μ,l}) α p(u) M x`.

The lines of the Pauli–Villars form of `X`: `0` (the outer electron, momentum `ℓ₀ - ℓ₁ + p`),
`1, 2` (the electron pair `ℓ₀ + p`, `ℓ₀ + p'`), `3` (`ℓ₁ + p'`), `4, 6` (the outer photon
`0–3`) and `5, 7` (the inner photon `1–4`), lines `4, 5` at `m_γ` and `6, 7` at `Λ`.
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitXGraph

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.ParamNumEval
open QED.TwoLoop.UnitLGraph
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic castLoopMatrix class5LoopMatrixPV symanzikV symanzikU
  symanzikMatrix lineMomentum loopShift)

/-! ### The crossed chain -/

/-- The photon weight of the crossed pairing (external photon at vertex `2`, photons `0–3` and
`1–4`): `c_{μ,l} = [l₂ = μ] η'_{l₀ l₃} η'_{l₁ l₄}`. -/
noncomputable def crossedWeight (P : Params) (μ : Fin 4) (l : Fin 5 → Fin 4) : ℂ :=
  kron μ (l (permX 0)) * pvEta P (l (permX 1)) (l (permX 2)) * pvEta P (l (permX 3)) (l (permX 4))

/-- The constant matrices of the crossed chain, after the cyclic move of `γ^{l₀}` and the Pauli
matrix: `(γ^{l₀} P_μ γ^{l₄}, γ^{l₃}, γ^{l₂}, γ^{l₁})`. -/
noncomputable def crossedB (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (l : Fin 5 → Fin 4) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![gamma (l 0) * pauliMat m p' p μ * gamma (l 4), gamma (l 3), gamma (l 2), gamma (l 1)]

/-- The lines of the Pauli–Villars form carrying the four chain slots: `E₃, E₂, E₁, E₀`. -/
def crossedLines : Fin 4 → Fin 8 := ![3, 2, 1, 0]

/-- The loop matrix of the Pauli–Villars form of the crossed ladder. -/
noncomputable abbrev crossedAlpha : Fin 8 → Fin 2 → ℝ := castLoopMatrix (class5LoopMatrixPV .X)

theorem classMomE_X_eq (p p' : Fin 4 → ℝ) (k : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    classMomE .X p p' ℓ (.inl (lineX k)) =
      lineMomentum crossedAlpha (pvMomentaE .X p p') (crossedLines (3 - k)) ℓ := by
  fin_cases k <;> rfl

/-- **The projected crossed numerator as a combination of electron chains.** -/
theorem sum_pauliWt_openF_X (P : Params) (p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ j : Idx, pauliWt P.m p' (restMomentum P.m) j.1 j.2.1 j.2.2 * openF .X P p' j ℓ =
      ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4, crossedWeight P μ l *
        elecChain crossedAlpha (pvMomentaE .X (restMomentum P.m) p')
          (crossedB P.m p' (restMomentum P.m) μ l) (fun _ => P.m) crossedLines ℓ := by
  have hF : ∀ j : Idx, openF .X P p' j ℓ = ladderConst P *
      ∑ l : Fin 5 → Fin 4, crossedWeight P j.1 l *
        openChain (fun t => gamma (l t))
          (fun i => electronNumerator P.m (classMomE .X (restMomentum P.m) p' ℓ (.inl (lineX i))))
          j.2.1 j.2.2 := fun j => by
    simp only [openF, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul, chain_X,
      chainNum, Matrix.sum_apply, ladderConst, crossedWeight]
    ring
  simp only [hF, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e : ∀ i j, pauliWt P.m p' (restMomentum P.m) μ i j * (ladderConst P *
      ∑ l : Fin 5 → Fin 4, crossedWeight P μ l *
        openChain (fun t => gamma (l t))
          (fun i => electronNumerator P.m (classMomE .X (restMomentum P.m) p' ℓ (.inl (lineX i))))
          i j) =
      ladderConst P * ∑ l : Fin 5 → Fin 4, crossedWeight P μ l *
        (pauliWt P.m p' (restMomentum P.m) μ i j *
          openChain (fun t => gamma (l t))
            (fun i => electronNumerator P.m (classMomE .X (restMomentum P.m) p' ℓ (.inl (lineX i))))
            i j) := fun i j => by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [e, ← Finset.mul_sum]
  congr 1
  rw [sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [← Finset.mul_sum, sum_pauliWt_mul, trace_openChain_mul, classMomE_X_eq]
  rfl

/-! ### The projected parametric numerator of the crossed ladder -/

theorem exists_quartic_openF_X (P : Params) (p' : Fin 4 → ℝ) (j : Idx) :
    ∃ Q : LoopQuartic, Q.eval = openF .X P p' j := by
  have hc : Class5.X ∈ QED.TwoLoop.ClassIntegrable.openClasses := by decide
  obtain ⟨Q, hQ⟩ := ((QED.TwoLoop.ClassIntegrable.isLoopPoly_classNumeratorE hc P
    (fun _ => p') (fun _ => restMomentum P.m) (fun _ => p' - restMomentum P.m) (fun _ => j.2.1)
    (fun _ => j.2.2) (fun _ => j.1)).const_mul twoLoopNorm).exists_loopQuartic
  refine ⟨Q, hQ.trans (funext fun ℓ => ?_)⟩
  simp only [openF, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul]

/-- The crossed chain at the Pauli index `μ` and Lorentz indices `l`, along the curve. -/
noncomputable def crossedChain (P : Params) (u : ℝ) (μ : Fin 4) (l : Fin 5 → Fin 4) :
    (Fin 2 → Fin 4 → ℝ) → ℂ :=
  elecChain crossedAlpha (pvMomentaE .X (restMomentum P.m) (curveMomentum P.m u))
    (crossedB P.m (curveMomentum P.m u) (restMomentum P.m) μ l) (fun _ => P.m) crossedLines

/-- **The projected parametric numerator of the crossed ladder as a combination of chain
numerators**: `N(x, u) = -π⁴ κ ∑_μ ∑_l c_{μ,l} paramNumOf (chain_{μ,l})`. -/
theorem openNum_X_eq (P : Params) (x : Fin 7 → ℝ) (u : ℝ) :
    openNum .X P x u = -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4,
      crossedWeight P μ l * paramNumOf (crossedChain P u μ l) crossedAlpha
        (pvMomentaE .X (restMomentum P.m) (curveMomentum P.m u)) (pvMasses P) x := by
  set α := crossedAlpha
  set pm := pvMomentaE .X (restMomentum P.m) (curveMomentum P.m u)
  have hq : ∀ μ l, ∃ Q : LoopQuartic, Q.eval = crossedChain P u μ l := fun μ l =>
    exists_quartic_elecChain _ _ _ _ _
  have hqμ : ∀ μ, ∃ Q : LoopQuartic,
      Q.eval = fun ℓ => ∑ l : Fin 5 → Fin 4, crossedWeight P μ l * crossedChain P u μ l ℓ :=
    fun μ => exists_quartic_sum _ _ (hq μ)
  have h1 : openNum .X P x u = -((π : ℂ) ^ 4) * paramNumOf (fun ℓ => ∑ j : Idx,
      pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
        openF .X P (curveMomentum P.m u) j ℓ) α pm (pvMasses P) x := by
    rw [paramNumOf_sum _ _ _ _ _ _ fun j => exists_quartic_openF_X P _ j, openNum,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (fun ℓ => ∑ j : Idx,
      pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
        openF .X P (curveMomentum P.m u) j ℓ) =
      fun ℓ => ladderConst P * ∑ μ, (1 : ℂ) *
        ∑ l : Fin 5 → Fin 4, crossedWeight P μ l * crossedChain P u μ l ℓ := by
    funext ℓ
    rw [sum_pauliWt_openF_X]
    simp only [one_mul]
    rfl
  rw [h1, h2, paramNumOf_const_mul _ _ _ _ _ (exists_quartic_sum _ _ hqμ),
    paramNumOf_sum _ _ _ _ _ _ hqμ]
  simp only [one_mul]
  rw [mul_assoc]
  congr 2
  exact Finset.sum_congr rfl fun μ _ => paramNumOf_sum _ _ _ _ _ _ (hq μ)

end QED.TwoLoop.UnitXGraph

end
