/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1DParamCont
public import QED.GradedProof.X1DVPert
public import QED.GradedProof.X1DOffLim
public import QED.TwoLoop.ClassLimit
public import QED.TwoLoop.PauliZeroLimitOpen

/-!
# (X₁) piece D: the open-line classes off the mass shell

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece D. For the six open-line classes `L, X, C±, S±` of the order-`e⁵` vertex,
at external momenta `y = (r', r)` near an on-shell pair `(p', p)` with `(p' - p)² ≥ 0`, the class
value (T₁₀) converges as `ε → 0⁺`, and the limit is continuous at `(p', p)`
(`offLim_contractionValue₂_open`).

The value at `ε > 0` is the joint integral of the class numerator over the eight denominators of
the Pauli–Villars form (`QED.TwoLoop.ClassLimit.contractionValue₂_open_eq_classRouting`, any
momenta). The numerator is polynomial in `y` at fixed loop momenta, the line momenta are `r'`,
`r` or `0`, and `V ≥ c/2` near the shell (`QED.GradedProof.X1D.eventually_symanzikV_ge` from the
on-shell `QED.TwoLoop.ClassLimit.symanzikV_open_ge`), so
`QED.GradedProof.X1D.exists_tendsto_cont` applies.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Integration.TwoLoop
open QED.TwoLoop.Enumeration (Class5)
open QED.TwoLoop.Bridge (IsLoopPoly IsLoopAffine extMomenta classMomE classNumeratorE pvMomentaE
  pvDenomE pvMasses amplitudeNumerator isLoopPoly_amplitudeNumerator lineIdx zeroFlavoring)
open QED.TwoLoop.ClassIntegrable (openClasses)

namespace QED.GradedProof.X1D

/-- The external data `y = (r', r)` as a pair of four-vectors: `y 0 = r'`, `y 1 = r`. -/
abbrev pairY (p' p : Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ := ![p', p]

/-- Each external line momentum of a class is `p`, `p'` or `0`, for all `p`, `p'`. -/
theorem extMomenta_cases₂ (c : Class5) (i : Fin 6) :
    (∀ p p', extMomenta c p p' i = p) ∨ (∀ p p', extMomenta c p p' i = p') ∨
      (∀ p p', extMomenta c p p' i = 0) := by
  cases c <;> fin_cases i <;>
    simp [extMomenta, classLXMomenta, classCpSpMomenta, classCmSmMomenta, classVPMomenta]

theorem isLoopPoly_ext (c : Class5) (i : Fin 6) (μ : Fin 4) :
    IsLoopPoly 2 1 fun y : Fin 2 → Fin 4 → ℝ => ((extMomenta c (y 1) (y 0) i μ : ℝ) : ℂ) := by
  rcases extMomenta_cases₂ c i with h | h | h <;> simp only [h]
  · exact IsLoopPoly.coord 1 μ le_rfl
  · exact IsLoopPoly.coord 0 μ le_rfl
  · simpa using IsLoopPoly.const (L := 2) (n := 1) (0 : ℂ)

theorem continuous_ext (c : Class5) (i : Fin 6) :
    Continuous fun y : Fin 2 → Fin 4 → ℝ => extMomenta c (y 1) (y 0) i := by
  rcases extMomenta_cases₂ c i with h | h | h <;> simp only [h]
  · exact continuous_apply 1
  · exact continuous_apply 0
  · exact continuous_const

theorem isLoopAffine_ext (c : Class5) (i : Fin 6) (b : Fin 4 → ℝ) :
    IsLoopAffine fun y : Fin 2 → Fin 4 → ℝ => b + extMomenta c (y 1) (y 0) i := by
  rcases extMomenta_cases₂ c i with h | h | h <;> simp only [h]
  · exact ⟨![0, 1], b, fun y => by simp [Fin.sum_univ_two, add_comm]⟩
  · exact ⟨![1, 0], b, fun y => by simp [Fin.sum_univ_two, add_comm]⟩
  · exact ⟨0, b, fun y => by simp⟩

/-- **The open-class numerators are polynomial in `(r', r)`**, at fixed loop momenta. -/
theorem isLoopPoly_classNumeratorE_ext {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsLoopPoly 2 4 fun y : Fin 2 → Fin 4 → ℝ => classNumeratorE c P (fun _ => y 0) (fun _ => y 1)
      (fun _ => y 0 - y 1) αOut βIn μ ℓ := by
  have e : ∀ y : Fin 2 → Fin 4 → ℝ, classNumeratorE c P (fun _ => y 0) (fun _ => y 1)
      (fun _ => y 0 - y 1) αOut βIn μ ℓ = amplitudeNumerator P c.rep zeroFlavoring (fun _ => 0)
        (fun _ => 0) (classMomE c (y 1) (y 0) ℓ) αOut βIn μ := fun y =>
    QED.TwoLoop.PauliZeroLimit.amplitudeNumerator_gauges P c.rep zeroFlavoring _ _ _ _ _ αOut βIn μ
  simp only [e]
  refine (isLoopPoly_amplitudeNumerator P c.rep zeroFlavoring (fun _ => 0) (fun _ => 0)
    (fun y => classMomE c (y 1) (y 0) ℓ) (fun f => ?_) αOut βIn μ).mono
    (QED.TwoLoop.ClassIntegrable.fermionLine_facts hc).2.2.le
  have := isLoopAffine_ext c (lineIdx (.inl f : QED.WickModel.Line c.rep))
    (fun ν => ∑ s, castLoopMatrix (class5LoopMatrix c) (lineIdx (.inl f)) s * ℓ s ν)
  refine this.imp fun a h => h.imp fun b h => fun y => ?_
  rw [← h y]
  funext ν
  simp [classMomE, lineMomentum]

/-- **The open-line classes off the shell.** For `c ∈ {L, X, C±, S±}`, `m, m_γ, Λ > 0` and an
on-shell pair `(p', p)` with `(p' - p)² ≥ 0`, the class value at the external momenta
`y = (r', r)` converges as `ε → 0⁺` for `y` near `(p', p)`, to a limit continuous at `(p', p)`. -/
theorem offLim_contractionValue₂_open {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (αOut βIn μ : Fin 1 → Fin 4) :
    OffLim (fun ε (y : Fin 2 → Fin 4 → ℝ) => QED.WickModel.contractionValue₂ { P with ε := ε }
      c.rep (fun _ => y 0) (fun _ => y 1) (fun _ => y 0 - y 1) αOut βIn μ) (pairY p' p) := by
  set mom : (Fin 2 → Fin 4 → ℝ) → Fin 8 → Fin 4 → ℝ := fun y => pvMomentaE c (y 1) (y 0)
  have hmom : ∀ i μ, IsLoopPoly 2 1 fun y => ((mom y i μ : ℝ) : ℂ) := fun i μ =>
    isLoopPoly_ext c _ μ
  have hmomc : ContinuousAt mom (pairY p' p) :=
    (continuous_pi fun i => continuous_ext c _).continuousAt
  set c₀ := 3 / 4 * min (P.m ^ 2 / 4) (min P.mγ P.Λ ^ 2)
  have hc₀ : 0 < c₀ := mul_pos (by norm_num) (lt_min (by positivity) (pow_pos (lt_min hmγ hΛ) 2))
  have hV := eventually_symanzikV_ge (α := castLoopMatrix (class5LoopMatrixPV c)) hmomc (pvMasses P)
    hc₀ fun z hz hz1 hU => QED.TwoLoop.ClassLimit.symanzikV_open_ge hc P hmγ hΛ hp hp' hq hz hz1 hU
  set N : (Fin 2 → Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ := fun y ℓ =>
    QED.TwoLoop.ClassLimit.twoLoopNorm * classNumeratorE c P (fun _ => y 0) (fun _ => y 1)
      (fun _ => y 0 - y 1) αOut βIn μ ℓ
  have h := exists_tendsto_cont (castLoopMatrix (class5LoopMatrixPV c)) (pvMasses P)
    (by norm_num : 7 ≤ 7) ((noSubdivergenceRefined_two_loopMatrixPV_iff c).mpr hc) hmom
    (N := N) (fun ℓ => (isLoopPoly_classNumeratorE_ext hc P αOut βIn μ ℓ).const_mul _)
    (fun y => (QED.TwoLoop.ClassIntegrable.isLoopPoly_classNumeratorE hc P _ _ _ αOut βIn
      μ).const_mul _)
    (fun y => (QED.TwoLoop.ClassIntegrable.refinedBound_classNumeratorE hc P _ _ _ αOut βIn
      μ).const_mul _) (half_pos hc₀) hV
  refine OffLim.congr h fun y ε hε => ?_
  rw [QED.TwoLoop.ClassLimit.contractionValue₂_open_eq_classRouting hc { P with ε := ε } hε.ne'
    (pOut := fun _ => y 0) (pIn := fun _ => y 1) (kIn := fun _ => y 0 - y 1) (by simp)]
  congr 1
  funext ℓ
  simp only [N, pvDenomE, mul_assoc]
  rfl

end QED.GradedProof.X1D

end
