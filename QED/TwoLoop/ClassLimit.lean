/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassIntegrable
public import QED.TwoLoop.ClassLimitParametric
public import QED.TwoLoop.JointIntegralInvariance
public import QED.Integration.SymanzikPositivityClasses

/-!
# The `ε → 0⁺` limit of the open-line classes

Obligation O2-7 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3), its limit part, for the six classes
of five gauge vertices with an open electron line through both loops: `L`, `X`, `C₊`, `C₋`, `S₊`,
`S₋`. For `m, m_γ, Λ > 0`, on-shell `p = pIn 0`, `p' = pOut 0` (`p·p = p'·p' = -m²`, mostly-plus
metric) with `q = p' - p`, `q·q ≥ 0`, and momentum conservation `p' = p + k`, the class value
(T₁₀) at the prescription `ε`, `contractionValue₂ {P with ε := ε} c.rep …`, converges as `ε → 0⁺`
for every choice of spinor and Lorentz indices
(`QED.TwoLoop.ClassLimit.tendsto_contractionValue₂_open`). The limit is the parametric integral
at `ε = 0`:

`-π⁴ ∫_Δ U⁻² (3! V⁻⁴ Q(-S) + V⁻³ H(-S)·G + ¼ V⁻² R·Π(G))`

over the simplex of the eight lines of the Pauli–Villars form `class5LoopMatrixPV c`, with the
class momenta `pvMomentaE c p p'` and masses `pvMasses P`, where `Q` is the class numerator
`(2π)⁻⁸ classNumeratorE c P …` written as a `LoopQuartic` (`paramIntegrand Q … 0`). The limit is
unique (`existsUnique_tendsto_contractionValue₂_open`) and its integrand is integrable.

## Proof

* For `ε ≠ 0` the value is the joint integral of `(2π)⁻⁸ N(ℓ) ∏ᵢ Dᵢ(ℓ)⁻¹` in the class routing
  (`contractionValue₂_open_eq_classRouting`, from the bridge and the invariance of the joint
  integral under integer unimodular affine changes). The numerator `N = classNumeratorE c P …` does
  not depend on `ε` (the Pauli–Villars photon factor of the bridge is `Λ² - m_γ²`); the masses
  `pvMasses P` neither; `ε` enters only through the line denominators `Dᵢ`.
* The positivity bounds of `QED/Integration/SymanzikPositivityClasses.lean` are stated for the
  same data: `pvMomentaE c p p' i = extMomenta c p p' (pvLines i)` is `classLXMomenta`,
  `classCpSpMomenta` or `classCmSmMomenta` at `pvLines i` (by definition), and
  `pvMasses P = classPVMasses m m_γ m_γ Λ Λ`. With photon-mass lower bound `μ = min(m_γ, Λ)` they
  give `V ≥ (3/4) min(m²/4, μ²) > 0` wherever `U ≠ 0` (`symanzikV_open_ge`).
* `QED.TwoLoop.ClassLimit.tendsto_jointEnergyFirstIntegral_of_refined` (dominated convergence,
  `QED/TwoLoop/ClassLimitParametric.lean`) with the refined criterion and the pointwise bound of
  `QED/TwoLoop/ClassIntegrable.lean`.

Positive energies of `p, p'` are not needed. The class `VP` is not covered here.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.TwoLoop.ClassLimit

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.Integration.TwoLoop (lineDenom castLoopMatrix class5LoopMatrixPV pvLines RefinedBound
  LoopQuartic NoSubdivergenceRefined symanzikU symanzikV classPVMasses classLXMomenta
  classCpSpMomenta classCmSmMomenta)
open QED.Integration.Feynman (simplexSet)

/-- The normalization `(2π)⁻⁸` of the two-loop value. -/
noncomputable abbrev twoLoopNorm : ℂ := (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹

/-- Transport of the value (T₉) along an integer unimodular affine change of loop momenta. -/
theorem jointEnergyFirstIntegral_eq_of_comp {G H : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : IsUnit M.det) (a : Fin 2 → Fin 4 → ℝ)
    (hH : ∀ ℓ, H ℓ = G ((fun s => ∑ r, M s r • ℓ r) + a)) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 H = QED.TwoLoop.jointEnergyFirstIntegral 2 G := by
  rw [show H = fun ℓ => G ((fun s => ∑ r, M s r • ℓ r) + a) from funext hH]
  exact JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2 G M hM a

/-- **The value of an open-line class in the class routing**: for `ε ≠ 0` and momentum
conservation, the joint energy-first integral of `(2π)⁻⁸ N(ℓ) ∏ᵢ₌₀⁷ Dᵢ(ℓ)⁻¹` with the class
numerator and the line denominators of the Pauli–Villars form. -/
theorem contractionValue₂_open_eq_classRouting {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hε : P.ε ≠ 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => twoLoopNorm *
        (classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ *
          ∏ i : Fin 8, (pvDenomE c P (pIn 0) (pOut 0) i ℓ)⁻¹)) := by
  rw [Relabel.contractionValue₂_eq_of_loopCount P (loopCount_rep c)]
  simp only [openClasses, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact jointEnergyFirstIntegral_eq_of_comp matL isUnit_det_matL ![-(pIn 0), -(pIn 0)]
      fun ℓ => by rw [regulatedAmplitude₂_lineMomentum₂_L P hε hmom]; rfl
  · exact jointEnergyFirstIntegral_eq_of_comp matX isUnit_det_matX ![-(pIn 0), 0]
      fun ℓ => by rw [regulatedAmplitude₂_lineMomentum₂_X P hε hmom]; rfl
  · exact jointEnergyFirstIntegral_eq_of_comp matCp isUnit_det_matCp ![-(pOut 0), pOut 0 - pIn 0]
      fun ℓ => by rw [regulatedAmplitude₂_lineMomentum₂_Cp P hε hmom]; rfl
  · exact jointEnergyFirstIntegral_eq_of_comp matCm isUnit_det_matCm ![-(pIn 0), 0]
      fun ℓ => by rw [regulatedAmplitude₂_lineMomentum₂_Cm P hε hmom]; rfl
  · exact jointEnergyFirstIntegral_eq_of_comp matSp isUnit_det_matSp ![-(pOut 0), pOut 0 - pIn 0]
      fun ℓ => by rw [regulatedAmplitude₂_lineMomentum₂_Sp P hε hmom]; rfl
  · exact jointEnergyFirstIntegral_eq_of_comp matSm isUnit_det_matSm ![-(pIn 0), 0]
      fun ℓ => by rw [regulatedAmplitude₂_lineMomentum₂_Sm P hε hmom]; rfl

/-- **Positivity of `V` for the Pauli–Villars forms of the open-line classes, in the class data
of the bridge**: with `μ = min(m_γ, Λ)`, `V ≥ (3/4) min(m²/4, μ²)` at every point of the simplex
with `U ≠ 0`, for on-shell `p, p'` with `q² ≥ 0`. -/
theorem symanzikV_open_ge {c : Class5} (hc : c ∈ openClasses) (P : Params) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix (class5LoopMatrixPV c)) z ≠ 0) :
    3 / 4 * min (P.m ^ 2 / 4) (min P.mγ P.Λ ^ 2) ≤
      symanzikV (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p') (pvMasses P) z := by
  set μ := min P.mγ P.Λ with hμ
  have hμ0 : 0 < μ := lt_min hmγ hΛ
  have h₁ : μ ^ 2 ≤ P.mγ ^ 2 := pow_le_pow_left₀ hμ0.le (min_le_left _ _) 2
  have h₂ : μ ^ 2 ≤ P.Λ ^ 2 := pow_le_pow_left₀ hμ0.le (min_le_right _ _) 2
  have hle : 3 / 4 * min (P.m ^ 2 / 4) (μ ^ 2) ≤ 3 / 4 * min (P.m ^ 2) (μ ^ 2) := by
    have : P.m ^ 2 / 4 ≤ P.m ^ 2 := by nlinarith [sq_nonneg P.m]
    exact mul_le_mul_of_nonneg_left (min_le_min this le_rfl) (by norm_num)
  simp only [openClasses, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hle.trans (QED.Integration.TwoLoop.symanzikV_classLPV_ge (mγ := μ) hp hp' hq h₁ h₁ h₂ h₂
      hz hz1 hU)
  · exact QED.Integration.TwoLoop.symanzikV_classXPV_ge (mγ := μ) hp hp' hq h₁ h₁ h₂ h₂ hz hz1 hU
  · exact QED.Integration.TwoLoop.symanzikV_classCpPV_ge (mγ := μ) hp hp' hq h₁ h₁ h₂ h₂ hz hz1 hU
  · exact QED.Integration.TwoLoop.symanzikV_classCmPV_ge (mγ := μ) hp hp' hq h₁ h₁ h₂ h₂ hz hz1 hU
  · exact hle.trans (QED.Integration.TwoLoop.symanzikV_classSpPV_ge (mγ := μ) hp hp' hq h₁ h₁ h₂
      h₂ hz hz1 hU)
  · exact hle.trans (QED.Integration.TwoLoop.symanzikV_classSmPV_ge (mγ := μ) hp hp' hq h₁ h₁ h₂
      h₂ hz hz1 hU)

/-- **O2-7's limit for the open-line classes, with the limit identified.** For
`c ∈ {L, X, C₊, C₋, S₊, S₋}`, `m, m_γ, Λ > 0`, on-shell `p = pIn 0`, `p' = pOut 0` with
`(p' - p)² ≥ 0`, and momentum conservation: there is a `LoopQuartic` `Q` with the values of the
normalized class numerator `(2π)⁻⁸ classNumeratorE c P …` (independent of `ε`) such that, for
every choice of indices, the class value (T₁₀) at prescription `ε` converges as `ε → 0⁺` to the
parametric integral at `ε = 0`,
`-π⁴ ∫_Δ U⁻² (3! V⁻⁴ Q(-S) + V⁻³ H(-S)·G + ¼ V⁻² R·Π(G))` (`paramIntegrand Q … 0`), over the
simplex of the eight Pauli–Villars lines with the class momenta and masses; this integrand is
integrable. -/
theorem tendsto_contractionValue₂_open {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (hp : Minkowski.dot (pIn 0) (pIn 0) = -P.m ^ 2)
    (hp' : Minkowski.dot (pOut 0) (pOut 0) = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (pOut 0 - pIn 0) (pOut 0 - pIn 0)) (αOut βIn μ : Fin 1 → Fin 4) :
    ∃ Q : LoopQuartic,
      Q.eval = (fun ℓ => twoLoopNorm * classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ) ∧
      IntegrableOn (paramIntegrand Q (castLoopMatrix (class5LoopMatrixPV c))
        (pvMomentaE c (pIn 0) (pOut 0)) (pvMasses P) 0) (simplexSet 7) ∧
      Tendsto (fun ε => contractionValue₂ { P with ε := ε } c.rep pOut pIn kIn αOut βIn μ)
        (𝓝[>] 0)
        (𝓝 (-((π : ℂ) ^ 4) * ∫ x in simplexSet 7, paramIntegrand Q
          (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c (pIn 0) (pOut 0)) (pvMasses P) 0
          x)) := by
  obtain ⟨Q, hQ⟩ := ((isLoopPoly_classNumeratorE hc P pOut pIn kIn αOut βIn μ).const_mul
    twoLoopNorm).exists_loopQuartic
  have hB : RefinedBound (castLoopMatrix (class5LoopMatrixPV c)) {0, 1, 2, 3} 4 Q.eval := by
    rw [hQ]
    exact (refinedBound_classNumeratorE hc P pOut pIn kIn αOut βIn μ).const_mul _
  have hcrit : NoSubdivergenceRefined 2 {0, 1, 2, 3} (castLoopMatrix (class5LoopMatrixPV c)) :=
    (QED.Integration.TwoLoop.noSubdivergenceRefined_two_loopMatrixPV_iff c).mpr hc
  have hc0 : 0 < 3 / 4 * min (P.m ^ 2 / 4) (min P.mγ P.Λ ^ 2) :=
    mul_pos (by norm_num) (lt_min (by positivity) (pow_pos (lt_min hmγ hΛ) 2))
  have hV : ∀ z : Fin 8 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU (castLoopMatrix (class5LoopMatrixPV c)) z ≠ 0 →
      3 / 4 * min (P.m ^ 2 / 4) (min P.mγ P.Λ ^ 2) ≤
        symanzikV (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c (pIn 0) (pOut 0))
          (pvMasses P) z :=
    fun z hz hz1 hU => symanzikV_open_ge hc P hmγ hΛ hp hp' hq hz hz1 hU
  refine ⟨Q, hQ, integrableOn_paramIntegrand_zero Q _ _ _ (by norm_num) hcrit hB hc0 hV, ?_⟩
  have h := tendsto_jointEnergyFirstIntegral_of_refined Q (castLoopMatrix (class5LoopMatrixPV c))
    (pvMomentaE c (pIn 0) (pOut 0)) (pvMasses P) (by norm_num) hcrit hB hc0 hV
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [contractionValue₂_open_eq_classRouting hc { P with ε := ε } hε.ne' hmom]
  congr 1
  funext ℓ
  simp only [hQ]
  exact mul_assoc _ _ _

/-- **The limit exists and is unique**, under the hypotheses of `tendsto_contractionValue₂_open`. -/
theorem existsUnique_tendsto_contractionValue₂_open {c : Class5} (hc : c ∈ openClasses)
    (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (hp : Minkowski.dot (pIn 0) (pIn 0) = -P.m ^ 2)
    (hp' : Minkowski.dot (pOut 0) (pOut 0) = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (pOut 0 - pIn 0) (pOut 0 - pIn 0)) (αOut βIn μ : Fin 1 → Fin 4) :
    ∃! L : ℂ, Tendsto (fun ε => contractionValue₂ { P with ε := ε } c.rep pOut pIn kIn αOut βIn μ)
      (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨Q, -, -, h⟩ := tendsto_contractionValue₂_open hc P hm hmγ hΛ hmom hp hp' hq αOut βIn μ
  exact ⟨_, h, fun L hL => tendsto_nhds_unique hL h⟩

end QED.TwoLoop.ClassLimit

end
