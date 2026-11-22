/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCCovMirror
public import QED.ChainProof.HCValueOuter
public import QED.Algebra.SandwichReductionMirror
public import QED.Algebra.FormFactorProjector
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Form-factor pairs and the Pauli limit of an abstract covariant family of vertex limits

Helper level for the set (a) Pauli link `QED.ChainProof.SetAPauli.SetAPauliLink`. This is the
argument by which set (b) passes from its limit links to its Pauli link
(`QED.ChainProof.chainFixedLink_of_links`, `QED.ChainProof.chainMirrorLink_of_mirrorAt`,
`QED.ChainProof.HCValue.chainPauliAtLink_of_nested`), written once for an **abstract** family of
vertex limits `Lim p' p V` at mass `m` (`QED.ChainProof.CovFamily`: limits exist, are unique and
are covariant on the on-shell positive-energy pairs with `q² > 0`). Nothing here refers to a
particular vertex.

* `chargeConj_lim_eq_of_eventually`: a fixed-`ε` identity `C X_εᵀ C = Γ Y_ε Γ` (eventually as
  `ε → 0⁺`) passes to the entrywise limits.
* `IsMirrorRel m Lim`: the limits at `(p', p)` and `(p, p')` satisfy `C Vᵀ C = Γ W Γ`.
* `CovFamily.isMirrorSymmetric_of_mirrorRel`: with covariance (applied to `-R_K`, which keeps
  positive energies), every limit is mirror symmetric.
* `CovFamily.formFactor_pauli_of_tendsto`: **form-factor pairs and the Pauli bound.** With
  mirror symmetry, if the Pauli projection at the canonical pair tends to `b` as `Q → 0⁺`, then
  for every `η > 0` there is `q₀ > 0` such that at every pair with `0 < q² < q₀` every limit has a
  form-factor pair and every pair has `‖64π⁶F₂/e⁶ - 64π⁶b/e⁶‖ < η`.
* `CovFamily.tendsto_pauliAtCanonical_of_nested`: if, for small `Q > 0`, every limit at the
  canonical pair has Pauli projection `c · outerAt m Q R` for a photon function `R` that is
  measurable, continuous on `(0, ∞)` and bounded on `[0, ∞)`, the canonical Pauli projection
  tends to `c · outerAt m 0 R` (`QED.ChainProof.HCValue.tendsto_outerAt`).
-/

@[expose] public section

open Complex Matrix Filter Topology Set
open scoped Real

namespace QED.ChainProof

open QED.TwoLoop.LimitCovariance QED.Dirac QED.TwoLoop.PauliZero

/-- **A fixed-`ε` mirror identity passes to the limits**: if `C X_εᵀ C = Γ Y_ε Γ` for `ε` near
`0⁺` and `X_ε → A`, `Y_ε → B` entrywise, then `C Aᵀ C = Γ B Γ`. -/
theorem chargeConj_lim_eq_of_eventually {X Y : ℝ → Matrix (Fin 4) (Fin 4) ℂ}
    {A B : Matrix (Fin 4) (Fin 4) ℂ}
    (hX : ∀ i j, Tendsto (fun ε => X ε i j) (𝓝[>] 0) (𝓝 (A i j)))
    (hY : ∀ i j, Tendsto (fun ε => Y ε i j) (𝓝[>] 0) (𝓝 (B i j)))
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), chargeConj * (X ε)ᵀ * chargeConj = chir * Y ε * chir) :
    chargeConj * Aᵀ * chargeConj = chir * B * chir := by
  have hX' := tendsto_matrix_iff.2 hX
  have hY' := tendsto_matrix_iff.2 hY
  have c1 : Continuous fun M : Matrix (Fin 4) (Fin 4) ℂ => chargeConj * Mᵀ * chargeConj :=
    (continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const
  have c2 : Continuous fun M : Matrix (Fin 4) (Fin 4) ℂ => chir * M * chir :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact tendsto_nhds_unique (((c1.tendsto A).comp hX').congr' h) ((c2.tendsto B).comp hY')

/-- **The mirror relation of a family of limits**: at every admissible pair, the limits `V` at
`(p', p)` and `W` at `(p, p')` satisfy `C V^μᵀ C = Γ W^μ Γ`. -/
def IsMirrorRel (m : ℝ)
    (Lim : (Fin 4 → ℝ) → (Fin 4 → ℝ) → (Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) → Prop) : Prop :=
  ∀ p' p, IsPairQ m p' p → ∀ V W, Lim p' p V → Lim p p' W →
    ∀ μ, chargeConj * (V μ)ᵀ * chargeConj = chir * W μ * chir

namespace CovFamily

variable {m : ℝ} {Lim : (Fin 4 → ℝ) → (Fin 4 → ℝ) → (Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) → Prop}
  (H : CovFamily m Lim)
include H

/-- **Mirror symmetry from covariance and the mirror relation.** -/
theorem isMirrorSymmetric_of_mirrorRel (hR : IsMirrorRel m Lim) {p' p : Fin 4 → ℝ}
    (hpq : IsPairQ m p' p) {V} (hV : Lim p' p V) : QED.OneLoop.IsMirrorSymmetric p' p V := by
  have hpq' := isPairQ_swap hpq
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := id hpq
  obtain ⟨W, hW⟩ := H.exists' p p' hpq'
  have hK := QED.OneLoop.dot_add_self_ne_zero hp' hp hq
  obtain ⟨hRp, hRp', -⟩ := QED.OneLoop.reflect_add_self hp' hp hq
  have hLp' : (-reflectMatrix (p' + p)) *ᵥ p' = p := by
    rw [Matrix.neg_mulVec, reflectMatrix_mulVec, hRp', neg_neg]
  have hLp : (-reflectMatrix (p' + p)) *ᵥ p = p' := by
    rw [Matrix.neg_mulVec, reflectMatrix_mulVec, hRp, neg_neg]
  have hcov := H.cov _ _ _ (isSpinLift_neg_reflect hK) p' p hpq (by rw [hLp']; exact hp0)
    (by rw [hLp]; exact hp0') V W hV (by rw [hLp', hLp]; exact hW)
  intro μ
  rw [hR p' p hpq V W hV hW μ, ← vecAct_neg, ← hcov μ]
  simp only [Matrix.mul_assoc]

/-- **Form-factor pairs and the Pauli bound.** With mirror symmetry of every limit, if the Pauli
projection at the canonical pair tends to `b` as `Q → 0⁺`, then near `q² = 0⁺` every limit has a
form-factor pair and every pair has `‖64π⁶F₂/e⁶ - 64π⁶b/e⁶‖ < η`. -/
theorem formFactor_pauli_of_tendsto
    (hM : ∀ p' p, IsPairQ m p' p → ∀ V, Lim p' p V → QED.OneLoop.IsMirrorSymmetric p' p V)
    {e : ℝ} (he : e ≠ 0) {b : ℂ} (hb : Tendsto (pauliAtCanonical Lim e m) (𝓝[>] 0) (𝓝 b))
    (η : ℝ) (hη : 0 < η) :
    ∃ q₀ > 0, ∀ p' p, IsPairQ m p' p → Minkowski.dot (p' - p) (p' - p) < q₀ →
      ∀ V, Lim p' p V → (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair e m p' p V F) ∧
        ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair e m p' p V F →
          ‖64 * (π : ℂ) ^ 6 * F.2 / (e : ℂ) ^ 6 - 64 * (π : ℂ) ^ 6 * b / (e : ℂ) ^ 6‖ < η := by
  have he' : (e : ℂ) ≠ 0 := ofReal_ne_zero.mpr he
  set c : ℂ := 64 * (π : ℂ) ^ 6 / (e : ℂ) ^ 6 with hc
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc0 : c ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 6 hπ))
    (pow_ne_zero 6 he')
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  obtain ⟨q₀, hq₀, hall⟩ := H.uniform_of_tendsto e hb (η / ‖c‖) (by positivity)
  refine ⟨q₀, hq₀, fun p' p hpq hqq V hV => ⟨?_, fun F hF => ?_⟩⟩
  · obtain ⟨F, hF, -⟩ := QED.OneLoop.existsUnique_isFormFactorPair_of_mirror he H.pos.ne'
      hpq.1 hpq.2.1 hpq.2.2.2.2 (H.isLittleGroupCovariant hpq hV) (hM p' p hpq V hV)
    exact ⟨F, hF⟩
  · have hF2 : F.2 = QED.OneLoop.formFactorProj₂ e m p' p V := by
      rw [QED.OneLoop.eq_formFactorProj_of_isFormFactorPair he H.pos.ne' hpq.1 hpq.2.1
        hpq.2.2.2.2 hF]
    have hB := hall p' p hpq hqq V hV
    rw [← hF2] at hB
    have e1 : 64 * (π : ℂ) ^ 6 * F.2 / (e : ℂ) ^ 6 - 64 * (π : ℂ) ^ 6 * b / (e : ℂ) ^ 6 =
        c * (F.2 - b) := by
      simp only [hc]
      field_simp
    rw [e1, norm_mul]
    calc ‖c‖ * ‖F.2 - b‖ < ‖c‖ * (η / ‖c‖) := mul_lt_mul_of_pos_left hB hcpos
      _ = η := by field_simp

/-- **The `q² → 0⁺` limit of the canonical Pauli projection from a nested value.** If, for all
small `Q > 0`, every limit at the canonical pair has Pauli projection `c · outerAt m Q R`, with a
photon function `R` measurable, continuous on `(0, ∞)` and bounded on `[0, ∞)`, then the canonical
Pauli projection tends to `c · outerAt m 0 R`. -/
theorem tendsto_pauliAtCanonical_of_nested (e c : ℝ) {R : ℝ → ℝ} {C : ℝ} (hR : Measurable R)
    (hRc : ContinuousOn R (Ioi 0)) (hRb : ∀ t, 0 ≤ t → |R t| ≤ C)
    (hN : ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ V, Lim (boostMomentum m Q) (restMomentum m) V →
      QED.OneLoop.formFactorProj₂ e m (boostMomentum m Q) (restMomentum m) V =
        ((c * QED.ChainProof.HCValue.outerAt m Q R : ℝ) : ℂ)) :
    Tendsto (pauliAtCanonical Lim e m) (𝓝[>] 0)
      (𝓝 ((c * QED.ChainProof.HCValue.outerAt m 0 R : ℝ) : ℂ)) := by
  have hT := (QED.ChainProof.HCValue.tendsto_outerAt H.pos hR hRc hRb).const_mul c
  have hT' := (continuous_ofReal.tendsto _).comp hT
  refine hT'.congr' ?_
  filter_upwards [hN, self_mem_nhdsWithin] with Q hQ (hQ0 : 0 < Q)
  exact (hQ _ (H.lim_canonicalLimit hQ0)).symm

end CovFamily

end QED.ChainProof

end
