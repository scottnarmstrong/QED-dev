/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1EVertexOne
public import QED.Frozen.Graded.LeptonRep
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Graded.VertexPartTwoEq
public import QED.Frozen.Graded.IsOnShellAtOneIff
public import QED.Frozen.Graded.IsChargeNormalizedAtOneIff
public import QED.Frozen.Graded.IsPhotonOnShellAtOneIff
public import QED.Frozen.Lepton.IsVertexOrderFiveLimit
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Frozen.OneLoop.VertexOneLoopSpec
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.WickModel.HeadlinePair

/-!
# (X₂) piece C: the bridge to (HM₂)

Helper level for the Phase 5 Stage 2 goal (X₂)
`QED.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit` (decision D-57), piece C. For the
lepton flavours `leptonFlavors P H` and counterterms `D` renormalized through order `e⁴` in the
per-lepton scheme, put `hmParams P D` for `P` with the level-`0` counterterms of the electron
(`δ₁ = e² d₁ 0`, `δ₂ = e² d₂ 0`, `δ_m = e² d_m 0`, `δ₃ = e² d₃ 0`). Then:

* `hm_conditions`: (Z₅), (K₀) and (F₁₁) of (HM₂) hold at `hmParams P D` (by the sealed
  (E-G₂ₛ), (E-G₂ₖ), (E-G₂ₚ); the graded objects do not read the `δ` fields of the record);
* `isVertexOrderFiveLimit_of_tendsto`: if `V₂` is the `ε → 0⁺` limit of the order-`5` graded
  vertex, then `V₂ - e⁵ d₁ 1 γ^μ` is the order-`5` vertex limit (F₁₀) of (HM₂) (sealed (E-G₃));
* `tendsto_vertexPart_one`: the order-`3` graded vertex tends to the one-loop vertex (F) plus
  `e³ d₁ 0 γ^μ` (sealed (F′));
* `isFormFactorPair_add_gamma`: adding `e c γ^μ` shifts the first form factor by `c`.
-/

@[expose] public section

open Matrix Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X2

/-- `P` with the level-`0` counterterms of the electron (open line `inl 0`) of `D`. -/
noncomputable def hmParams {n : ℕ} (P : Params) (D : Counterterms (Fin 3 ⊕ Fin n × Fin 3)) :
    Params :=
  { P with
    δ₁ := P.e ^ 2 * D.d₁ (Sum.inl 0) 0
    δ₂ := P.e ^ 2 * D.d₂ (Sum.inl 0) 0
    δm := P.e ^ 2 * D.dm (Sum.inl 0) 0
    δ₃ := P.e ^ 2 * D.d₃ 0 }

variable {n : ℕ} (P : Params) (H : Fin n → Lepton.HeavyLepton)
  (D : Counterterms (Fin 3 ⊕ Fin n × Fin 3))

/-- The renormalization conditions do not read the `δ` fields of the record. -/
theorem isRenormalizedThrough_hmParams_iff :
    IsRenormalizedThrough (hmParams P D) (Lepton.leptonFlavors (hmParams P D) H) D leptonRep 2 ↔
      IsRenormalizedThrough P (Lepton.leptonFlavors P H) D leptonRep 2 :=
  Iff.rfl

/-- **(Z₅), (K₀), (F₁₁) of (HM₂) from the renormalization conditions** at level `1`. -/
theorem hm_conditions (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hD : IsRenormalizedThrough P (Lepton.leptonFlavors P H) D leptonRep 2) :
    WickModel.IsElectronOnShell (hmParams P D) hm hmγ hΛ ∧
      QED.OneLoop.IsChargeNormalized P.e (1 + P.e ^ 2 * D.d₁ (Sum.inl 0) 0) P.m P.mγ P.Λ hm hmγ
        hΛ ∧
      Lepton.IsPhotonOnShell (hmParams P D) (Lepton.leptonFlavors (hmParams P D) H) := by
  have hD' := (isRenormalizedThrough_hmParams_iff P H D).2 hD
  obtain ⟨hZK, hF⟩ := hD'.2 1 le_rfl (by norm_num)
  have hZ' := (hZK (Sum.inl 0) rfl).1
  have hK' := (hZK (Sum.inl 0) rfl).2
  refine ⟨?_, ?_, ?_⟩
  · exact (isOnShellAt_one_iff (hmParams P D) (Lepton.leptonFlavors (hmParams P D) H) D (Sum.inl 0)
      hm hmγ hΛ).1 hZ'
  · exact (isChargeNormalizedAt_one_iff (hmParams P D) (Lepton.leptonFlavors (hmParams P D) H)
      D (Sum.inl 0) hm hmγ hΛ).1 hK'
  · exact (isPhotonOnShellAt_one_iff (hmParams P D) (Lepton.leptonFlavors (hmParams P D) H)
      D).1 hF

/-- **The order-`5` vertex limit of (HM₂) from the graded one** (sealed (E-G₃)). -/
theorem isVertexOrderFiveLimit_of_tendsto {p' p : Fin 4 → ℝ}
    {V₂ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV₂ : ∀ μ, Tendsto (fun ε => vertexPart { P with ε := ε } (Lepton.leptonFlavors P H) D
      (Sum.inl 0) 2 p' p μ) (𝓝[>] 0) (𝓝 (V₂ μ))) :
    Lepton.IsVertexOrderFiveLimit (hmParams P D) (Lepton.leptonFlavors (hmParams P D) H) p' p
      (fun μ => V₂ μ - ((P.e ^ 4 * D.d₁ (Sum.inl 0) 1 * P.e : ℝ) : ℂ) • Dirac.gamma μ) := by
  intro μ i j
  have e : ∀ ε : ℝ, Lepton.vertexOrderFive { hmParams P D with ε := ε }
      (Lepton.leptonFlavors (hmParams P D) H) p' p μ =
      vertexPart { P with ε := ε } (Lepton.leptonFlavors P H) D (Sum.inl 0) 2 p' p μ -
        ((P.e ^ 4 * D.d₁ (Sum.inl 0) 1 * P.e : ℝ) : ℂ) • Dirac.gamma μ := fun ε => by
    have h := vertexPart_two_eq { hmParams P D with ε := ε }
      (Lepton.leptonFlavors (hmParams P D) H) D rfl rfl rfl rfl rfl p' p μ
    exact eq_sub_of_add_eq h.symm
  simp only [e, Matrix.sub_apply]
  exact ((((continuous_apply j).comp (continuous_apply i)).tendsto _).comp (hV₂ μ)).sub
    tendsto_const_nhds

/-- **The order-`3` graded vertex tends to the one-loop vertex (F) plus `e³ d₁ 0 γ^μ`** at an
on-shell positive-energy pair of the electron (sealed (F′)). -/
theorem tendsto_vertexPart_one (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ : Fin 4) :
    Tendsto
      (fun ε => vertexPart { P with ε := ε } (Lepton.leptonFlavors P H) D (Sum.inl 0) 1 p' p μ)
      (𝓝[>] 0) (𝓝 (QED.OneLoop.vertexOneLoop P.e P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ +
        ((P.e ^ 2 * D.d₁ (Sum.inl 0) 0 * P.e : ℝ) : ℂ) • Dirac.gamma μ)) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hI := (QED.OneLoop.tendsto_energyFirstIntegral_iff_vertexOneLoop P.e P.m P.mγ P.Λ hm hmγ
    hΛ p' p hp' hp hp0' hp0 μ i j _).2 rfl
  have e : ∀ ε : ℝ,
      vertexPart { P with ε := ε } (Lepton.leptonFlavors P H) D (Sum.inl 0) 1 p' p μ i j =
        ((P.e ^ 2 * D.d₁ (Sum.inl 0) 0 * P.e : ℝ) : ℂ) * Dirac.gamma μ i j + (1 / I) *
          QED.OneLoop.energyFirstIntegral fun ℓ =>
            QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ ε p' p μ ℓ i j := fun ε => by
    rw [X1D.vertexPart_one_apply_eq]
    rfl
  simp only [e]
  have hlim := (tendsto_const_nhds (x := ((P.e ^ 2 * D.d₁ (Sum.inl 0) 0 * P.e : ℝ) : ℂ) *
    Dirac.gamma μ i j)).add (hI.const_mul (1 / I))
  convert hlim using 2
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **Adding `e c γ^μ` shifts the first form factor by `c`.** -/
theorem isFormFactorPair_add_gamma {e m : ℝ} {p' p : Fin 4 → ℝ}
    {W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {G : ℂ × ℂ}
    (hW : QED.OneLoop.IsFormFactorPair e m p' p W G)
    (c : ℝ) :
    QED.OneLoop.IsFormFactorPair e m p' p (fun μ => W μ + ((c * e : ℝ) : ℂ) • Dirac.gamma μ)
      (G.1 + c, G.2) := by
  intro μ u w hu hw
  have h := hW μ u w hu hw
  rw [WickModel.Headline.dotProduct_formFactor_mulVec] at h
  rw [WickModel.Headline.dotProduct_formFactor_mulVec, add_mulVec, dotProduct_add, h,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  push_cast
  ring

end QED.GradedProof.X2

end
