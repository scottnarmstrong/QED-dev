/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X2Bridge
public import QED.GradedProof.X2LegForm
public import QED.GradedProof.X2Pair
public import QED.GradedProof.RPi4Reduce
public import QED.Frozen.Graded.IsLSZAmplitudePart
public import QED.Frozen.Graded.IsSpinFormFactorPair
public import QED.Frozen.Lepton.VertexOrderFiveLeptonPauliLimit
public import QED.Frozen.OneLoop.PauliFormFactorLimit
public import QED.Frozen.TwoLoop.A1Four
public import QED.Frozen.Lepton.A2Four

/-!
# (X₂) piece G: the conditional theorem

Helper level for the Phase 5 Stage 2 goal (X₂)
`QED.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit` (decision D-57), piece G. The exact
frozen conclusion of (X₂) from its exact hypotheses plus the order-`e⁵` Dyson decomposition
`QED.GradedProof.X1C.DysonFive` (piece C of (X₁), a separate proof) at the records of the
statement and every `ε > 0`.

Proof: renormalized counterterms exist (`QED.GradedProof.RPi4.exists_renormalized`). For each of
them the level-`1` conditions are (HM₂)'s (Z₅), (K₀), (F₁₁) at the level-`0` counterterms
(piece C), so the sealed (HM₂) at `η / 2` applies to `V₂ - e⁵ d₁ 1 γ^μ`, `V₂` the order-`5`
vertex limit. The LSZ amplitude exists and is unique (piece E, `QED.GradedProof.X1`), and on
shell it is `ū' V_HM u + e c ū' γ^μ u + κ ū' V₁ u` with `V₁` the one-loop vertex plus a multiple
of `γ^μ` (piece F). So its spin pairs are (HM₂)'s pairs of `V_HM` shifted by `(c + κ G₁, κ G₂)`,
`G` a pair of `V₁` (`isSpinFormFactorPair_iff_shift`), and `|G₂| < e² / 8π² + 1` by the sealed
(I) at `η = 1`, while `κ = D(q²) Pol₁(q²) q² → 0` as `q² → 0` at fixed regulators.

* `norm_kappa_term_lt`, `isSpinFormFactorPair_lszFive_lepton_pauli_limit_of_dysonFive`.
-/

@[expose] public section

open Matrix Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X2

/-- The `κ G₂` term is small: `‖16 π⁴ κ G₂ / e⁴‖ < η / 2` when `‖κ‖ < η |e|⁴ / (32 π⁴ B)` and
`‖G₂‖ < B`. -/
theorem norm_kappa_term_lt {e η B : ℝ} (he : e ≠ 0) (hB : 0 < B) {κ G₂ : ℂ}
    (hκ : ‖κ‖ < η * |e| ^ 4 / (32 * Real.pi ^ 4 * B)) (hG : ‖G₂‖ < B) :
    ‖16 * (Real.pi : ℂ) ^ 4 * (κ * G₂) / (e : ℂ) ^ 4‖ < η / 2 := by
  have hpi : 0 < Real.pi ^ 4 := by positivity
  have he4 : 0 < |e| ^ 4 := by positivity
  have hnorm : ‖16 * (Real.pi : ℂ) ^ 4 * (κ * G₂) / (e : ℂ) ^ 4‖ =
      16 * Real.pi ^ 4 * (‖κ‖ * ‖G₂‖) / |e| ^ 4 := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_mul, RCLike.norm_ofNat, Real.norm_eq_abs]
  rw [hnorm, div_lt_iff₀ he4]
  have h1 : ‖κ‖ * ‖G₂‖ < η * |e| ^ 4 / (32 * Real.pi ^ 4 * B) * B := by
    calc ‖κ‖ * ‖G₂‖ ≤ ‖κ‖ * B := mul_le_mul_of_nonneg_left hG.le (norm_nonneg _)
      _ < _ := mul_lt_mul_of_pos_right hκ hB
  have h2 : η * |e| ^ 4 / (32 * Real.pi ^ 4 * B) * B * (16 * Real.pi ^ 4) = η / 2 * |e| ^ 4 := by
    field_simp
    ring
  nlinarith

/-- **(X₂) given the order-`e⁵` Dyson decomposition.** The frozen conclusion of
`QED.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit` from its hypotheses and
`QED.GradedProof.X1C.DysonFive` (piece C of (X₁)) at every record of the statement and every
`ε > 0`. -/
theorem isSpinFormFactorPair_lszFive_lepton_pauli_limit_of_dysonFive {n : ℕ} (P₀ : Params)
    (mH : Fin n → ℝ) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ) (η : ℝ)
    (hη : 0 < η)
    (hC : ∀ (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ)
      (D : Counterterms (Fin 3 ⊕ Fin n × Fin 3)), ∀ ε > 0,
      X1C.DysonFive
        { { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ } with ε := ε }
        (Lepton.leptonFlavors
          { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
          fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
        (∀ ℓ, RM < MH₁ ℓ) → (∀ ℓ, RM < MH₂ ℓ) → (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
        (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
          IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D leptonRep 2) ∧
        ∀ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
          IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D leptonRep 2 →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ M, IsLSZAmplitudePart
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 5 p' p M) ∧
            ∀ M, IsLSZAmplitudePart
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 5 p' p M →
              (∃ F : ℂ × ℂ, IsSpinFormFactorPair P₀.e P₀.m p' p M F) ∧
              ∀ F : ℂ × ℂ, IsSpinFormFactorPair P₀.e P₀.m p' p M F →
                ‖16 * (Real.pi : ℂ) ^ 4 * F.2 / (P₀.e : ℂ) ^ 4 -
                  ((QED.TwoLoop.a1Four + ∑ ℓ, Lepton.a2Four (P₀.m / mH ℓ) : ℝ) : ℂ)‖ < η := by
  classical
  obtain ⟨RM, hRM⟩ := QED.Lepton.isFormFactorPair_vertexOrderFive_lepton_pauli_limit P₀ mH he hm
    hmH (η / 2) (by positivity)
  obtain ⟨δI, hδI, RI, hI⟩ :=
    QED.OneLoop.isFormFactorPair_vertexOneLoop_pauli_limit P₀.e P₀.m he hm 1 one_pos
  refine ⟨RM, fun M₁ M₂ c₁ c₂ hM₁ hM₂ hRM₁ hRM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hRMH₁ hRMH₂
    hcH₁ hcH₂ => ?_⟩
  obtain ⟨δH, hδH, RH, hH⟩ := hRM M₁ M₂ c₁ c₂ hM₁ hM₂ hRM₁ hRM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁
    hMH₂ hRMH₁ hRMH₂ hcH₁ hcH₂
  refine ⟨min δH δI, lt_min hδH hδI, max RH RI, fun mγ Λ hmγ hΛ hmγδ hΛR => ?_⟩
  set P : Params := { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
    with hP
  set H : Fin n → Lepton.HeavyLepton := fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩ with hHdef
  set Φ := Lepton.leptonFlavors P H with hΦ
  have hmass : ∀ g, P.m ≤ Φ.mass g :=
    RPi4.le_leptonFlavors_mass P H hM₁ hM₂ hmH hMH₁ hMH₂
  have hPV₁ := RPi4.leptonFlavors_blockPV₁ P H hc₁ hcH₁
  have hPV₂ := RPi4.leptonFlavors_blockPV₂ P H hc₂ hcH₂
  have hs₁ := RPi4.leptonFlavors_sum_coeff P H hc₁ hcH₁
  have hs₂ := RPi4.leptonFlavors_sum_coeff_mass P H hc₂ hcH₂
  refine ⟨RPi4.exists_renormalized P H he hm hmγ hΛ hM₁ hM₂ hmH hMH₁ hMH₂ hc₁ hc₂ hcH₁ hcH₂,
    fun D hD => ?_⟩
  -- (HM₂) at the level-`0` counterterms
  obtain ⟨hZ, hK, hF⟩ := hm_conditions P H D hm hmγ hΛ hD
  obtain ⟨q₀H, hq₀H, hHq⟩ := (hH mγ Λ hmγ hΛ (hmγδ.trans_le (min_le_left _ _))
    ((le_max_left _ _).trans_lt hΛR)).2 (P.e ^ 2 * D.d₁ (Sum.inl 0) 0)
    (P.e ^ 2 * D.d₂ (Sum.inl 0) 0) (P.e ^ 2 * D.dm (Sum.inl 0) 0) (P.e ^ 2 * D.d₃ 0) hZ hK hF
  -- the photon-leg coefficient is small for small `q²`
  set B : ℝ := P₀.e ^ 2 / (8 * Real.pi ^ 2) + 1 with hB
  have hB0 : 0 < B := by positivity
  obtain ⟨δκ, hδκ, hκ⟩ := exists_kappa_small P Φ D hm hmass hmγ hΛ
    (t := η * |P₀.e| ^ 4 / (32 * Real.pi ^ 4 * B)) (by positivity)
  obtain ⟨Pol₂, hPol₂⟩ := exists_piTwoLim_eq P Φ D leptonRep P.m hm hmass hmγ hΛ RPi4.leptonRep_idem
    hPV₁ hPV₂ hD
  refine ⟨min q₀H (min δI δκ), lt_min hq₀H (lt_min hδI hδκ),
    fun p' p hp' hp hp0' hp0 hs0 hsq => ?_⟩
  set s := Minkowski.dot (p' - p) (p' - p) with hs
  have hsH : s < q₀H := hsq.trans_le (min_le_left _ _)
  have hsI : s < δI := hsq.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsκ : s < δκ := hsq.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  -- the vertex limits
  set V₁ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun μ =>
    QED.OneLoop.vertexOneLoop P₀.e P₀.m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 μ +
      ((P.e ^ 2 * D.d₁ (Sum.inl 0) 0 * P.e : ℝ) : ℂ) • Dirac.gamma μ with hV₁def
  have hV₁ := tendsto_vertexPart_one P H D hm hmγ hΛ hp' hp hp0' hp0
  obtain ⟨W₂, hW₂, -⟩ := X1D.exists_vertexPart_two_offShell P Φ D Φ.openLine P.m hm hmass hmγ
    hΛ hs₁ hs₂ hp hp' hp0 hp0' hs0.le
  have hV₂ := hW₂.self_of_nhds
  set V₂ := W₂ (p', p) with hV₂def
  have hVHM := isVertexOrderFiveLimit_of_tendsto P H D hV₂
  -- the LSZ amplitude
  have hM0 := isLSZAmplitudePart_five_of_dysonFive P Φ D leptonRep P.m hm hmass hmγ hΛ
    RPi4.leptonRep_idem hPV₁ hPV₂ rfl hD hp' hp hp0' hp0 hs0.le
    (hC M₁ M₂ c₁ c₂ mγ Λ MH₁ MH₂ cH₁ cH₂ D) (V₁ := V₁) (V₂ := V₂) hV₁ hV₂
  -- the one-loop vertex pair, (I) at `η = 1`
  obtain ⟨⟨G', hG'⟩, hG'b⟩ := hI mγ Λ hmγ hΛ p' p hp' hp hp0' hp0 hs0 hsI
    (hmγδ.trans_le (min_le_right _ _)) ((le_max_right _ _).trans_lt hΛR)
  have hGpair : QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V₁
      (G'.1 + (P.e ^ 2 * D.d₁ (Sum.inl 0) 0 : ℝ), G'.2) :=
    isFormFactorPair_add_gamma hG' (P.e ^ 2 * D.d₁ (Sum.inl 0) 0)
  have hG2 : ‖G'.2‖ < B := by
    have h := hG'b G' hG'
    have h2 := norm_sub_norm_le G'.2 ((P₀.e ^ 2 / (8 * Real.pi ^ 2) : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h2
    linarith
  -- the decomposition of the amplitude
  set κ : ℂ := dprop mγ Λ s * polOne P Φ D s * (s : ℂ) with hκdef
  set c : ℂ := ((P.e ^ 4 * D.d₁ (Sum.inl 0) 1 : ℝ) : ℂ) +
    (dprop mγ Λ s * Pol₂ s * (s : ℂ) + κ ^ 2) with hcdef
  have hdec : ∀ s' s₀ μ, lszFive P Φ D leptonRep P.m V₁ V₂ p' p s' s₀ μ =
      Dirac.bar (Dirac.spinor P₀.m p' s') ⬝ᵥ
          ((fun μ => V₂ μ - ((P.e ^ 4 * D.d₁ (Sum.inl 0) 1 * P.e : ℝ) : ℂ) • Dirac.gamma μ) μ
            *ᵥ Dirac.spinor P₀.m p s₀) +
        (P₀.e : ℂ) * c * (Dirac.bar (Dirac.spinor P₀.m p' s') ⬝ᵥ
          (Dirac.gamma μ *ᵥ Dirac.spinor P₀.m p s₀)) +
        κ * (Dirac.bar (Dirac.spinor P₀.m p' s') ⬝ᵥ (V₁ μ *ᵥ Dirac.spinor P₀.m p s₀)) := by
    intro s' s₀ μ
    rw [lszFive_eq P Φ D leptonRep P.m hp' hp (piOneLim_eq P Φ D (p' - p))
      (fun μ ρ => hPol₂ (p' - p) (by nlinarith [pow_pos hm 2]) μ ρ) hGpair s' s₀ μ]
    have e1 : P.e = P₀.e := rfl
    have e2 : Φ.mass Φ.openLine = P₀.m := rfl
    have e3 : P.mγ = mγ := rfl
    have e4 : P.Λ = Λ := rfl
    rw [e1, e2, e3, e4, ← hs]
    simp only [sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    simp only [hcdef, hκdef]
    push_cast
    ring
  have key := fun F => isSpinFormFactorPair_iff_shift hm hp' hp hp0' hp0 hdec hGpair F
  refine ⟨⟨_, hM0⟩, fun M hM => ?_⟩
  obtain rfl := X1.eq_of_isLSZAmplitudePart hm.ne' hp' hp hM hM0
  obtain ⟨⟨FH, hFH⟩, hFHb⟩ := (hHq p' p hp' hp hp0' hp0 hs0 hsH).2 _ hVHM
  refine ⟨⟨(FH.1 + c + κ * (G'.1 + (P.e ^ 2 * D.d₁ (Sum.inl 0) 0 : ℝ)), FH.2 + κ * G'.2),
    (key _).2 ?_⟩, fun F hF => ?_⟩
  · convert hFH using 2 <;> ring
  · have h1 := hFHb _ ((key F).1 hF)
    have h2 := norm_kappa_term_lt he hB0 (hκ s (by rw [abs_of_pos hs0]; exact hsκ)) hG2
    have e : 16 * (Real.pi : ℂ) ^ 4 * F.2 / (P₀.e : ℂ) ^ 4 -
        ((QED.TwoLoop.a1Four + ∑ ℓ, Lepton.a2Four (P₀.m / mH ℓ) : ℝ) : ℂ) =
        (16 * (Real.pi : ℂ) ^ 4 * (F.2 - κ * G'.2) / (P₀.e : ℂ) ^ 4 -
          ((QED.TwoLoop.a1Four + ∑ ℓ, Lepton.a2Four (P₀.m / mH ℓ) : ℝ) : ℂ)) +
        16 * (Real.pi : ℂ) ^ 4 * (κ * G'.2) / (P₀.e : ℂ) ^ 4 := by
      ring
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ < η / 2 + η / 2 := add_lt_add h1 h2
      _ = η := add_halves η

end QED.GradedProof.X2

end
