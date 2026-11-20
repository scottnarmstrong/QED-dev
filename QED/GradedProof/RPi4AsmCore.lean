/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4AsmJoint
public import QED.GradedProof.RPi4Reduce

/-!
# (R-Π₄) steps L8–L11: assembly of the analytic core

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57). This file assembles the
analytic core `QED.GradedProof.RPi4.Core` from:

* the face-limit identity (step L6d3), `AsmFaceIds`: `FaceLimitId` at every fermion-regulator
  point of the frozen statement, for every tilt scale `c ≥ 1` and every `s ∈ (-4m², 2c²)`;
* the joint photon-regulator limit (step L8, `asm_exists_norm_sub_polLim_le`, proved);
* the decoupling of the fermion regulators (step L9), stated as the named proposition
  `AsmDecoupling`: the photon-regulator limit `asmPolLim` converges, as all fermion regulators
  go to infinity, to a function `Π_∞`, uniformly on compact intervals of `s > -4m²`;
* the majorant (step L10), stated as the named proposition `AsmMajorant` on the subtracted class
  sum `Q(m_γ, Λ; s) - Q(m_γ, Λ; 0)` (which is `Π(s)` by `pol_eq_qPair_sub`).

Main results:

* `asm_core`: `AsmFaceIds → AsmDecoupling → AsmMajorant → Core`;
* `asm_two_lepton_limit_of_decoupling_majorant`: the frozen conclusion of (R-Π₄) from its
  binders and these three propositions.

Steps L9 and L10 are not proved here; `AsmDecoupling` and `AsmMajorant` record exactly what
remains of them.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

section Asm

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- The flavours of the frozen statement at the fermion regulators `(M, c)`, `(MH, cH)`. The
photon masses of `regP` do not enter (`leptonFlavors` reads only the fermion data). -/
abbrev asmΦ (M₁ M₂ c₁ c₂ : ℝ) (MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ) :
    Lepton.Flavors (Fin 3 ⊕ Fin n × Fin 3) :=
  Lepton.leptonFlavors (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂)

/-- **(L6d3 hypothesis) the face-limit identity at every fermion-regulator point** of the frozen
statement, for every tilt scale `c ≥ 1` and every `s` with `-4m² < s < 2c²`. -/
def AsmFaceIds : Prop :=
  ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ →
    1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
    ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
      (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
      (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
      ∀ c s : ℝ, 1 ≤ c → -(4 * P₀.m ^ 2) < s → s < 2 * c ^ 2 →
        FaceLimitId (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e P₀.m c s

/-- **(L9, open) decoupling of the fermion regulators**: the photon-regulator limit `asmPolLim`
(step L8) tends to a function `Π_∞` as every fermion regulator goes to infinity, uniformly on
compact intervals of `s > -4m²` and in the regulator coefficients allowed by the
Pauli–Villars conditions. -/
def AsmDecoupling : Prop :=
  ∃ Pinf : ℝ → ℂ, ∀ S₀ S η : ℝ, -(4 * P₀.m ^ 2) < S₀ → 0 < η →
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
        (∀ ℓ, RM < MH₁ ℓ) → (∀ ℓ, RM < MH₂ ℓ) → (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
        (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
        ∀ s : ℝ, S₀ ≤ s → s ≤ S →
          ‖asmPolLim (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e s /
            (P₀.e : ℂ) ^ 4 - Pinf s‖ < η

/-- **(L10, open) the majorant** of the subtracted class sum, for all spacelike `s ≥ 0`,
uniformly in the regulators beyond thresholds. -/
def AsmMajorant : Prop :=
  ∃ C RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
    1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
    ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
      (∀ ℓ, RM < MH₁ ℓ) → (∀ ℓ, RM < MH₂ ℓ) → (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
      (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        ∀ s : ℝ, 0 ≤ s →
          ‖(qPair (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e mγ Λ s -
              qPair (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e mγ Λ 0) /
            (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2

/-- The tilt bound used for the face-limit identity: `max S 0 < 2 (1 + |max S 0|)²`. -/
theorem asm_max_lt_two_mul_sq (S : ℝ) : max S 0 < 2 * (1 + |max S 0|) ^ 2 := by
  have := le_abs_self (max S 0)
  nlinarith [abs_nonneg (max S 0)]

/-- **Assembly (L11): the analytic core** from the face-limit identity (L6d3), the decoupling
(L9) and the majorant (L10); the joint photon-regulator limit (L8) is proved. -/
theorem asm_core (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hId : AsmFaceIds P₀ mH) (hDec : AsmDecoupling P₀ mH) (hMaj : AsmMajorant P₀ mH) :
    Core P₀ mH := by
  obtain ⟨Pinf, hDec⟩ := hDec
  obtain ⟨C, RM₀, hMaj⟩ := hMaj
  refine ⟨Pinf, C, fun S₀ S η hS₀ hη => ?_⟩
  obtain ⟨RM₁, hRM₁⟩ := hDec S₀ S (η / 2) hS₀ (half_pos hη)
  refine ⟨max RM₀ RM₁, fun M₁ M₂ c₁ c₂ hM₁ hM₂ hR₁ hR₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂
    hRH₁ hRH₂ hcH₁ hcH₂ => ?_⟩
  set Φ := asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂ with hΦ
  have hmass : ∀ g, P₀.m ≤ Φ.mass g :=
    le_leptonFlavors_mass (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂) hM₁ hM₂
      hmH hMH₁ hMH₂
  have hPV₁ := leptonFlavors_blockPV₁ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ)
    (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₁ hcH₁
  have hPV₂ := leptonFlavors_blockPV₂ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ)
    (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₂ hcH₂
  -- L9 at these regulators
  have hdec := hRM₁ M₁ M₂ c₁ c₂ hM₁ hM₂ (le_max_right _ _ |>.trans_lt hR₁)
    (le_max_right _ _ |>.trans_lt hR₂) hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂
    (fun ℓ => le_max_right _ _ |>.trans_lt (hRH₁ ℓ))
    (fun ℓ => le_max_right _ _ |>.trans_lt (hRH₂ ℓ)) hcH₁ hcH₂
  -- L10 at these regulators
  obtain ⟨δ₁, hδ₁, R₁, hmaj⟩ := hMaj M₁ M₂ c₁ c₂ hM₁ hM₂ (le_max_left _ _ |>.trans_lt hR₁)
    (le_max_left _ _ |>.trans_lt hR₂) hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂
    (fun ℓ => le_max_left _ _ |>.trans_lt (hRH₁ ℓ))
    (fun ℓ => le_max_left _ _ |>.trans_lt (hRH₂ ℓ)) hcH₁ hcH₂
  -- L8 at these regulators
  have h00 : -(4 * P₀.m ^ 2) < 0 := by nlinarith
  obtain ⟨C₈, hC₈⟩ := asm_exists_norm_sub_polLim_le Φ leptonRep P₀ hm hmass leptonRep_idem
    hPV₁ hPV₂ he hS₀ fun s h₀ h₁ =>
      hId M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂ _ s
        (by linarith [abs_nonneg (max S 0)]) ((lt_min hS₀ h00).trans_le h₀)
        (h₁.trans_lt (asm_max_lt_two_mul_sq S))
  -- thresholds
  have he4 : 0 < |P₀.e| ^ 4 := by positivity
  set K : ℝ := |C₈| / |P₀.e| ^ 4 + 1 with hK
  have hK0 : 0 < K := by positivity
  set r : ℝ := η / (4 * K) with hr
  have hr0 : 0 < r := by positivity
  refine ⟨min δ₁ (min 1 (r ^ 2)), lt_min hδ₁ (lt_min one_pos (by positivity)),
    max R₁ (max 1 r⁻¹), fun mγ Λ hmγ hΛ hmγδ hRΛ D hD Pol hPol => ?_⟩
  have hmγ1 : mγ ≤ 1 := (hmγδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hmγr : mγ < r ^ 2 := hmγδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hΛ1 : 1 ≤ Λ := ((le_max_left _ _).trans (le_max_right _ _)).trans hRΛ.le
  have hΛr : r⁻¹ < Λ := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hRΛ
  have hmass' : ∀ g, P₀.m ≤ (Lepton.leptonFlavors (regP P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (heavyH mH MH₁ MH₂ cH₁ cH₂)).mass g := hmass
  have hpol : ∀ s, -(4 * P₀.m ^ 2) < s →
      Pol s = qPair Φ leptonRep P₀.e mγ Λ s - qPair Φ leptonRep P₀.e mγ Λ 0 := fun s hs =>
    pol_eq_qPair_sub _ leptonRep hm hmass' leptonRep_idem hPV₁ hPV₂
      (regP P₀ M₁ M₂ c₁ c₂ mγ Λ) D he hmγ hΛ hD hPol hs
  refine ⟨fun s h₀ h₁ => ?_, fun s hs => ?_⟩
  · -- the limit clause
    have hs : -(4 * P₀.m ^ 2) < s := hS₀.trans_le h₀
    have e8 := hC₈ s h₀ h₁ mγ Λ hmγ hmγ1 hΛ1
    have e9 := hdec s h₀ h₁
    have hsq : Real.sqrt mγ < r := by
      rw [show r = Real.sqrt (r ^ 2) from (Real.sqrt_sq hr0.le).symm]
      exact Real.sqrt_lt_sqrt hmγ.le hmγr
    have hinv : Λ⁻¹ < r := by
      rw [inv_lt_comm₀ (one_pos.trans_le hΛ1) hr0]
      exact hΛr
    have hsplit : Pol s / (P₀.e : ℂ) ^ 4 - Pinf s =
        (qPair Φ leptonRep P₀.e mγ Λ s - qPair Φ leptonRep P₀.e mγ Λ 0 -
            asmPolLim Φ leptonRep P₀.e s) / (P₀.e : ℂ) ^ 4 +
          (asmPolLim Φ leptonRep P₀.e s / (P₀.e : ℂ) ^ 4 - Pinf s) := by
      rw [hpol s hs]
      ring
    have hnorm : ‖(qPair Φ leptonRep P₀.e mγ Λ s - qPair Φ leptonRep P₀.e mγ Λ 0 -
        asmPolLim Φ leptonRep P₀.e s) / (P₀.e : ℂ) ^ 4‖ ≤ η / 2 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ he4]
      have hsum : Real.sqrt mγ + Λ⁻¹ ≤ 2 * r := by linarith
      have hsum0 : 0 ≤ Real.sqrt mγ + Λ⁻¹ := by
        have := inv_pos.2 (one_pos.trans_le hΛ1)
        positivity
      have hKr : K * (2 * r) = η / 2 := by
        rw [hr]
        field_simp
        ring
      have hC : |C₈| ≤ K * |P₀.e| ^ 4 := by
        rw [hK, add_mul, div_mul_cancel₀ _ he4.ne']
        linarith
      calc _ ≤ C₈ * (Real.sqrt mγ + Λ⁻¹) := e8
        _ ≤ |C₈| * (Real.sqrt mγ + Λ⁻¹) := mul_le_mul_of_nonneg_right (le_abs_self _) hsum0
        _ ≤ (K * |P₀.e| ^ 4) * (2 * r) := mul_le_mul hC hsum hsum0 (by positivity)
        _ = η / 2 * |P₀.e| ^ 4 := by rw [mul_comm K, mul_assoc, hKr, mul_comm]
    rw [hsplit]
    calc _ ≤ _ := norm_add_le _ _
      _ < η / 2 + η / 2 := add_lt_add_of_le_of_lt hnorm e9
      _ = η := add_halves η
  · -- the majorant clause
    rw [hpol s (h00.trans_le hs)]
    exact hmaj mγ Λ hmγ hΛ (hmγδ.trans_le (min_le_left _ _))
      ((le_max_left _ _).trans_lt hRΛ) s hs

/-- **(R-Π₄), conditional on the face-limit identity (L6d3), the decoupling (L9) and the
majorant (L10)**: the frozen conclusion, with its binders. -/
theorem asm_two_lepton_limit_of_decoupling_majorant (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hmH : ∀ ℓ, P₀.m < mH ℓ) (hId : AsmFaceIds P₀ mH) (hDec : AsmDecoupling P₀ mH)
    (hMaj : AsmMajorant P₀ mH) :
    ∃ (Pinf : ℝ → ℂ) (C : ℝ), ∀ S₀ S η : ℝ, -(4 * P₀.m ^ 2) < S₀ → 0 < η →
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
            (∃ Pol : ℝ → ℂ, ∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) ∧
            ∀ Pol : ℝ → ℂ, (∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) →
              (∀ s : ℝ, S₀ ≤ s → s ≤ S → ‖Pol s / (P₀.e : ℂ) ^ 4 - Pinf s‖ < η) ∧
              ∀ s : ℝ, 0 ≤ s →
                ‖Pol s / (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2 :=
  vacuumPolarizationPart_two_lepton_limit_of_core P₀ mH he hm hmH
    (asm_core P₀ mH he hm hmH hId hDec hMaj)

end Asm

end QED.GradedProof.RPi4

end
