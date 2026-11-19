/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Setup
public import QED.Frozen.Graded.ExistsUniqueWithLevelZero
public import QED.Frozen.Graded.ExistsUniqueWithLevelOne

/-!
# (R-Π₄): reduction to the counterterm existence and the analytic core

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57). The frozen statement has
three parts at each regulator point beyond the thresholds: renormalized counterterms exist; for
each of them a transverse form factor exists; every such form factor is within `η` of `Π_∞` and
obeys the majorant. The second part is the sealed (G-Π₂) (`QED.GradedProof.RPi4.exists_pol`).
This file isolates the other two.

* `exists_renormalized`: from the sealed (G-ex₁) and (G-ex₂), renormalized counterterms through
  order `e⁴` exist for the multi-lepton data of the frozen statement.
* `Core`: the analytic core (limit and majorant clauses), quantified over every renormalized `D`
  and every form factor `Pol` of `D`.
* `vacuumPolarizationPart_two_lepton_limit_of_core`: `Core` gives the frozen statement.
-/

@[expose] public section

open Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

/-- The regulator point of the frozen statement. -/
abbrev regP (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) : Params :=
  { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }

/-- The heavy-lepton data of the frozen statement. -/
abbrev heavyH {n : ℕ} (mH MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ) : Fin n → Lepton.HeavyLepton :=
  fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩

section Exists

variable {n : ℕ} (P : Params) (H : Fin n → Lepton.HeavyLepton)

theorem sum_leptonFlavors_univ (G : Fin 3 ⊕ Fin n × Fin 3 → ℝ) :
    ∑ f, G f = ∑ i : Fin 3, G (.inl i) + ∑ ℓ : Fin n, ∑ i : Fin 3, G (.inr (ℓ, i)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem leptonFlavors_sum_coeff (hPV : 1 + P.c₁ + P.c₂ = 0)
    (hH : ∀ ℓ, 1 + (H ℓ).c₁ + (H ℓ).c₂ = 0) :
    ∑ f, (Lepton.leptonFlavors P H).coeff f = 0 := by
  rw [sum_leptonFlavors_univ]
  simp only [Fin.sum_univ_three]
  have h : ∀ ℓ, (Lepton.leptonFlavors P H).coeff (.inr (ℓ, 0)) +
      (Lepton.leptonFlavors P H).coeff (.inr (ℓ, 1)) +
      (Lepton.leptonFlavors P H).coeff (.inr (ℓ, 2)) = 0 := fun ℓ => by
    simpa [Lepton.leptonFlavors] using hH ℓ
  simp only [h, Finset.sum_const_zero, add_zero]
  simpa [Lepton.leptonFlavors, Params.loopCoeff] using hPV

theorem leptonFlavors_sum_coeff_mass (hPV : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hH : ∀ ℓ, (H ℓ).m ^ 2 + (H ℓ).c₁ * (H ℓ).M₁ ^ 2 + (H ℓ).c₂ * (H ℓ).M₂ ^ 2 = 0) :
    ∑ f, (Lepton.leptonFlavors P H).coeff f * (Lepton.leptonFlavors P H).mass f ^ 2 = 0 := by
  rw [sum_leptonFlavors_univ]
  simp only [Fin.sum_univ_three]
  have h : ∀ ℓ, (Lepton.leptonFlavors P H).coeff (.inr (ℓ, 0)) *
        (Lepton.leptonFlavors P H).mass (.inr (ℓ, 0)) ^ 2 +
      (Lepton.leptonFlavors P H).coeff (.inr (ℓ, 1)) *
        (Lepton.leptonFlavors P H).mass (.inr (ℓ, 1)) ^ 2 +
      (Lepton.leptonFlavors P H).coeff (.inr (ℓ, 2)) *
        (Lepton.leptonFlavors P H).mass (.inr (ℓ, 2)) ^ 2 = 0 := fun ℓ => by
    simpa [Lepton.leptonFlavors] using hH ℓ
  simp only [h, Finset.sum_const_zero, add_zero]
  simpa [Lepton.leptonFlavors, Params.loopCoeff, Params.mass] using hPV

/-- **Renormalized counterterms through order `e⁴` exist** for the multi-lepton data, from the
sealed (G-ex₁) and (G-ex₂). -/
theorem exists_renormalized (he : P.e ≠ 0) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hH : ∀ ℓ, P.m < (H ℓ).m) (hH₁ : ∀ ℓ, (H ℓ).m < (H ℓ).M₁) (hH₂ : ∀ ℓ, (H ℓ).m < (H ℓ).M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hHPV₁ : ∀ ℓ, 1 + (H ℓ).c₁ + (H ℓ).c₂ = 0)
    (hHPV₂ : ∀ ℓ, (H ℓ).m ^ 2 + (H ℓ).c₁ * (H ℓ).M₁ ^ 2 + (H ℓ).c₂ * (H ℓ).M₂ ^ 2 = 0) :
    ∃ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
      IsRenormalizedThrough P (Lepton.leptonFlavors P H) D leptonRep 2 := by
  have hmass := le_leptonFlavors_mass P H hM₁ hM₂ hH hH₁ hH₂
  let D₀ : Counterterms (Fin 3 ⊕ Fin n × Fin 3) :=
    ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0⟩
  obtain ⟨x, hx, -⟩ := existsUnique_withLevel_zero P (Lepton.leptonFlavors P H) D₀ leptonRep he
    (fun f => hm.trans_le (hmass f)) hmγ hΛ leptonRep_idem
    (leptonFlavors_sum_coeff P H hPV₁ hHPV₁) (leptonFlavors_sum_coeff_mass P H hPV₂ hHPV₂)
  obtain ⟨y, hy, -⟩ := existsUnique_withLevel_one P (Lepton.leptonFlavors P H)
    (D₀.withLevel 0 x.1 x.2) leptonRep P.m
    he hm hmass hmγ hΛ leptonRep_idem (leptonFlavors_blockPV₁ P H hPV₁ hHPV₁)
    (leptonFlavors_blockPV₂ P H hPV₂ hHPV₂) hx
  exact ⟨_, hy⟩

end Exists

/-! ### The analytic core and the reduction -/

/-- **The analytic core of (R-Π₄)**: the limit and majorant clauses of the frozen statement, for
every renormalized `D` and every form factor of `D` on `s > -4m²`. -/
def Core {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ) : Prop :=
  ∃ (Pinf : ℝ → ℂ) (C : ℝ), ∀ S₀ S η : ℝ, -(4 * P₀.m ^ 2) < S₀ → 0 < η →
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
        (∀ ℓ, RM < MH₁ ℓ) → (∀ ℓ, RM < MH₂ ℓ) → (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
        (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        ∀ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
          IsRenormalizedThrough (regP P₀ M₁ M₂ c₁ c₂ mγ Λ)
            (Lepton.leptonFlavors (regP P₀ M₁ M₂ c₁ c₂ mγ Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂)) D
            leptonRep 2 →
          ∀ Pol : ℝ → ℂ, IsPol (regP P₀ M₁ M₂ c₁ c₂ mγ Λ)
            (Lepton.leptonFlavors (regP P₀ M₁ M₂ c₁ c₂ mγ Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂)) D
            (4 * P₀.m ^ 2) Pol →
            (∀ s : ℝ, S₀ ≤ s → s ≤ S → ‖Pol s / (P₀.e : ℂ) ^ 4 - Pinf s‖ < η) ∧
            ∀ s : ℝ, 0 ≤ s →
              ‖Pol s / (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2

/-- **Reduction**: the analytic core gives the frozen statement (R-Π₄), with its binders. -/
theorem vacuumPolarizationPart_two_lepton_limit_of_core {n : ℕ}
    (P₀ : Params) (mH : Fin n → ℝ) (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hcore : Core P₀ mH) :
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
                ‖Pol s / (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2 := by
  obtain ⟨Pinf, C, hcore⟩ := hcore
  refine ⟨Pinf, C, fun S₀ S η hS₀ hη => ?_⟩
  obtain ⟨RM, hRM⟩ := hcore S₀ S η hS₀ hη
  refine ⟨RM, fun M₁ M₂ c₁ c₂ hM₁ hM₂ hR₁ hR₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hRH₁ hRH₂
    hcH₁ hcH₂ => ?_⟩
  obtain ⟨δ, hδ, R, hR⟩ := hRM M₁ M₂ c₁ c₂ hM₁ hM₂ hR₁ hR₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂
    hRH₁ hRH₂ hcH₁ hcH₂
  refine ⟨δ, hδ, R, fun mγ Λ hmγ hΛ hmγδ hRΛ => ⟨?_, fun D hD => ⟨?_, fun Pol hPol =>
    hR mγ Λ hmγ hΛ hmγδ hRΛ D hD Pol hPol⟩⟩⟩
  · exact exists_renormalized (regP P₀ M₁ M₂ c₁ c₂ mγ Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂) he hm
      hmγ hΛ hM₁ hM₂ hmH hMH₁ hMH₂ hc₁ hc₂ hcH₁ hcH₂
  · have hmass := le_leptonFlavors_mass (regP P₀ M₁ M₂ c₁ c₂ mγ Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂)
      hM₁ hM₂ hmH hMH₁ hMH₂
    exact exists_pol (regP P₀ M₁ M₂ c₁ c₂ mγ Λ) _ D leptonRep P₀.m hm hmass hmγ hΛ leptonRep_idem
      (leptonFlavors_blockPV₁ _ _ hc₁ hcH₁) (leptonFlavors_blockPV₂ _ _ hc₂ hcH₂) hD

end QED.GradedProof.RPi4

end
