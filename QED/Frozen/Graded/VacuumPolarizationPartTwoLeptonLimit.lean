-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.LeptonRep
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Lepton.LeptonFlavors
public import QED.Provider.Graded.VacuumPolarizationPartTwoLeptonLimit

@[expose] public section

open Filter Topology
open QED.WickModel (Params)

namespace QED.Graded

/-- (R-Π₄) **The renormalized two-loop vacuum polarization `Π̂⁽⁴⁾(s)`: regulator limit and a
uniform majorant** (memo section 3; ruling S7: a reusable object with fixed-regulator, limit and
majorant clauses; decision D-54.3; the order of limits of D-37.4 and D-49.2). Fix the model data
`P₀` with `e ≠ 0` and electron mass `m > 0`, and `n` heavy leptons with masses `m_ℓ > m`; each
lepton has its own regulator pair with the Pauli–Villars conditions at its mass, as in (HM₂), and
the counterterms are those of the per-lepton scheme `leptonRep` (G₁₂′) renormalized through order
`e⁴` (G₁₂), so that `Π̂⁽⁴⁾(0) = 0` by the order-`e⁴` photon condition. Then there are a function
`Pinf` (`Π_∞`) and a constant `C` such that:
* (limit) for every compact interval `[S₀, S]` of the region `s > -4m²` and every `η > 0` there
  is `R_M` such that for all regulator fermions heavier than their leptons and than `R_M` there
  are `δ > 0` and `R` such that for `0 < m_γ < δ` and `Λ > R`: renormalized counterterms exist,
  and for every choice of them the `ε → 0⁺` limit of the order-`e⁴` vacuum polarization (G₈ₚ) has
  a transverse form `Π(k²) (k² g^{μν} - k^μ k^ν)` on the region, and every such `Π` satisfies
  `|Π(s)/e⁴ - Π_∞(s)| < η` on `[S₀, S]`;
* (majorant) every such `Π` also satisfies `|Π(s)/e⁴| ≤ C (1 + ln(1 + s/m²))²` for all
  spacelike `s ≥ 0`, uniformly in the regulators beyond those thresholds; this is what an
  insertion into an outer energy-first integral consumes by dominated convergence.
The existence of the fixed-regulator transverse form is (G-Π₂). `Pinf` (`Π_∞`) is the sum of the
Källén–Sabry functions of the electron and of the heavy leptons, normalized by `e⁴`; that
identification, and the spectral representation, are deferred until the Källén–Sabry source is
pinned (design note, deferred item D6). The statement is exact without them: the limit is unique
where it exists. **Domain.** The limit clause is for `s > -4m²` (spacelike, and timelike below the
electron pair threshold, on compact intervals) and the majorant for spacelike `s ≥ 0`. The timelike
region above threshold, where `Π̂⁽⁴⁾` has an imaginary part, is deferred (author question Q6): the
planned consumers, the set (a) chain integral after the Wick rotation and the dispersive (spectral)
form, evaluate `Π̂⁽⁴⁾` only at `s ≥ 0` or through its spectral function. -/
theorem vacuumPolarizationPart_two_lepton_limit {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ) :
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
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.vacuumPolarizationPart_two_lepton_limit
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
