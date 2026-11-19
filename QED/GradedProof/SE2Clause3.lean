/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2FormFD
public import QED.GradedProof.SE2FormVD

/-!
# Clause 3 of G-Σ₂

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57). `selfEnergyPart_two_clause3` is exactly the third conjunct of the frozen
statement: for any `A, B` with the limit property on the region, `z ↦ A(-z²) z + B(-z²) M_f` is
differentiable at `z = -M_f`.

## Proof

The order-`e⁴` self-energy has a limit `W(t)` along the time axis `p = t e₀`, `e₀ = (1, 0, 0, 0)`,
differentiable at every `t` with `t² < T²` (`hasSEFormD_selfEnergyPart`, from the eight
`ClassFormD`). On that open set the limit is also `A(-t²) t e̸₀ + B(-t²) M_f`, and `e̸₀ = -γ⁰`
has entries `(0, 2) = -1`, `(0, 0) = 0`; hence `A(-t²) t + B(-t²) M_f = W(t)₀₀ - W(t)₀₂` near
`t = -M_f` (`differentiableAt_of_hasSEFormD`).
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.SE2

open QED.WickModel QED.Graded

/-- The time axis. -/
def timeVec : Fin 4 → ℝ := ![1, 0, 0, 0]

theorem dot_smul_timeVec (t : ℝ) : Minkowski.dot (t • timeVec) (t • timeVec) = -t ^ 2 := by
  rw [dot_smul_smul]
  simp [Minkowski.dot_eq, timeVec]
  ring

theorem slash_timeVec_apply :
    Dirac.slash timeVec 0 2 = -1 ∧ Dirac.slash timeVec 0 0 = 0 := by
  simp [Dirac.slash, Minkowski.lower, Minkowski.metric, Fin.sum_univ_four, timeVec, Dirac.gamma]

/-- **Differentiability of `A(-z²) z + B(-z²) M` at `z = -M`** for a family with a limit
differentiable along lines whose limit is `A(p²) p̸ + B(p²) M` on the region. -/
theorem differentiableAt_of_hasSEFormD {T M : ℝ} {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hG : HasSEFormD T G) (hM : 0 < M) (hMT : M < T) (A B : ℝ → ℂ)
    (hAB : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε : ℝ => G ε p α β) (𝓝[>] 0)
        (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
          + (B (Minkowski.dot p p) * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) :
    DifferentiableAt ℝ (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * M) (-M) := by
  obtain ⟨W, hW⟩ := hG timeVec
  have hreg : ∀ t : ℝ, -T ^ 2 < -t ^ 2 → -T ^ 2 < Minkowski.dot (t • timeVec) (t • timeVec) :=
    fun t ht => by rwa [dot_smul_timeVec]
  have hM' : -T ^ 2 < -(-M) ^ 2 := by nlinarith
  have hopen : ∀ᶠ z in 𝓝 (-M), -T ^ 2 < -z ^ 2 :=
    (continuous_neg.comp (continuous_pow 2)).continuousAt.eventually (lt_mem_nhds hM')
  have hd := ((hW (-M) (hreg _ hM') 0 0).2.sub (hW (-M) (hreg _ hM') 0 2).2)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hopen] with z hz
  have hlim := fun α β => tendsto_nhds_unique (hAB _ (hreg z hz) α β) (hW z (hreg z hz) α β).1
  have h00 := hlim 0 0
  have h02 := hlim 0 2
  obtain ⟨s02, s00⟩ := slash_timeVec_apply
  simp only [dot_smul_timeVec, Dirac.slash_smul, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, s02, s00, Matrix.one_apply_eq] at h00 h02
  show _ = W z 0 0 - W z 0 2
  rw [← h00, ← h02]
  simp
  ring

/-- **Clause 3 of G-Σ₂**, with exactly the hypotheses and third conclusion of
`QED.Graded.selfEnergyPart_two_existsUnique`. -/
theorem selfEnergyPart_two_clause3 (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) :
    ∀ A B : ℝ → ℂ,
      (∀ p : Fin 4 → ℝ,
        -(Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
        Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f 2 p α β) (𝓝[>] 0)
          (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
            + (B (Minkowski.dot p p) * Φ.mass f) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) →
      DifferentiableAt ℝ (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * Φ.mass f)
        (-Φ.mass f) := by
  intro A B hAB
  have hν0 : 0 < min (min P.mγ P.Λ) (2 * m₀) := lt_min (lt_min hmγ hΛ) (by linarith)
  exact differentiableAt_of_hasSEFormD
    (hasSEFormD_selfEnergyPart (fun C h4 hC => classFormD_of_order_four classFormD_repR
      classFormD_repX classFormD_repV classFormD_repF classFormD_repP0 classFormD_repP1
      classFormD_repC1 classFormD_repC2 h4 C hC) P Φ D f m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂)
    (hm₀.trans_le (hmass f)) (by linarith) A B hAB

end QED.GradedProof.SE2

end
