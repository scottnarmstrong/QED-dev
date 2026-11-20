/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1DCt
public import QED.GradedProof.X1DVertex
public import QED.GradedProof.LevelOneCharge
public import QED.Frozen.Wick.WickVertexEq

/-!
# (X₁) piece E: the order-`3` graded vertex off the mass shell

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece E. The order-`3` graded vertex (G₈ᵥ) `vertexPart … f 1` is, entrywise and
at every `ε` and all momenta, `(1/i)` times the Wick vertex at the open-line level-`0` data minus
the tree (`QED.GradedProof.vertexPart_one_apply`); by the sealed (W₁) `QED.Wick.wickVertex_eq` it
is a multiple of `γ^μ` plus `(1/i)` times the energy-first integral of the one-loop integrand at
mass `M_f`. That integral has an off-shell limit near an on-shell positive-energy pair, continuous
at the pair (`QED.GradedProof.X1D.offLim_vertexValue`). So (`exists_vertexPart_one_offShell`):
the order-`3` vertex at `x = (r', r)` near `(p', p)` converges as `ε → 0⁺` to `V x`, with `V`
continuous at `(p', p)`.
-/

@[expose] public section

open Complex Filter Topology Matrix
open QED.Graded
open QED.WickModel (Params)

namespace QED.GradedProof.X1D

/-- The order-`3` vertex entry as a constant multiple of `γ^μ` plus `(1/i)` times the one-loop
vertex value at mass `M_f`. -/
theorem vertexPart_one_apply_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    vertexPart P Φ D f 1 p' p μ i j =
      ((P.e ^ 2 * D.d₁ f 0 * P.e : ℝ) : ℂ) * Dirac.gamma μ i j +
        (1 / I) * QED.TwoLoop.Insertion.vertexValue { P with m := Φ.mass f } p' p μ i j := by
  rw [vertexPart_one_apply, QED.Wick.wickVertex_eq]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    QED.TwoLoop.Insertion.vertexValue]
  push_cast
  field_simp
  change _ = _ + QED.OneLoop.energyFirstIntegral fun ℓ =>
    QED.OneLoop.vertexIntegrand P.e (Φ.mass f) P.mγ P.Λ P.ε p' p μ ℓ i j
  ring

/-- **(X₁) piece E: the order-`3` graded vertex off the shell, with a continuous limit**, for
`M_f, m_γ, Λ > 0` and an on-shell positive-energy pair `(p', p)` of flavour `f`. -/
theorem exists_vertexPart_one_offShell (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (hm : 0 < Φ.mass f) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -Φ.mass f ^ 2)
    (hp' : Minkowski.dot p' p' = -Φ.mass f ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0) :
    ∃ V : (Fin 4 → ℝ) × (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ᶠ x in 𝓝 (p', p), ∀ μ, Tendsto (fun ε => vertexPart { P with ε := ε } Φ D f 1 x.1 x.2 μ)
        (𝓝[>] 0) (𝓝 (V x μ))) ∧ ContinuousAt V (p', p) := by
  set P' : Params := { P with m := Φ.mass f }
  have hf : ContinuousAt (fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => (![x.1, x.2] : Fin 2 → Fin 4 → ℝ))
      (p', p) := by
    refine continuous_pi (fun s => ?_) |>.continuousAt
    fin_cases s
    · exact continuous_fst
    · exact continuous_snd
  have key : ∀ μ i j, OffLim (fun ε (x : (Fin 4 → ℝ) × (Fin 4 → ℝ)) =>
      vertexPart { P with ε := ε } Φ D f 1 x.1 x.2 μ i j) (p', p) := fun μ i j => by
    have h := OffLim.comp
      (F := fun ε (y : Fin 2 → Fin 4 → ℝ) =>
        QED.TwoLoop.Insertion.vertexValue { P' with ε := ε } (y 0) (y 1) μ i j)
      (f := fun x : (Fin 4 → ℝ) × (Fin 4 → ℝ) => (![x.1, x.2] : Fin 2 → Fin 4 → ℝ))
      (z₀ := (p', p)) (offLim_vertexValue P' hm hmγ hΛ hp hp' hp0 hp0' μ i j) hf
    have hc : OffLim (fun (_ : ℝ) (_ : (Fin 4 → ℝ) × (Fin 4 → ℝ)) =>
        ((P.e ^ 2 * D.d₁ f 0 * P.e : ℝ) : ℂ) * Dirac.gamma μ i j) (p', p) :=
      ⟨fun _ => _, Eventually.of_forall fun _ => tendsto_const_nhds, continuousAt_const⟩
    refine (hc.add (h.const_mul (1 / I))).congr fun x ε _ => ?_
    rw [vertexPart_one_apply_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rfl
  exact exists_matrix_of_offLim key

end QED.GradedProof.X1D

end
