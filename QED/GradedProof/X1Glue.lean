/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsLSZAmplitudePart
public import QED.WickModel.LszLimit

/-!
# (X₁): the LSZ amplitude from an off-shell limit function

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57). The LSZ amplitude (G-L₁) `QED.Graded.IsLSZAmplitudePart` is an `η`-`δ`
statement about the iterated limit of the sandwiched order-`K` connected function `sandwich`:
first `ε → 0⁺` at off-shell `(r', r)`, then `(r', r) → (p', p)`. As for the one-loop LSZ
amplitude (`QED.WickModel.LszLimit`):

* `isLSZAmplitudePart_of_tendsto`: a function `G` of the off-shell pairs that is the inner limit
  near `(p', p)` and tends to `M s' s μ` at the shell gives (G-L₁) for `M`;
* `eq_of_isLSZAmplitudePart`: the amplitude is unique (for a nonzero open-line mass and on-shell
  `p'`, `p`), since near the shell there are off-shell pairs;
* `exists_and_eq_zero_of_tendsto`: the conclusion of (X₁) from such limit functions tending
  to `0`.
-/

@[expose] public section

open Matrix Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X1

variable {F : Type} [Fintype F] [DecidableEq F]

/-- The sandwiched order-`K` connected function of (G-L₁) at the prescription `ε`, outgoing
momentum `r'`, incoming momentum `r` and photon momentum `r' - r`, between the spinors at the
limit momenta `p'`, `p`. -/
noncomputable def sandwich (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F) (K : ℕ)
    (p' p : Fin 4 → ℝ) (s' s : Fin 2) (μ : Fin 4) (r' r : Fin 4 → ℝ) (ε : ℝ) : ℂ :=
  (1 / I) *
    (Dirac.bar (Dirac.spinor (Φ.mass Φ.openLine) p' s') ⬝ᵥ
      (Matrix.of (fun α β => connectedPart { P with ε := ε } Φ D 1 1 K ![r'] ![r]
        ![r' - r] ![α] ![β] ![μ]) *ᵥ Dirac.spinor (Φ.mass Φ.openLine) p s))

/-- **(G-L₁) from an off-shell limit function.** If for every `s'`, `s`, `μ` a function `G` of
the pairs `(r', r)` is the `ε → 0⁺` limit of `sandwich` at every off-shell pair near `(p', p)`
and tends to `M s' s μ` as `(r', r) → (p', p)` through off-shell pairs, then `M` is the
order-`K` LSZ amplitude at `(p', p)`. -/
theorem isLSZAmplitudePart_of_tendsto {P : Params} {Φ : Lepton.Flavors F} {D : Counterterms F}
    {K : ℕ} {p' p : Fin 4 → ℝ} {M : Fin 2 → Fin 2 → Fin 4 → ℂ}
    (h : ∀ (s' s : Fin 2) (μ : Fin 4), ∃ G : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℂ,
      (∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p),
        Minkowski.dot x.1 x.1 ≠ -Φ.mass Φ.openLine ^ 2 →
        Minkowski.dot x.2 x.2 ≠ -Φ.mass Φ.openLine ^ 2 →
          Tendsto (sandwich P Φ D K p' p s' s μ x.1 x.2) (𝓝[>] 0) (𝓝 (G x))) ∧
      Tendsto G (𝓝[WickModel.LszLimit.offShellPairs (Φ.mass Φ.openLine)] (p', p))
        (𝓝 (M s' s μ))) :
    IsLSZAmplitudePart P Φ D K p' p M := by
  intro s' s μ
  obtain ⟨G, h1, h2⟩ := h s' s μ
  exact WickModel.LszLimit.etaDelta_of_tendsto h1 h2

/-- **The LSZ amplitude is unique**, for a nonzero open-line mass and on-shell `p'`, `p`. -/
theorem eq_of_isLSZAmplitudePart {P : Params} {Φ : Lepton.Flavors F} {D : Counterterms F}
    {K : ℕ} {p' p : Fin 4 → ℝ} {M₁ M₂ : Fin 2 → Fin 2 → Fin 4 → ℂ}
    (hm : Φ.mass Φ.openLine ≠ 0) (hp' : Minkowski.dot p' p' = -Φ.mass Φ.openLine ^ 2)
    (hp : Minkowski.dot p p = -Φ.mass Φ.openLine ^ 2)
    (h₁ : IsLSZAmplitudePart P Φ D K p' p M₁) (h₂ : IsLSZAmplitudePart P Φ D K p' p M₂) :
    M₁ = M₂ := by
  funext s' s μ
  exact WickModel.LszLimit.eq_of_etaDelta (F := sandwich P Φ D K p' p s' s μ) hm hp' hp
    (h₁ s' s μ) (h₂ s' s μ)

/-- **The conclusion of (X₁) from off-shell limit functions tending to `0`.** -/
theorem exists_and_eq_zero_of_tendsto {P : Params} {Φ : Lepton.Flavors F} {D : Counterterms F}
    {K : ℕ} {p : Fin 4 → ℝ} (hm : Φ.mass Φ.openLine ≠ 0)
    (hp : Minkowski.dot p p = -Φ.mass Φ.openLine ^ 2)
    (h : ∀ (s' s : Fin 2) (μ : Fin 4), ∃ G : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℂ,
      (∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p, p),
        Minkowski.dot x.1 x.1 ≠ -Φ.mass Φ.openLine ^ 2 →
        Minkowski.dot x.2 x.2 ≠ -Φ.mass Φ.openLine ^ 2 →
          Tendsto (sandwich P Φ D K p p s' s μ x.1 x.2) (𝓝[>] 0) (𝓝 (G x))) ∧
      Tendsto G (𝓝[WickModel.LszLimit.offShellPairs (Φ.mass Φ.openLine)] (p, p)) (𝓝 0)) :
    (∃ M, IsLSZAmplitudePart P Φ D K p p M) ∧
      ∀ M, IsLSZAmplitudePart P Φ D K p p M → M = 0 := by
  have h0 : IsLSZAmplitudePart P Φ D K p p 0 := isLSZAmplitudePart_of_tendsto h
  exact ⟨⟨0, h0⟩, fun M hM => eq_of_isLSZAmplitudePart hm hp hp hM h0⟩

end QED.GradedProof.X1

end
