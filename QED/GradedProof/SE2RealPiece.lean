/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2RealParam
public import QED.GradedProof.SE2RealLim
public import QED.GradedProof.SE2SEChain
public import QED.TwoLoop.ParametricBridge

/-!
# `♯`-symmetric limits of self-energy pieces, and `♯` on the numerator building blocks

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `SEReal`.

* `SEPiece.hasSharpLim`: a family that is eventually `h(ε)` times the joint integral of a
  self-energy piece with `N♯ = c N` and `h(ε) → h₀` with `h₀` real has a limit with phase `c`.
* The numerator building blocks are `♯`-fixed: the electron numerator `m - p̸`
  (`sharp_electronNumerator`) and the self-energy chain `∑ D_{νρ} γ^ρ A γ^ν` of a `♯`-fixed `A`
  with a real photon tensor `D` (`sharp_seChain`); traces of `♯`-fixed matrices are real
  (`conj_trace_of_sharp`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.SE2Real

open QED.Integration.TwoLoop QED.GradedProof.SE2

/-- **The limit of a piece with a `♯`-symmetric numerator**, times a factor `h(ε) → h₀` with
`h̄₀ = d h₀`: the phase is `d c`. -/
theorem SEPiece.hasSharpLim' {T : ℝ} (P : SEPiece T) {c : ℂ}
    (hN : ∀ p ℓ, sharp (P.N p ℓ) = c • P.N p ℓ) {h : ℝ → ℂ} {h₀ d : ℂ}
    (hh : Tendsto h (𝓝[>] 0) (𝓝 h₀)) (hd : starRingEnd ℂ h₀ = d * h₀)
    {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hG : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ i j : Fin 4,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε p i j = h ε * QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.N p ℓ i j * ∏ k, (lineDenom P.D.α (P.D.mom p) P.D.M ε k ℓ)⁻¹)) :
    HasSharpLim T (d * c) G := by
  refine ⟨fun p => h₀ • P.W p, fun p hp => ⟨fun i j => ?_, ?_⟩⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]
    exact (hh.mul (P.tendsto hp i j)).congr' (by
      filter_upwards [hG p hp i j] with ε hε
      exact hε.symm)
  · rw [sharp_smul, hd, SEPiece.sharp_W P hN hp, smul_smul, smul_smul]
    congr 1
    ring

/-- **The limit of a piece with a `♯`-symmetric numerator**, times a factor with a real limit. -/
theorem SEPiece.hasSharpLim {T : ℝ} (P : SEPiece T) {c : ℂ}
    (hN : ∀ p ℓ, sharp (P.N p ℓ) = c • P.N p ℓ) {h : ℝ → ℂ} {h₀ : ℝ}
    (hh : Tendsto h (𝓝[>] 0) (𝓝 (h₀ : ℂ))) {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hG : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ i j : Fin 4,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε p i j = h ε * QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.N p ℓ i j * ∏ k, (lineDenom P.D.α (P.D.mom p) P.D.M ε k ℓ)⁻¹)) :
    HasSharpLim T c G := by
  have := SEPiece.hasSharpLim' P hN hh (d := 1) (by rw [Complex.conj_ofReal, one_mul]) hG
  rwa [one_mul] at this

/-! ### The numerator building blocks -/

theorem sharp_electronNumerator (m : ℝ) (p : Fin 4 → ℝ) :
    sharp (QED.TwoLoop.Bridge.electronNumerator m p) =
      QED.TwoLoop.Bridge.electronNumerator m p := by
  rw [QED.TwoLoop.Bridge.electronNumerator, sharp_sub, sharp_smul, sharp_one, sharp_slash,
    Complex.conj_ofReal]

/-- **The self-energy chain of a `♯`-fixed matrix with a real photon tensor is `♯`-fixed.** -/
theorem sharp_seChain {A : Matrix (Fin 4) (Fin 4) ℂ} (hA : sharp A = A)
    {D : Fin 4 → Fin 4 → ℂ} (hD : ∀ ν ρ, starRingEnd ℂ (D ν ρ) = D ν ρ) :
    sharp (seChain A D) = seChain A D := by
  simp only [seChain, sharp_sum, sharp_smul, sharp_mul, sharp_gamma, hA, hD]

/-- The trace of a `♯`-fixed matrix is real. -/
theorem conj_trace_of_sharp {X : Matrix (Fin 4) (Fin 4) ℂ} (hX : sharp X = X) :
    starRingEnd ℂ (trace X) = trace X := by
  rw [← trace_sharp, hX]

end QED.GradedProof.SE2Real

end
