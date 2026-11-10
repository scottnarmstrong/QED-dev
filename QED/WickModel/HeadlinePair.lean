/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LszAmplitude
public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Frozen.OneLoop.VertexFunction
public import QED.Frozen.Algebra.LorentzGen
public import QED.Frozen.Algebra.Lower
import QED.Frozen.WickModel.LszAmplitudeEq
import QED.Frozen.OneLoop.CountertermShift
import QED.Frozen.OneLoop.FormFactorExistsUnique
import QED.WickModel.HeadlineSpinor
import QED.Algebra.Spinor
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Form-factor pairs of the LSZ amplitude

An internal copy `QED.WickModel.Headline.LszPair` of the on-shell form-factor decomposition of
the LSZ amplitude (L₂): `(A, B)` decomposes `M^μ_{s's}(p', p)` if
`M^μ_{s's}(p', p) = e ū_{s'}(p') [A γ^μ - (i/m) B S^{μν} q_ν] u_s(p)` for all spins and `μ`.

By the sealed closed form (L₃), `M = ū' V u + e κ ū' γ^μ u` with `V` the vertex function (J) at
`Z₁ = 1 + δ₁` and `κ = q² D(q²) Π(q²)` the photon-leg coefficient. The photon-leg term only
shifts the `γ^μ` coefficient, and the on-shell spinors span the Dirac solution spaces
(`QED.WickModel.Headline.sandwich_eq_zero_of_spinor`), so `(A, B)` decomposes the LSZ amplitude
if and only if `(A - κ, B)` is a form-factor pair (G₀) of `V`, and by the sealed (N) if and only
if `(A - κ - Z₁, B)` is a form-factor pair of the one-loop vertex (F).

## Main statements

* `QED.WickModel.Headline.LszPair`: the internal copy of the LSZ form-factor decomposition.
* `QED.WickModel.Headline.lszPair_iff_isFormFactorPair_vertexFunction`: the pairs of the LSZ
  amplitude are those of the vertex function, shifted by the photon-leg coefficient.
* `QED.WickModel.Headline.lszPair_iff_isFormFactorPair_vertexOneLoop`: the same, for the
  one-loop vertex.
* `QED.WickModel.Headline.existsUnique_lszPair`: for `e ≠ 0` and `q² > 0` the LSZ amplitude has
  exactly one form-factor pair; by the sealed (G).

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex

namespace QED.WickModel

/-- **Internal copy of the on-shell form-factor decomposition of the LSZ amplitude**: the pair
`F = (A, B)` decomposes the LSZ amplitude (L₂) at the on-shell positive-energy momenta `(p', p)`
if `M^μ_{s's}(p', p) = e ū_{s'}(p') [A γ^μ - (i/m) B S^{μν} q_ν] u_s(p)` for all spins `s'`,
`s` and every `μ`, with `q = p' - p`. -/
def Headline.LszPair (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (F : ℂ × ℂ) : Prop :=
  ∀ (s' s : Fin 2) (μ : Fin 4),
    lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ =
      (P.e : ℂ) * (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
        ((F.1 • Dirac.gamma μ - (I / (P.m : ℂ) * F.2) •
          ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ
            Dirac.spinor P.m p s))

/-- The photon-leg coefficient `κ = q² D(q²) Π(q²)` of the closed form (L₃) of the LSZ
amplitude, with `D(q²) = 1/(q² + m_γ²) - 1/(q² + Λ²)` and `Π` the vacuum polarization (Z₇). -/
noncomputable def Headline.photonLegCoeff (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) : ℂ :=
  ((Minkowski.dot (p' - p) (p' - p) *
      ((Minkowski.dot (p' - p) (p' - p) + P.mγ ^ 2)⁻¹
        - (Minkowski.dot (p' - p) (p' - p) + P.Λ ^ 2)⁻¹) : ℝ) : ℂ)
    * vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂ ⟨Minkowski.dot (p' - p) (p' - p),
        lt_of_lt_of_le (neg_lt_zero.mpr (mul_pos four_pos (pow_pos hm 2)))
          (Minkowski.dot_sub_self_nonneg_of_onShell hp' hp hp0' hp0)⟩

/-- The closed form (L₃) with the photon-leg coefficient named:
`M^μ_{s's}(p', p) = ū_{s'}(p') V^μ u_s(p) + e κ ū_{s'}(p') γ^μ u_s(p)`. -/
theorem Headline.lszAmplitude_eq_photonLegCoeff (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (s' s : Fin 2)
    (μ : Fin 4) :
    lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ =
      Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
          (QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0'
            hp0 μ *ᵥ Dirac.spinor P.m p s)
        + (P.e : ℂ) * Headline.photonLegCoeff P hm hM₁ hM₂ hPV₁ hPV₂ p' p hp' hp hp0' hp0
          * (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ (Dirac.gamma μ *ᵥ Dirac.spinor P.m p s)) := by
  rw [lszAmplitude_eq, Headline.photonLegCoeff]
  ring

/-- The sandwich of the form-factor structure, expanded:
`w [A γ^μ - (i/m) B S^{μν} q_ν] u = A (w γ^μ u) - (i/m) B (w S^{μν} q_ν u)`. -/
theorem Headline.dotProduct_formFactor_mulVec (w u : Fin 4 → ℂ) (m : ℝ) (p' p : Fin 4 → ℝ)
    (A B : ℂ) (μ : Fin 4) :
    w ⬝ᵥ ((A • Dirac.gamma μ - (I / (m : ℂ) * B) •
        ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ u) =
      A * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) - I / (m : ℂ) * B *
        (w ⬝ᵥ ((∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ u)) := by
  simp only [sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]

/-- **The pairs of the LSZ amplitude are those of the vertex function, shifted by the
photon-leg coefficient.** For on-shell positive-energy momenta, `(A, B)` decomposes the LSZ
amplitude if and only if `(A - κ, B)` is a form-factor pair (G₀) of the vertex function (J) at
`Z₁ = 1 + δ₁`, with `κ = q² D(q²) Π(q²)`. -/
theorem Headline.lszPair_iff_isFormFactorPair_vertexFunction (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (F : ℂ × ℂ) :
    Headline.LszPair P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F ↔
      QED.OneLoop.IsFormFactorPair P.e P.m p' p
        (QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0' hp0)
        (F.1 - Headline.photonLegCoeff P hm hM₁ hM₂ hPV₁ hPV₂ p' p hp' hp hp0' hp0, F.2) := by
  set κ := Headline.photonLegCoeff P hm hM₁ hM₂ hPV₁ hPV₂ p' p hp' hp hp0' hp0 with hκ
  set V := QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0'
    hp0 with hV
  set S : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
    fun μ => ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν with hS
  constructor
  · intro h μ u w hu hw
    have key := Headline.sandwich_eq_zero_of_spinor hm hp' hp hp0' hp0
      (X := V μ - (P.e : ℂ) • ((F.1 - κ) • Dirac.gamma μ - (I / (P.m : ℂ) * F.2) • S μ))
      (fun s' s => by
        have h1 := h s' s μ
        rw [Headline.lszAmplitude_eq_photonLegCoeff, Headline.dotProduct_formFactor_mulVec]
          at h1
        rw [sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
          Headline.dotProduct_formFactor_mulVec]
        linear_combination h1) hu hw
    rw [sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      sub_eq_zero] at key
    exact key
  · intro h s' s μ
    have h1 := h μ _ _ (Dirac.slash_mulVec_spinor P.m p hp s)
      (Dirac.bar_vecMul_slash P.m p' _ (Dirac.slash_mulVec_spinor P.m p' hp' s'))
    rw [Headline.dotProduct_formFactor_mulVec] at h1
    rw [Headline.lszAmplitude_eq_photonLegCoeff, Headline.dotProduct_formFactor_mulVec, ← hV, h1]
    ring

/-- **The pairs of the LSZ amplitude are those of the one-loop vertex, shifted.** For on-shell
positive-energy momenta, `(A, B)` decomposes the LSZ amplitude if and only if
`(A - κ - Z₁, B)` is a form-factor pair (G₀) of the one-loop vertex (F), with
`κ = q² D(q²) Π(q²)` and `Z₁ = 1 + δ₁`; by the sealed (N). In particular the Pauli components
agree. -/
theorem Headline.lszPair_iff_isFormFactorPair_vertexOneLoop (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (F : ℂ × ℂ) :
    Headline.LszPair P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F ↔
      QED.OneLoop.IsFormFactorPair P.e P.m p' p
        (QED.OneLoop.vertexOneLoop P.e P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0' hp0)
        (F.1 - Headline.photonLegCoeff P hm hM₁ hM₂ hPV₁ hPV₂ p' p hp' hp hp0' hp0
          - ((1 + P.δ₁ : ℝ) : ℂ), F.2) := by
  rw [Headline.lszPair_iff_isFormFactorPair_vertexFunction,
    QED.OneLoop.isFormFactorPair_vertexOneLoop_iff_vertexFunction P.e (1 + P.δ₁)]
  have h : ((1 + P.δ₁ : ℝ) : ℂ) + (F.1 - Headline.photonLegCoeff P hm hM₁ hM₂ hPV₁ hPV₂ p' p hp'
      hp hp0' hp0 - ((1 + P.δ₁ : ℝ) : ℂ)) =
      F.1 - Headline.photonLegCoeff P hm hM₁ hM₂ hPV₁ hPV₂ p' p hp' hp hp0' hp0 := by ring
  rw [h]

/-- **The LSZ amplitude has exactly one form-factor pair** for `e ≠ 0` and on-shell
positive-energy momenta with `q² > 0`; by the sealed (G) and
`QED.WickModel.Headline.lszPair_iff_isFormFactorPair_vertexOneLoop`. -/
theorem Headline.existsUnique_lszPair (P : Params) (he : P.e ≠ 0) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    ∃! F : ℂ × ℂ, Headline.LszPair P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 F := by
  set κ := Headline.photonLegCoeff P hm hM₁ hM₂ hPV₁ hPV₂ p' p hp' hp hp0' hp0 with hκ
  obtain ⟨G, hG, huniq⟩ := QED.OneLoop.existsUnique_isFormFactorPair_vertexOneLoop P.e P.m P.mγ
    P.Λ he hm hmγ hΛ p' p hp' hp hp0' hp0 hq
  refine ⟨(G.1 + κ + ((1 + P.δ₁ : ℝ) : ℂ), G.2), ?_, fun F hF => ?_⟩
  · beta_reduce
    rw [Headline.lszPair_iff_isFormFactorPair_vertexOneLoop, ← hκ]
    have h : G.1 + κ + ((1 + P.δ₁ : ℝ) : ℂ) - κ - ((1 + P.δ₁ : ℝ) : ℂ) = G.1 := by ring
    rw [h]
    exact hG
  · beta_reduce at hF
    rw [Headline.lszPair_iff_isFormFactorPair_vertexOneLoop, ← hκ] at hF
    have h := huniq _ hF
    rw [← h]
    ext
    · simp only
      ring
    · rfl

end QED.WickModel

end
