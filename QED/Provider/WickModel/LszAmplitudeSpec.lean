/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.LszAmplitude
public import QED.Frozen.WickModel.LszAmplitudeExistsUnique
public import QED.Frozen.WickModel.VacuumPolarization
public import QED.Frozen.OneLoop.VertexFunction
public import QED.Frozen.OneLoop.IsResponseMagneticMoment
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.Frozen.OneLoop.PacketNormSq
public import QED.OneLoop.OneParticle
public import QED.Algebra.OnShell
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support

/-!
# Provider for `QED.WickModel.lszAmplitude_spec`

Proves packet 6c-2's characterization (L₂′) (decision D-31) as
`QED.Provider.WickModel.lszAmplitude_spec`, with the binder convention of decision D-13. It follows
directly from the existence and uniqueness of the sealed theorem (L₁). This module must never import
the frozen anchor.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.Provider.WickModel

open QED.WickModel in
/-- Packet 6c-2's (L₂′), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem lszAmplitude_spec {P : Params} (hm : 0 < P.m := by assumption)
    (hmγ : 0 < P.mγ := by assumption) (hΛ : 0 < P.Λ := by assumption)
    (hM₁ : P.m < P.M₁ := by assumption) (hM₂ : P.m < P.M₂ := by assumption)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption)
    (hon : IsElectronOnShell P hm hmγ hΛ := by assumption) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2 := by assumption)
    (hp : Minkowski.dot p p = -P.m ^ 2 := by assumption) (hp0' : 0 < p' 0 := by assumption)
    (hp0 : 0 < p 0 := by assumption) {s' s : Fin 2} {μ : Fin 4} :
    (∀ η > 0, ∃ δ > 0, ∀ r' r : Fin 4 → ℝ,
        Minkowski.dot r' r' ≠ -P.m ^ 2 → Minkowski.dot r r ≠ -P.m ^ 2 →
        dist r' p' < δ → dist r p < δ →
        ∃ G : ℂ, Tendsto (fun ε : ℝ => (1 / I) *
            (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
              (Matrix.of (fun α β => connectedFunction { P with ε := ε } 1 1 3 ![r'] ![r]
                ![r' - r] ![α] ![β] ![μ]) *ᵥ Dirac.spinor P.m p s)))
          (𝓝[>] 0) (𝓝 G) ∧
          ‖G - lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ‖ < η) ∧
    ∀ M : ℂ, (∀ η > 0, ∃ δ > 0, ∀ r' r : Fin 4 → ℝ,
        Minkowski.dot r' r' ≠ -P.m ^ 2 → Minkowski.dot r r ≠ -P.m ^ 2 →
        dist r' p' < δ → dist r p < δ →
        ∃ G : ℂ, Tendsto (fun ε : ℝ => (1 / I) *
            (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
              (Matrix.of (fun α β => connectedFunction { P with ε := ε } 1 1 3 ![r'] ![r]
                ![r' - r] ![α] ![β] ![μ]) *ᵥ Dirac.spinor P.m p s)))
          (𝓝[>] 0) (𝓝 G) ∧
          ‖G - M‖ < η) →
      M = lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ := by
  have h := (QED.WickModel.lszAmplitude_existsUnique P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon).2 p' p
    hp' hp hp0' hp0 s' s μ
  exact ⟨h.exists.choose_spec, fun M hM => h.unique hM h.exists.choose_spec⟩

end QED.Provider.WickModel

end
