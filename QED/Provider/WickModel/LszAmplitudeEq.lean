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
import QED.WickModel.LszLimit

/-!
# Provider for `QED.WickModel.lszAmplitude_eq`

Proves packet 6c-2's theorem goal (L₃) (decision D-31) as
`QED.Provider.WickModel.lszAmplitude_eq`, with the binder convention of decision D-13. By the
uniqueness in the sealed theorem (L₁), it suffices that the closed form has the limit property,
which is `QED.WickModel.lszLimit_closedForm`. This module must never import the frozen anchor.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory
open scoped ContDiff

namespace QED.Provider.WickModel

open QED.WickModel in
/-- Packet 6c-2's (L₃), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem lszAmplitude_eq {P : Params} (hm : 0 < P.m := by assumption)
    (hmγ : 0 < P.mγ := by assumption) (hΛ : 0 < P.Λ := by assumption)
    (hM₁ : P.m < P.M₁ := by assumption) (hM₂ : P.m < P.M₂ := by assumption)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0 := by assumption)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0 := by assumption)
    (hon : IsElectronOnShell P hm hmγ hΛ := by assumption) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2 := by assumption)
    (hp : Minkowski.dot p p = -P.m ^ 2 := by assumption) (hp0' : 0 < p' 0 := by assumption)
    (hp0 : 0 < p 0 := by assumption) {s' s : Fin 2} {μ : Fin 4} :
    lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ =
      Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
          (QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0'
            hp0 μ *ᵥ Dirac.spinor P.m p s)
        + (P.e : ℂ) * ((Minkowski.dot (p' - p) (p' - p) *
            ((Minkowski.dot (p' - p) (p' - p) + P.mγ ^ 2)⁻¹
              - (Minkowski.dot (p' - p) (p' - p) + P.Λ ^ 2)⁻¹) : ℝ) : ℂ)
          * vacuumPolarization P hm hM₁ hM₂ hPV₁ hPV₂ ⟨Minkowski.dot (p' - p) (p' - p),
              lt_of_lt_of_le (neg_lt_zero.mpr (mul_pos four_pos (pow_pos hm 2)))
                (Minkowski.dot_sub_self_nonneg_of_onShell hp' hp hp0' hp0)⟩
          * (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ (Dirac.gamma μ *ᵥ Dirac.spinor P.m p s)) := by
  have h := (QED.WickModel.lszAmplitude_existsUnique P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon).2 p' p
    hp' hp hp0' hp0 s' s μ
  exact h.unique h.exists.choose_spec
    (lszLimit_closedForm P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ)

end QED.Provider.WickModel

end
