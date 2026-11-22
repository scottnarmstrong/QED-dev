/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestLFB
public import QED.ChainProof.SetANestLFBound

/-!
# Set (a), obligation (N): the nested form of the fermion-counterterm classes `FA`, `FB`

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`. Under the hypotheses
`IntHypA` of (HA₀) and a positive mass floor, the classes `FA`, `FB` are in nested form
(`QED.ChainProof.SetANest.LoopNested`) with the photon tensors `(1/i) val0(F0)(-k)` and
`(1/i) val0(F1)(-k)`: the routing and Wick steps (`loopNested_repFA_of_bound`,
`loopNested_repFB_of_bound`) with the inner bound `OneLoopInnerBound 8 4` of the block-summed
`δ₂, δ_m` bubble (`oneLoopInnerBound_insBubble`). The group identity `hF` of `hsum_of_groups` is
`fermion_group_sum`.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetANest

open QED.WickModel QED.ChainProof.SetALink QED.ChainProof.Enum QED.GradedProof.VP2

/-- **`FA` in nested form**, with `X(k)^{ab} = (1/i) val0(F0)(-k)^{ab}`. -/
theorem loopNested_repFA (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hH : IntHypA P Φ D rep)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (p' p : Fin 4 → ℝ) :
    LoopNested P Φ D repFA (fun k a b => (1 / I) * val0 P Φ D (-k) a b repF0) p' p :=
  loopNested_repFA_of_bound P Φ D rep hH p' p (by norm_num : (0 : ℝ) ≤ 8) (by norm_num)
    (by norm_num : (3 : ℝ) < 4)
    (oneLoopInnerBound_insBubble Φ rep hm₀ hmass hH.hrep hH.hPV₁ hH.hPV₂
      (fun r => P.e ^ 2 * D.d₂ r 0) (fun r => P.e ^ 2 * D.dm r 0) hH.hε (kF P.e)
      (fun a b => Dirac.gamma b) (fun a b => Dirac.gamma a) (fun a b => isOddG_gamma b)
      (fun a b => isOddG_gamma a) (-1) (by norm_num))

/-- **`FB` in nested form**, with `X(k)^{ab} = (1/i) val0(F1)(-k)^{ab}`. -/
theorem loopNested_repFB (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (hH : IntHypA P Φ D rep)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (p' p : Fin 4 → ℝ) :
    LoopNested P Φ D repFB (fun k a b => (1 / I) * val0 P Φ D (-k) a b repF1) p' p :=
  loopNested_repFB_of_bound P Φ D rep hH p' p (by norm_num : (0 : ℝ) ≤ 8) (by norm_num)
    (by norm_num : (3 : ℝ) < 4)
    (oneLoopInnerBound_insBubble Φ rep hm₀ hmass hH.hrep hH.hPV₁ hH.hPV₂
      (fun r => P.e ^ 2 * D.d₂ r 0) (fun r => P.e ^ 2 * D.dm r 0) hH.hε (kF P.e)
      (fun a b => Dirac.gamma a) (fun a b => Dirac.gamma b) (fun a b => isOddG_gamma a)
      (fun a b => isOddG_gamma b) 1 (by norm_num))

end QED.ChainProof.SetANest

end
