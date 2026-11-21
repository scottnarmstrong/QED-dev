/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsVPSelfEnergy
public import QED.Frozen.Graded.IsOnShellSelAt
public import QED.Frozen.Graded.IsChargeNormalizedSelAt
public import QED.Frozen.Graded.CountertermsWithLevel
public import QED.Frozen.VPChain.IsVPChain
public import QED.Frozen.WickModel.IsOnePI

@[expose] public section

open QED.WickModel (Params IsOnePI)

namespace QED.ThreeLoop

/-- (Sc₂) **The vacuum-polarization share of the level-`1` counterterms** (questions Q-c1 of
`SETC-KERNEL-PLAN.md`, (G₁₄); rulings S4, S5 of the Stage 2 design note; Srednicki (62.27),
(62.36)–(62.38), (63.1)–(63.2)). The triple `s = (d₁ˢ, d₂ˢ, d_mˢ)` is a VP share of the open-line
flavour's level-`1` counterterms for the data `D` if, with the level-`1` fermion counterterms of
`D` replaced by `s` (and `d₃ 1` kept), the order-`e⁴` on-shell conditions (Gs₂) hold for the
vacuum-polarization family of the self-energy (Sc₁) together with its level-`1` tree graph (a single
counterterm vertex, here the level-`1` `fermionCt`), and the order-`e⁵` charge condition (Gs₃)
holds for the vacuum-polarization family of the vertex (the one-insertion chains (C₁) of Stage 1a,
`IsVPChain 1`) together with its level-`1` tree graph (the level-`1` `gaugeCt`). Both families are
filtered by 1PI. The conditions are affine in `s` with the tree coefficients of (G-ex₂), so for
`e ≠ 0` they fix `s` (goal (G-ex-s)). Only the open-line entries of the replaced level are read by
these graphs: a level-`1` counterterm on a closed loop has order at least `6`. Physically `s` is
the part of the on-shell order-`e⁴` counterterms `δ₁⁽⁴⁾, δ₂⁽⁴⁾, δ_m⁽⁴⁾` that renormalizes the
two-loop self-energy and vertex subgraphs with a vacuum-polarization insertion: the counterterms
set (c) needs where the bubble sits inside a divergent subgraph. -/
def IsVPShareOnShell (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (s : ℝ × ℝ × ℝ) : Prop :=
  Graded.IsOnShellSelAt P Φ (D.withLevel 1 (fun _ => s) (D.d₃ 1))
      (fun {_ κ} C _ => IsOnePI C ∧ (IsVPSelfEnergy C ∨ ∀ t, κ t ≠ .gauge)) Φ.openLine 2 ∧
    Graded.IsChargeNormalizedSelAt P Φ (D.withLevel 1 (fun _ => s) (D.d₃ 1))
      (fun {_ κ} C _ => IsOnePI C ∧ (VPChain.IsVPChain 1 C ∨ ∀ t, κ t ≠ .gauge)) Φ.openLine 2

end QED.ThreeLoop

end
