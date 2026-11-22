/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersGamma
public import QED.DimReg.MasslessBubble
public import QED.DimReg.OneLoopClosedForm

/-!
# Set (e) of `A₁⁽⁶⁾`: the master `I₁₇`, a product of one-loop `Γ`-function closed forms

**The integral.** Laporta–Remiddi (Phys. Lett. B 379 (1996) 283, arXiv:hep-ph/9602417; the list
of basic integrals before their eq. (14)) define

  `I₁₇ = ((-i) / π ^ (n - 2))³ ∫ dⁿk₁ dⁿk₂ dⁿk₃ 1 / (D₃ D₆ D₇ D₈)`,

with (their eq. (9), `m = 1`, `p² = -1`) `D₃ = (p - k₁ - k₂ - k₃)² + 1`, `D₆ = k₁²`, `D₇ = k₂²`,
`D₈ = k₃²`; the normalization is the one of `QED.DimReg.LR96Family` (a factor
`QED.DimReg.lr96LoopFactor` per loop relative to `dᵈk / π ^ (d/2)`, Euclidean). The graph is the
on-shell three-loop banana with one unit-mass line and three photons.

**The factorization.** With the textbook massless bubble
`∫ dᵈk / π ^ (d/2) · 1 / ((k²) ^ a ((k + q)²) ^ b) = G(a, b) (q²) ^ (d/2 - a - b)`
(`QED.DimReg.masslessBubbleCoeff`, proved from its parametric integral in
`QED.DimReg.integral_masslessBubbleFamily`):

* the photons `k₁, k₂` (total momentum `Q = k₁ + k₂`) give `G(1, 1) (Q²) ^ (d/2 - 2)`;
* this line of power `2 - d/2` and the photon `k₃` (total momentum `q = Q + k₃`) give
  `G(1, 2 - d/2) (q²) ^ (d - 3)`;
* the last loop is the on-shell one-loop integral of the massive line `D₃ = (p - q)² + 1` (power
  `1`) against the massless line `q` of power `3 - d`, whose closed form is
  `QED.DimReg.OneLoopSchwinger.phi (3 - d) 1 d` (massless power first; proved from the
  Schwinger integral in `QED.DimReg.OneLoopSchwinger.schw_eq_phi` where it converges, and taken
  as the meromorphic continuation here).

So, per loop measure `dᵈk / π ^ (d/2)`, `d = 4 - 2ε`,

  `I₁₇ = π ^ (3ε) G(1, 1) G(1, ε) φ(2ε - 1, 1, 4 - 2ε)`
  `    = π ^ (3ε) Γ(1 - ε)³ Γ(2ε - 1) Γ(3ε - 2) Γ(5 - 6ε) / (Γ(3 - 3ε) Γ(4 - 4ε))`.

The factorization of the graph into these pieces (and the Wick rotation) is a convention recorded
here, not formalized, as for `I₁₄` and `I₁₆` (`QED.ThreeLoopD.SetDMastersGamma2`). Numerically
(`scripts/numerics/three_loop_masters/i17num.py`, 40 digits) `I₁₇ C⁻¹` reproduces the LR96
table entry for `I₁₇` through `ε²` (the leading term `-1/(6ε²)` fixes the sign convention).

## Main definitions

* `QED.ThreeLoopE.lr96I17`: `I₁₇` in LR96's normalization.
* `QED.ThreeLoopE.setEMasterI17`: the master `I₁₇ C⁻¹`, `C(ε) = (π ^ ε Γ(1 + ε))³`.
-/

@[expose] public section

open Complex

namespace QED.ThreeLoopE

/-- `I₁₇` in LR96's normalization, `1 / (D₃ D₆ D₇ D₈)`: the photon bubble `G(1, 1)`, the bubble
`G(1, 2 - d/2)` of that line with the third photon, and the on-shell one-loop closed form
`φ(3 - d, 1, d)` of the massive line `D₃` against the resulting massless line of power `3 - d`.
Each loop carries `QED.DimReg.lr96LoopFactor`. -/
noncomputable def lr96I17 (ω : ℂ) : ℂ :=
  QED.DimReg.lr96LoopFactor (4 - 2 * ω) ^ 3 *
    (QED.DimReg.masslessBubbleCoeff 1 1 (4 - 2 * ω) *
      QED.DimReg.masslessBubbleCoeff 1 (2 - (4 - 2 * ω) / 2) (4 - 2 * ω) *
      QED.DimReg.OneLoopSchwinger.phi (3 - (4 - 2 * ω)) 1 (4 - 2 * ω))

/-- The master `I₁₇ C⁻¹`. -/
noncomputable def setEMasterI17 (ε : ℂ) : ℂ := lr96I17 ε / QED.ThreeLoopD.lr96C ε

end QED.ThreeLoopE
