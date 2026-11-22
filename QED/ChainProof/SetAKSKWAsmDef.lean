/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWQDisp
public import QED.ChainProof.SetAKSKUVBDec

/-!
# Set (a), stage D: the spectral densities of the `VA` and `VB` classes

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. In the
velocity `δ ∈ (0, 1)`, `T = ksDT 1 δ = 4/(1-δ²)`, the subtracted finite parts of the two
classes have the form `∫₀¹ ksSpecKer(s, δ) ρ(δ) dδ`. This file fixes the densities as explicit
integrals over the Feynman parameters.

* `VA`: the node density `ksWnA x σ T` lives above the threshold `T₀(σ) = 1/(σ(1-σ)) < T`,
  i.e. on `σ ∈ ((1-δ)/2, (1+δ)/2)`; the threshold term `-C s/(s + T₀)` of the node dispersion
  (`ksW_ksUQ_sub_eq`) gives `-(1-δ²)/(4δ) (C̄((1-δ)/2) + C̄((1+δ)/2))`,
  `C̄(σ) = ∫₀¹ ksWCA x σ dx` (`ksW_integral_threshold_delta`).
* `VB`: the node density `ksWnB ρ β w T` is `(1/π) Im` of the finite part density
  `ksUb0 1 s ρ β w` at `s = -T + i0`. With `A_w = ksDA 1 (-T) w`, `A_β = ksDA 1 (-T) β`,
  `Y = ksDYmax β w`, `D = (1-ρ)A_w + ρY A_β` and `z = ρY A_β/((1-ρ)A_w)`:

  `n_B = G₀/(ρA_β) ([D < 0] - [A_w < 0]) - qY/2 [D < 0] + f₀/(1-ρ) ([A_β < 0] - [D < 0])`
      `- ρc (log(Y/ρ) - log(-A_w)) [A_w < 0] - ρc ε log(-z) [z < -1] + f₀ log(-A_β) [A_β < 0]`,

  `ε = sign(β(1-β) - w(1-w))` (the sign of `Im z`), `K(z) = -Li₂(-z)` having the cut
  `z ≤ -1` with `Im K(z ± i0) = ±π log(-z)`.

Main definitions: **`ksWRhoA`**, **`ksWRhoB`** (with `ksWRhoAn`, `ksWRhoAc`, `ksWnB`).
-/

@[expose] public section

open Real MeasureTheory Set

namespace QED.ChainProof.SetAKS

/-- The node part of the `VA` density: `∫₀¹ dx ∫_{σ₋}^{σ₊} dσ n_A(x, σ, T)`,
`σ± = (1 ± δ)/2` (the nodes with `T₀(σ) < T = 4/(1-δ²)`). -/
noncomputable def ksWRhoAn (δ : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) 1, ∫ σ in Ioo ((1 - δ) / 2) ((1 + δ) / 2), ksWnA x σ (ksDT 1 δ)

/-- The threshold part of the `VA` density:
`(1-δ²)/(4δ) (C̄((1-δ)/2) + C̄((1+δ)/2))`, `C̄(σ) = ∫₀¹ ksWCA x σ dx`. -/
noncomputable def ksWRhoAc (δ : ℝ) : ℝ :=
  (1 - δ ^ 2) / (4 * δ) *
    ((∫ x in Ioo (0 : ℝ) 1, ksWCA x ((1 - δ) / 2)) + ∫ x in Ioo (0 : ℝ) 1, ksWCA x ((1 + δ) / 2))

/-- **The spectral density of the `VA` class** in the velocity `δ`. -/
noncomputable def ksWRhoA (δ : ℝ) : ℝ := ksWRhoAn δ - ksWRhoAc δ

/-- The `VB` spectral density at the node `(ρ, β, w)` in the spectral variable `T`:
`(1/π) Im ksUb0 1 (-T + i0) ρ β w`. -/
noncomputable def ksWnB (ρ β w T : ℝ) : ℝ :=
  ksUG0 1 (-T) ρ β w / (ρ * ksDA 1 (-T) β) *
      ((if (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β < 0 then 1 else 0) -
        (if ksDA 1 (-T) w < 0 then 1 else 0)) -
    (if (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β < 0 then
      ksUq ρ β w * ksDYmax β w / 2 else 0) +
    (1 - ρ)⁻¹ * ksUf0 β w *
      ((if ksDA 1 (-T) β < 0 then 1 else 0) -
        (if (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β < 0 then 1 else 0)) -
    (if ksDA 1 (-T) w < 0 then
      ρ * ksUcB w * (log (ksDYmax β w / ρ) - log (-ksDA 1 (-T) w)) else 0) -
    (if ρ * ksDYmax β w * ksDA 1 (-T) β / ((1 - ρ) * ksDA 1 (-T) w) < -1 then
      ρ * ksUcB w * ((if w * (1 - w) < β * (1 - β) then 1 else -1) *
        log (-(ρ * ksDYmax β w * ksDA 1 (-T) β / ((1 - ρ) * ksDA 1 (-T) w)))) else 0) +
    (if ksDA 1 (-T) β < 0 then ksUf0 β w * log (-ksDA 1 (-T) β) else 0)

/-- **The spectral density of the `VB` class** in the velocity `δ`:
`∫₀¹ dβ ∫₀¹ dw ∫₀¹ dρ n_B(ρ, β, w, 4/(1-δ²))`. -/
noncomputable def ksWRhoB (δ : ℝ) : ℝ :=
  ∫ β in Ioo (0 : ℝ) 1, ∫ w in Ioo (0 : ℝ) 1, ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ β w (ksDT 1 δ)

end QED.ChainProof.SetAKS

end
