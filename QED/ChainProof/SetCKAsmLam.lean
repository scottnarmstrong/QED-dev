/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormCRho
public import QED.ChainProof.SetCKFormXRho
public import QED.ChainProof.SetCKFormOSK
public import QED.ChainProof.SetCKSelfInRho
public import QED.ChainProof.SetCKDensity
public import QED.Chain.SetCKernel

/-!
# Set (c), Stage K, assembly: the six densities add up to `λ⁽⁴⁾`

Helper level (no frozen statement). The Stieltjes densities of the six groups of the set (c)
kernel are, in the letters `log X`, `log (1 - X)`, `log (2 - X)` and the weight-two function
`W(X) = 4 Li₂(X - 1) + 2 Li₂(1 - X) + 2 log (1 - X) log (2 - X) + log X log (1 - X)`
(`formXW`; the inner corner file uses the same body under the name `formCW`,
**`formCW_eq_formXW`**):

* `ρ_L = rhoL`, `ρ_S = rhoSelfIn` (no `W`), `ρ_C = rhoCornC`, `ρ_X = rhoCrossX` (counted
  twice: the two mirror placements), `ρ_oS = rhoScOutS` (no `W`), and
* **`rhoScOutC`**, the density `ρ_oC` of the outer-massive corner, defined here by its closed
  form (found numerically, scratch `stageK/pslq`, Session 16; the identity
  `scOutCH = H_ρ` for it is the one input of the assembly not yet proved).

**`setCKRhoSum_eq_setCLambda`**: on `(0, 1)`,
`ρ_L + ρ_S + ρ_C + 2 ρ_X + ρ_oS + ρ_oC = λ⁽⁴⁾` (`setCLambda`, Balzani–Laporta–Passera eq. (38),
stated with `F⁽⁴⁾(X - 1)` and `Π̂(X²/(1 - X))`). In the literal kernel the bracket of
`R₅` at `u = X - 1` is `W(X)` (`log((1 - u)²(1 + u)) = 2 log (2 - X) + log X`), and
`Π̂(X²/(1 - X))` has the closed form `piHatX` (`piHat_photonVar`), so the identity is an
identity of rational coefficients of `1, log X, log (1 - X), log (2 - X), W`; no dilogarithm
functional equation enters.
-/

@[expose] public section

open Real Set QED.Polylog

namespace QED.ChainProof.SetCK

open QED.Chain

/-- The two names of the weight-two function `W` agree. -/
theorem formCW_eq_formXW : formCW = formXW := rfl

/-- **The Stieltjes density of the outer-massive corner group** `ρ_oC`, in closed form. -/
noncomputable def rhoScOutC (X : ℝ) : ℝ :=
  -X * (17 * X ^ 2 - 39 * X + 16) / (12 * (X - 1) ^ 2) -
    (X ^ 5 - 4 * X ^ 4 + 10 * X ^ 3 - 17 * X ^ 2 + 18 * X - 4) / (6 * (X - 1) ^ 4) * log X +
    (2 * X ^ 6 - 11 * X ^ 5 + 30 * X ^ 4 - 51 * X ^ 3 + 52 * X ^ 2 - 24 * X + 4) /
      (3 * X * (X - 2) * (X - 1) ^ 2) * log (1 - X) -
    2 * (X ^ 2 - 2 * X + 2) * (X ^ 4 - 3 * X ^ 3 + 2 * X ^ 2 + 2 * X - 1) / (3 * (X - 1) ^ 4) *
      log (2 - X) +
    (X - 2) * (2 * X ^ 4 - 3 * X ^ 3 + 2 * X ^ 2 + 2 * X - 1) / (3 * X * (X - 1) ^ 3) * formXW X

/-- The `R₅` bracket of `F⁽⁴⁾(X - 1)` is `W(X)`. -/
theorem setCKAsm_log_bracket {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    4 * Li 2 (X - 1) + 2 * Li 2 (-(X - 1)) +
        log (-(X - 1)) * log ((1 - (X - 1)) ^ 2 * (1 + (X - 1))) = formXW X := by
  have h2 : (2 - X) ≠ 0 := by linarith [hX.2]
  have e1 : -(X - 1) = 1 - X := by ring
  have e2 : (1 - (X - 1)) ^ 2 * (1 + (X - 1)) = (2 - X) ^ 2 * X := by ring
  rw [e1, e2, log_mul (pow_ne_zero 2 h2) hX.1.ne', log_pow, Li_two, formXW]
  push_cast
  ring

/-- **The six densities add up to `λ⁽⁴⁾`** on `(0, 1)`. -/
theorem setCKRhoSum_eq_setCLambda {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    rhoL X + rhoSelfIn X + rhoCornC X + 2 * rhoCrossX X + rhoScOutS X + rhoScOutC X =
      setCLambda X := by
  have hX0 : X ≠ 0 := hX.1.ne'
  have hX1 : X - 1 ≠ 0 := by linarith [hX.2]
  have h1X : 1 - X ≠ 0 := by linarith [hX.2]
  have hX2 : X - 2 ≠ 0 := by linarith [hX.2]
  have hb := setCKAsm_log_bracket hX
  have e1 : -(X - 1) = 1 - X := by ring
  have e3 : 1 + (X - 1) = X := by ring
  have e4 : 1 - (X - 1) = 2 - X := by ring
  have e5 : X - 1 - 1 = X - 2 := by ring
  have e6 : X - 1 + 1 = X := by ring
  rw [rhoL_eq hX]
  unfold setCLambda setCKappa setCF4 setCDeltaAlpha
  rw [piHat_photonVar hX, hb]
  rw [e1, e3, e4]
  unfold rhoSelfIn rhoCornC rhoCrossX rhoScOutS rhoScOutC setCR1 setCR2 setCR3 setCR4 setCR5
    piHatX
  simp only [e5, e6]
  rw [formCW_eq_formXW]
  generalize log X = a
  generalize log (1 - X) = b
  generalize log (2 - X) = c
  generalize formXW X = w
  field_simp
  ring

end QED.ChainProof.SetCK

end
