/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9Def

/-!
# Set (e) of `A₁⁽⁶⁾`: the master `I₁₀`, defined through a representation analytic at `ε = 0`

**The integral.** Laporta–Remiddi (Phys. Lett. B 379 (1996) 283, arXiv:hep-ph/9602417; the list
of basic integrals before their eq. (14)) define `I₁₀ = ∫ 1 / (D₂ D₄ D₆ D₇ D₈)` with (their
eq. (9), `m = 1`, `p² = -1`) `D₂ = (p - k₁ - k₂)² + 1`, `D₄ = (p - k₂ - k₃)² + 1`, `D₆ = k₁²`,
`D₇ = k₂²`, `D₈ = k₃²`; normalization as in `QED.DimReg.LR96Family`. The loop `k₁` runs only
through `D₂, D₆` and `k₃` only through `D₄, D₈`: with `r = p - k₂` each is the one-mass bubble

  `B(r) = ∫ dᵈℓ / π ^ (d/2) 1 / (ℓ² ((ℓ + r)² + 1)) = Γ(ε) ∫₀¹ (1 - ρ) ^ (-ε) (1 + ρ r²) ^ (-ε) dρ`

(Feynman parameter `1 - ρ` on the massive line), and `I₁₀ = ∫ dᵈk₂ / π ^ (d/2) B(p - k₂)² / k₂²`.

**The Feynman-parameter form.** Join the two factors `(1 + ρ r²) ^ (-ε)`, `(1 + σ r²) ^ (-ε)` by a
parameter `z` (weight `Γ(2ε) / Γ(ε)² (z(1 - z)) ^ (ε - 1)`) into `(1 + τ r²) ^ (-2ε)`,
`τ = z ρ + (1 - z) σ` (`QED.ThreeLoopE.i10Tau`), write it as `τ ^ (-2ε) (r² + 1/τ) ^ (-2ε)`, and do
the on-shell one-loop integral with the massless line `k₂` (power `1`) and the massive line
`r² + 1/τ` (power `2ε`, Feynman parameter `u` on it):
`∫ dᵈk / π ^ (d/2) 1 / (k² ((p - k)² + M²) ^ (2ε)) = Γ(3ε - 1) / Γ(2ε) ∫₀¹ u ^ (-ε)
(M² - 1 + u) ^ (1 - 3ε) du`. With `M² = 1/τ` the powers of `τ` combine, and, per loop measure
`dᵈk / π ^ (d/2)`, `d = 4 - 2ε`,

  `I₁₀ = π ^ (3ε) Γ(3ε - 1) T(ε)`,
  `T(ε) = ∫_{(0,1)⁴} A(ρ) A(σ) (z(1 - z)) ^ (ε - 1) τ ^ (ε - 1) u ^ (-ε)`
  `       · (1 - (1 - u) τ) ^ (1 - 3ε)`,

`A(x) = (1 - x) ^ (-ε)` (`QED.ThreeLoopE.i10Feyn`). This factorization is a convention recorded
here, as for `I₉` (`QED.ThreeLoopD.SetDMastersI9Def`).

**Why not the integral itself.** `T(ε)` converges only for `re ε > 0` (and `re ε` small): the
faces `z = 0, 1` carry `z ^ (ε - 1)`, and the corners `z, σ → 0` and `1 - z, ρ → 0` (where
`τ → 0`) carry the log-divergence `λ ^ (2ε - 1)`. A Bochner integral would silently be `0` near
`ε = 0`, so the master is defined through a subtracted representation (`QED.ThreeLoopE.i10T`).
Every closed part below is a product of `Γ` functions (`B(a, b) = QED.ThreeLoopD.i9Beta a b`).

**The subtraction.** Write `(1 - (1 - u) τ) ^ (1 - 3ε) = 1 + ((1 - (1 - u) τ) ^ (1 - 3ε) - 1)`.
* The second part gives `ψ(τ) = ∫₀¹ u ^ (-ε) τ ^ (ε - 1) ((1 - (1 - u) τ) ^ (1 - 3ε) - 1) du`
  (`QED.ThreeLoopE.i10Psi`, `O(τ ^ ε)`), and only the faces `z = 0, 1` diverge. Subtracting the
  linear interpolation `(1 - z) ψ(σ) + z ψ(ρ)` leaves the convergent `K₂`
  (`QED.ThreeLoopE.i10K2`) and, by the symmetry `ρ ↔ σ`, `z ↔ 1 - z`, the face part
  `2 B(ε, 1 + ε) G₀`, `G₀ = (1 - ε)⁻¹ ∫₀¹ A(σ) ψ(σ) dσ` (`QED.ThreeLoopE.i10G0`;
  `∫₀¹ A = 1/(1 - ε)`, `∫₀¹ (z(1 - z)) ^ (ε - 1) (1 - z) dz = B(ε, 1 + ε)`).
* The first part gives `S / (1 - ε)` (`∫₀¹ u ^ (-ε) du = 1/(1 - ε)`), with
  `S = ∫_{(0,1)³} A(ρ) A(σ) (z(1 - z)) ^ (ε - 1) τ ^ (ε - 1)`. Split
  `A(ρ) A(σ) = 1 + (A(ρ) - 1) + (A(σ) - 1) + (A(ρ) - 1)(A(σ) - 1)`; the two middle terms are
  equal by the symmetry. With `a₀ = ∫₀¹ (A - 1) = 1/(1 - ε) - 1`, `a₁ = ∫₀¹ (A(ρ) - 1) ρ ^ ε dρ =
  Γ(1 + ε) Γ(1 - ε) - 1/(1 + ε)`, `a₂ = ∫₀¹ (A(ρ) - 1) ρ ^ (ε - 1) dρ = Γ(ε) Γ(1 - ε) - 1/ε`:
  - `1`: `S₀ = (B(ε - 1, ε - 1) - 2 B(2ε, ε - 1)) / (ε (1 + ε))` (`QED.ThreeLoopE.i10S0`; the
    `ρ, σ` integral is elementary).
  - `A(ρ) - 1`: the `σ` integral is `f = ((1 - z(1 - ρ)) ^ ε - (z ρ) ^ ε) / (ε (1 - z))`, which
    behaves as `(1 - (z ρ) ^ ε) / ε` at `z = 0` and as `ρ ^ (ε - 1)` at `z = 1`. Subtracting
    `(1 - z)(1 - (z ρ) ^ ε) / ε + z ρ ^ (ε - 1)` leaves `K_a / ε` (`QED.ThreeLoopE.i10Ka`), and the
    subtracted terms give `C_a = B(ε, 1 + ε) a₀ / ε - B(2ε, 1 + ε) a₁ / ε + B(1 + ε, ε) a₂`
    (`QED.ThreeLoopE.i10Ca`).
  - `(A(ρ) - 1)(A(σ) - 1)`: subtracting `τ ^ (ε - 1) ↦ (1 - z) σ ^ (ε - 1) + z ρ ^ (ε - 1)` leaves
    `K_ab` (`QED.ThreeLoopE.i10Kab`) and the closed part
    `C_ab = B(ε, 1 + ε) a₀ a₂ + B(1 + ε, ε) a₂ a₀` (`QED.ThreeLoopE.i10Cab`).

  So `S = S₀ + 2 (C_a + K_a / ε) + C_ab + K_ab` (`QED.ThreeLoopE.i10S`) and
  `T = S / (1 - ε) + 2 B(ε, 1 + ε) G₀ + K₂` (`QED.ThreeLoopE.i10T`). The integrals `K_a`, `K_ab`,
  `G₀`, `K₂` converge on a neighbourhood of `ε = 0` (each integrand gained a factor `z` or `1 - z`
  at the face it was subtracted at, the corners are tamed by the factors `A - 1 = O(ρ)` resp. by
  `ψ = O(τ ^ ε)`, and `K_a = O(ε²)`); for small `re ε > 0` each split is a split of convergent
  integrals, so the right side is the continuation of `T(ε)` that defines
  `QED.ThreeLoopE.lr96I10`. At `ε = 0` the term `K_a / ε` is Lean's `x / 0 = 0`; only the
  punctured neighbourhood matters.

**Numerics** (`scripts/numerics/three_loop_masters/i10grid.py`, `i10rep.py`, `i10taylor.py`,
`i10gen.py`): the unsubtracted `T` (tensor Gauss–Legendre) and the subtracted form (tanh-sinh)
agree at `ε = 0.1` to `10⁻⁵` (`T = 131.9148473`). The Taylor coefficients at `ε = 0` of
`ε (T - (S₀ + 2 C_a + C_ab) / (1 - ε))`, computed directly from the integrands as power series in
`ε`, are `-1`, `π² - 10`, `5π²/6 + 44ζ₃ - 55`, `401π⁴/90 - 47π²/3 + 6ζ₃ - 285` to `5 · 10⁻¹³`:
exactly the values the LR96 table forces through the order `ε`.

## Main definitions

* `QED.ThreeLoopE.i10A`, `QED.ThreeLoopE.i10W`, `QED.ThreeLoopE.i10Tau`,
  `QED.ThreeLoopE.i10Psi`, `QED.ThreeLoopE.i10Feyn` (the unsubtracted `T`, for reference).
* `QED.ThreeLoopE.i10S0`, `QED.ThreeLoopE.i10Ca`, `QED.ThreeLoopE.i10Cab` (closed parts),
  `QED.ThreeLoopE.i10Ka`, `QED.ThreeLoopE.i10Kab`, `QED.ThreeLoopE.i10G0`,
  `QED.ThreeLoopE.i10K2` (convergent integrals), `QED.ThreeLoopE.i10S`, `QED.ThreeLoopE.i10T`.
* `QED.ThreeLoopE.lr96I10`, `QED.ThreeLoopE.setEMasterI10`.
-/

@[expose] public section

open MeasureTheory Set Complex QED.ThreeLoopD

namespace QED.ThreeLoopE

/-- The bubble weight `A(x) = (1 - x) ^ (-ε)`. -/
noncomputable def i10A (ε : ℂ) (x : ℝ) : ℂ := ((1 - x : ℝ) : ℂ) ^ (-ε)

/-- The joining weight `(z(1 - z)) ^ (ε - 1)`. -/
noncomputable def i10W (ε : ℂ) (z : ℝ) : ℂ := ((z * (1 - z) : ℝ) : ℂ) ^ (ε - 1)

/-- The joined parameter `τ = z ρ + (1 - z) σ`. -/
def i10Tau (z ρ σ : ℝ) : ℝ := z * ρ + (1 - z) * σ

/-- **The Feynman-parameter integral of `I₁₀`**, `T(ε)` (convergent for `0 < re ε < 2/3`), over
`(z, ρ, σ, u) ∈ (0,1)⁴`. For reference: `QED.ThreeLoopE.lr96I10` uses its continuation
`QED.ThreeLoopE.i10T`. -/
noncomputable def i10Feyn (ε : ℂ) : ℂ :=
  ∫ q in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)),
    i10A ε q.2.1 * i10A ε q.2.2.1 * i10W ε q.1 * ((i10Tau q.1 q.2.1 q.2.2.1 : ℝ) : ℂ) ^ (ε - 1) *
      (q.2.2.2 : ℂ) ^ (-ε) * ((1 - (1 - q.2.2.2) * i10Tau q.1 q.2.1 q.2.2.1 : ℝ) : ℂ) ^ (1 - 3 * ε)

/-- `ψ(τ) = ∫₀¹ u ^ (-ε) τ ^ (ε - 1) ((1 - (1 - u) τ) ^ (1 - 3ε) - 1) du`. -/
noncomputable def i10Psi (ε : ℂ) (τ : ℝ) : ℂ :=
  ∫ u in Ioo (0 : ℝ) 1,
    (u : ℂ) ^ (-ε) * ((τ : ℂ) ^ (ε - 1) * (((1 - (1 - u) * τ : ℝ) : ℂ) ^ (1 - 3 * ε) - 1))

/-- `S₀ = ∫_{(0,1)³} (z(1 - z)) ^ (ε - 1) τ ^ (ε - 1) = (B(ε - 1, ε - 1) - 2 B(2ε, ε - 1)) /
(ε (1 + ε))` (continued). -/
noncomputable def i10S0 (ε : ℂ) : ℂ :=
  (i9Beta (ε - 1) (ε - 1) - 2 * i9Beta (2 * ε) (ε - 1)) / (ε * (1 + ε))

/-- The closed part of the `A(ρ) - 1` term:
`C_a = B(ε, 1 + ε) a₀ / ε - B(2ε, 1 + ε) a₁ / ε + B(1 + ε, ε) a₂` with `a₀ = 1/(1 - ε) - 1`,
`a₁ = Γ(1 + ε) Γ(1 - ε) - 1/(1 + ε)`, `a₂ = Γ(ε) Γ(1 - ε) - 1/ε`. -/
noncomputable def i10Ca (ε : ℂ) : ℂ :=
  i9Beta ε (1 + ε) * (1 / (1 - ε) - 1) / ε -
    i9Beta (2 * ε) (1 + ε) * (Gamma (1 + ε) * Gamma (1 - ε) - 1 / (1 + ε)) / ε +
    i9Beta (1 + ε) ε * (Gamma ε * Gamma (1 - ε) - 1 / ε)

/-- The closed part of the `(A(ρ) - 1)(A(σ) - 1)` term: `C_ab = B(ε, 1 + ε) a₀ a₂ +
B(1 + ε, ε) a₂ a₀` with `a₀ = 1/(1 - ε) - 1`, `a₂ = Γ(ε) Γ(1 - ε) - 1/ε`. -/
noncomputable def i10Cab (ε : ℂ) : ℂ :=
  i9Beta ε (1 + ε) * (1 / (1 - ε) - 1) * (Gamma ε * Gamma (1 - ε) - 1 / ε) +
    i9Beta (1 + ε) ε * (Gamma ε * Gamma (1 - ε) - 1 / ε) * (1 / (1 - ε) - 1)

/-- `K_a = ∫∫_{(0,1)²} (A(ρ) - 1) (z(1 - z)) ^ (ε - 1) (((1 - z(1 - ρ)) ^ ε - (z ρ) ^ ε) / (1 - z)
- (1 - z)(1 - (z ρ) ^ ε) - ε z ρ ^ (ε - 1))` (the pair is `(z, ρ)`). -/
noncomputable def i10Ka (ε : ℂ) : ℂ :=
  ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
    (i10A ε q.2 - 1) * i10W ε q.1 *
      ((((1 - q.1 * (1 - q.2) : ℝ) : ℂ) ^ ε - ((q.1 * q.2 : ℝ) : ℂ) ^ ε) / (1 - q.1 : ℂ) -
        (1 - q.1 : ℂ) * (1 - ((q.1 * q.2 : ℝ) : ℂ) ^ ε) - ε * q.1 * (q.2 : ℂ) ^ (ε - 1))

/-- `K_ab = ∫_{(0,1)³} (A(ρ) - 1)(A(σ) - 1) (z(1 - z)) ^ (ε - 1)
(τ ^ (ε - 1) - (1 - z) σ ^ (ε - 1) - z ρ ^ (ε - 1))` (the triple is `(z, ρ, σ)`). -/
noncomputable def i10Kab (ε : ℂ) : ℂ :=
  ∫ q in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
    (i10A ε q.2.1 - 1) * (i10A ε q.2.2 - 1) * i10W ε q.1 *
      (((i10Tau q.1 q.2.1 q.2.2 : ℝ) : ℂ) ^ (ε - 1) - (1 - q.1 : ℂ) * (q.2.2 : ℂ) ^ (ε - 1) -
        (q.1 : ℂ) * (q.2.1 : ℂ) ^ (ε - 1))

/-- `G₀ = (1 - ε)⁻¹ ∫₀¹ A(σ) ψ(σ) dσ`. -/
noncomputable def i10G0 (ε : ℂ) : ℂ :=
  (∫ σ in Ioo (0 : ℝ) 1, i10A ε σ * i10Psi ε σ) / (1 - ε)

/-- `K₂ = ∫_{(0,1)³} A(ρ) A(σ) (z(1 - z)) ^ (ε - 1) (ψ(τ) - (1 - z) ψ(σ) - z ψ(ρ))` (the triple is
`(z, ρ, σ)`). -/
noncomputable def i10K2 (ε : ℂ) : ℂ :=
  ∫ q in Ioo (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1),
    i10A ε q.2.1 * i10A ε q.2.2 * i10W ε q.1 *
      (i10Psi ε (i10Tau q.1 q.2.1 q.2.2) - (1 - q.1 : ℂ) * i10Psi ε q.2.2 -
        (q.1 : ℂ) * i10Psi ε q.2.1)

/-- The continued `S = ∫_{(0,1)³} A(ρ) A(σ) (z(1 - z)) ^ (ε - 1) τ ^ (ε - 1)`:
`S₀ + 2 (C_a + K_a / ε) + C_ab + K_ab`. -/
noncomputable def i10S (ε : ℂ) : ℂ :=
  i10S0 ε + 2 * (i10Ca ε + i10Ka ε / ε) + i10Cab ε + i10Kab ε

/-- **The continued Feynman-parameter integral** `T(ε) = S / (1 - ε) + 2 B(ε, 1 + ε) G₀ + K₂`. -/
noncomputable def i10T (ε : ℂ) : ℂ :=
  i10S ε / (1 - ε) + 2 * i9Beta ε (1 + ε) * i10G0 ε + i10K2 ε

/-- `I₁₀` in LR96's normalization, `1 / (D₂ D₄ D₆ D₇ D₈)`: `π ^ (3ε) Γ(3ε - 1) T(ε)`, with `T`
continued by `QED.ThreeLoopE.i10T`. Each loop carries `QED.DimReg.lr96LoopFactor`. -/
noncomputable def lr96I10 (ω : ℂ) : ℂ :=
  QED.DimReg.lr96LoopFactor (4 - 2 * ω) ^ 3 * (Gamma (3 * ω - 1) * i10T ω)

/-- The master `I₁₀ C⁻¹`. -/
noncomputable def setEMasterI10 (ε : ℂ) : ℂ := lr96I10 ε / lr96C ε

end QED.ThreeLoopE
