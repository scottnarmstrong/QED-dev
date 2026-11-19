/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCrossTW
public import QED.ChainProof.SetCKCornIn
public import QED.ChainProof.SetCKCornInCV

/-!
# Set (c), Stage K, group G3: the crossed unit with a massive inner photon

Helper level (no frozen statement). Group G3 of the set (c) kernel plan is the crossed-ladder
unit `X` with the photon of mass² `t > 0` on the line `z_b` and the other photon massless,
`X(t, 0)` (equal to `X(0, t)` by the mirror symmetry of the graph, `SetCKCrossMirror`).
It has no subdivergence and no counterterm.

**The two-mass integrand.** In the frame of section 2.2 of `docs/TWO-LOOP-UNITS.md` (inner
simplex `(z₂, z₃, z_b) = (y₃, y₄, 1 - Y)`, `Y = y₃ + y₄`, outer `b = z₁ + g`, `w = z_a + e`,
`g = y₃(1-Y)`, `e = y₃ y₄`, `w = b(1-x)/x`), the merged integrand `crossedTerm μ_a μ_b` of
`QED/TwoLoop/UnitXGraphReduce.lean` times the Jacobian `b/x²` is
`A₂(b)/(M + b h)² + A₁(b)/(M + b h)` with `A₂ = a₁/b + a₂/b²`, `A₁ = c₁/b + c₂/b² + c₃/b³`
(coefficients `crossTA1`, …, `crossTC3`, polynomials in `x, y₃, y₄`), `M = cornerMass`,
`h = (x² + (1-x) μ_a)/x`. Its `b`-integral over `b > β(x) = max(g, e x/(1-x))` is
`cForm(0, a₁, a₂, 0, c₁, c₂, c₃, β, h, M, …)` (**`crossTGm`**, outer photon mass `la`, inner
photon mass `lb`). The Cheng–Wu reduction and the `b`-integration are proved in
`SetCKCrossLink` (`crossT_eq_crossUnit`). Checks
(scratch `stageK/g3`): the coefficients are the Laurent coefficients of the parametric engine
(`coef.py`, `chkEng.py`, exact); `∫∫ crossedTerm 0 t dz_A dz_a` at three inner points equals
`∫₀¹ crossTGm 0 (√t) y₃ y₄ x dx` to `10⁻¹⁴` (`chkTerm.py`); the unit at `(t, 0)` and `(0, t)`,
`t = 1`, reproduces the engine values of the set (c) plan digit for digit at level 8/16
(`mirror.py`: `-0.019753240328477760096`, `-0.019753240271253305679`).

**The unit** (`crossT`): `X(t, 0) = ∫₀¹ dY ∫₀^Y dy₃ ∫₀¹ dx crossTGm 0 (√t) y₃ (Y - y₃) x`.

**The `(M + v)⁻²`-form** (`crossTGm_eq_integral`): with `M = M_t(Y)` and the weight
`T = crossTT` of `SetCKCrossTW`, `crossTGm 0 (√t) y₃ (Y - y₃) x = ∫₀^∞ T(v)/(M + v)² dv`.

**Why the target is `IsCrossTHDensity`.** The per-node function `∫₀^Y dy₃ ∫₀¹ dx crossTGm` has
a pole `e₁M/M` with `e₁M = Y²(7Y² - 14Y + 8)/(8(Y - 1))` (from `a₁(x = 0) ≠ 0`; checked
numerically, scratch `g3/pole.py`), which is not integrable at `Y → 1` after the node change of
variables; the density form `∫ ρ Q/(Q + t)` therefore needs a cancellation between nodes. The
`(M + v)⁻²`-form avoids it: the statement proved is `X(t, 0) = ∫₀¹ H(X) Q'(X)/(Q(X) + t)² dX`,
the `Q`-derivative form of a Stieltjes transform (`ρ = H'/Q` after an integration by parts).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The polynomial `N₁` of `a₁ = -y₃ N₁/4`. -/
noncomputable def crossTN1 (x y3 y4 : ℝ) : ℝ :=
  x ^ 4 * (4 * y3 ^ 3 - 8 * y3 ^ 2 + 4 * y3) +
    x ^ 3 * (-14 * y3 ^ 3 - 12 * y3 ^ 2 * y4 + 34 * y3 ^ 2 + 16 * y3 * y4 - 24 * y3 - 4 * y4 + 4) +
    x ^ 2 * (19 * y3 ^ 3 + 32 * y3 ^ 2 * y4 - 50 * y3 ^ 2 + 12 * y3 * y4 ^ 2 - 56 * y3 * y4 +
      41 * y3 - 8 * y4 ^ 2 + 22 * y4 - 8) +
    x * (-12 * y3 ^ 3 - 30 * y3 ^ 2 * y4 + 30 * y3 ^ 2 - 22 * y3 * y4 ^ 2 + 54 * y3 * y4 -
      26 * y3 - 4 * y4 ^ 3 + 22 * y4 ^ 2 - 24 * y4 + 4) +
    (3 * y3 ^ 3 + 10 * y3 ^ 2 * y4 - 6 * y3 ^ 2 + 11 * y3 * y4 ^ 2 - 14 * y3 * y4 + 4 * y3 +
      4 * y4 ^ 3 - 8 * y4 ^ 2 + 4 * y4)

/-- `a₁ = -y₃ N₁/4`, the coefficient of `1/(b (M + b h)²)`. -/
noncomputable def crossTA1 (x y3 y4 : ℝ) : ℝ := -(y3 * crossTN1 x y3 y4) / 4

/-- The polynomial `P_a` of `a₂ = x y₃² P_a`. -/
noncomputable def crossTPa (x y3 y4 : ℝ) : ℝ :=
  -((y3 + 1) * (y3 + 2 * y4 - 1) * (x * y3 - x - y3 - y4) * (x * y3 - x - y3 - y4 + 2)) / 4

/-- `a₂ = x y₃² P_a`, the coefficient of `1/(b² (M + b h)²)`. -/
noncomputable def crossTA2 (x y3 y4 : ℝ) : ℝ := x * y3 ^ 2 * crossTPa x y3 y4

/-- `c₁`, the coefficient of `1/(b (M + b h))`. -/
noncomputable def crossTC1 (x y3 y4 : ℝ) : ℝ :=
  y3 * (4 * x ^ 2 * y3 - 4 * x ^ 2 - 2 * x * y3 - 4 * x * y4 + 4 * x + y3 + 4 * y4 - 2) / 4

/-- The polynomial `N₂` of `c₂ = x y₃ N₂/2`. -/
noncomputable def crossTN2 (x y3 y4 : ℝ) : ℝ :=
  x ^ 2 * (8 * y3 ^ 3 - 16 * y3 ^ 2 + 8 * y3) +
    x * (-13 * y3 ^ 3 - 14 * y3 ^ 2 * y4 + 31 * y3 ^ 2 + 16 * y3 * y4 - 20 * y3 - 2 * y4 + 2) +
    (8 * y3 ^ 3 + 17 * y3 ^ 2 * y4 - 19 * y3 ^ 2 + 6 * y3 * y4 ^ 2 - 20 * y3 * y4 + 12 * y3 -
      2 * y4 ^ 2 + 2 * y4 - 1)

/-- `c₂ = x y₃ N₂/2`, the coefficient of `1/(b² (M + b h))`. -/
noncomputable def crossTC2 (x y3 y4 : ℝ) : ℝ := x * y3 * crossTN2 x y3 y4 / 2

/-- `P₃ = 3(y₃ + 1)(y₃ + 2y₄ - 1)/4`. -/
noncomputable def crossTP3 (y3 y4 : ℝ) : ℝ := 3 * (y3 + 1) * (y3 + 2 * y4 - 1) / 4

/-- `c₃ = x² y₃² (1-y₃)² P₃`, the coefficient of `1/(b³ (M + b h))`. -/
noncomputable def crossTC3 (x y3 y4 : ℝ) : ℝ := x ^ 2 * y3 ^ 2 * (1 - y3) ^ 2 * crossTP3 y3 y4

/-- **The two-mass crossed integrand** (outer photon mass `la`, inner photon mass `lb`): the
`b`-integral over `b > β(x)` of `A₂/(M + b h)² + A₁/(M + b h)`, in closed form. -/
noncomputable def crossTGm (la lb y3 y4 x : ℝ) : ℝ :=
  cForm 0 (crossTA1 x y3 y4) (crossTA2 x y3 y4) 0 (crossTC1 x y3 y4) (crossTC2 x y3 y4)
    (crossTC3 x y3 y4) (betaG (cornerG y3 y4) (y3 * y4) x) (ladderInnerMass 1 la x / x)
    (cornerMass la lb y3 y4)
    (log (cornerMass la lb y3 y4 +
      betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 la x / x)))
    (log (1 + cornerMass la lb y3 y4 /
      (betaG (cornerG y3 y4) (y3 * y4) x * (ladderInnerMass 1 la x / x))))

/-- The `Y`-integrand of the inner-massive crossed unit. -/
noncomputable def crossTIntegrand (t Y : ℝ) : ℝ :=
  ∫ y3 in (0 : ℝ)..Y, ∫ x in (0 : ℝ)..1, crossTGm 0 (√t) y3 (Y - y3) x

/-- **The inner-massive crossed unit** `X(t, 0)`. -/
noncomputable def crossT (t : ℝ) : ℝ := ∫ Y in (0 : ℝ)..1, crossTIntegrand t Y

/-- **The `Q`-derivative form of the Stieltjes identity for G3**: for a candidate `H`,
`X(t, 0) = ∫₀¹ H(X) Q'(X)/(Q(X) + t)² dX` for every `t > 0`. -/
def IsCrossTHDensity (H : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → crossT t = ∫ X in (0 : ℝ)..1, H X * (setCKdQ X / (setCKQ X + t) ^ 2)

/-- The `(M + v)⁻²`-weight of the unit at `(Y, y₃, x)`. -/
noncomputable def crossTT (Y y3 x v : ℝ) : ℝ :=
  crossTTg (crossTA1 x y3 (Y - y3)) (crossTA2 x y3 (Y - y3)) (crossTC1 x y3 (Y - y3))
    (crossTC2 x y3 (Y - y3)) (crossTC3 x y3 (Y - y3))
    (betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x) x v

/-- **The `(M + v)⁻²`-representation of the crossed integrand** in the inner-massive unit. -/
theorem crossTGm_eq_integral {t Y y3 x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : 0 < y3) (hx : x ∈ Ioo (0 : ℝ) 1) :
    crossTGm 0 (√t) y3 (Y - y3) x = ∫ v in Ioi 0, crossTT Y y3 x v / (massIn t Y + v) ^ 2 := by
  have hM := massIn_pos ht ⟨hY.1.le, hY.2.le⟩
  have hβ := betaG_pos (e := y3 * (Y - y3)) (x := x) (cornerG_pos hY.2 h3)
  unfold crossTGm crossTT
  rw [ladderInnerMass_zero_div hx.1.ne', cornerMass_zero_sqrt ht.le]
  exact crossT_cForm_eq hM hβ hx.1

end QED.ChainProof.SetCK

end
