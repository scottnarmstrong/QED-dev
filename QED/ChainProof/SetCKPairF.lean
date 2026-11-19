/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKOuterL

/-!
# Set (c), Stage K: the L-pair integrand in the node variable

Helper level (no frozen statement). In both placements the photon mass² `t` enters only through
`u = Q(x) + t`, `Q(x) = x²/(1-x)`: the inner mass is `M_t(x) = (1-x) u` and the outer one
`h_t(x) = ((1-x)/x) u`. The pair integrand per node `x` (the inner `Y` renamed `x`),

`F(x, u) = Ψ_in(x, x(1-x), (1-x) u) + Φ_out(x, (1-x) u/x) - (3/2) x²/u`,

is `α log u + β log(u + x) + γ Li₂(1 - p/u) + δ₀ + δₓ log x + δ₁ log(1-x)`, `p = x/(1-x)`, with
rational `α, …, δ₁` (`pairFe`, `pairF_eq`). The `-(3/2) x²/u` is the per-node integrand of
`(3/2) F₂(t) = (3/2) ∫₀¹ (1-x) Q/(Q+t)`. The `ln u/u` terms of the two placements cancel in `F`.
-/

@[expose] public section

namespace QED.ChainProof.SetCK

open Real Set QED.TwoLoop.UnitXClose

noncomputable def pairAl (x u : ℝ) : ℝ :=
    -(u ^ 4 - 150*x ^ 4 - 141*x ^ 6 + 4*u ^ 3 + 24*x ^ 3 + 27*x ^ 7 + 237*x ^ 5 - u ^ 4*x ^ 3 -
      518*u*x ^ 4 - 379*u ^ 2*x ^ 4 - 180*u*x ^ 6 - 64*u ^ 2*x ^ 2 - 54*u ^ 2*x ^ 6 - 20*u*x ^ 2
      - 20*x*u ^ 3 - 20*u ^ 3*x ^ 3 - 3*x*u ^ 4 - 2*x*u ^ 2 + 3*u ^ 4*x ^ 2 + 4*u ^ 3*x ^ 4 +
      18*u*x ^ 7 + 32*u ^ 3*x ^ 2 + 218*u*x ^ 3 + 234*u ^ 2*x ^ 5 + 265*u ^ 2*x ^ 3 + 480*u*x ^
      5)/(12*x*(-1 + x)*(x - u + u*x) ^ 2)

noncomputable def pairBe (x u : ℝ) : ℝ :=
    (u + x) ^ 2*(u ^ 2 - 4*x ^ 2 - 2*x + 4*u + 7*x ^ 3 - x*u ^ 2 - 12*u*x + 6*u*x ^ 2)/(12*u ^
      2*x*(-1 + x))

noncomputable def pairGa (x u : ℝ) : ℝ :=
    (-1 + x)*(2 - 10*x + 3*x ^ 2 + 9*u - 9*u*x)/2

noncomputable def pairD0 (x u : ℝ) : ℝ :=
    -(-94*x ^ 4 - 8*u ^ 2 - 4*x ^ 2 - 2*u ^ 3 + 18*x ^ 5 + 76*x ^ 3 - 356*u ^ 2*x ^ 2 - 286*u*x ^
      4 - 263*u*x ^ 2 - 108*u ^ 2*x ^ 4 - 18*π ^ 2*u ^ 3 - 4*π ^ 2*u ^ 2 - 2*u ^ 3*x ^ 2 + 4*x*u
      ^ 3 + 24*u*x + 36*u*x ^ 5 + 139*x*u ^ 2 + 333*u ^ 2*x ^ 3 + 485*u*x ^ 3 - 132*π ^ 2*u ^ 2*x
      ^ 2 - 108*π ^ 2*u ^ 3*x ^ 2 - 56*π ^ 2*u ^ 2*x ^ 4 - 32*u*π ^ 2*x ^ 4 - 28*u*π ^ 2*x ^ 2 -
      18*π ^ 2*u ^ 3*x ^ 4 + 4*u*x*π ^ 2 + 6*u*π ^ 2*x ^ 5 + 6*π ^ 2*u ^ 2*x ^ 5 + 50*u*π ^ 2*x ^
      3 + 50*x*π ^ 2*u ^ 2 + 72*x*π ^ 2*u ^ 3 + 72*π ^ 2*u ^ 3*x ^ 3 + 136*π ^ 2*u ^ 2*x ^
      3)/(24*u*(-1 + x)*(x - u + u*x))

noncomputable def pairDx (x u : ℝ) : ℝ :=
    x*(-54*u ^ 4 - 12*u ^ 3 - 7*x ^ 5 + 2*x ^ 3 + 4*x ^ 4 - 492*u ^ 3*x ^ 2 - 324*u ^ 4*x ^ 2 -
      200*u ^ 3*x ^ 4 - 163*u ^ 2*x ^ 2 - 163*u ^ 2*x ^ 4 - 54*u ^ 4*x ^ 4 - 14*u*x ^ 5 - 4*u*x ^
      2 + 2*u*x ^ 4 + 16*u*x ^ 3 + 18*u ^ 3*x ^ 5 + 20*x*u ^ 2 + 20*u ^ 2*x ^ 5 + 182*x*u ^ 3 +
      216*x*u ^ 4 + 216*u ^ 4*x ^ 3 + 286*u ^ 2*x ^ 3 + 504*u ^ 3*x ^ 3)/(12*u ^ 2*(-1 + x)*(x -
      u + u*x) ^ 2)

noncomputable def pairD1 (x u : ℝ) : ℝ :=
    -x*(-4*x ^ 3 + 4*u ^ 2 + 18*u ^ 3 - 58*u ^ 2*x ^ 3 - 54*x*u ^ 2 - 54*x*u ^ 3 - 46*u*x ^ 3 -
      18*u ^ 3*x ^ 3 - 6*u*x + 6*u ^ 2*x ^ 4 + 9*u*x ^ 4 + 43*u*x ^ 2 + 54*u ^ 3*x ^ 2 + 102*u ^
      2*x ^ 2)/(4*u*(x - u + u*x) ^ 2)

/-- The pair integrand per node, in closed form. -/
noncomputable def pairFe (x u : ℝ) : ℝ :=
  pairAl x u * log u + pairBe x u * log (u + x) + pairGa x u * dilogI (1 - x / ((1 - x) * u)) +
    pairD0 x u + pairDx x u * log x + pairD1 x u * log (1 - x)

/-- The pair integrand per node, from the two placements. -/
noncomputable def pairF (x u : ℝ) : ℝ :=
  psiIn x (x * (1 - x)) ((1 - x) * u) + phiOut x ((1 - x) / x * u) - 3 / 2 * (x ^ 2 / u)

noncomputable def nodeInAl (x u : ℝ) : ℝ :=
    -(u ^ 3 - 12*x ^ 3 + 4*u ^ 2 + 12*x ^ 4 - x*u ^ 3 - 27*u*x ^ 2 - 10*x*u ^ 2 + 4*u ^ 2*x ^ 2 +
      6*u*x + 18*u*x ^ 3)/(12*u*x*(-1 + x))

noncomputable def nodeInBe (x u : ℝ) : ℝ :=
    (u + x) ^ 2*(u ^ 2 - 4*x ^ 2 - 2*x + 4*u + 7*x ^ 3 - x*u ^ 2 - 12*u*x + 6*u*x ^ 2)/(12*u ^
      2*x*(-1 + x))

noncomputable def nodeInD0 (x u : ℝ) : ℝ :=
    (-8*u - 8*x - 4*x ^ 2 - 2*u ^ 2 + 16*x ^ 3 - 9*u*x ^ 2 + 2*x*u ^ 2 + 21*u*x)/(24*u*(-1 + x))

noncomputable def nodeInDx (x u : ℝ) : ℝ :=
    -x ^ 2*(-2 - 8*u - 4*x + 7*x ^ 2 + 8*u*x)/(12*u ^ 2*(-1 + x))

noncomputable def nodeOutAl (x u : ℝ) : ℝ :=
    -x*(-4*x ^ 3 + 4*u ^ 2 + 18*u ^ 3 - 58*u ^ 2*x ^ 3 - 54*x*u ^ 2 - 54*x*u ^ 3 - 46*u*x ^ 3 -
      18*u ^ 3*x ^ 3 - 6*u*x + 6*u ^ 2*x ^ 4 + 9*u*x ^ 4 + 43*u*x ^ 2 + 54*u ^ 3*x ^ 2 + 102*u ^
      2*x ^ 2)/(4*u*(x - u + u*x) ^ 2)

noncomputable def nodeOutGa (x u : ℝ) : ℝ :=
    (-1 + x)*(2 - 10*x + 3*x ^ 2 + 9*u - 9*u*x)/2

noncomputable def nodeOutD0 (x u : ℝ) : ℝ :=
    -(-48*x ^ 3 + 6*x ^ 2 + 9*x ^ 4 - 135*u*x ^ 3 - 54*x*u ^ 2 - 54*u ^ 2*x ^ 3 - 12*u*x + 2*π ^
      2*u ^ 2 + 9*π ^ 2*u ^ 3 + 18*u*x ^ 4 + 108*u ^ 2*x ^ 2 + 129*u*x ^ 2 - 27*x*π ^ 2*u ^ 3 -
      25*π ^ 2*u ^ 2*x ^ 3 - 23*x*π ^ 2*u ^ 2 - 13*u*π ^ 2*x ^ 3 - 9*π ^ 2*u ^ 3*x ^ 3 - 2*u*x*π
      ^ 2 + 3*u*π ^ 2*x ^ 4 + 3*π ^ 2*u ^ 2*x ^ 4 + 12*u*π ^ 2*x ^ 2 + 27*π ^ 2*u ^ 3*x ^ 2 +
      43*π ^ 2*u ^ 2*x ^ 2)/(12*u*(x - u + u*x))

noncomputable def nodeOutDx (x u : ℝ) : ℝ :=
    x*(-4*x ^ 3 + 4*u ^ 2 + 18*u ^ 3 - 58*u ^ 2*x ^ 3 - 54*x*u ^ 2 - 54*x*u ^ 3 - 46*u*x ^ 3 -
      18*u ^ 3*x ^ 3 - 6*u*x + 6*u ^ 2*x ^ 4 + 9*u*x ^ 4 + 43*u*x ^ 2 + 54*u ^ 3*x ^ 2 + 102*u ^
      2*x ^ 2)/(4*u*(x - u + u*x) ^ 2)

noncomputable def nodeOutD1 (x u : ℝ) : ℝ :=
    -x*(-4*x ^ 3 + 4*u ^ 2 + 18*u ^ 3 - 58*u ^ 2*x ^ 3 - 54*x*u ^ 2 - 54*x*u ^ 3 - 46*u*x ^ 3 -
      18*u ^ 3*x ^ 3 - 6*u*x + 6*u ^ 2*x ^ 4 + 9*u*x ^ 4 + 43*u*x ^ 2 + 54*u ^ 3*x ^ 2 + 102*u ^
      2*x ^ 2)/(4*u*(x - u + u*x) ^ 2)

theorem psiIn_node {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) :
    psiIn x (x * (1 - x)) ((1 - x) * u) = nodeInAl x u * log u + nodeInBe x u * log (u + x) +
      nodeInD0 x u + nodeInDx x u * log x := by
  have hx0 := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have e1 : log ((1 - x) * u + x * (1 - x)) = log (1 - x) + log (u + x) := by
    rw [← log_mul hx1.ne' (by positivity)]; congr 1; ring
  have e2 : log ((1 - x) * u) = log (1 - x) + log u := log_mul hx1.ne' hu.ne'
  have e3 : log (x * (1 - x)) = log x + log (1 - x) := log_mul hx0.ne' hx1.ne'
  unfold psiIn phiIn nodeInAl nodeInBe nodeInD0 nodeInDx
  rw [e1, e2, e3]
  generalize log (u + x) = Lux
  generalize log u = Lu
  generalize log x = Lx
  generalize log (1 - x) = L1x
  have hux : u + x ≠ 0 := by positivity
  have hx0' := hx0.ne'
  have hx1' := hx1.ne'
  have hu' := hu.ne'
  have hxm : -1 + x ≠ 0 := fun h => hx1' (by linarith)
  field_simp
  ring

theorem phiOut_node {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) (hup : x - u + u * x ≠ 0) :
    phiOut x ((1 - x) / x * u) = nodeOutAl x u * log u +
      nodeOutGa x u * dilogI (1 - x / ((1 - x) * u)) + nodeOutD0 x u + nodeOutDx x u * log x +
      nodeOutD1 x u * log (1 - x) := by
  have hx0 := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have e4 : log ((1 - x) / x * u) = log (1 - x) - log x + log u := by
    rw [log_mul (by positivity) hu.ne', log_div hx1.ne' hx0.ne']
  have e5 : 1 - 1 / ((1 - x) / x * u) = 1 - x / ((1 - x) * u) := by
    field_simp
  unfold phiOut outerKD nodeOutAl nodeOutGa nodeOutD0 nodeOutDx nodeOutD1
  rw [e4, e5]
  generalize dilogI (1 - x / ((1 - x) * u)) = D
  generalize log u = Lu
  generalize log x = Lx
  generalize log (1 - x) = L1x
  have hx0' := hx0.ne'
  have hx1' := hx1.ne'
  have hu' := hu.ne'
  have hh1 : (1 - x) / x * u - 1 ≠ 0 := by
    intro h
    apply hup
    field_simp at h
    linarith
  have hup2 : (1 - x) * u - x ≠ 0 := fun h => hup (by linarith)
  have hup3 : u - u * x - x ≠ 0 := fun h => hup (by linarith)
  have hup4 : x - u + x * u ≠ 0 := fun h => hup (by linarith)
  have hxm : -1 + x ≠ 0 := fun h => hx1' (by linarith)
  field_simp
  ring

theorem pairF_eq {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) (hup : x - u + u * x ≠ 0) :
    pairF x u = pairFe x u := by
  have hx0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hu' := hu.ne'
  have hup4 : x - u + x * u ≠ 0 := fun h => hup (by linarith)
  have hxm : -1 + x ≠ 0 := fun h => hx1 (by linarith)
  have hAl : nodeInAl x u + nodeOutAl x u = pairAl x u := by
    unfold nodeInAl nodeOutAl pairAl; field_simp; ring
  have hBe : nodeInBe x u = pairBe x u := by
    unfold nodeInBe pairBe; field_simp
  have hGa : nodeOutGa x u = pairGa x u := by
    unfold nodeOutGa pairGa; field_simp
  have hD0 : nodeInD0 x u + nodeOutD0 x u - 3 / 2 * (x ^ 2 / u) = pairD0 x u := by
    unfold nodeInD0 nodeOutD0 pairD0; field_simp; ring
  have hDx : nodeInDx x u + nodeOutDx x u = pairDx x u := by
    unfold nodeInDx nodeOutDx pairDx; field_simp; ring
  have hD1 : nodeOutD1 x u = pairD1 x u := by
    unfold nodeOutD1 pairD1; field_simp
  rw [pairF, psiIn_node hx hu, phiOut_node hx hu hup, pairFe]
  linear_combination log u * hAl + log (u + x) * hBe + dilogI (1 - x / ((1 - x) * u)) * hGa +
    hD0 + log x * hDx + log (1 - x) * hD1

end QED.ChainProof.SetCK
