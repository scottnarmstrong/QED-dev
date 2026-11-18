/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassIntegrableFurryRouting

/-!
# The Furry triangle `F₊`: the numerator is even in the loop mass

Part of obligation O2-7 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3) for the class `Fp`. The
numerator (`QED.TwoLoop.Bridge.amplitudeNumerator`) of the amplitude of `F₊` with loop flavour `f`
depends on the flavour only through the loop mass `M_f` (`amplitudeNumerator_flavF`); as a
function of the loop mass `M` (`furryNum`) it is

`N(M) = N(0) + M² (N(1) - N(0))` (`furryNum_eq`),

at every line momentum and all indices. So `N_f = E₀ + M_f² E₂` with `E₀ = N(0)` and
`E₂ = N(1) - N(0)` independent of the flavour.

## Proof

Term by term in the spinor index sum. Each loop propagator numerator `(M - k̸)_{ba}` is affine in
`M` (`electronNumerator_affine`), so each term is a cubic polynomial in `M`; it is enough that its
odd part vanishes. With `s = diag γ⁵ = (-1, -1, 1, 1)` (`sgn`), `γ⁵ X γ⁵ = c X` gives
`X_{ab} s_a s_b = c X_{ab}` (`entry_mul_sgn`): the gamma matrices and `k̸` change sign
(`gamma_mul_sgn`, `electronNumerator_zero_mul_sgn`) and `1` does not (`unit_mul_sgn`). Around the
closed loop every spinor index of the loop vertices occurs exactly twice, so the product of the
three vertex factors times the product of the signs of the three loop propagators is minus
itself, which kills the terms of odd degree in `M` (`even_core`, `term_even`). This is the
pointwise form of `Tr[γ γ γ γ γ] = Tr[γ γ γ] = 0`; no trace is formed.
-/

@[expose] public section

namespace QED.TwoLoop.FurryIntegrable

open Complex QED.WickModel QED.TwoLoop.Enumeration
open QED.TwoLoop.Furry (cP lineP tail_lineP val_lineP prod_lineP)
open QED.TwoLoop.Bridge (amplitudeNumerator electronNumerator gamma5 gamma5_conj_gamma
  gamma5_conj_slash gamma5_mul_gamma5)

/-! ### The loop mass as a parameter -/

/-- The parameters with the mass of the regulator fermion of flavour `1` replaced by `M`. -/
def withLoopMass (P : Params) (M : ℝ) : Params := { P with M₁ := M }

section WithLoopMass

variable (P : Params) (M : ℝ)

@[simp] theorem withLoopMass_e : (withLoopMass P M).e = P.e := rfl
@[simp] theorem withLoopMass_δ₁ : (withLoopMass P M).δ₁ = P.δ₁ := rfl
@[simp] theorem withLoopMass_δ₂ : (withLoopMass P M).δ₂ = P.δ₂ := rfl
@[simp] theorem withLoopMass_δm : (withLoopMass P M).δm = P.δm := rfl
@[simp] theorem withLoopMass_δ₃ : (withLoopMass P M).δ₃ = P.δ₃ := rfl
@[simp] theorem withLoopMass_m : (withLoopMass P M).m = P.m := rfl
@[simp] theorem withLoopMass_mγ : (withLoopMass P M).mγ = P.mγ := rfl
@[simp] theorem withLoopMass_Λ : (withLoopMass P M).Λ = P.Λ := rfl
@[simp] theorem withLoopMass_mass_zero : (withLoopMass P M).mass 0 = P.m := rfl
@[simp] theorem withLoopMass_mass_one : (withLoopMass P M).mass 1 = M := rfl

end WithLoopMass

/-- The numerator of the amplitude of `F₊` with loop mass `M`: the open line of mass `m`, the
loop of mass `M`, at the line momenta `k`. -/
noncomputable def furryNum (P : Params) (M : ℝ) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line cP → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) : ℂ :=
  amplitudeNumerator (withLoopMass P M) cP (flavF 1) pIn kIn k αOut βIn μ

theorem mass_flavF (P : Params) (f : Fin 3) (t : Wick.FermionVertex (gauges 5)) :
    P.mass ((flavF f).1 t) = (withLoopMass P (P.mass f)).mass ((flavF 1).1 t) := by
  obtain ⟨j, hj⟩ := t
  fin_cases j <;> fin_cases f <;> rfl

/-- **The numerator of flavour `f` is the numerator at the loop mass `M_f`.** -/
theorem amplitudeNumerator_flavF (P : Params) (f : Fin 3) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line cP → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    amplitudeNumerator P cP (flavF f) pIn kIn k αOut βIn μ =
      furryNum P (P.mass f) pIn kIn k αOut βIn μ := by
  unfold furryNum amplitudeNumerator
  simp only [mass_flavF P f]
  rfl

/-! ### Signs from `γ⁵` -/

/-- The diagonal of `γ⁵`. -/
def sgn : Fin 4 → ℂ := ![-1, -1, 1, 1]

theorem conj_gamma5_apply (X : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    (gamma5 * X * gamma5) a b = sgn a * X a b * sgn b := by
  rw [gamma5, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

theorem entry_mul_sgn {X : Matrix (Fin 4) (Fin 4) ℂ} {c : ℂ} (h : gamma5 * X * gamma5 = c • X)
    (a b : Fin 4) : X a b * (sgn a * sgn b) = c * X a b := by
  have h' := congrFun (congrFun h a) b
  rw [conj_gamma5_apply, Matrix.smul_apply, smul_eq_mul] at h'
  linear_combination h'

theorem gamma_mul_sgn (μ a b : Fin 4) :
    Dirac.gamma μ a b * (sgn a * sgn b) = -Dirac.gamma μ a b := by
  have h := entry_mul_sgn (c := -1) (X := Dirac.gamma μ)
    (by rw [gamma5_conj_gamma, neg_one_smul]) a b
  linear_combination h

theorem electronNumerator_zero_mul_sgn (k : Fin 4 → ℝ) (a b : Fin 4) :
    electronNumerator 0 k a b * (sgn a * sgn b) = -electronNumerator 0 k a b := by
  have h := entry_mul_sgn (c := -1) (X := electronNumerator 0 k) (by
    simp only [electronNumerator, Complex.ofReal_zero, zero_smul, zero_sub, Matrix.mul_neg,
      Matrix.neg_mul, gamma5_conj_slash, neg_neg, neg_one_smul]) a b
  linear_combination h

theorem unit_mul_sgn (k : Fin 4 → ℝ) (a b : Fin 4) :
    (electronNumerator 1 k a b - electronNumerator 0 k a b) * (sgn a * sgn b) =
      electronNumerator 1 k a b - electronNumerator 0 k a b := by
  have h1 : electronNumerator 1 k - electronNumerator 0 k = 1 := by
    simp [electronNumerator]
  have h := entry_mul_sgn (c := 1) (X := electronNumerator 1 k - electronNumerator 0 k) (by
    rw [h1, Matrix.mul_one, gamma5_mul_gamma5, one_smul]) a b
  rw [Matrix.sub_apply] at h
  linear_combination h

/-- `(M - k̸)_{ab}` is affine in `M`. -/
theorem electronNumerator_affine (M : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    electronNumerator M k a b = electronNumerator 0 k a b +
      (M : ℂ) * (electronNumerator 1 k a b - electronNumerator 0 k a b) := by
  simp only [electronNumerator, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_zero, Complex.ofReal_one]
  ring

/-! ### The odd part vanishes -/

/-- A monomial `w` with `w S = w`, multiplied by `G` with `G S = -G`, vanishes. -/
theorem mul_eq_zero_of_sign {G w S : ℂ} (hG : G * S = -G) (hw : w * S = w) : G * w = 0 := by
  have h : G * w = -(G * w) := by
    calc G * w = G * (w * S) := by rw [hw]
      _ = (G * S) * w := by ring
      _ = -(G * w) := by rw [hG]; ring
  linear_combination h / 2

/-- **The cubic with vanishing odd part.** If `G σ₁σ₂σ₃ = -G`, `xᵢ σᵢ = -xᵢ` and `uᵢ σᵢ = uᵢ`,
then `G ∏ᵢ (xᵢ + M uᵢ)` is even in `M`, hence `G ∏ᵢ x_i + M² (G ∏ᵢ (xᵢ + uᵢ) - G ∏ᵢ xᵢ)`. -/
theorem even_core {G u1 u2 u3 x1 x2 x3 σ1 σ2 σ3 : ℂ} (hG : G * (σ1 * σ2 * σ3) = -G)
    (hu1 : u1 * σ1 = u1) (hu2 : u2 * σ2 = u2) (hu3 : u3 * σ3 = u3)
    (hx1 : x1 * σ1 = -x1) (hx2 : x2 * σ2 = -x2) (hx3 : x3 * σ3 = -x3) (M : ℂ) :
    G * ((x1 + M * u1) * (x2 + M * u2) * (x3 + M * u3)) =
      G * (x1 * x2 * x3) +
        M ^ 2 * (G * ((x1 + u1) * (x2 + u2) * (x3 + u3)) - G * (x1 * x2 * x3)) := by
  have k1 : G * (u1 * x2 * x3) = 0 := mul_eq_zero_of_sign hG (by
    calc u1 * x2 * x3 * (σ1 * σ2 * σ3) = (u1 * σ1) * (x2 * σ2) * (x3 * σ3) := by ring
      _ = u1 * x2 * x3 := by rw [hu1, hx2, hx3]; ring)
  have k2 : G * (x1 * u2 * x3) = 0 := mul_eq_zero_of_sign hG (by
    calc x1 * u2 * x3 * (σ1 * σ2 * σ3) = (x1 * σ1) * (u2 * σ2) * (x3 * σ3) := by ring
      _ = x1 * u2 * x3 := by rw [hx1, hu2, hx3]; ring)
  have k3 : G * (x1 * x2 * u3) = 0 := mul_eq_zero_of_sign hG (by
    calc x1 * x2 * u3 * (σ1 * σ2 * σ3) = (x1 * σ1) * (x2 * σ2) * (u3 * σ3) := by ring
      _ = x1 * x2 * u3 := by rw [hx1, hx2, hu3]; ring)
  have k4 : G * (u1 * u2 * u3) = 0 := mul_eq_zero_of_sign hG (by
    calc u1 * u2 * u3 * (σ1 * σ2 * σ3) = (u1 * σ1) * (u2 * σ2) * (u3 * σ3) := by ring
      _ = u1 * u2 * u3 := by rw [hu1, hu2, hu3])
  linear_combination (M - M ^ 2) * (k1 + k2 + k3) + (M ^ 3 - M ^ 2) * k4

/-- **One term of the spinor sum is even in the loop mass**, in the shape of the summand of
`amplitudeNumerator` for `F₊`: the factor `W` of the external indices, the five vertex factors,
the open-line factor `n₀`, the three loop propagator numerators `yᵢ` (at `M`), `zᵢ` (at `0`),
`wᵢ` (at `1`), and the photon factor. The signs: the vertex `t` has indices `(aₜ, bₜ)`; the loop
lines run `4 → 2`, `2 → 3`, `3 → 4`. -/
theorem term_even {W V0 V1 V2 V3 V4 n0 Ph c y1 y2 y3 z1 z2 z3 w1 w2 w3 a2 b2 a3 b3 a4 b4 : ℂ}
    (M : ℂ) (hV2 : V2 * (a2 * b2) = -V2) (hV3 : V3 * (a3 * b3) = -V3)
    (hV4 : V4 * (a4 * b4) = -V4)
    (hz1 : z1 * (b2 * a4) = -z1) (hz2 : z2 * (b3 * a2) = -z2) (hz3 : z3 * (b4 * a3) = -z3)
    (hu1 : (w1 - z1) * (b2 * a4) = w1 - z1) (hu2 : (w2 - z2) * (b3 * a2) = w2 - z2)
    (hu3 : (w3 - z3) * (b4 * a3) = w3 - z3)
    (hy1 : y1 = z1 + M * (w1 - z1)) (hy2 : y2 = z2 + M * (w2 - z2))
    (hy3 : y3 = z3 + M * (w3 - z3)) :
    W * (V0 * V1 * V2 * V3 * V4 * (n0 * (c * y1) * (c * y2) * (c * y3)) * Ph) =
      W * (V0 * V1 * V2 * V3 * V4 * (n0 * (c * z1) * (c * z2) * (c * z3)) * Ph) +
        M ^ 2 * (W * (V0 * V1 * V2 * V3 * V4 * (n0 * (c * w1) * (c * w2) * (c * w3)) * Ph) -
          W * (V0 * V1 * V2 * V3 * V4 * (n0 * (c * z1) * (c * z2) * (c * z3)) * Ph)) := by
  have hG : V2 * V3 * V4 * ((b2 * a4) * (b3 * a2) * (b4 * a3)) = -(V2 * V3 * V4) := by
    calc V2 * V3 * V4 * ((b2 * a4) * (b3 * a2) * (b4 * a3)) =
        (V2 * (a2 * b2)) * (V3 * (a3 * b3)) * (V4 * (a4 * b4)) := by ring
      _ = -(V2 * V3 * V4) := by rw [hV2, hV3, hV4]; ring
  have h := even_core hG hu1 hu2 hu3 hz1 hz2 hz3 M
  subst hy1 hy2 hy3
  linear_combination (W * V0 * V1 * n0 * c ^ 3 * Ph) * h

/-! ### The numerator -/

theorem sum_even {ι : Type*} (s : Finset ι) {X0 X1 XM : ι → ℂ} (c : ℂ)
    (h : ∀ i ∈ s, XM i = X0 i + c * (X1 i - X0 i)) :
    ∑ i ∈ s, XM i = ∑ i ∈ s, X0 i + c * (∑ i ∈ s, X1 i - ∑ i ∈ s, X0 i) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl h

/-- **The numerator of `F₊` is even in the loop mass**: `N(M) = N(0) + M² (N(1) - N(0))`, at
every line momentum and all indices. -/
theorem furryNum_eq (P : Params) (M : ℝ) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line cP → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    furryNum P M pIn kIn k αOut βIn μ =
      furryNum P 0 pIn kIn k αOut βIn μ + ((M ^ 2 : ℝ) : ℂ) *
        (furryNum P 1 pIn kIn k αOut βIn μ - furryNum P 0 pIn kIn k αOut βIn μ) := by
  obtain ⟨t0, t1, t2, t3⟩ := tail_lineP
  obtain ⟨v0, v1, v2, v3⟩ := val_lineP
  obtain ⟨-, f1, f2, f3, f4⟩ := flavF_apply 1
  unfold furryNum amplitudeNumerator
  refine sum_even _ _ fun α _ => sum_even _ _ fun β _ => sum_even _ _ fun lor _ => ?_
  simp only [Fin.prod_univ_five, prod_lineP, QED.TwoLoop.NestedVP.vertexFactor_fv5, t0, t1, t2, t3,
    v0, v1, v2, v3, f1, f2, f3, f4, withLoopMass_e, withLoopMass_δ₁, withLoopMass_δ₂,
    withLoopMass_δm, withLoopMass_δ₃, withLoopMass_m, withLoopMass_mγ, withLoopMass_Λ,
    withLoopMass_mass_zero, withLoopMass_mass_one, Complex.ofReal_pow]
  refine term_even (M : ℂ) (a2 := sgn (α (fv5 2))) (b2 := sgn (β (fv5 2)))
    (a3 := sgn (α (fv5 3))) (b3 := sgn (β (fv5 3))) (a4 := sgn (α (fv5 4)))
    (b4 := sgn (β (fv5 4))) ?_ ?_ ?_ (electronNumerator_zero_mul_sgn _ _ _)
    (electronNumerator_zero_mul_sgn _ _ _) (electronNumerator_zero_mul_sgn _ _ _)
    (unit_mul_sgn _ _ _) (unit_mul_sgn _ _ _) (unit_mul_sgn _ _ _)
    (electronNumerator_affine _ _ _ _) (electronNumerator_affine _ _ _ _)
    (electronNumerator_affine _ _ _ _) <;>
  · linear_combination (I * (P.e : ℂ)) * gamma_mul_sgn _ _ _

end QED.TwoLoop.FurryIntegrable

end
