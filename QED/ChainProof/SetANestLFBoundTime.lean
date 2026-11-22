/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2FAlg
public import QED.TwoLoop.VPHalfAtLimitFeynman
public import QED.WickModel.VacuumPolarizationEnergyFirst
public import QED.Integration.FeynmanParameterGeneral
public import QED.Integration.LoopBounds

/-!
# Set (a), obligation (N): the energy integral of the `δ₂, δ_m` bubble in closed form

Helper level for the inner bound of the fermion-counterterm classes `FA`, `FB` of obligation (N)
(`QED.ChainProof.SetANest.LoopNested`): the inner integrand is the block-summed inserted bubble
`QED.GradedProof.VP2.insG A B d₂ d_m M ε (p + q) q` (counterterm on the line of momentum `q`).
For one flavour of mass `M` and `ε > 0`:

* `insTr_eq_tau`: by `y̸ y̸ = -(y·y)`, the trace is `d₂ (y·y) τ + M² (…) + M⁴ d_m Tr[AB]` with
  `τ(x, y) = Tr[A x̸ B y̸]` (`insTau`), for `A`, `B` anticommuting with `γ⁵`;
* `insTr_cons_eq`: along `q = (t, v⃗)` the trace is a quartic polynomial in `s = t + a`, with the
  even coefficients `insP0 + M² insP2 + M⁴ insP4`, `insQ0 + M² insQ2`, `insN4`;
* `inv_mul_inv_sq_eq_integral`: `1/(A B²) = ∫₀¹ 2 (1 - u) (u A + (1 - u) B)⁻³ du`, the
  combined denominator being `QED.WickModel.SelfEnergyLimit.combDen M M ε p u q`;
* `integral_quartic_mul_shifted_three`: `∫ N(t + a) ((t + a)² + z)⁻³ dt` for a quartic `N`;
* **`integral_insG_time`**: the energy integral of the flavour term is
  `∫₀¹ 2 (1 - u) insCF(u) du`, with the closed form `insCF` a combination of
  `z^{-5/2}`, `z^{-3/2}`, `z^{-1/2}`, `z = -W(u) + iε`.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.ChainProof.SetANest

open QED.GradedProof.VP2 QED.TwoLoop.Bridge QED.TwoLoop.VPHalfAtLimit QED.Integration
open QED.WickModel.SelfEnergyLimit (massW combDen combDen_cons)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### The trace -/

/-- `τ(x, y) = Tr[A x̸ B y̸]`. -/
noncomputable def insTau (A B : Mat) (x y : Fin 4 → ℝ) : ℂ :=
  (A * (Dirac.slash x * (B * Dirac.slash y))).trace

theorem insTr_eq_tau {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (d₂ dm M : ℝ)
    (x y : Fin 4 → ℝ) :
    insTr A B d₂ dm M x y = (d₂ : ℂ) * ((Minkowski.dot y y : ℝ) : ℂ) * insTau A B x y +
      (M : ℂ) ^ 2 * (-((dm : ℂ) - 2 * d₂) * ((Minkowski.dot y y : ℝ) : ℂ) * (A * B).trace +
        (2 * (dm : ℂ) - d₂) * insTau A B x y) + ((M : ℂ) ^ 2) ^ 2 * ((dm : ℂ) * (A * B).trace) := by
  rw [insTr_eq hA hB]
  have hy := Dirac.slash_mul_slash y
  have e1 : Dirac.slash y * (Dirac.slash y * Dirac.slash y) =
      ((-Minkowski.dot y y : ℝ) : ℂ) • Dirac.slash y := by
    rw [← Matrix.mul_assoc, hy, Matrix.smul_mul, Matrix.one_mul]
  unfold insT0 insT2 insT4 insTau
  rw [e1, hy]
  simp only [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_one, smul_eq_mul]
  push_cast
  ring

/-- The unit time vector. -/
def eT : Fin 4 → ℝ := Fin.cons 1 0

/-- The spatial part with the energy `-a`. -/
def insY (a : ℝ) (v : Fin 3 → ℝ) : Fin 4 → ℝ := Fin.cons (-a) v

theorem cons_eq_insY_add (t a : ℝ) (v : Fin 3 → ℝ) :
    (Fin.cons t v : Fin 4 → ℝ) = insY a v + (t + a) • eT := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [insY, eT]
  · simp [insY, eT]

theorem insTau_add_smul (A B : Mat) (X Y e : Fin 4 → ℝ) (s : ℝ) :
    insTau A B (X + s • e) (Y + s • e) = insTau A B X Y +
      (s : ℂ) * (insTau A B e Y + insTau A B X e) + (s : ℂ) ^ 2 * insTau A B e e := by
  simp only [insTau, Dirac.slash_add, Dirac.slash_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring

theorem dot_cons_cons (t : ℝ) (v : Fin 3 → ℝ) :
    Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v) = -t ^ 2 + ∑ k, v k ^ 2 := by
  have h0 : (Fin.cons t v : Fin 4 → ℝ) 0 = t := rfl
  have h1 : (Fin.cons t v : Fin 4 → ℝ) 1 = v 0 := rfl
  have h2 : (Fin.cons t v : Fin 4 → ℝ) 2 = v 1 := rfl
  have h3 : (Fin.cons t v : Fin 4 → ℝ) 3 = v 2 := rfl
  rw [Minkowski.dot_eq, h0, h1, h2, h3, Fin.sum_univ_three]
  ring

/-! ### The coefficients in `s = t + a` -/

section Coeff

variable (A B : Mat) (d₂ dm : ℝ) (p : Fin 4 → ℝ) (a : ℝ) (v : Fin 3 → ℝ)

/-- `α₀ = -a² + |v⃗|²`, the constant term of `q·q` in `s`. -/
noncomputable def insAl (a : ℝ) (v : Fin 3 → ℝ) : ℂ := ((-a ^ 2 + ∑ k, v k ^ 2 : ℝ) : ℂ)

/-- The constant term of `τ` in `s`. -/
noncomputable def insT0' : ℂ := insTau A B (p + insY a v) (insY a v)

/-- The linear term of `τ` in `s`. -/
noncomputable def insT1' : ℂ := insTau A B eT (insY a v) + insTau A B (p + insY a v) eT

/-- The quadratic term of `τ` in `s`. -/
noncomputable def insT2' : ℂ := insTau A B eT eT

/-- `s⁰`, `M⁰`. -/
noncomputable def insP0 : ℂ := (d₂ : ℂ) * insAl a v * insT0' A B p a v

/-- `s⁰`, `M²`. -/
noncomputable def insP2 : ℂ :=
  -((dm : ℂ) - 2 * d₂) * insAl a v * (A * B).trace + (2 * (dm : ℂ) - d₂) * insT0' A B p a v

/-- `s⁰`, `M⁴`. -/
noncomputable def insP4 : ℂ := (dm : ℂ) * (A * B).trace

/-- `s²`, `M⁰`. -/
noncomputable def insQ0 : ℂ :=
  (d₂ : ℂ) * (insAl a v * insT2' A B + 2 * a * insT1' A B p a v - insT0' A B p a v)

/-- `s²`, `M²`. -/
noncomputable def insQ2 : ℂ :=
  ((dm : ℂ) - 2 * d₂) * (A * B).trace + (2 * (dm : ℂ) - d₂) * insT2' A B

/-- `s⁴`. -/
noncomputable def insN4 : ℂ := -(d₂ : ℂ) * insT2' A B

/-- `s¹`. -/
noncomputable def insO1 (M : ℝ) : ℂ :=
  (d₂ : ℂ) * (insAl a v * insT1' A B p a v + 2 * a * insT0' A B p a v) +
    (M : ℂ) ^ 2 * (-((dm : ℂ) - 2 * d₂) * (2 * a) * (A * B).trace +
      (2 * (dm : ℂ) - d₂) * insT1' A B p a v)

/-- `s³`. -/
noncomputable def insO3 : ℂ := (d₂ : ℂ) * (2 * a * insT2' A B - insT1' A B p a v)

end Coeff

/-- **The trace along `q = (t, v⃗)` as a quartic in `s = t + a`.** -/
theorem insTr_cons_eq {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (d₂ dm M : ℝ)
    (p : Fin 4 → ℝ) (a t : ℝ) (v : Fin 3 → ℝ) :
    insTr A B d₂ dm M (p + Fin.cons t v) (Fin.cons t v) =
      (insP0 A B d₂ p a v + (M : ℂ) ^ 2 * insP2 A B d₂ dm p a v +
          ((M : ℂ) ^ 2) ^ 2 * insP4 A B dm) +
        insO1 A B d₂ dm p a v M * ((t : ℂ) + a) +
        (insQ0 A B d₂ p a v + (M : ℂ) ^ 2 * insQ2 A B d₂ dm) * ((t : ℂ) + a) ^ 2 +
        insO3 A B d₂ p a v * ((t : ℂ) + a) ^ 3 + insN4 A B d₂ * ((t : ℂ) + a) ^ 4 := by
  have hτ : insTau A B (p + Fin.cons t v) (Fin.cons t v) =
      insT0' A B p a v + ((t + a : ℝ) : ℂ) * insT1' A B p a v +
        ((t + a : ℝ) : ℂ) ^ 2 * insT2' A B := by
    rw [cons_eq_insY_add t a v, ← add_assoc, insTau_add_smul]
    rfl
  rw [insTr_eq_tau hA hB, hτ, dot_cons_cons]
  simp only [insP0, insP2, insP4, insQ0, insQ2, insN4, insO1, insO3, insAl]
  push_cast
  ring

/-! ### Feynman parameters for `1/(A B²)` -/

theorem combDen_eq (M ε : ℝ) (p ℓ : Fin 4 → ℝ) (u : ℝ) :
    combDen M M ε p u ℓ = (u : ℂ) * propDenom M ε (p + ℓ) + (1 - u) * propDenom M ε ℓ :=
  rfl

/-- `1/(A B²) = ∫₀¹ 2 (1 - u) (u A + (1 - u) B)⁻³ du`. -/
theorem inv_mul_inv_sq_eq_integral {ε : ℝ} (hε : 0 < ε) (M : ℝ) (p ℓ : Fin 4 → ℝ) :
    (propDenom M ε (p + ℓ))⁻¹ * ((propDenom M ε ℓ)⁻¹) ^ 2 =
      ∫ u in Ioc (0 : ℝ) 1, 2 * (1 - (u : ℂ)) * combDen M M ε p u ℓ ^ (-3 : ℤ) := by
  have hA : (propDenom M ε (p + ℓ)).im < 0 := by rw [im_propDenom]; linarith
  have hB : (propDenom M ε ℓ).im < 0 := by rw [im_propDenom]; linarith
  have h := QED.Integration.Feynman.integral_one_sub_pow_mul_inv_pow hB hA 1
  rw [intervalIntegral.integral_of_le zero_le_one] at h
  have e : ∀ u : ℝ, 2 * (1 - (u : ℂ)) * combDen M M ε p u ℓ ^ (-3 : ℤ) =
      2 * ((1 - (u : ℂ)) ^ 1 * (((u : ℂ) * propDenom M ε (p + ℓ) +
        (1 - u) * propDenom M ε ℓ) ^ (1 + 2))⁻¹) := fun u => by
    rw [combDen_eq, zpow_neg, pow_one]
    norm_num
    ring
  simp_rw [e]
  rw [integral_const_mul, h]
  have h1 := QED.Integration.ne_zero_of_im_neg hA
  have h2 := QED.Integration.ne_zero_of_im_neg hB
  field_simp
  push_cast
  ring

/-! ### The energy integral of a quartic against `((t + a)² + z)⁻³` -/

theorem integral_cube_mul_sq_add_zpow (z : ℂ) (k : ℤ) :
    ∫ t : ℝ, (t : ℂ) ^ 3 * ((t : ℂ) ^ 2 + z) ^ k = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ => (t : ℂ) ^ 3 * ((t : ℂ) ^ 2 + z) ^ k) volume
  simp only [ofReal_neg, neg_sq, Odd.neg_pow (⟨1, rfl⟩ : Odd 3), neg_mul, integral_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

theorem cube_mul_sq_add_zpow {z : ℂ} (hz : z ∈ slitPlane) (t : ℝ) :
    (t : ℂ) ^ 3 * ((t : ℂ) ^ 2 + z) ^ (-3 : ℤ) =
      (t : ℂ) * ((t : ℂ) ^ 2 + z) ^ (-((0 + 2 : ℕ) : ℤ)) -
        z * ((t : ℂ) * ((t : ℂ) ^ 2 + z) ^ (-((1 + 2 : ℕ) : ℤ))) := by
  have h := sq_add_ne_zero_of_mem_slitPlane hz t
  simp only [zpow_neg]
  norm_num
  field_simp
  ring

theorem quartic_mul_sq_add_zpow {z : ℂ} (hz : z ∈ slitPlane) (t : ℝ) :
    (t : ℂ) ^ 4 * ((t : ℂ) ^ 2 + z) ^ (-3 : ℤ) =
      ((t : ℂ) ^ 2 + z) ^ (-((1 : ℕ) : ℤ)) - 2 * z * ((t : ℂ) ^ 2 + z) ^ (-((2 : ℕ) : ℤ)) +
        z ^ 2 * ((t : ℂ) ^ 2 + z) ^ (-((3 : ℕ) : ℤ)) := by
  have h := sq_add_ne_zero_of_mem_slitPlane hz t
  simp only [zpow_neg, Nat.cast_ofNat, Nat.cast_one]
  norm_num
  field_simp
  ring

theorem cpow_mul_self {z : ℂ} (hz : z ≠ 0) (w : ℂ) : z * z ^ w = z ^ (w + 1) := by
  rw [Complex.cpow_add _ _ hz, Complex.cpow_one, mul_comm]

/-- **The energy integral of a quartic against `((t + a)² + z)⁻³`.** -/
theorem integral_quartic_mul_shifted_three {z : ℂ} (hz : z ∈ slitPlane) (a : ℝ)
    (c0 c1 c2 c3 c4 : ℂ) :
    ∫ t : ℝ, (c0 + c1 * ((t : ℂ) + a) + c2 * ((t : ℂ) + a) ^ 2 + c3 * ((t : ℂ) + a) ^ 3 +
        c4 * ((t : ℂ) + a) ^ 4) * (((t : ℂ) + a) ^ 2 + z) ^ (-3 : ℤ) =
      c0 * (energyConst 3 : ℂ) * z ^ (-(5 / 2 : ℂ)) +
        c2 * ((energyConst 2 - energyConst 3 : ℝ) : ℂ) * z ^ (-(3 / 2 : ℂ)) +
        c4 * ((energyConst 1 - 2 * energyConst 2 + energyConst 3 : ℝ) : ℂ) *
          z ^ (-(1 / 2 : ℂ)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  set f0 : ℝ → ℂ := fun s => ((s : ℂ) ^ 2 + z) ^ (-3 : ℤ)
  set f1 : ℝ → ℂ := fun s => (s : ℂ) * ((s : ℂ) ^ 2 + z) ^ (-3 : ℤ)
  set f2 : ℝ → ℂ := fun s => (s : ℂ) ^ 2 * ((s : ℂ) ^ 2 + z) ^ (-3 : ℤ)
  set f3 : ℝ → ℂ := fun s => (s : ℂ) ^ 3 * ((s : ℂ) ^ 2 + z) ^ (-3 : ℤ)
  set f4 : ℝ → ℂ := fun s => (s : ℂ) ^ 4 * ((s : ℂ) ^ 2 + z) ^ (-3 : ℤ)
  have i0 : Integrable f0 := integrable_sq_add_zpow hz 3 (by norm_num)
  have i1 : Integrable f1 := integrable_mul_sq_add_zpow hz 1
  have i2 : Integrable f2 := integrable_sq_mul_sq_add_zpow hz 1
  have i3 : Integrable f3 := by
    refine ((integrable_mul_sq_add_zpow hz 0).sub
      ((integrable_mul_sq_add_zpow hz 1).const_mul z)).congr
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply, f3]
    rw [cube_mul_sq_add_zpow hz t]
  have i4 : Integrable f4 := by
    refine (((integrable_sq_add_zpow hz 1 le_rfl).sub
      ((integrable_sq_add_zpow hz 2 (by norm_num)).const_mul (2 * z))).add
      ((integrable_sq_add_zpow hz 3 (by norm_num)).const_mul (z ^ 2))).congr
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply, Pi.add_apply, f4]
    rw [quartic_mul_sq_add_zpow hz t]
  set G : ℝ → ℂ := fun s => c0 * f0 s + c1 * f1 s + c2 * f2 s + c3 * f3 s + c4 * f4 s
  have hpt : ∀ t : ℝ, (c0 + c1 * ((t : ℂ) + a) + c2 * ((t : ℂ) + a) ^ 2 +
      c3 * ((t : ℂ) + a) ^ 3 + c4 * ((t : ℂ) + a) ^ 4) * (((t : ℂ) + a) ^ 2 + z) ^ (-3 : ℤ) =
      G (t + a) := fun t => by
    simp only [G, f0, f1, f2, f3, f4, ofReal_add]
    ring
  simp_rw [hpt]
  rw [integral_add_right_eq_self G a]
  have I0 : ∫ s, f0 s = (energyConst 3 : ℂ) * z ^ (-(5 / 2 : ℂ)) := by
    have h := integral_sq_add_zpow_eq 3 (by norm_num) hz
    rw [show (-((3 : ℕ) : ℤ)) = (-3 : ℤ) by norm_num,
      show (1 / 2 : ℂ) - ((3 : ℕ) : ℂ) = -(5 / 2) by norm_num] at h
    exact h
  have I1 : ∫ s, f1 s = 0 := integral_mul_sq_add_zpow z (-3)
  have I2 : ∫ s, f2 s = ((energyConst 2 - energyConst 3 : ℝ) : ℂ) * z ^ (-(3 / 2 : ℂ)) := by
    have h := integral_sq_mul_sq_add_zpow hz 1
    rw [show (-((1 + 2 : ℕ) : ℤ)) = (-3 : ℤ) by norm_num,
      show (3 / 2 : ℂ) - ((1 + 2 : ℕ) : ℂ) = -(3 / 2) by norm_num] at h
    exact h
  have I3 : ∫ s, f3 s = 0 := integral_cube_mul_sq_add_zpow z (-3)
  have I4 : ∫ s, f4 s = ((energyConst 1 - 2 * energyConst 2 + energyConst 3 : ℝ) : ℂ) *
      z ^ (-(1 / 2 : ℂ)) := by
    have e : ∀ s : ℝ, f4 s = ((s : ℂ) ^ 2 + z) ^ (-((1 : ℕ) : ℤ)) -
        2 * z * ((s : ℂ) ^ 2 + z) ^ (-((2 : ℕ) : ℤ)) +
        z ^ 2 * ((s : ℂ) ^ 2 + z) ^ (-((3 : ℕ) : ℤ)) := quartic_mul_sq_add_zpow hz
    have j1 : Integrable fun s : ℝ => ((s : ℂ) ^ 2 + z) ^ (-((1 : ℕ) : ℤ)) :=
      integrable_sq_add_zpow hz 1 le_rfl
    have j2 : Integrable fun s : ℝ => 2 * z * ((s : ℂ) ^ 2 + z) ^ (-((2 : ℕ) : ℤ)) :=
      (integrable_sq_add_zpow hz 2 (by norm_num)).const_mul (2 * z)
    have j3 : Integrable fun s : ℝ => z ^ 2 * ((s : ℂ) ^ 2 + z) ^ (-((3 : ℕ) : ℤ)) :=
      (integrable_sq_add_zpow hz 3 (by norm_num)).const_mul (z ^ 2)
    have j12 : Integrable fun s : ℝ => ((s : ℂ) ^ 2 + z) ^ (-((1 : ℕ) : ℤ)) -
        2 * z * ((s : ℂ) ^ 2 + z) ^ (-((2 : ℕ) : ℤ)) := j1.sub j2
    simp_rw [e]
    rw [integral_add j12 j3, integral_sub j1 j2, integral_const_mul, integral_const_mul,
      integral_sq_add_zpow_eq 1 le_rfl hz, integral_sq_add_zpow_eq 2 (by norm_num) hz,
      integral_sq_add_zpow_eq 3 (by norm_num) hz]
    have e2 : z * z ^ ((1 / 2 : ℂ) - ((2 : ℕ) : ℂ)) = z ^ (-(1 / 2 : ℂ)) := by
      rw [cpow_mul_self hz0]; norm_num
    have e3 : z ^ 2 * z ^ ((1 / 2 : ℂ) - ((3 : ℕ) : ℂ)) = z ^ (-(1 / 2 : ℂ)) := by
      rw [sq, mul_assoc, cpow_mul_self hz0, cpow_mul_self hz0]; norm_num
    have e1 : z ^ ((1 / 2 : ℂ) - ((1 : ℕ) : ℂ)) = z ^ (-(1 / 2 : ℂ)) := by norm_num
    rw [e1, show 2 * z * ((energyConst 2 : ℂ) * z ^ ((1 / 2 : ℂ) - ((2 : ℕ) : ℂ))) =
      2 * (energyConst 2 : ℂ) * (z * z ^ ((1 / 2 : ℂ) - ((2 : ℕ) : ℂ))) by ring, e2,
      show z ^ 2 * ((energyConst 3 : ℂ) * z ^ ((1 / 2 : ℂ) - ((3 : ℕ) : ℂ))) =
      (energyConst 3 : ℂ) * (z ^ 2 * z ^ ((1 / 2 : ℂ) - ((3 : ℕ) : ℂ))) by ring, e3]
    push_cast
    ring
  have k1 : Integrable fun s => c0 * f0 s := i0.const_mul c0
  have k2 : Integrable fun s => c0 * f0 s + c1 * f1 s := k1.add (i1.const_mul c1)
  have k3 : Integrable fun s => c0 * f0 s + c1 * f1 s + c2 * f2 s := k2.add (i2.const_mul c2)
  have k4 : Integrable fun s => c0 * f0 s + c1 * f1 s + c2 * f2 s + c3 * f3 s :=
    k3.add (i3.const_mul c3)
  simp only [G]
  rw [integral_add k4 (i4.const_mul c4), integral_add k3 (i3.const_mul c3),
    integral_add k2 (i2.const_mul c2), integral_add k1 (i1.const_mul c1)]
  simp only [integral_const_mul]
  rw [I0, I1, I2, I3, I4]
  ring

/-! ### The flavour term -/

section Flavour

variable {A B : Mat} (hA : IsOddG A) (hB : IsOddG B) (d₂ dm M : ℝ) {ε : ℝ} (hε : 0 < ε)
  (p : Fin 4 → ℝ) (v : Fin 3 → ℝ)

/-- `z = -W(u) + iε`, `W(u) = |v⃗ + u p⃗|² + M² + u (1 - u) p·p`. -/
noncomputable def insZ (M ε : ℝ) (p : Fin 4 → ℝ) (u : ℝ) (v : Fin 3 → ℝ) : ℂ :=
  -(massW M M p u v : ℂ) + ε * I

/-- The closed-form energy integral of the flavour term at Feynman parameter `u`. -/
noncomputable def insCF (A B : Mat) (d₂ dm M ε : ℝ) (p : Fin 4 → ℝ) (u : ℝ) (v : Fin 3 → ℝ) :
    ℂ :=
  -((insP0 A B d₂ p (u * p 0) v + (M : ℂ) ^ 2 * insP2 A B d₂ dm p (u * p 0) v +
        ((M : ℂ) ^ 2) ^ 2 * insP4 A B dm) * (energyConst 3 : ℂ) *
        insZ M ε p u v ^ (-(5 / 2 : ℂ)) +
      (insQ0 A B d₂ p (u * p 0) v + (M : ℂ) ^ 2 * insQ2 A B d₂ dm) *
        ((energyConst 2 - energyConst 3 : ℝ) : ℂ) * insZ M ε p u v ^ (-(3 / 2 : ℂ)) +
      insN4 A B d₂ * ((energyConst 1 - 2 * energyConst 2 + energyConst 3 : ℝ) : ℂ) *
        insZ M ε p u v ^ (-(1 / 2 : ℂ)))

include hA hB hε in
/-- **The energy integral at fixed Feynman parameter** is `insCF`. -/
theorem integral_insTr_combDen_time (u : ℝ) :
    ∫ t : ℝ, insTr A B d₂ dm M (p + Fin.cons t v) (Fin.cons t v) *
        combDen M M ε p u (Fin.cons t v) ^ (-3 : ℤ) = insCF A B d₂ dm M ε p u v := by
  have hz : insZ M ε p u v ∈ slitPlane :=
    QED.OneLoop.VertexLimit.mem_slitPlane_neg_add_mul_I hε _
  have hodd : Odd (-3 : ℤ) := ⟨-2, by norm_num⟩
  have hpt : ∀ t : ℝ, insTr A B d₂ dm M (p + Fin.cons t v) (Fin.cons t v) *
      combDen M M ε p u (Fin.cons t v) ^ (-3 : ℤ) =
      -(((insP0 A B d₂ p (u * p 0) v + (M : ℂ) ^ 2 * insP2 A B d₂ dm p (u * p 0) v +
          ((M : ℂ) ^ 2) ^ 2 * insP4 A B dm) +
        insO1 A B d₂ dm p (u * p 0) v M * ((t : ℂ) + (u * p 0 : ℝ)) +
        (insQ0 A B d₂ p (u * p 0) v + (M : ℂ) ^ 2 * insQ2 A B d₂ dm) *
          ((t : ℂ) + (u * p 0 : ℝ)) ^ 2 +
        insO3 A B d₂ p (u * p 0) v * ((t : ℂ) + (u * p 0 : ℝ)) ^ 3 +
        insN4 A B d₂ * ((t : ℂ) + (u * p 0 : ℝ)) ^ 4) *
        (((t : ℂ) + (u * p 0 : ℝ)) ^ 2 + insZ M ε p u v) ^ (-3 : ℤ)) := fun t => by
    rw [insTr_cons_eq hA hB d₂ dm M p (u * p 0) t v, combDen_cons,
      show -((t : ℂ) + (u * p 0 : ℝ)) ^ 2 + ((massW M M p u v : ℂ) - (ε : ℂ) * I) =
        -(((t : ℂ) + (u * p 0 : ℝ)) ^ 2 + insZ M ε p u v) by unfold insZ; ring,
      hodd.neg_zpow]
    ring
  simp_rw [hpt]
  rw [integral_neg, integral_quartic_mul_shifted_three hz, insCF]

/-- The flavour integrand on `ℝ × (0, 1]` (loop energy, Feynman parameter). -/
noncomputable def insJoint (A B : Mat) (d₂ dm M ε : ℝ) (p : Fin 4 → ℝ) (v : Fin 3 → ℝ)
    (q : ℝ × ℝ) : ℂ :=
  insTr A B d₂ dm M (p + Fin.cons q.1 v) (Fin.cons q.1 v) *
    (2 * (1 - (q.2 : ℂ)) * combDen M M ε p q.2 (Fin.cons q.1 v) ^ (-3 : ℤ))

include hA hB in
/-- The trace along `q = (t, v⃗)` is a polynomial in `t`. -/
theorem insTr_cons_eq_zero (t : ℝ) :
    insTr A B d₂ dm M (p + Fin.cons t v) (Fin.cons t v) =
      (insP0 A B d₂ p 0 v + (M : ℂ) ^ 2 * insP2 A B d₂ dm p 0 v +
          ((M : ℂ) ^ 2) ^ 2 * insP4 A B dm) +
        insO1 A B d₂ dm p 0 v M * (t : ℂ) +
        (insQ0 A B d₂ p 0 v + (M : ℂ) ^ 2 * insQ2 A B d₂ dm) * (t : ℂ) ^ 2 +
        insO3 A B d₂ p 0 v * (t : ℂ) ^ 3 + insN4 A B d₂ * (t : ℂ) ^ 4 := by
  rw [insTr_cons_eq hA hB d₂ dm M p 0 t v]
  push_cast
  ring

include hA hB in
theorem exists_norm_insTr_cons_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖insTr A B d₂ dm M (p + Fin.cons t v) (Fin.cons t v)‖ ≤ C * (1 + t ^ 2) ^ 2 := by
  set c0 := insP0 A B d₂ p 0 v + (M : ℂ) ^ 2 * insP2 A B d₂ dm p 0 v +
    ((M : ℂ) ^ 2) ^ 2 * insP4 A B dm
  set c1 := insO1 A B d₂ dm p 0 v M
  set c2 := insQ0 A B d₂ p 0 v + (M : ℂ) ^ 2 * insQ2 A B d₂ dm
  set c3 := insO3 A B d₂ p 0 v
  set c4 := insN4 A B d₂
  refine ⟨‖c0‖ + ‖c1‖ + ‖c2‖ + ‖c3‖ + ‖c4‖, by positivity, fun t => ?_⟩
  rw [insTr_cons_eq_zero hA hB]
  set T := (1 + t ^ 2) ^ 2
  have ht : |t| ≤ 1 + t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]
  have h1 : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hT1 : 1 ≤ T := one_le_pow₀ h1
  have n1 : ‖(t : ℂ)‖ ≤ T := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact ht.trans (le_self_pow₀ h1 (by norm_num))
  have n2 : ‖(t : ℂ) ^ 2‖ ≤ T := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith
  have n3 : ‖(t : ℂ) ^ 3‖ ≤ T := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, show |t| ^ 3 = |t| * t ^ 2 by
      rw [pow_succ, sq_abs, mul_comm]]
    have := abs_nonneg t
    nlinarith [sq_nonneg t]
  have n4 : ‖(t : ℂ) ^ 4‖ ≤ T := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, show |t| ^ 4 = (t ^ 2) ^ 2 by
      rw [← sq_abs t, ← pow_mul]]
    have := sq_nonneg t
    nlinarith
  calc ‖c0 + c1 * (t : ℂ) + c2 * (t : ℂ) ^ 2 + c3 * (t : ℂ) ^ 3 + c4 * (t : ℂ) ^ 4‖
      ≤ ‖c0‖ + ‖c1‖ * ‖(t : ℂ)‖ + ‖c2‖ * ‖(t : ℂ) ^ 2‖ + ‖c3‖ * ‖(t : ℂ) ^ 3‖ +
          ‖c4‖ * ‖(t : ℂ) ^ 4‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mul_le _ _))
        refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mul_le _ _))
        refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mul_le _ _))
        exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
    _ ≤ ‖c0‖ * T + ‖c1‖ * T + ‖c2‖ * T + ‖c3‖ * T + ‖c4‖ * T := by
        gcongr
        exact le_mul_of_one_le_right (norm_nonneg _) hT1
    _ = _ := by ring

theorem norm_zpow_neg_three_le {c s : ℝ} {Z : ℂ} (hc : 0 < c) (hs : 0 ≤ s)
    (hZ : c * (1 + s) ≤ ‖Z‖) : ‖Z ^ (-3 : ℤ)‖ ≤ (c ^ 3)⁻¹ * ((1 + s) ^ 3)⁻¹ := by
  have h1 : 0 < c * (1 + s) := by positivity
  rw [norm_zpow, zpow_neg, zpow_ofNat, ← mul_inv, ← mul_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le hZ 3)

include hA hB hε in
/-- The flavour integrand is integrable in the loop energy and the Feynman parameter. -/
theorem integrable_insJoint :
    Integrable (insJoint A B d₂ dm M ε p v)
      ((volume : Measure ℝ).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  obtain ⟨CW, hCW⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (QED.WickModel.SelfEnergyLimit.continuous_massW M M p v).continuousOn
    (s := Icc (0 : ℝ) 1)
  obtain ⟨c, hc, hcb⟩ := exists_mul_one_add_sq_le_norm hε |p 0| CW
  obtain ⟨Cn, hCn0, hCn⟩ := exists_norm_insTr_cons_le hA hB d₂ dm M p v
  have hcont : Continuous (insJoint A B d₂ dm M ε p v) := by
    have hD := (QED.WickModel.SelfEnergyLimit.continuous_combDen_cons M M ε p v).zpow₀ (-3)
      fun q => Or.inl (QED.WickModel.SelfEnergyLimit.combDen_ne_zero hε.ne' _ _ p q.2 _)
    have hN : Continuous fun q : ℝ × ℝ =>
        insTr A B d₂ dm M (p + Fin.cons q.1 v) (Fin.cons q.1 v) := by
      simp_rw [insTr_cons_eq_zero hA hB]
      fun_prop
    unfold insJoint
    exact hN.mul ((continuous_const.mul (continuous_const.sub
      (continuous_ofReal.comp continuous_snd))).mul hD)
  refine Integrable.mono' (g := fun q : ℝ × ℝ => 2 * Cn * (c ^ 3)⁻¹ * (1 + q.1 ^ 2)⁻¹ * 1) ?_
    hcont.aestronglyMeasurable
    ((QED.WickModel.SelfEnergyLimit.ae_prod_restrict_Ioc _).mono fun q hq => ?_)
  · exact (integrable_inv_one_add_sq.const_mul _).mul_prod (integrable_const (1 : ℝ))
  obtain ⟨t, u⟩ := q
  simp only at hq ⊢
  have huI : u ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hq
  have ha : |u * p 0| ≤ |p 0| := by
    rw [abs_mul, abs_of_nonneg huI.1]
    exact mul_le_of_le_one_left (abs_nonneg _) huI.2
  have hW : massW M M p u v ≤ CW :=
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hCW u huI)
  have hZ : c * (1 + t ^ 2) ≤ ‖combDen M M ε p u (Fin.cons t v : Fin 4 → ℝ)‖ := by
    rw [combDen_cons, ← add_sub_assoc]
    exact hcb t _ _ ha hW
  have hb := norm_zpow_neg_three_le hc (sq_nonneg t) hZ
  have h1t : 0 < 1 + t ^ 2 := by positivity
  have h2 : ‖2 * (1 - (u : ℂ))‖ ≤ 2 := by
    rw [norm_mul, show (1 : ℂ) - u = ((1 - u : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith [huI.2])]
    norm_num
    linarith [huI.1]
  rw [insJoint, norm_mul, norm_mul, mul_one]
  calc ‖insTr A B d₂ dm M (p + Fin.cons t v) (Fin.cons t v)‖ *
        (‖2 * (1 - (u : ℂ))‖ * ‖combDen M M ε p u (Fin.cons t v) ^ (-3 : ℤ)‖)
      ≤ (Cn * (1 + t ^ 2) ^ 2) * (2 * ((c ^ 3)⁻¹ * ((1 + t ^ 2) ^ 3)⁻¹)) := by
        gcongr
        exact hCn t
    _ = 2 * Cn * (c ^ 3)⁻¹ * (1 + t ^ 2)⁻¹ := by
        field_simp

include hε in
theorem insG_cons_eq_integral (t : ℝ) :
    insG A B d₂ dm M ε (p + Fin.cons t v) (Fin.cons t v) =
      ∫ u in Ioc (0 : ℝ) 1, insJoint A B d₂ dm M ε p v (t, u) := by
  rw [insG, mul_assoc, inv_mul_inv_sq_eq_integral hε, ← integral_const_mul]
  rfl

include hA hB hε in
/-- **The flavour term is integrable in the loop energy.** -/
theorem integrable_insG_time :
    Integrable fun t : ℝ => insG A B d₂ dm M ε (p + Fin.cons t v) (Fin.cons t v) := by
  refine (integrable_insJoint hA hB d₂ dm M hε p v).integral_prod_left.congr
    (Filter.Eventually.of_forall fun t => ?_)
  exact (insG_cons_eq_integral d₂ dm M hε p v t).symm

include hA hB hε in
/-- **The energy integral of the flavour term** is the Feynman-parameter integral of the closed
form. -/
theorem integral_insG_time :
    ∫ t : ℝ, insG A B d₂ dm M ε (p + Fin.cons t v) (Fin.cons t v) =
      ∫ u in Ioc (0 : ℝ) 1, 2 * (1 - (u : ℂ)) * insCF A B d₂ dm M ε p u v := by
  simp_rw [insG_cons_eq_integral d₂ dm M hε p v]
  rw [integral_integral_swap (f := fun t u => insJoint A B d₂ dm M ε p v (t, u))
    (integrable_insJoint hA hB d₂ dm M hε p v)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [insJoint]
  simp_rw [show ∀ t : ℝ, insTr A B d₂ dm M (p + Fin.cons t v) (Fin.cons t v) *
      (2 * (1 - (u : ℂ)) * combDen M M ε p u (Fin.cons t v) ^ (-3 : ℤ)) =
      2 * (1 - (u : ℂ)) * (insTr A B d₂ dm M (p + Fin.cons t v) (Fin.cons t v) *
        combDen M M ε p u (Fin.cons t v) ^ (-3 : ℤ)) from fun t => by ring]
  rw [integral_const_mul, integral_insTr_combDen_time hA hB d₂ dm M hε p v u]

include hA hB hε in
/-- The Feynman-parameter integrand of the closed form is integrable on `(0, 1]`. -/
theorem integrableOn_insCF :
    IntegrableOn (fun u : ℝ => 2 * (1 - (u : ℂ)) * insCF A B d₂ dm M ε p u v)
      (Ioc (0 : ℝ) 1) := by
  refine (integrable_insJoint hA hB d₂ dm M hε p v).integral_prod_right.congr
    (Filter.Eventually.of_forall fun u => ?_)
  simp only [insJoint]
  simp_rw [show ∀ t : ℝ, insTr A B d₂ dm M (p + Fin.cons t v) (Fin.cons t v) *
      (2 * (1 - (u : ℂ)) * combDen M M ε p u (Fin.cons t v) ^ (-3 : ℤ)) =
      2 * (1 - (u : ℂ)) * (insTr A B d₂ dm M (p + Fin.cons t v) (Fin.cons t v) *
        combDen M M ε p u (Fin.cons t v) ^ (-3 : ℤ)) from fun t => by ring]
  rw [integral_const_mul, integral_insTr_combDen_time hA hB d₂ dm M hε p v u]

end Flavour

end QED.ChainProof.SetANest

end
