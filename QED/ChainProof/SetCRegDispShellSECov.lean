/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSEQZ
public import QED.Integration.EnergyIntegral
public import QED.ChainProof.SetCRegDispShellSELimG
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Covariance of the closed form of the quadratic self-energy block

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan (the covariant
form of the class `V` limit). The closed form `seQuadY` of the spatial integral of the quadratic
numerator `(p·ℓ) ℓ̸` splits into a time part (the energy-squared coefficient
`seQuadA p = (p·e₀) e̸₀`) and a space part `⅓ (p⃗·γ⃗)`. With the recursions
`K_{n+2} = (2n+1)/(2n+2) K_{n+1}` of the energy constants and `c_{i+1} = (2i+2)/(2i+5) c_i` of the
radial constants, the two parts recombine into the covariant `p̸`:

`seQuadY (seQuadA p) p = (-1)^{i+4} (K_{i+4} e^{-iπ(i+7/2)} Q(-yP) 4π c_{i+1} Δ^{-(i+2)}`
`  - (K_{i+3} - K_{i+4}) e^{-iπ(i+5/2)} 4π c_i Δ^{-(i+1)} p̸_{αβ})`.

* `energyConst_succ_succ`: `K_{n+2} = (2n+1)/(2n+2) K_{n+1}` (integration by parts);
* `slash_eq_time_add_space`, `seQuadA_eq`: the time and space parts of `p̸`;
* **`seQuadY_seQuadA`**: the covariant form above.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.WickModel.SelfEnergyLimit QED.OneLoop
open QED.ChainProof.SetCRegDispSE (seRadC)
open QED.TwoLoop.VPHalfAtLimit (energyConst)

/-! ### The recursion of the energy constants -/

/-- **`K_{n+2} = (2n+1)/(2n+2) K_{n+1}`**, from `d/dt [t (1 + t²)^{-(n+1)}]`. -/
theorem energyConst_succ_succ (n : ℕ) :
    energyConst (n + 2) = (2 * n + 1) / (2 * n + 2) * energyConst (n + 1) := by
  set F : ℝ → ℝ := fun t => t * ((1 + t ^ 2) ^ (n + 1))⁻¹ with hF
  set F' : ℝ → ℝ := fun t => (1 - 2 * ((n : ℝ) + 1)) * ((1 + t ^ 2) ^ (n + 1))⁻¹ +
    2 * ((n : ℝ) + 1) * ((1 + t ^ 2) ^ (n + 2))⁻¹ with hF'
  have hderiv : ∀ t : ℝ, HasDerivAt F (F' t) t := by
    intro t
    have h1 : 0 < 1 + t ^ 2 := by positivity
    have h2 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).const_add 1
    have hp := h2.fun_pow (n + 1)
    have hq := (hasDerivAt_id' t).fun_mul (hp.fun_inv (by positivity))
    refine hq.congr_deriv ?_
    simp only [hF', Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hi1 := QED.Integration.integrable_inv_one_add_sq_pow (n + 1) (by omega)
  have hi2 := QED.Integration.integrable_inv_one_add_sq_pow (n + 2) (by omega)
  have hint : Integrable F' :=
    (hi1.const_mul _).add
      (hi2.const_mul _)
  have hlim : ∀ {l : Filter ℝ}, Tendsto (fun t : ℝ => t / (1 + t ^ 2)) l (𝓝 0) →
      Tendsto (fun t : ℝ => (1 + t ^ 2)⁻¹) l (𝓝 0) → Tendsto F l (𝓝 0) := by
    intro l h1 h2
    have e : F = fun t => t / (1 + t ^ 2) * ((1 + t ^ 2)⁻¹) ^ n := by
      funext t
      have : (1 + t ^ 2) ≠ 0 := by positivity
      simp only [hF, inv_pow, pow_succ]
      field_simp
    rw [e]
    simpa using h1.mul (h2.pow n)
  have h0 := integral_of_hasDerivAt_of_tendsto hderiv hint
    (hlim QED.Integration.tendsto_div_one_add_sq_atBot
      QED.Integration.tendsto_inv_one_add_sq_atBot)
    (hlim QED.Integration.tendsto_div_one_add_sq_atTop
      QED.Integration.tendsto_inv_one_add_sq_atTop)
  rw [sub_self, hF', integral_add (hi1.const_mul _)
    (hi2.const_mul _), integral_const_mul,
    integral_const_mul] at h0
  unfold energyConst
  have hn : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hn]
  linear_combination h0

/-! ### Time and space parts of the slash -/

/-- The time unit vector `e₀`. -/
def seTimeE0 : Fin 4 → ℝ := Fin.cons 1 0

theorem slash_eq_time_add_space (p : Fin 4 → ℝ) (α β : Fin 4) :
    Dirac.slash p α β =
      (p 0 : ℂ) * Dirac.slash seTimeE0 α β + ∑ k, (p k.succ : ℂ) * seSl α β k := by
  have hp : p = (Fin.cons (p 0) (fun k => p k.succ) : Fin 4 → ℝ) := (Fin.cons_self_tail p).symm
  conv_lhs => rw [hp]
  rw [slash_cons_apply, slash_cons_zero_apply]
  rfl

theorem seQuadA_eq (p : Fin 4 → ℝ) (α β : Fin 4) :
    seQuadA p α β = -(p 0 : ℂ) * Dirac.slash seTimeE0 α β := by
  unfold seQuadA seTimeE0
  have c2 : (Fin.cons (1 : ℝ) (0 : Fin 3 → ℝ) : Fin 4 → ℝ) 2 = 0 := rfl
  have c3 : (Fin.cons (1 : ℝ) (0 : Fin 3 → ℝ) : Fin 4 → ℝ) 3 = 0 := rfl
  rw [Minkowski.dot_eq]
  simp [c2, c3]

/-! ### The covariant form -/

theorem radial_energy_identity (i : ℕ) :
    energyConst (i + 4) * ((seRadC i - seRadC (i + 1)) / 3) =
      (energyConst (i + 3) - energyConst (i + 4)) * seRadC i := by
  have hK := energyConst_succ_succ (i + 2)
  have hc : seRadC (i + 1) = (2 * i + 2) / (2 * i + 5) * seRadC i := rfl
  rw [show i + 2 + 2 = i + 4 by ring, show i + 2 + 1 = i + 3 by ring] at hK
  rw [hK, hc]
  push_cast
  have h1 : (2 * (i : ℝ) + 5) ≠ 0 := by positivity
  have h2 : (2 * ((i : ℝ) + 2) + 2) ≠ 0 := by positivity
  field_simp
  ring

theorem exp_phase_succ (i : ℕ) :
    exp (π * I * (-(((i : ℝ) + 7 / 2 : ℝ) : ℂ))) =
      -exp (π * I * (-(((i : ℝ) + 5 / 2 : ℝ) : ℂ))) := by
  have e : π * I * (-(((i : ℝ) + 7 / 2 : ℝ) : ℂ)) =
      π * I * (-(((i : ℝ) + 5 / 2 : ℝ) : ℂ)) + (-(π * I)) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
  ring

/-- **The covariant form of the quadratic block**: with the energy-squared coefficient
`seQuadA p`, the time and space parts of `seQuadY` recombine into `p̸`. -/
theorem seQuadY_seQuadA (p : Fin 4 → ℝ) (α β : Fin 4) (m M : ℝ) (i : ℕ) (P : Fin 4 → ℝ)
    (y : ℝ) :
    seQuadY (seQuadA p α β) p α β m M i P y =
      (-1) ^ (i + 4) *
        (((energyConst (i + 4) : ℝ) : ℂ) * exp (π * I * (-(((i : ℝ) + 7 / 2 : ℝ) : ℂ))) *
            (seQuad p α β (-(y • P)) *
              ((4 * π * (seRadC (i + 1) *
                selfEnergyFeynmanMass m M (Minkowski.dot P P) y ^ (-((i : ℝ) + 2))) : ℝ) : ℂ)) -
          ((energyConst (i + 3) - energyConst (i + 4) : ℝ) : ℂ) *
            exp (π * I * (-(((i : ℝ) + 5 / 2 : ℝ) : ℂ))) *
            ((4 * π * (seRadC i *
              selfEnergyFeynmanMass m M (Minkowski.dot P P) y ^ (-((i : ℝ) + 1))) : ℝ) : ℂ) *
            Dirac.slash p α β) := by
  set D := selfEnergyFeynmanMass m M (Minkowski.dot P P) y ^ (-((i : ℝ) + 1))
  have hR := radial_energy_identity i
  have hR' : ((energyConst (i + 4) : ℝ) : ℂ) *
      ((4 * π * ((seRadC i - seRadC (i + 1)) * D) / 3 : ℝ) : ℂ) =
      ((energyConst (i + 3) - energyConst (i + 4) : ℝ) : ℂ) *
        ((4 * π * (seRadC i * D) : ℝ) : ℂ) := by
    have : energyConst (i + 4) * (4 * π * ((seRadC i - seRadC (i + 1)) * D) / 3) =
        (energyConst (i + 3) - energyConst (i + 4)) * (4 * π * (seRadC i * D)) := by
      linear_combination (4 * π * D) * hR
    exact_mod_cast this
  unfold seQuadY
  rw [seQuadA_eq, slash_eq_time_add_space p α β, exp_phase_succ]
  linear_combination
    (-1) ^ (i + 4) * (-exp (π * I * (-(((i : ℝ) + 5 / 2 : ℝ) : ℂ)))) *
      (∑ k, (p k.succ : ℂ) * seSl α β k) * hR'

end QED.ChainProof.SetCRegDisp

end
