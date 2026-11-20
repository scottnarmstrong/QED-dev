/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Gordon
public import QED.GradedProof.VP2TensorForm

/-!
# (X₂) piece A: transverse photon legs act on on-shell sandwiches as scalars

Helper level for the Phase 5 Stage 2 goal (X₂)
`QED.Graded.isSpinFormFactorPair_lszFive_lepton_pauli_limit` (decision D-57). At the LSZ limit
the photon legs of the order-`e⁵` amplitude are `Δ_{νρ}(q) Π^{μρ}(q)` with the Feynman-gauge
propagator `Δ_{νρ} = g_{νρ} D` and a transverse vacuum polarization
`Π^{μρ} = Pol (q² g^{μρ} - q^μ q^ρ)` (`QED.GradedProof.VP2.vpT`). Contracted with a vector `Y`
with `q_ν Y^ν = 0` such a leg is the scalar `D Pol q²`. The on-shell sandwiches of `γ^ν` and of
any form-factor structure `A γ^ν - (i/m) B S^{νλ} q_λ` are such vectors.

* `sum_metric_mul_vpT`: `∑_ρ g_{νρ} (q² g_{μρ} - q_μ q_ρ) = q² δ_{νμ} - q_μ q_ν`.
* `sum_leg_mul_of_transverse`: the contraction with a transverse vector.
* `sum_lower_mul_gamma_sandwich`: `q_ν ū' γ^ν u = 0` on shell, `q = p' - p`.
* `sum_lower_mul_formFactor_sandwich`: the same for a form-factor structure.
-/

@[expose] public section

open Matrix Complex
open QED.GradedProof.VP2 (vpT)

namespace QED.GradedProof.X2

/-- `∑_ρ g_{νρ} (q² g_{μρ} - q_μ q_ρ) = q² δ_{νμ} - q_μ q_ν` (`q_ν` covariant). -/
theorem sum_metric_mul_vpT (q : Fin 4 → ℝ) (ν μ : Fin 4) :
    ∑ ρ, ((Minkowski.metric ν ρ : ℝ) : ℂ) * vpT q μ ρ =
      ((Minkowski.dot q q : ℝ) : ℂ) * (if ν = μ then 1 else 0) -
        ((q μ : ℝ) : ℂ) * ((Minkowski.lower q ν : ℝ) : ℂ) := by
  fin_cases ν <;> fin_cases μ <;>
    simp [vpT, Minkowski.metric, Minkowski.lower, Fin.sum_univ_four, add_comm]

/-- **A transverse photon leg acts on a transverse vector as a scalar**: if `q_ν Y^ν = 0` then
`∑_ν (∑_ρ g_{νρ} c (q² g_{μρ} - q_μ q_ρ)) Y^ν = c q² Y^μ`. -/
theorem sum_leg_mul_of_transverse (q : Fin 4 → ℝ) (c : ℂ) (Y : Fin 4 → ℂ)
    (hY : ∑ ν, ((Minkowski.lower q ν : ℝ) : ℂ) * Y ν = 0) (μ : Fin 4) :
    ∑ ν, (∑ ρ, ((Minkowski.metric ν ρ : ℝ) : ℂ) * (c * vpT q μ ρ)) * Y ν =
      c * ((Minkowski.dot q q : ℝ) : ℂ) * Y μ := by
  have h : ∀ ν, (∑ ρ, ((Minkowski.metric ν ρ : ℝ) : ℂ) * (c * vpT q μ ρ)) * Y ν =
      c * ((Minkowski.dot q q : ℝ) : ℂ) * ((if ν = μ then 1 else 0) * Y ν) -
        c * ((q μ : ℝ) : ℂ) * (((Minkowski.lower q ν : ℝ) : ℂ) * Y ν) := fun ν => by
    have e : ∑ ρ, ((Minkowski.metric ν ρ : ℝ) : ℂ) * (c * vpT q μ ρ) =
        c * ∑ ρ, ((Minkowski.metric ν ρ : ℝ) : ℂ) * vpT q μ ρ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ρ _ => by ring
    rw [e, sum_metric_mul_vpT]
    ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, hY, mul_zero, sub_zero]
  simp

/-- `(v - w)̸ = v̸ - w̸`. -/
theorem slash_sub (v w : Fin 4 → ℝ) : Dirac.slash (v - w) = Dirac.slash v - Dirac.slash w := by
  simp only [Dirac.slash, Minkowski.lower, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    Complex.ofReal_sub, sub_smul]

/-- `∑_ν q_ν (w ⬝ X^ν u) = w ⬝ (∑_ν q_ν X^ν) u`. -/
theorem sum_lower_mul_sandwich (q : Fin 4 → ℝ) (X : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (w u : Fin 4 → ℂ) :
    ∑ ν, ((Minkowski.lower q ν : ℝ) : ℂ) * (w ⬝ᵥ (X ν *ᵥ u)) =
      w ⬝ᵥ ((∑ ν, ((Minkowski.lower q ν : ℝ) : ℂ) • X ν) *ᵥ u) := by
  simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

/-- **Current conservation of `γ^ν` on shell**: `q_ν ū' γ^ν u = 0` for `q = p' - p`,
`p̸ u = -m u` and `ū' p̸' = -m ū'`. -/
theorem sum_lower_mul_gamma_sandwich {m : ℝ} {p' p : Fin 4 → ℝ} {w u : Fin 4 → ℂ}
    (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u)) (hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w)) :
    ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) * (w ⬝ᵥ (Dirac.gamma ν *ᵥ u)) = 0 := by
  rw [sum_lower_mul_sandwich]
  change w ⬝ᵥ (Dirac.slash (p' - p) *ᵥ u) = 0
  rw [slash_sub, Matrix.sub_mulVec, dotProduct_sub, Matrix.dotProduct_mulVec w (Dirac.slash p') u,
    hw, hu]
  simp [dotProduct_smul, smul_dotProduct]

/-- `∑_{νλ} q_ν q_λ S^{νλ} = 0` (antisymmetry). -/
theorem sum_lower_mul_lorentzGen (q : Fin 4 → ℝ) :
    ∑ ν, ((Minkowski.lower q ν : ℝ) : ℂ) •
      ∑ l, ((Minkowski.lower q l : ℝ) : ℂ) • Dirac.lorentzGen ν l = 0 := by
  set a : Fin 4 → ℂ := fun ν => ((Minkowski.lower q ν : ℝ) : ℂ)
  have h : ∑ ν, a ν • ∑ l, a l • Dirac.lorentzGen ν l =
      ∑ ν, ∑ l, (a ν * a l) • Dirac.lorentzGen ν l := by
    simp only [Finset.smul_sum, smul_smul]
  change ∑ ν, a ν • ∑ l, a l • Dirac.lorentzGen ν l = 0
  rw [h]
  have hs : ∑ ν, ∑ l, (a ν * a l) • Dirac.lorentzGen ν l =
      -∑ ν, ∑ l, (a ν * a l) • Dirac.lorentzGen ν l := by
    conv_rhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Dirac.lorentzGen_antisymm, smul_neg, mul_comm]
  have h2 : (2 : ℂ) • ∑ ν, ∑ l, (a ν * a l) • Dirac.lorentzGen ν l = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hs]
    exact add_neg_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- **Current conservation of a form-factor structure on shell**:
`q_ν ū' [A γ^ν - (i/m) B S^{νλ} q_λ] u = 0` for `q = p' - p`. -/
theorem sum_lower_mul_formFactor_sandwich {m : ℝ} {p' p : Fin 4 → ℝ} {w u : Fin 4 → ℂ}
    (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u)) (hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w))
    (A B : ℂ) :
    ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) *
      (w ⬝ᵥ ((A • Dirac.gamma ν - (I / (m : ℂ) * B) •
        ∑ l, ((Minkowski.lower (p' - p) l : ℝ) : ℂ) • Dirac.lorentzGen ν l) *ᵥ u)) = 0 := by
  rw [sum_lower_mul_sandwich]
  have e : ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • (A • Dirac.gamma ν - (I / (m : ℂ) * B) •
      ∑ l, ((Minkowski.lower (p' - p) l : ℝ) : ℂ) • Dirac.lorentzGen ν l) =
      A • ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.gamma ν -
        (I / (m : ℂ) * B) • ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) •
          ∑ l, ((Minkowski.lower (p' - p) l : ℝ) : ℂ) • Dirac.lorentzGen ν l := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_comm _ A,
      smul_comm _ (I / (m : ℂ) * B)]
  rw [e, sum_lower_mul_lorentzGen, smul_zero, sub_zero, Matrix.smul_mulVec, dotProduct_smul,
    ← sum_lower_mul_sandwich, sum_lower_mul_gamma_sandwich hu hw, smul_zero]

end QED.GradedProof.X2

end
