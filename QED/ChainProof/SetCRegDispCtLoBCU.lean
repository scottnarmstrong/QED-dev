/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBCD
public import QED.ChainProof.SetCRegDispCtLoBPauli
public import QED.TwoLoop.VPHalfAtGenPow
import Mathlib.Tactic.Ring

/-!
# The undoubled `CD1` piece of the mass part, and the `q → 0` value of `CD1`

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), layer 6. At
`δ₂ = 0` (the parameters `cbBParams …`) the inserted electron line of the undoubled piece of
`CD1 t` carries the numerator `δ_m m · 1`. Its photon numerator is the `δ₃` insertion: the
transverse part gives the undoubled chain `undChain … 0` with weight `k²`, and the longitudinal
part reduces by the Ward identity on the outgoing line to `((p'+k)² + m²) γ^μ k̸`. The factor
`(p'+k)² + m²` cancels the outgoing denominator up to `iε`; what is left is odd in the spatial
loop momentum at the rest momentum `p`, because the time component of `γ^μ k̸` has no Pauli part
there (`ggWt_zero`). So no integrability of the pieces beyond the product data is needed.

* `pauliNum_congr_sandwich`: the Pauli numerator depends only on the on-shell sandwich;
* `pauliNum_numIn₁`: the Pauli projection of the undoubled `CD1` numerator;
* `efi_eq_zero_of_odd`, `efInt_of_joint_one`: odd integrands, integrability from (T₉′);
* **`pauliNum_pieceLim_in₁`**: the fixed-`q` value `undCoeff · undValJ … 1 (phMs Q)`;
* **`kindsZero_in₁_eq`**, **`cdInZero_eq`**: the `q → 0` value of `CD1`,
  `cdInZero Q = undZeroVal Q + cdZeroVal Q 0` at `δ₂ = 0`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open QED.WickModel (Params)

namespace QED.ChainProof.CtLoB

open QED.Dirac QED.TwoLoop.CountertermLimit QED.TwoLoop.Insertion QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.VPUnitNested QED.ChainProof.SetCPauli QED.TwoLoop.VPHalfAtLimit
open QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.ReflCovariance QED.TwoLoop.VPHalfAtGen
open QED.GradedProof.X0 (AffPoly)

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### Sandwiches -/

/-- The Pauli numerator depends only on the on-shell sandwich `(m - p̸') V^μ (m - p̸)`. -/
theorem pauliNum_congr_sandwich {m : ℝ} {p' p : Fin 4 → ℝ}
    {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ μ, electronNumerator m p' * V μ * electronNumerator m p =
      electronNumerator m p' * W μ * electronNumerator m p) :
    pauliNum m p' p V = pauliNum m p' p W := by
  have h' : ∀ μ, ((m : ℂ) • 𝟙 - slash p') * V μ * ((m : ℂ) • 𝟙 - slash p) =
      ((m : ℂ) • 𝟙 - slash p') * W μ * ((m : ℂ) • 𝟙 - slash p) := h
  simp only [pauliNum, traceGammaProj, traceVecProj, h']

/-- The Pauli weights of `γ^μ γ^ν`. -/
noncomputable def ggWt (m : ℝ) (p' p : Fin 4 → ℝ) (ν : Fin 4) : ℂ :=
  pauliNum m p' p fun μ => gamma μ * gamma ν

/-- Linearity of the Pauli numerator in a finite combination. -/
theorem pauliNum_sum_smul (m : ℝ) (p' p : Fin 4 → ℝ) (c : Fin 4 → ℂ)
    (W : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pauliNum m p' p (fun μ => ∑ ν, c ν • W ν μ) = ∑ ν, c ν * pauliNum m p' p (W ν) := by
  simp only [pauliNum_eq_sum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ν _ => ?_
  ring

theorem pauliNum_gamma_slash (m : ℝ) (p' p k : Fin 4 → ℝ) :
    pauliNum m p' p (fun μ => gamma μ * slash k) =
      ∑ ν, ((Minkowski.lower k ν : ℝ) : ℂ) * ggWt m p' p ν := by
  have h : (fun μ => gamma μ * slash k) =
      fun μ => ∑ ν, ((Minkowski.lower k ν : ℝ) : ℂ) • (fun ν μ => gamma μ * gamma ν) ν μ := by
    funext μ
    simp only [slash, Matrix.mul_sum, Matrix.mul_smul]
  rw [h, pauliNum_sum_smul]
  rfl

/-- At the rest momentum the time weight vanishes: `γ⁰ ∝ p̸` and `p̸ (m - p̸) = -m (m - p̸)`. -/
theorem ggWt_zero {m : ℝ} (hm : m ≠ 0) {p' : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - restMomentum m) (p' - restMomentum m)) :
    ggWt m p' (restMomentum m) 0 = 0 := by
  have hs : slash (restMomentum m) = (-(m : ℂ)) • gamma 0 := by
    simp [slash, restMomentum, Minkowski.lower_eq, Fin.sum_univ_four]
  have hpA : slash (restMomentum m) * electronNumerator m (restMomentum m) =
      (-(m : ℂ)) • electronNumerator m (restMomentum m) := by
    have h := slash_add_mul_mass_sub_slash (dot_restMomentum (m := m))
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] at h
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have h1 : pauliNum m p' (restMomentum m) (fun μ => gamma μ * gamma 0) =
      pauliNum m p' (restMomentum m) (fun μ => (1 : ℂ) • gamma μ) := by
    refine pauliNum_congr_sandwich fun μ => ?_
    have hg : gamma 0 = (-(m : ℂ))⁻¹ • slash (restMomentum m) := by
      rw [hs, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hm'), one_smul]
    rw [hg]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hpA, smul_smul, one_smul]
    rw [inv_mul_cancel₀ (neg_ne_zero.2 hm'), one_smul]
  rw [ggWt, h1, pauliNum_smul, pauliNum_gamma hm hp' dot_restMomentum hq, mul_zero]

/-! ### The undoubled numerator -/

/-- The chain constant `(ie)³ (1/i)³ (2π)⁻⁴`. -/
noncomputable def chainC (e : ℝ) : ℂ :=
  (I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹

/-- The coefficient of `k² Pu(k)` in the Pauli projection of the undoubled `CD` numerators at
`δ₂ = 0`. -/
noncomputable def undCoeff (P : Params) : ℂ :=
  ((P.δm * P.m : ℝ) : ℂ) * (-(P.δ₃ / 2) * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℂ)

theorem neg_mergeY_of_zero (P : Params) (hδ : P.δ₂ = 0) (k : Fin 4 → ℝ) :
    -mergeY P.m P.δ₂ P.δm k = ((P.δm * P.m : ℝ) : ℂ) • 𝟙 := by
  simp [mergeY, hδ]

/-- The longitudinal chain with the identity on the incoming line, between on-shell spinors. -/
theorem pauliNum_longitudinal_in (e : ℝ) {m : ℝ} {p' : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (p k : Fin 4 → ℝ) :
    pauliNum m p' p (fun μ => vertexChain e μ (electronNumerator m (p' + k)) 𝟙
        (fun ν ρ => ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ))) =
      chainC e * ((Minkowski.dot (p' + k) (p' + k) + m ^ 2 : ℝ) : ℂ) *
        pauliNum m p' p (fun μ => gamma μ * slash k) := by
  rw [mul_assoc, ← pauliNum_smul, ← pauliNum_smul]
  refine pauliNum_congr_sandwich fun μ => ?_
  rw [vertexChain_longitudinal, ← chainC]
  have e1 : electronNumerator m p' *
      (chainC e • (slash k * electronNumerator m (p' + k) * gamma μ * 𝟙 * slash k)) *
        electronNumerator m p =
      chainC e • ((electronNumerator m p' * slash k * electronNumerator m (p' + k)) *
        (gamma μ * slash k) * electronNumerator m p) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e1, ward_out hp' k]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]

/-- **The Pauli projection of the undoubled `CD1` numerator** at `δ₂ = 0`. -/
theorem pauliNum_numIn₁ (P : Params) (hδ : P.δ₂ = 0) {p' : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (p k : Fin 4 → ℝ) :
    pauliNum P.m p' p (fun μ => numIn₁ P p' p μ k) =
      undCoeff P * ((Minkowski.dot k k : ℝ) : ℂ) * undChain P.e P.m 0 p' p k -
        undCoeff P * chainC P.e * ((Minkowski.dot (p' + k) (p' + k) + P.m ^ 2 : ℝ) : ℂ) *
          pauliNum P.m p' p (fun μ => gamma μ * slash k) := by
  simp only [numIn₁, neg_mergeY_of_zero P hδ, photonNum_eq, vertexChain_smul_in,
    vertexChain_add_photon, vertexChain_smul_photon, smul_smul]
  rw [QED.TwoLoop.PauliZeroLimit.pauliNum_add, pauliNum_smul, pauliNum_smul,
    pauliNum_longitudinal_in P.e hp' p k]
  have hg : (pauliNum P.m p' p fun μ =>
      vertexChain P.e μ (electronNumerator P.m (p' + k)) 𝟙 gPhoton) =
        undChain P.e P.m 0 p' p k := by
    simp [undChain]
  rw [hg, undCoeff]
  ring

/-! ### Oddness and integrability -/

/-- **An integrand odd in the spatial momentum has energy-first integral zero.** -/
theorem efi_eq_zero_of_odd {F : (Fin 4 → ℝ) → ℂ}
    (h : ∀ (t : ℝ) (v : Fin 3 → ℝ), F (Fin.cons t (-v)) = -F (Fin.cons t v)) :
    QED.OneLoop.energyFirstIntegral F = 0 := by
  unfold QED.OneLoop.energyFirstIntegral
  set g : (Fin 3 → ℝ) → ℂ := fun v => ∫ t : ℝ, F (Fin.cons t v : Fin 4 → ℝ)
  have hg : ∀ v, g (-v) = -g v := fun v => by
    simp only [g, h, integral_neg]
  have h1 : ∫ v, g v = ∫ v, g (-v) := (integral_neg_eq_self g volume).symm
  simp only [hg, integral_neg] at h1
  change ∫ v, g v = 0
  linear_combination h1 / 2

/-- Both stages of the energy-first integral from the one-loop joint integrability. -/
theorem efInt_of_joint_one {G : (Fin 4 → ℝ) → ℂ}
    (h : QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => G (ℓ 0)) : EFInt G := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun v => ?_, ?_⟩
  · exact ((volume_preserving_funUnique (Fin 1) ℝ).integrable_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
      (g := fun t : ℝ => G (Fin.cons t v))).mp (h1 fun _ => v)
  · have hin : ∀ v : Fin 1 → Fin 3 → ℝ, ∫ t : Fin 1 → ℝ, G (Fin.cons (t 0) (v 0)) =
        ∫ t : ℝ, G (Fin.cons t (v 0)) := fun v =>
      (volume_preserving_funUnique (Fin 1) ℝ).integral_comp'
        (g := fun t : ℝ => G (Fin.cons t (v 0)))
    have h2' : Integrable fun v : Fin 1 → Fin 3 → ℝ => ∫ t : ℝ, G (Fin.cons t (v 0)) := by
      simpa only [hin] using h2
    exact ((volume_preserving_funUnique (Fin 1) (Fin 3 → ℝ)).integrable_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) (Fin 3 → ℝ)).measurableEmbedding
      (g := fun v : Fin 3 → ℝ => ∫ t : ℝ, G (Fin.cons t v))).mp h2'

/-- The spatial linear form `Σ_ν k_ν w_ν` of the longitudinal part at the rest momentum. -/
noncomputable def spatL (m : ℝ) (p' k : Fin 4 → ℝ) : ℂ :=
  ∑ ν, ((Minkowski.lower k ν : ℝ) : ℂ) * ggWt m p' (restMomentum m) ν

theorem affPoly_spatL (m : ℝ) (p' : Fin 4 → ℝ) : AffPoly 1 (spatL m p') := by
  have h := AffPoly.aff 0 fun ν => ((Minkowski.metric ν ν : ℝ) : ℂ) * ggWt m p' (restMomentum m) ν
  refine (congrArg (AffPoly 1) (funext fun k => ?_)).mp h
  simp only [spatL, Minkowski.lower_eq, Fin.sum_univ_four, Minkowski.metric]
  simp
  ring

theorem cons_eq_vec (t : ℝ) (v : Fin 3 → ℝ) :
    (Fin.cons t v : Fin 4 → ℝ) = ![t, v 0, v 1, v 2] := by
  ext i
  fin_cases i <;> rfl

theorem spatL_neg {m : ℝ} (hm : m ≠ 0) {p' : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hq : 0 < Minkowski.dot (p' - restMomentum m) (p' - restMomentum m)) (t : ℝ)
    (v : Fin 3 → ℝ) : spatL m p' (Fin.cons t (-v)) = -spatL m p' (Fin.cons t v) := by
  simp only [spatL, Minkowski.lower_eq, Fin.sum_univ_four, ggWt_zero hm hp' hq, cons_eq_vec]
  simp
  ring

theorem propDenom_rest_neg (m M ε t : ℝ) (v : Fin 3 → ℝ) :
    propDenom M ε (restMomentum m + Fin.cons t (-v)) =
      propDenom M ε (restMomentum m + Fin.cons t v) := by
  simp only [propDenom, Minkowski.dot_eq, restMomentum, cons_eq_vec]
  simp

theorem propDenom_neg_spatial (M ε t : ℝ) (v : Fin 3 → ℝ) :
    propDenom M ε (Fin.cons t (-v)) = propDenom M ε (Fin.cons t v) := by
  simp only [propDenom, Minkowski.dot_eq, cons_eq_vec]
  simp

/-! ### The fixed-`q` value of the undoubled `CD1` piece -/

section FixedU

variable (P : Params) (hδ : P.δ₂ = 0) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
  {p' : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0' : 0 < p' 0)
  (hq : 0 < Minkowski.dot (p' - restMomentum P.m) (p' - restMomentum P.m))

/-- The odd part of the undoubled integrand after the Ward identity. -/
noncomputable def oddInt (ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  (propDenom P.m ε (restMomentum P.m + k))⁻¹ * phDen P ε k * spatL P.m p' k

/-- The engine hypotheses for the undoubled chain: continuous, affine, quadratically bounded. -/
theorem undChain_engine (e m : ℝ) (d : Fin 2) (p' p : Fin 4 → ℝ) :
    Continuous (undChain e m d p' p) ∧
      (∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
        undChain e m d p' p (Fin.cons t v : Fin 4 → ℝ) = 0 * (t : ℂ) ^ 2 + β * t + γ) ∧
      ∀ ℓ, ‖undChain e m d p' p ℓ‖ ≤
        (‖undC₀ e m d p' p‖ + ∑ i, ‖undC e m p' p i‖) * (1 + ‖ℓ‖) ^ 2 := by
  rw [undChain_eq_affN]
  exact ⟨continuous_affN _ _, affN_cons _ _, norm_affN_le _ _⟩

include hδ hp' in
theorem den₁_mul_numIn₁ {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) :
    den₁ P p' (restMomentum P.m) ε k *
        pauliNum P.m p' (restMomentum P.m) (fun μ => numIn₁ P p' (restMomentum P.m) μ k) =
      undCoeff P * powInt (undChain P.e P.m 0 p' (restMomentum P.m)) P.m 1 (phMs P)
          (fun _ => ε) ε p' (restMomentum P.m) k +
        (-(undCoeff P * chainC P.e)) * oddInt P (p' := p') ε k +
        (-(undCoeff P * chainC P.e * ((ε : ℂ) * I))) *
          (den₁ P p' (restMomentum P.m) ε k * spatL P.m p' k) := by
  have hD := propDenom_ne_zero (M := P.m) hε.ne' (p' + k)
  have hD0 : ((Minkowski.dot (p' + k) (p' + k) + P.m ^ 2 : ℝ) : ℂ) =
      propDenom P.m ε (p' + k) + (ε : ℂ) * I := by
    simp only [propDenom]
    ring
  rw [pauliNum_numIn₁ P hδ hp', pauliNum_gamma_slash, hD0]
  rw [show (∑ ν, ((Minkowski.lower k ν : ℝ) : ℂ) * ggWt P.m p' (restMomentum P.m) ν) =
    spatL P.m p' k from rfl]
  have hprod : ∏ j : Fin (2 + 2), (QED.OneLoop.denom (phMs P j) ε k)⁻¹ =
      (propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹ *
        ((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹) := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, phMs]
    simp only [QED.OneLoop.denom, propDenom]
    simp
    ring
  simp only [den₁, phDen, oddInt, powInt, prodIntegrand, hprod, pow_one]
  rw [show QED.OneLoop.denom P.m ε (p' + k) = propDenom P.m ε (p' + k) from rfl,
    show QED.OneLoop.denom P.m ε (restMomentum P.m + k) =
      propDenom P.m ε (restMomentum P.m + k) from rfl]
  generalize propDenom P.m ε (p' + k) = a at hD ⊢
  field_simp
  ring

include hm hp' hq in
/-- The odd part has energy-first integral zero. -/
theorem efi_oddInt (ε : ℝ) : QED.OneLoop.energyFirstIntegral (oddInt P (p' := p') ε) = 0 :=
  efi_eq_zero_of_odd fun t v => by
    simp only [oddInt, phDen, propDenom_rest_neg, propDenom_neg_spatial,
      spatL_neg hm.ne' hp' hq]
    ring

theorem efInt_oddInt {ε : ℝ} (hε : 0 < ε) : EFInt (oddInt P (p' := p') ε) := by
  have h := jointEnergyFirstIntegrable_affPoly_prod ![restMomentum P.m, 0, 0, 0, 0]
    ![P.m, P.mγ, P.Λ, P.mγ, P.Λ] hε (by simp) ((affPoly_spatL P.m p').mono (by norm_num))
  refine efInt_of_joint_one ((congrArg _ (funext fun ℓ => ?_)).mp h)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, oddInt, phDen, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  simp only [add_comm (ℓ 0)]
  ring

include hδ hm hmγ hΛ hp' hp0' hq

/-- **The Pauli projection of the undoubled `CD1` piece at fixed `q² > 0`**, at `δ₂ = 0` and the
rest momentum. -/
theorem pauliNum_pieceLim_in₁ :
    pauliNum P.m p' (restMomentum P.m)
        (pieceLim (den₁ P p' (restMomentum P.m)) (numIn₁ P p' (restMomentum P.m))) =
      undCoeff P * undValJ P.e P.m p' (restMomentum P.m) 1 (phMs P) := by
  classical
  set p := restMomentum P.m with hpdef
  have hp : Minkowski.dot p p = -P.m ^ 2 := dot_restMomentum
  have hp0 : 0 < p 0 := restMomentum_pos hm
  have hN : ∀ μ i j, IsLoopPoly 2 4 fun ℓ => numIn₁ P p' p μ (ℓ 0) i j :=
    fun μ i j => (affMat_numIn₁ P p' p μ i j).isLoopPoly
  choose v hv _hT hV using fun x : Idx => pieceLim_entry (by norm_num) kindsD3 (massesD3 P) hm
    (lt_min hmγ hΛ) (massesD3_sq_of_ne_pho P) (min_sq_le_massesD3_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD3 (by decide) (by decide) hp hp' hq.le (den₁ P p' p)
    (numIn₁ P p' p) hN (fun ε _ ℓ => den₁_fac P p p' ε ℓ) x.1 x.2.1 x.2.2
  set w : Idx → ℂ := fun x => pauliWt P.m p' p x.1 x.2.1 x.2.2
  have hsum := IsParamValue.sum Finset.univ w fun x _ => hv x
  set Np : (Fin 4 → ℝ) → ℂ := fun k => ∑ x : Idx, w x * numIn₁ P p' p x.1 k x.2.1 x.2.2
  have hNp : IsLoopPoly 2 4 fun ℓ => Np (ℓ 0) :=
    IsLoopPoly.sum _ fun x _ => (hN _ _ _).const_mul _
  obtain ⟨u, hu, hTu⟩ := exists_paramValue_of_kinds (by norm_num) kindsD3 (massesD3 P) hm
    (lt_min hmγ hΛ) hp hp' hq.le (massesD3_sq_of_ne_pho P) (min_sq_le_massesD3_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD3 (by decide) (by decide) Np hNp
    (fun ε k => den₁ P p' p ε k * Np k) (fun ε _ ℓ => by rw [den₁_fac P p p' ε ℓ]; ring)
  have huv : u = ∑ x, w x * v x := hu.unique hsum
  have hval : pauliNum P.m p' p (pieceLim (den₁ P p' p) (numIn₁ P p' p)) = u / auxLimit P.m := by
    rw [pauliNum_eq_sum_idx, huv, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hV x, mul_div_assoc]
  have hNpe : ∀ k, Np k = pauliNum P.m p' p (fun μ => numIn₁ P p' p μ k) :=
    fun k => by rw [pauliNum_eq_sum_idx]
  -- the three limits
  have hL : AffPoly 4 (spatL P.m p') := (affPoly_spatL P.m p').mono (by norm_num)
  obtain ⟨uL, -, hTL⟩ := exists_paramValue_of_kinds (by norm_num) kindsD3 (massesD3 P) hm
    (lt_min hmγ hΛ) hp hp' hq.le (massesD3_sq_of_ne_pho P) (min_sq_le_massesD3_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD3 (by decide) (by decide) (spatL P.m p') hL.isLoopPoly
    (fun ε k => den₁ P p' p ε k * spatL P.m p' k)
    (fun ε _ ℓ => by rw [den₁_fac P p p' ε ℓ]; ring)
  obtain ⟨hNc, hNq, hNb⟩ := undChain_engine P.e P.m 0 p' p
  have hU := tendsto_efi_powInt (M₀ := min P.mγ P.Λ) hm (lt_min hmγ hΛ) hp' hp hp0' hp0 hNc hNq
    hNb (l := 𝓝[>] (0 : ℝ)) (ε := id) tendsto_id 1 2 (by norm_num) (phMs P) (fun t _ => t)
    (le_phMs P) (fun _ => tendsto_id)
  rw [powLimit_undChain_eq hm hp' hp hp0' hp0 hq 1 (phMs P) (by norm_num) (phMs_pos P hmγ hΛ)
    0] at hU
  have hεI : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Complex.continuous_ofReal.tendsto (0 : ℝ)).mul_const I).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h
  have hlim := ((hU.const_mul (undCoeff P)).add
    (((hεI.const_mul (-(undCoeff P * chainC P.e))).mul hTL)))
  rw [hval]
  refine tendsto_nhds_unique hTu (hlim.congr' ?_ |>.trans_eq (by simp))
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hF : (fun k => den₁ P p' p ε k * Np k) = fun k =>
      undCoeff P * powInt (undChain P.e P.m 0 p' p) P.m 1 (phMs P) (fun _ => ε) ε p' p k +
        ((-(undCoeff P * chainC P.e)) * oddInt P (p' := p') ε k +
          (-(undCoeff P * chainC P.e * ((ε : ℂ) * I))) * (den₁ P p' p ε k * spatL P.m p' k)) := by
    funext k
    rw [hNpe, den₁_mul_numIn₁ P hδ hp' hε k, add_assoc]
  have i1 := efInt_powInt hm (lt_min hmγ hΛ) hp' hp hp0' hp0 hNc hNq hNb (j := 1) (k := 2)
    (by norm_num) (le_phMs P) (es := fun _ => ε) (fun _ => hε) hε
  have i2 := efInt_oddInt P hε (p' := p')
  have i3 := efInt_of_joint_one (G := fun k => den₁ P p' p ε k * spatL P.m p' k)
    (jointEnergyFirstIntegrable_den₁ P p' p hε hL)
  simp only [id]
  rw [hF, efi_add (i1.const_mul _) ((i2.const_mul _).add (i3.const_mul _)),
    efi_add (i2.const_mul _) (i3.const_mul _), efi_const_mul, efi_const_mul, efi_const_mul,
    efi_oddInt P hm hp' hq]
  ring

end FixedU

/-! ### `q → 0` along the curve -/

/-- The `q → 0` value of the even quotient of the undoubled `CD1` piece. -/
noncomputable def undZeroVal (P : Params) : ℂ :=
  undCoeff P * (I * ((Real.pi ^ 2 / 6 : ℝ) : ℂ) *
    (4 * QED.OneLoop.VertexLimit.kappa P.e * (4 * (P.m : ℂ) ^ 2 * (4 * (P.m : ℂ) ^ 2) ^ 2)) *
    ((∫ z, undKernJ P.m 0 1 (phMs P) z ∂QED.Integration.feynmanMeasure : ℝ) : ℂ))

/-- **The even quotient of the undoubled `CD1` piece along the curve.** -/
theorem tendsto_evenQuot_und (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (S : ℝ → ℂ) (hS : ∀ u ∈ Ioo (-1 : ℝ) 1, u ≠ 0 →
      S u = undCoeff P * undValJ P.e P.m (curveMomentum P.m u) (restMomentum P.m) 1 (phMs P)) :
    Tendsto (evenQuot S) (𝓝[≠] 0) (𝓝 (undZeroVal P)) := by
  have hev : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  set g : ℝ → ℂ := fun u => undCoeff P * (I * ((Real.pi ^ 2 / 6 : ℝ) : ℂ) *
    (4 * QED.OneLoop.VertexLimit.kappa P.e * (((curveQ P.m u / u ^ 2 : ℝ) : ℂ) *
      (4 * (P.m : ℂ) ^ 2 + (curveQ P.m u : ℂ)) ^ 2)) *
    ((∫ z, undKernJ P.m (curveQ P.m u) 1 (phMs P) z ∂QED.Integration.feynmanMeasure : ℝ) : ℂ))
  have hI := ((tendsto_integral_undKernJ hm (lt_min hmγ hΛ) (j := 1) (by norm_num)
    (le_phMs P)).comp (tendsto_curveQ_nhdsGE P.m))
  have hq0 : Tendsto (fun u => curveQ P.m u) (𝓝[≠] 0) (𝓝 0) :=
    (tendsto_curveQ_nhdsGE P.m).mono_right nhdsWithin_le_nhds
  have hg : Tendsto g (𝓝[≠] 0) (𝓝 (undZeroVal P)) := by
    have h1 := (Complex.continuous_ofReal.tendsto _).comp (tendsto_curveQ_div P.m)
    have h2 := (Complex.continuous_ofReal.tendsto _).comp hq0
    have h3 := (Complex.continuous_ofReal.tendsto _).comp hI
    have h := (tendsto_const_nhds (x := undCoeff P * (I * ((Real.pi ^ 2 / 6 : ℝ) : ℂ) *
      (4 * QED.OneLoop.VertexLimit.kappa P.e)))).mul ((h1.mul
        (((tendsto_const_nhds (x := 4 * (P.m : ℂ) ^ 2)).add h2).pow 2)).mul h3)
    convert h using 2
    · simp only [g, Function.comp]
      ring
    · simp only [undZeroVal]
      push_cast
      ring
  refine hg.congr' ?_
  filter_upwards [hev, self_mem_nhdsWithin] with u hu (hu0 : u ≠ 0)
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  rw [evenQuot, hS u hu hu0, hS (-u) hu' (neg_ne_zero.2 hu0), undValJ, undValJ,
    dot_curveMomentum_sub P.m hu, dot_curveMomentum_sub P.m hu', curveQ_neg]
  simp only [g]
  have hu2 : (u : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.2 hu0)
  push_cast
  field_simp
  ring

section ZeroU

variable (P : Params) (hδ : P.δ₂ = 0) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
include hδ hm hmγ hΛ

/-- **The `q → 0` value of the undoubled `CD1` piece**, explicitly, at `δ₂ = 0`. -/
theorem kindsZero_in₁_eq :
    kindsZero kindsD3 (massesD3 P) P (fun p' => numIn₁ P p' (restMomentum P.m)) =
      undZeroVal P := by
  have h₁ := tendsto_evenQuot_pieceLim (by norm_num) kindsD3 (massesD3 P) P hm (lt_min hmγ hΛ)
    (massesD3_sq_of_ne_pho P) (min_sq_le_massesD3_sq P hmγ hΛ) intNoSubdivergenceRefined_kindsD3
    (by decide) (by decide) (fun p' => den₁ P p' (restMomentum P.m))
    (fun p' => numIn₁ P p' (restMomentum P.m))
    (fun p' μ i j => (affMat_numIn₁ P p' _ μ i j).isLoopPoly)
    (fun μ i j k => isLoopPoly_numIn₁_out P _ μ i j k)
    (fun p' ε _ ℓ => den₁_fac P _ p' ε ℓ)
  refine tendsto_nhds_unique h₁ (tendsto_evenQuot_und P hm hmγ hΛ _ fun u hu hu0 => ?_)
  have hq := curveQ_pos P.m hm hu hu0
  rw [← dot_curveMomentum_sub P.m hu] at hq
  exact pauliNum_pieceLim_in₁ P hδ hm hmγ hΛ (dot_curveMomentum P.m hu)
    (curveMomentum_pos hm hu) hq

/-- **The `q → 0` value of the limit of `CD1 t`** at `δ₂ = 0`: the undoubled and the doubled
pieces. -/
theorem cdInZero_eq : cdInZero P = undZeroVal P + cdZeroVal P 0 := by
  rw [cdInZero, kindsZero_in₁_eq P hδ hm hmγ hΛ, kindsZero_in_eq P hm hmγ hΛ]

end ZeroU

end QED.ChainProof.CtLoB

end
