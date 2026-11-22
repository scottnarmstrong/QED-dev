/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBCU
public import QED.ChainProof.SetCLimCtCD01
import Mathlib.Tactic.Ring

/-!
# The undoubled `CD0` piece of the mass part, and the `q → 0` value of `CD0`

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), layer 6. The
mirror of `QED/ChainProof/SetCRegDispCtLoBCU.lean` for the outgoing line. Along the curve the
outgoing momentum moves, so the spatial-oddness argument is run with the outgoing momentum at
rest, and the two frames are related by the reflection in `p' - p`, which exchanges the two
on-shell momenta and has a spinor lift (`pieceLim_map`, `pauliNum_map`).

* `pauliNum_numOut₁`: the Pauli projection of the undoubled `CD0` numerator at `δ₂ = 0`;
* `pauliNum_pieceLim_out₁_rest`: the fixed-`q` value with the outgoing momentum at rest;
* **`pauliNum_pieceLim_out₁_swap`**: the Pauli projection is symmetric in `(p', p)`;
* **`kindsZero_out₁_eq`**, **`cdOutZero_eq`**: the `q → 0` value of `CD0`,
  `cdOutZero Q = undZeroVal Q + cdZeroVal Q 1` at `δ₂ = 0`;
* **`undZeroVal_add_cdZeroVal`**, `cdOutZero_eq_cdInZero`: the closed form
  `-(δ_m δ₃/2)(Λ² - m_γ²)² i (π²/6) 4κ_e 64 m⁷ ∫₀¹ 6y (K² g)'(K) dy`, independent of the line.
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

/-! ### The mirrored sandwiches -/

/-- The Pauli weights of `γ^ν γ^μ`. -/
noncomputable def ggWtO (m : ℝ) (p' p : Fin 4 → ℝ) (ν : Fin 4) : ℂ :=
  pauliNum m p' p fun μ => gamma ν * gamma μ

theorem pauliNum_slash_gamma (m : ℝ) (p' p k : Fin 4 → ℝ) :
    pauliNum m p' p (fun μ => slash k * gamma μ) =
      ∑ ν, ((Minkowski.lower k ν : ℝ) : ℂ) * ggWtO m p' p ν := by
  have h : (fun μ => slash k * gamma μ) =
      fun μ => ∑ ν, ((Minkowski.lower k ν : ℝ) : ℂ) • (fun ν μ => gamma ν * gamma μ) ν μ := by
    funext μ
    simp only [slash, Matrix.sum_mul, Matrix.smul_mul]
  rw [h, pauliNum_sum_smul]
  rfl

/-- With the outgoing momentum at rest the time weight vanishes. -/
theorem ggWtO_zero {m : ℝ} (hm : m ≠ 0) {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (restMomentum m - p) (restMomentum m - p)) :
    ggWtO m (restMomentum m) p 0 = 0 := by
  have hs : slash (restMomentum m) = (-(m : ℂ)) • gamma 0 := by
    simp [slash, restMomentum, Minkowski.lower_eq, Fin.sum_univ_four]
  have hAp : electronNumerator m (restMomentum m) * slash (restMomentum m) =
      (-(m : ℂ)) • electronNumerator m (restMomentum m) := by
    have h := mass_sub_slash_mul_slash_add (dot_restMomentum (m := m))
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at h
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have h1 : pauliNum m (restMomentum m) p (fun μ => gamma 0 * gamma μ) =
      pauliNum m (restMomentum m) p (fun μ => (1 : ℂ) • gamma μ) := by
    refine pauliNum_congr_sandwich fun μ => ?_
    have hg : gamma 0 = (-(m : ℂ))⁻¹ • slash (restMomentum m) := by
      rw [hs, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hm'), one_smul]
    rw [hg]
    simp only [Matrix.mul_smul, Matrix.smul_mul, one_smul]
    rw [← Matrix.mul_assoc (electronNumerator m (restMomentum m)), hAp, Matrix.smul_mul,
      Matrix.smul_mul, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hm'), one_smul]
  rw [ggWtO, h1, pauliNum_smul, pauliNum_gamma hm dot_restMomentum hp hq, mul_zero]

/-- The longitudinal chain with the identity on the outgoing line, between on-shell spinors. -/
theorem pauliNum_longitudinal_out (e : ℝ) {m : ℝ} {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (p' k : Fin 4 → ℝ) :
    pauliNum m p' p (fun μ => vertexChain e μ 𝟙 (electronNumerator m (p + k))
        (fun ν ρ => ((Minkowski.lower k ν : ℝ) : ℂ) * ((Minkowski.lower k ρ : ℝ) : ℂ))) =
      chainC e * ((Minkowski.dot (p + k) (p + k) + m ^ 2 : ℝ) : ℂ) *
        pauliNum m p' p (fun μ => slash k * gamma μ) := by
  rw [mul_assoc, ← pauliNum_smul, ← pauliNum_smul]
  refine pauliNum_congr_sandwich fun μ => ?_
  rw [vertexChain_longitudinal, ← chainC]
  have e1 : electronNumerator m p' *
      (chainC e • (slash k * 𝟙 * gamma μ * electronNumerator m (p + k) * slash k)) *
        electronNumerator m p =
      chainC e • ((electronNumerator m p' * (slash k * gamma μ)) *
        (electronNumerator m (p + k) * slash k * electronNumerator m p)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e1, ward_in hp k]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]

/-- **The Pauli projection of the undoubled `CD0` numerator** at `δ₂ = 0`. -/
theorem pauliNum_numOut₁ (P : Params) (hδ : P.δ₂ = 0) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (p' k : Fin 4 → ℝ) :
    pauliNum P.m p' p (fun μ => numOut₁ P p' p μ k) =
      undCoeff P * ((Minkowski.dot k k : ℝ) : ℂ) * undChain P.e P.m 1 p' p k -
        undCoeff P * chainC P.e * ((Minkowski.dot (p + k) (p + k) + P.m ^ 2 : ℝ) : ℂ) *
          pauliNum P.m p' p (fun μ => slash k * gamma μ) := by
  simp only [numOut₁, neg_mergeY_of_zero P hδ, photonNum_eq, vertexChain_smul_out,
    vertexChain_add_photon, vertexChain_smul_photon, smul_smul]
  rw [QED.TwoLoop.PauliZeroLimit.pauliNum_add, pauliNum_smul, pauliNum_smul,
    pauliNum_longitudinal_out P.e hp p' k]
  have hg : (pauliNum P.m p' p fun μ =>
      vertexChain P.e μ 𝟙 (electronNumerator P.m (p + k)) gPhoton) =
        undChain P.e P.m 1 p' p k := by
    simp [undChain]
  rw [hg, undCoeff]
  ring

/-! ### The odd part with the outgoing momentum at rest -/

/-- The spatial linear form of the longitudinal part with the outgoing momentum at rest. -/
noncomputable def spatLO (m : ℝ) (p k : Fin 4 → ℝ) : ℂ :=
  ∑ ν, ((Minkowski.lower k ν : ℝ) : ℂ) * ggWtO m (restMomentum m) p ν

theorem affPoly_spatLO (m : ℝ) (p : Fin 4 → ℝ) : AffPoly 1 (spatLO m p) := by
  have h := AffPoly.aff 0 fun ν =>
    ((Minkowski.metric ν ν : ℝ) : ℂ) * ggWtO m (restMomentum m) p ν
  refine (congrArg (AffPoly 1) (funext fun k => ?_)).mp h
  simp only [spatLO, Minkowski.lower_eq, Fin.sum_univ_four, Minkowski.metric]
  simp
  ring

theorem spatLO_neg {m : ℝ} (hm : m ≠ 0) {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2)
    (hq : 0 < Minkowski.dot (restMomentum m - p) (restMomentum m - p)) (t : ℝ)
    (v : Fin 3 → ℝ) : spatLO m p (Fin.cons t (-v)) = -spatLO m p (Fin.cons t v) := by
  simp only [spatLO, Minkowski.lower_eq, Fin.sum_univ_four, ggWtO_zero hm hp hq, cons_eq_vec]
  simp
  ring

section FixedO

variable (P : Params) (hδ : P.δ₂ = 0) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
  {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp0 : 0 < p 0)
  (hq : 0 < Minkowski.dot (restMomentum P.m - p) (restMomentum P.m - p))

/-- The odd part of the undoubled `CD0` integrand after the Ward identity. -/
noncomputable def oddIntO (ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  (propDenom P.m ε (restMomentum P.m + k))⁻¹ * phDen P ε k * spatLO P.m p k

include hδ hp in
theorem den₁_mul_numOut₁ {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) :
    den₁ P (restMomentum P.m) p ε k *
        pauliNum P.m (restMomentum P.m) p (fun μ => numOut₁ P (restMomentum P.m) p μ k) =
      undCoeff P * powInt (undChain P.e P.m 1 (restMomentum P.m) p) P.m 1 (phMs P)
          (fun _ => ε) ε (restMomentum P.m) p k +
        (-(undCoeff P * chainC P.e)) * oddIntO P (p := p) ε k +
        (-(undCoeff P * chainC P.e * ((ε : ℂ) * I))) *
          (den₁ P (restMomentum P.m) p ε k * spatLO P.m p k) := by
  have hD := propDenom_ne_zero (M := P.m) hε.ne' (p + k)
  have hD0 : ((Minkowski.dot (p + k) (p + k) + P.m ^ 2 : ℝ) : ℂ) =
      propDenom P.m ε (p + k) + (ε : ℂ) * I := by
    simp only [propDenom]
    ring
  rw [pauliNum_numOut₁ P hδ hp, pauliNum_slash_gamma, hD0]
  rw [show (∑ ν, ((Minkowski.lower k ν : ℝ) : ℂ) * ggWtO P.m (restMomentum P.m) p ν) =
    spatLO P.m p k from rfl]
  have hprod : ∏ j : Fin (2 + 2), (QED.OneLoop.denom (phMs P j) ε k)⁻¹ =
      (propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹ *
        ((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹) := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, phMs]
    simp only [QED.OneLoop.denom, propDenom]
    simp
    ring
  simp only [den₁, phDen, oddIntO, powInt, prodIntegrand, hprod, pow_one]
  rw [show QED.OneLoop.denom P.m ε (p + k) = propDenom P.m ε (p + k) from rfl,
    show QED.OneLoop.denom P.m ε (restMomentum P.m + k) =
      propDenom P.m ε (restMomentum P.m + k) from rfl]
  generalize propDenom P.m ε (p + k) = a at hD ⊢
  field_simp
  ring

include hm hp hq in
theorem efi_oddIntO (ε : ℝ) : QED.OneLoop.energyFirstIntegral (oddIntO P (p := p) ε) = 0 :=
  efi_eq_zero_of_odd fun t v => by
    simp only [oddIntO, phDen, propDenom_rest_neg, propDenom_neg_spatial,
      spatLO_neg hm.ne' hp hq]
    ring

theorem efInt_oddIntO {ε : ℝ} (hε : 0 < ε) : EFInt (oddIntO P (p := p) ε) := by
  have h := jointEnergyFirstIntegrable_affPoly_prod ![restMomentum P.m, 0, 0, 0, 0]
    ![P.m, P.mγ, P.Λ, P.mγ, P.Λ] hε (by simp) ((affPoly_spatLO P.m p).mono (by norm_num))
  refine efInt_of_joint_one ((congrArg _ (funext fun ℓ => ?_)).mp h)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, oddIntO, phDen, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  simp only [add_comm (ℓ 0)]
  ring

include hδ hm hmγ hΛ hp hp0 hq

/-- **The Pauli projection of the undoubled `CD0` piece at fixed `q² > 0`**, at `δ₂ = 0` with
the outgoing momentum at rest. -/
theorem pauliNum_pieceLim_out₁_rest :
    pauliNum P.m (restMomentum P.m) p
        (pieceLim (den₁ P (restMomentum P.m) p) (numOut₁ P (restMomentum P.m) p)) =
      undCoeff P * undValJ P.e P.m (restMomentum P.m) p 1 (phMs P) := by
  classical
  set p' := restMomentum P.m with hp'def
  have hp' : Minkowski.dot p' p' = -P.m ^ 2 := dot_restMomentum
  have hp0' : 0 < p' 0 := restMomentum_pos hm
  have hN : ∀ μ i j, IsLoopPoly 2 4 fun ℓ => numOut₁ P p' p μ (ℓ 0) i j :=
    fun μ i j => (affMat_numOut₁ P p' p μ i j).isLoopPoly
  choose v hv _hT hV using fun x : Idx => pieceLim_entry (by norm_num) kindsD3 (massesD3 P) hm
    (lt_min hmγ hΛ) (massesD3_sq_of_ne_pho P) (min_sq_le_massesD3_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD3 (by decide) (by decide) hp hp' hq.le (den₁ P p' p)
    (numOut₁ P p' p) hN (fun ε _ ℓ => den₁_fac P p p' ε ℓ) x.1 x.2.1 x.2.2
  set w : Idx → ℂ := fun x => pauliWt P.m p' p x.1 x.2.1 x.2.2
  have hsum := IsParamValue.sum Finset.univ w fun x _ => hv x
  set Np : (Fin 4 → ℝ) → ℂ := fun k => ∑ x : Idx, w x * numOut₁ P p' p x.1 k x.2.1 x.2.2
  have hNp : IsLoopPoly 2 4 fun ℓ => Np (ℓ 0) :=
    IsLoopPoly.sum _ fun x _ => (hN _ _ _).const_mul _
  obtain ⟨u, hu, hTu⟩ := exists_paramValue_of_kinds (by norm_num) kindsD3 (massesD3 P) hm
    (lt_min hmγ hΛ) hp hp' hq.le (massesD3_sq_of_ne_pho P) (min_sq_le_massesD3_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD3 (by decide) (by decide) Np hNp
    (fun ε k => den₁ P p' p ε k * Np k) (fun ε _ ℓ => by rw [den₁_fac P p p' ε ℓ]; ring)
  have huv : u = ∑ x, w x * v x := hu.unique hsum
  have hval : pauliNum P.m p' p (pieceLim (den₁ P p' p) (numOut₁ P p' p)) =
      u / auxLimit P.m := by
    rw [pauliNum_eq_sum_idx, huv, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hV x, mul_div_assoc]
  have hNpe : ∀ k, Np k = pauliNum P.m p' p (fun μ => numOut₁ P p' p μ k) :=
    fun k => by rw [pauliNum_eq_sum_idx]
  have hL : AffPoly 4 (spatLO P.m p) := (affPoly_spatLO P.m p).mono (by norm_num)
  obtain ⟨uL, -, hTL⟩ := exists_paramValue_of_kinds (by norm_num) kindsD3 (massesD3 P) hm
    (lt_min hmγ hΛ) hp hp' hq.le (massesD3_sq_of_ne_pho P) (min_sq_le_massesD3_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD3 (by decide) (by decide) (spatLO P.m p) hL.isLoopPoly
    (fun ε k => den₁ P p' p ε k * spatLO P.m p k)
    (fun ε _ ℓ => by rw [den₁_fac P p p' ε ℓ]; ring)
  obtain ⟨hNc, hNq, hNb⟩ := undChain_engine P.e P.m 1 p' p
  have hU := tendsto_efi_powInt (M₀ := min P.mγ P.Λ) hm (lt_min hmγ hΛ) hp' hp hp0' hp0 hNc hNq
    hNb (l := 𝓝[>] (0 : ℝ)) (ε := id) tendsto_id 1 2 (by norm_num) (phMs P) (fun t _ => t)
    (le_phMs P) (fun _ => tendsto_id)
  have hq' : 0 < Minkowski.dot (p' - p) (p' - p) := hq
  rw [powLimit_undChain_eq hm hp' hp hp0' hp0 hq' 1 (phMs P) (by norm_num) (phMs_pos P hmγ hΛ)
    1] at hU
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
      undCoeff P * powInt (undChain P.e P.m 1 p' p) P.m 1 (phMs P) (fun _ => ε) ε p' p k +
        ((-(undCoeff P * chainC P.e)) * oddIntO P (p := p) ε k +
          (-(undCoeff P * chainC P.e * ((ε : ℂ) * I))) *
            (den₁ P p' p ε k * spatLO P.m p k)) := by
    funext k
    rw [hNpe, den₁_mul_numOut₁ P hδ hp hε k, add_assoc]
  have i1 := efInt_powInt hm (lt_min hmγ hΛ) hp' hp hp0' hp0 hNc hNq hNb (j := 1) (k := 2)
    (by norm_num) (le_phMs P) (es := fun _ => ε) (fun _ => hε) hε
  have i2 := efInt_oddIntO P hε (p := p)
  have i3 := efInt_of_joint_one (G := fun k => den₁ P p' p ε k * spatLO P.m p k)
    (jointEnergyFirstIntegrable_den₁ P p' p hε hL)
  simp only [id]
  rw [hF, efi_add (i1.const_mul _) ((i2.const_mul _).add (i3.const_mul _)),
    efi_add (i2.const_mul _) (i3.const_mul _), efi_const_mul, efi_const_mul, efi_const_mul,
    efi_oddIntO P hm hp hq]
  ring

end FixedO

/-! ### Exchanging the external momenta -/

theorem dot_sub_comm (a b : Fin 4 → ℝ) :
    Minkowski.dot (a - b) (a - b) = Minkowski.dot (b - a) (b - a) := by
  simp only [Minkowski.dot_eq, Pi.sub_apply]
  ring

theorem undValJ_comm (e m : ℝ) (p' p : Fin 4 → ℝ) (j : ℕ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) :
    undValJ e m p' p j Ms = undValJ e m p p' j Ms := by
  rw [undValJ, undValJ, dot_sub_comm]

/-- The reflection in `p' - p` exchanges two on-shell momenta of the same mass. -/
theorem reflect_sub_swap {m : ℝ} {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hK : Minkowski.dot (p' - p) (p' - p) ≠ 0) :
    reflect (p' - p) p' = p ∧ reflect (p' - p) p = p' := by
  have h1 : 2 * Minkowski.dot (p' - p) p' = Minkowski.dot (p' - p) (p' - p) := by
    simp only [Minkowski.dot_eq, Pi.sub_apply] at hp' hp ⊢
    linear_combination hp' - hp
  have h2 : 2 * Minkowski.dot (p' - p) p = -Minkowski.dot (p' - p) (p' - p) := by
    simp only [Minkowski.dot_eq, Pi.sub_apply] at hp' hp ⊢
    linear_combination hp' - hp
  have c1 : 2 * Minkowski.dot (p' - p) p' / Minkowski.dot (p' - p) (p' - p) = 1 := by
    rw [h1, div_self hK]
  have c2 : 2 * Minkowski.dot (p' - p) p / Minkowski.dot (p' - p) (p' - p) = -1 := by
    rw [h2, neg_div, div_self hK]
  refine ⟨?_, ?_⟩
  · rw [reflect, c1, one_smul]
    abel
  · rw [reflect, c2, neg_one_smul, sub_neg_eq_add]
    abel

/-- **The undoubled `CD0` piece is symmetric in the external momenta**: the reflection in
`p' - p` exchanges them and is a spinor-lifted Lorentz map. -/
theorem pauliNum_pieceLim_out₁_swap (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hp : Minkowski.dot p p = -P.m ^ 2) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) :
    pauliNum P.m p' p (pieceLim (den₁ P p' p) (numOut₁ P p' p)) =
      pauliNum P.m p p' (pieceLim (den₁ P p p') (numOut₁ P p p')) := by
  have h := isSpinLift_reflect hq.ne'
  obtain ⟨e1, e2⟩ := reflect_sub_swap hp' hp hq.ne'
  have hL' : reflectMatrix (p' - p) *ᵥ p' = p := by rw [reflectMatrix_mulVec, e1]
  have hL : reflectMatrix (p' - p) *ᵥ p = p' := by rw [reflectMatrix_mulVec, e2]
  have hW := fun μ => pieceLim_map (by norm_num) kindsD3 (massesD3 P) hm (lt_min hmγ hΛ)
    (massesD3_sq_of_ne_pho P) (min_sq_le_massesD3_sq P hmγ hΛ)
    intNoSubdivergenceRefined_kindsD3 (by decide) (by decide) h (fun p p' => den₁ P p' p)
    (fun p p' => numOut₁ P p' p) (fun p p' μ i j => (affMat_numOut₁ P p' p μ i j).isLoopPoly)
    (fun p p' ε _ ℓ => den₁_fac P p p' ε ℓ) (fun p p' μ k => numOut₁_map h P p' p μ k)
    hp hp' hq.le μ
  have key := pauliNum_map h P.m p' p hW
  simp only [hL, hL'] at key
  exact key.symm

section ZeroO

variable (P : Params) (hδ : P.δ₂ = 0) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
include hδ hm hmγ hΛ

/-- **The `q → 0` value of the undoubled `CD0` piece**, explicitly, at `δ₂ = 0`. -/
theorem kindsZero_out₁_eq :
    kindsZero kindsD3 (massesD3 P) P (fun p' => numOut₁ P p' (restMomentum P.m)) =
      undZeroVal P := by
  have h₁ := tendsto_evenQuot_pieceLim (by norm_num) kindsD3 (massesD3 P) P hm (lt_min hmγ hΛ)
    (massesD3_sq_of_ne_pho P) (min_sq_le_massesD3_sq P hmγ hΛ) intNoSubdivergenceRefined_kindsD3
    (by decide) (by decide) (fun p' => den₁ P p' (restMomentum P.m))
    (fun p' => numOut₁ P p' (restMomentum P.m))
    (fun p' μ i j => (affMat_numOut₁ P p' _ μ i j).isLoopPoly)
    (fun μ i j k => isLoopPoly_numOut₁_out P _ μ i j k)
    (fun p' ε _ ℓ => den₁_fac P _ p' ε ℓ)
  refine tendsto_nhds_unique h₁ (tendsto_evenQuot_und P hm hmγ hΛ _ fun u hu hu0 => ?_)
  have hq := curveQ_pos P.m hm hu hu0
  rw [← dot_curveMomentum_sub P.m hu] at hq
  have hq' := hq
  rw [dot_sub_comm] at hq'
  rw [pauliNum_pieceLim_out₁_swap P hm hmγ hΛ (dot_curveMomentum P.m hu) dot_restMomentum hq,
    pauliNum_pieceLim_out₁_rest P hδ hm hmγ hΛ (dot_curveMomentum P.m hu)
      (curveMomentum_pos hm hu) hq', undValJ_comm]

/-- **The `q → 0` value of the limit of `CD0 t`** at `δ₂ = 0`. -/
theorem cdOutZero_eq : cdOutZero P = undZeroVal P + cdZeroVal P 1 := by
  rw [cdOutZero, kindsZero_out₁_eq P hδ hm hmγ hΛ, kindsZero_out_eq P hm hmγ hΛ]

end ZeroO

/-! ### The `CD` value in closed form -/

/-- **The `q → 0` value of `CD0`, `CD1` at `δ₂ = 0` as one radial integral**, independent of the
line `d`: with `K = y² m²/(1 - y)` and `g = ∏ (K + M_i²)⁻¹` over `(m_γ, Λ, m_γ, Λ)`,
`undZeroVal + cdZeroVal d = -(δ_m δ₃/2)(Λ² - m_γ²)² · i (π²/6) 4κ_e (64 m⁷) ∫₀¹ 6y (K² g)'(K) dy`.
-/
theorem undZeroVal_add_cdZeroVal (P : Params) (hδ : P.δ₂ = 0) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (d : Fin 2) :
    undZeroVal P + cdZeroVal P d =
      -((P.δm * P.δ₃ / 2 * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ) *
        (I * ((Real.pi ^ 2 / 6 : ℝ) : ℂ) * (4 * QED.OneLoop.VertexLimit.kappa P.e) *
          (64 * (P.m : ℂ) ^ 7)) *
        ((∫ y in (0 : ℝ)..1, 6 * y *
          deriv (fun K => K ^ 2 * phf (phMs P) K) (radKY P.m y) : ℝ) : ℂ) := by
  have h := integral_combJ_zero_deriv hm (phMs_pos P hmγ hΛ) d (j := 1) (by norm_num)
  rw [integral_sub (integrable_undKernJ hm le_rfl (lt_min hmγ hΛ) (by norm_num) (le_phMs P))
    ((integrable_dblKernJ hm le_rfl (lt_min hmγ hΛ) (by norm_num) (le_phMs P) d).const_mul _),
    integral_const_mul] at h
  rw [← h]
  simp only [undZeroVal, cdZeroVal, undCoeff, cdCoeff, mergeC, hδ]
  push_cast
  ring

/-- **The `q → 0` values of `CD0` and `CD1` agree** at `δ₂ = 0`. -/
theorem cdOutZero_eq_cdInZero (P : Params) (hδ : P.δ₂ = 0) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) : cdOutZero P = cdInZero P := by
  rw [cdOutZero_eq P hδ hm hmγ hΛ, cdInZero_eq P hδ hm hmγ hΛ,
    undZeroVal_add_cdZeroVal P hδ hm hmγ hΛ, undZeroVal_add_cdZeroVal P hδ hm hmγ hΛ]

end QED.ChainProof.CtLoB

end
