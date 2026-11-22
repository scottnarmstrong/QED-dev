/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideBDNestedGen
public import QED.ChainProof.SetCMainBDecayBub
public import QED.GradedProof.SE2ClassV

/-!
# Set (c): the vacuum-polarization self-energy class at fixed `ε`, nested equals joint

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values`, step S2 of the plan: the class `V`
(`QED.GradedProof.SE2.repV`, the two-loop self-energy with a fermion loop on the photon line) at
fixed `ε > 0` is the one-loop energy-first integral over the photon momentum `k` of an outer factor
contracted with the closed form of the inner vacuum polarization.

The outer factor is `seVOuter P p α β k ρ σ`: the open-line chain `γ^{l₁} S_m(p - k) γ^{l₀}`
contracted with the photon propagators `D(k)_{l₀ρ}`, `D(-k)_{l₁σ}`, with the constants of the two
open-line vertices, the three outer propagators and `(2π)⁻⁴`, and `-1` (carried by the vacuum
polarization integrand). It decays like `(1 + |k⁰|)⁻⁹`, one power less than the vertex outer
factor, which the bound `(1 + ‖k‖)⁶` of the inner energy integral
(`QED.ChainProof.SetCMainB.exists_norm_spatialG_le_six`) accommodates.

## Main statements

* `integrable_outer_mul_spatialG_eight`, `jointEnergyFirstIntegral_nestedF_eight`: nested equals
  joint for `QED.ChainProof.HCSide.nestedF` with an outer factor decaying like `(1 + |t|)⁻⁸`;
* `repV_integrand_unswap`: in the routing `q = ℓ 0` (fermion loop), `k = ℓ 1` (photon), the
  integrand of the value of `repV` is `nestedF P (seVOuter P p α β)`;
* `decaysLike_seVOuter`, `continuous_seVOuter`;
* **`contractionValue₂_repV_eq_outerF`**: for admissible parameters with `m < M₁, M₂`, the value
  of `repV` at the self-energy kinematics is the energy-first integral of
  `outerF P (seVOuter P p α β)`, which is integrable in both stages.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.WickModel.VacuumPolarizationLimit QED.OneLoop
open QED.TwoLoop.NestedVPFubiniBound (DecaysLike one_add_abs_pos one_add_norm_cons_le
  aestronglyMeasurable_spatialG_cons)
open QED.ChainProof.HCSide (nestedF outerF integral_nestedF_time energyFirstIntegral_nestedF)
open QED.TwoLoop.VPUnitNested (EFInt)

/-! ### Nested equals joint under the decay `(1 + |t|)⁻⁸` -/

section Generic

variable {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
  (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
  (hε : 0 < P.ε)

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **One term of the Fubini condition**: a continuous factor decaying like `(1 + |t|)⁻⁸` times
the energy integral of the vacuum polarization integrand is integrable in `(t, v⃗)`. -/
theorem integrable_outer_mul_spatialG_eight {g : ℝ → ℂ} (hc : Continuous g)
    (hd : DecaysLike g 8) (w : Fin 3 → ℝ) (ρ σ : Fin 4) :
    Integrable fun x : ℝ × (Fin 3 → ℝ) => g x.1 * spatialG P P.ε (Fin.cons x.1 w) ρ σ x.2 := by
  obtain ⟨Co, hCo⟩ := hd
  have hCo0 := QED.TwoLoop.NestedVPFubiniBound.DecaysLike.const_nonneg hCo
  obtain ⟨Ci, hCi0, hCi⟩ :=
    QED.ChainProof.SetCMainB.exists_norm_spatialG_le_six hm hM₁ hM₂ hPV₁ hPV₂ hε ρ σ
  set K := Co * Ci * (1 + ‖w‖) ^ 6
  have hint : Integrable (fun x : ℝ × (Fin 3 → ℝ) =>
      K * ((1 + ‖x.1‖) ^ (-(2 : ℝ)) * (1 + ‖x.2‖) ^ (-(7 / 2 : ℝ)))) := by
    refine Integrable.const_mul ?_ K
    exact (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).mul_prod
      (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 7 / 2) (by simp; norm_num))
  refine hint.mono' ((hc.comp continuous_fst).aestronglyMeasurable.mul
    (aestronglyMeasurable_spatialG_cons P hε w ρ σ)) (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨t, v⟩ := x
  simp only
  rw [norm_mul, Real.norm_eq_abs]
  have ht0 : 0 < 1 + |t| := one_add_abs_pos t
  have hw0 : 0 < 1 + ‖w‖ := by positivity
  have h1 := hCo t
  have h2 := hCi (Fin.cons t w) v
  have hk : (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ 6 ≤ (1 + |t|) ^ 6 * (1 + ‖w‖) ^ 6 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_norm_cons_le t w) 6
  have hz : (1 + |t|) ^ (-(8 : ℤ)) * (1 + |t|) ^ 6 = (1 + |t|) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_add ht0]
    norm_num
  calc ‖g t‖ * ‖spatialG P P.ε (Fin.cons t w) ρ σ v‖
      ≤ (Co * (1 + |t|) ^ (-(8 : ℤ))) *
          (Ci * (1 + ‖(Fin.cons t w : Fin 4 → ℝ)‖) ^ 6 * (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ ≤ (Co * (1 + |t|) ^ (-(8 : ℤ))) *
          (Ci * ((1 + |t|) ^ 6 * (1 + ‖w‖) ^ 6) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) := by gcongr
    _ = K * (((1 + |t|) ^ (-(8 : ℤ)) * (1 + |t|) ^ 6) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) := by ring
    _ = K * ((1 + |t|) ^ (-(2 : ℝ)) * (1 + ‖v‖) ^ (-(7 / 2 : ℝ))) := by rw [hz]

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **Nested equals joint with the inner loop in closed form**, for an outer factor with
continuous entries decaying like `(1 + |t|)⁻⁸` along `k = (t, w)`. -/
theorem jointEnergyFirstIntegral_nestedF_eight (O : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hc : ∀ w ρ σ, Continuous fun t => O (Fin.cons t w) ρ σ)
    (hd : ∀ w ρ σ, DecaysLike (fun t => O (Fin.cons t w) ρ σ) 8)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 2 (nestedF P O)) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (nestedF P O) = energyFirstIntegral (outerF P O) ∧
      EFInt (outerF P O) := by
  have hG : ∀ w : Fin 3 → ℝ, Integrable fun x : ℝ × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, nestedF P O ![Fin.cons t₁ x.2, Fin.cons x.1 w] := fun w => by
    simp only [integral_nestedF_time hε]
    exact integrable_finsetSum _ fun ρ _ => integrable_finsetSum _ fun σ _ =>
      integrable_outer_mul_spatialG_eight hm hM₁ hM₂ hPV₁ hPV₂ hε (hc w ρ σ) (hd w ρ σ) w ρ σ
  have he : (fun k => energyFirstIntegral fun q => nestedF P O ![q, k]) = outerF P O :=
    funext (energyFirstIntegral_nestedF hm hM₁ hM₂ hPV₁ hPV₂ hε O)
  refine ⟨?_, ?_⟩
  · rw [QED.TwoLoop.NestedVP.jointEnergyFirstIntegral_eq_nested _ hF (ae_of_all _ hG), he]
  · have h := QED.TwoLoop.VPHalfAtAssembly.efInt_of_joint _ hF hG
    rwa [he] at h

end Generic

/-! ### The class `V` in the nested routing -/

/-- **The outer factor of the class `V`**, for the Lorentz indices `ρ, σ` of the two ends of the
inserted vacuum polarization: the open-line chain `γ^{l₁} S_m(p - k) γ^{l₀}` contracted with the
photon propagators of momenta `k` and `-k`, the constants of the two open-line vertices, of the
three outer propagators and of `(2π)⁻⁴`, and `-1`. -/
noncomputable def seVOuter (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (k : Fin 4 → ℝ)
    (ρ σ : Fin 4) : ℂ :=
  -(((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 2 * (1 / I) ^ 3 *
    ∑ l0 : Fin 4, ∑ l1 : Fin 4,
      (Dirac.gamma l1 * electronPropagator P.m P.ε (p - k) * Dirac.gamma l0) α β *
        photonPropagator P.mγ P.Λ P.ε k l0 ρ * photonPropagator P.mγ P.Λ P.ε (-k) l1 σ

open QED.GradedProof.SE2 in
/-- **The integrand factorizes**: at the loop momenta `(p - ℓ 1, ℓ 0)` of the frozen routing
(open line `p - k`, loop lines `q`, `q + k`, photons `k`, `-k` with `q = ℓ 0`, `k = ℓ 1`),
`(2π)⁻⁸` times the regulated amplitude of `repV` is `nestedF P (seVOuter P p α β) ℓ`. -/
theorem repV_integrand_unswap (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repV ![p] ![] (lineMomentum₂ repV ![p] ![p] ![]
          ((fun s => ∑ r, QED.TwoLoop.NestedVP.unswapMat s r • ℓ r) + ![p, 0])) ![α] ![β] ![] =
      nestedF P (seVOuter P p α β) ℓ := by
  obtain ⟨h0, h1⟩ := QED.TwoLoop.NestedVP.unswapMat_act ℓ p
  set L := (fun s => ∑ r, QED.TwoLoop.NestedVP.unswapMat s r • ℓ r) + ![p, 0] with hL
  obtain ⟨m1, m2, m3, m4, m5⟩ := vMom_apply p L
  have m1' : vMom p L (.inl vf1) = p - ℓ 1 := by rw [m1, h0]
  have m2' : vMom p L (.inl vf2) = ℓ 0 := by rw [m2, h1]
  have m3' : vMom p L (.inl vf3) = ℓ 0 + ℓ 1 := by rw [m3, h0, h1]; abel
  have m4' : vMom p L (.inr vg1) = ℓ 1 := by rw [m4, h0]; abel
  have m5' : vMom p L (.inr vg2) = -ℓ 1 := by rw [m5, h0]; abel
  rw [lineMomentum₂_repV, regulatedAmplitude₂_repV]
  simp only [v_amplitude, m1', m2', m3', m4', m5']
  unfold nestedF seVOuter vacuumPolarizationIntegrand
  simp only [Matrix.cons_val_zero]
  simp only [QED.TwoLoop.NestedVP.trace_rotate (electronPropagator _ P.ε (ℓ 0 + ℓ 1))]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => enter [2, a]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_rhs => enter [2, a, 2, b, 2, c]; rw [Finset.sum_comm]
  conv_rhs => enter [2, a]; rw [Finset.sum_comm]
  conv_rhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

/-- The outer factor is continuous in the photon energy, for `ε > 0`. -/
theorem continuous_seVOuter (P : Params) (hε : 0 < P.ε) (p : Fin 4 → ℝ) (α β : Fin 4)
    (w : Fin 3 → ℝ) (ρ σ : Fin 4) :
    Continuous fun t => seVOuter P p α β (Fin.cons t w) ρ σ := by
  have hk : Continuous fun t : ℝ => (Fin.cons t w : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_id continuous_const
  unfold seVOuter
  refine continuous_const.mul (continuous_finsetSum _ fun l0 _ =>
    continuous_finsetSum _ fun l1 _ => ?_)
  have hch : Continuous fun t => Dirac.gamma l1 *
      electronPropagator P.m P.ε (p - (Fin.cons t w : Fin 4 → ℝ)) * Dirac.gamma l0 :=
    (continuous_const.matrix_mul (QED.TwoLoop.NestedVPFubiniBound.continuous_electronPropagator
      P.m hε (continuous_const.sub hk))).matrix_mul continuous_const
  exact (((continuous_apply β).comp ((continuous_apply α).comp hch)).mul
    (QED.TwoLoop.NestedVPFubiniBound.continuous_photonPropagator P.mγ P.Λ hε hk l0 ρ)).mul
      (QED.TwoLoop.NestedVPFubiniBound.continuous_photonPropagator P.mγ P.Λ hε hk.neg l1 σ)

section MatrixNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **The outer factor decays like `(1 + |t|)⁻⁹`** (stated with the exponent `8`) in the photon
energy, at fixed `ε > 0`, external momentum and spatial photon momentum `w`. -/
theorem decaysLike_seVOuter (P : Params) (hε : 0 < P.ε) (p : Fin 4 → ℝ) (α β : Fin 4)
    (w : Fin 3 → ℝ) (ρ σ : Fin 4) :
    DecaysLike (fun t => seVOuter P p α β (Fin.cons t w) ρ σ) 8 := by
  have hS : DecaysLike (fun t => electronPropagator P.m P.ε
      (p - (Fin.cons t w : Fin 4 → ℝ))) 1 := by
    refine QED.TwoLoop.NestedVPFubiniBound.decaysLike_electronPropagator P.m hε _
      (abs_nonneg (p 0)) (by positivity : 0 ≤ ‖p‖ + ‖w‖) (fun t => ?_) (fun t i => ?_)
      (fun t => ?_)
    · simp only [Pi.sub_apply, Fin.cons_zero]
      have := abs_sub_abs_le_abs_sub t (p 0)
      rw [abs_sub_comm] at this
      linarith [abs_sub_comm (p 0) t]
    · simp
    · refine (norm_sub_le _ _).trans ?_
      have := QED.Integration.norm_finCons_le t w
      linarith
  have hk := QED.TwoLoop.NestedVPFubiniBound.decaysLike_photonPropagator P.mγ P.Λ hε
    (fun t => (Fin.cons t w : Fin 4 → ℝ)) (fun t => by simp) (fun t i => by simp)
  have hk' := QED.TwoLoop.NestedVPFubiniBound.decaysLike_photonPropagator P.mγ P.Λ hε
    (fun t => -(Fin.cons t w : Fin 4 → ℝ)) (fun t => by simp) (fun t i => by simp)
  have h := (DecaysLike.const (-(((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 2 *
      (1 / I) ^ 3)).mul
    (DecaysLike.sum Finset.univ fun l0 _ => DecaysLike.sum Finset.univ fun l1 _ =>
      (((((DecaysLike.const (Dirac.gamma l1)).mul hS).mul
        (DecaysLike.const (Dirac.gamma l0))).apply α β).mul (hk l0 ρ)).mul (hk' l1 σ))
  exact (h.congr fun t => rfl).mono (by norm_num)

end MatrixNorm

open QED.GradedProof.SE2 in
/-- **The class `V` at fixed `ε`, nested equals joint, the inner loop in closed form**: for
admissible parameters with `m < M₁`, `m < M₂`, the value of `repV` at the self-energy kinematics
`pOut = pIn = p` is the energy-first integral over the photon momentum of
`outerF P (seVOuter P p α β) k = ∑ ρ σ, seVOuter … k ρ σ · T^{ρσ}(k)`,
`T = i Π̂_ε(k²)(k² g - k k) + ε S_ε(k²) g`, and that integrand is integrable in both stages. -/
theorem contractionValue₂_repV_eq_outerF {P : Params} (hP : Adm P) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (p : Fin 4 → ℝ) (α β : Fin 4) :
    contractionValue₂ P repV ![p] ![p] ![] ![α] ![β] ![] =
        energyFirstIntegral (outerF P (seVOuter P p α β)) ∧
      EFInt (outerF P (seVOuter P p α β)) := by
  have hJ2 : QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P repV ![p] ![] (lineMomentum₂ repV ![p] ![p] ![] ℓ) ![α] ![β] ![] := by
    have hJ := classInt_repV P hP p α β
    have hL := loopCount_repV
    revert hJ
    generalize loopCount repV = L at hL ⊢
    subst hL
    exact id
  have hF := QED.TwoLoop.NestedVP.jointEnergyFirstIntegrable_comp_matrix_add 2 _
    QED.TwoLoop.NestedVP.unswapMat QED.TwoLoop.NestedVP.isUnit_det_unswapMat ![p, 0] hJ2
  simp only [repV_integrand_unswap] at hF
  have hv : contractionValue₂ P repV ![p] ![p] ![] ![α] ![β] ![] =
      QED.TwoLoop.jointEnergyFirstIntegral 2 (nestedF P (seVOuter P p α β)) := by
    rw [QED.TwoLoop.Relabel.contractionValue₂_eq_of_loopCount P loopCount_repV,
      ← QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2 _
        QED.TwoLoop.NestedVP.unswapMat QED.TwoLoop.NestedVP.isUnit_det_unswapMat ![p, 0]]
    simp only [repV_integrand_unswap]
  obtain ⟨h1, h2⟩ := jointEnergyFirstIntegral_nestedF_eight hP.hm hM₁ hM₂ hP.pv₁ hP.pv₂ hP.hε _
    (continuous_seVOuter P hP.hε p α β) (decaysLike_seVOuter P hP.hε p α β) hF
  exact ⟨hv.trans h1, h2⟩

end QED.ChainProof.SetCRegDisp

end
