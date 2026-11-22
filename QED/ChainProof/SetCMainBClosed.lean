/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBFub
public import QED.ChainProof.HCSideBDNestedGen

/-!
# Set (c), the bubble classes: the bubble in closed form inside a two-loop outer factor

Helper level for set (c), the bubble classes `QED.ChainProof.SetCLink.repB i`, at fixed
`ε > 0`. In a routing with the bubble momentum `ℓ 0 = q` innermost, the three-loop integrand of a
bubble on a photon line of a two-loop skeleton has the form

`nestB P O K ℓ = ∑_{ρ σ} O(ℓ')^{ρσ} Π^{ρσ}_ε(K(ℓ'), q)`,   `ℓ' = (ℓ 1, ℓ 2)`,

with `Π` the one-loop vacuum polarization integrand of (62.12) (the Pauli–Villars flavours of `P`
summed), `K(ℓ')` the photon momentum through the bubble and `O` the outer factor (open line, the
other photon lines, the two photon propagators of momentum `K`, constants). This file inserts
the closed form of the bubble and proves the Fubini condition of
`QED.ChainProof.SetCMainB.jointEnergyFirstIntegral_three_eq_inner` from a decay bound on the
outer factor:

* `nestB`, `outerBub` (the outer integrand `∑ O(ℓ') T(K(ℓ'))` with
  `T = i Π̂_ε(k²)(k² g - k k) + ε S_ε(k²) g`, `QED.ChainProof.HCSide.outerF`);
* `bubbleJ_nestB`: the energy-first integral of the bubble is `outerBub`
  (`QED.TwoLoop.VPHalfAt.energyFirstIntegral_vacuumPolarizationIntegrand_eq`);
* `bubbleT_nestB`: the energy integral of the bubble at fixed spatial momenta is
  `∑ O(ℓ') G(K(ℓ'), w)`, `G = QED.WickModel.VacuumPolarizationLimit.spatialG`;
* `OuterDecay`: at every outer spatial momentum, each entry of `O`, times
  `(1 + ‖K‖)^{17/2}`, is dominated by an integrable function of the outer energies;
* **`integrable_bubbleT_nestB`**: the Fubini condition `hK`, at every outer spatial momentum,
  from continuity and `OuterDecay` (the bound
  `‖G(k, w)‖ ≤ C (1 + ‖k‖)^{17/2} (1 + ‖w‖)^{-7/2}`,
  `QED.TwoLoop.NestedVPFubiniBound.exists_norm_spatialG_le_poly`);
* **`jointEnergyFirstIntegral_nestB`**: given both stages of (T₉) at three loops, the value is
  the joint energy-first integral at two loops of `outerBub`, and `outerBub` is integrable in both
  stages.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.ChainProof.SetCMainB

open QED.WickModel QED.WickModel.VacuumPolarizationLimit QED.OneLoop
open QED.TwoLoop.NestedVPFubiniBound (exists_norm_spatialG_le_poly continuous_timeSum_joint)
open QED.ChainProof.HCSide (nestedF outerF)

/-- The three-loop integrand with the bubble at `ℓ 0`, outer factor `O` and photon momentum
`K` through the bubble. -/
noncomputable def nestB (P : Params) (O : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ) (ℓ : Fin 3 → Fin 4 → ℝ) : ℂ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, O (Fin.tail ℓ) ρ σ *
    vacuumPolarizationIntegrand P P.ε (K (Fin.tail ℓ)) (ℓ 0) ρ σ

/-- The outer integrand with the bubble in closed form. -/
noncomputable def outerBub (P : Params) (O : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ) (ℓ' : Fin 2 → Fin 4 → ℝ) : ℂ :=
  outerF P (fun _ => O ℓ') (K ℓ')

theorem nestB_cons (P : Params) (O : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ) (q : Fin 4 → ℝ) (ℓ' : Fin 2 → Fin 4 → ℝ) :
    nestB P O K (Fin.cons q ℓ') = nestedF P (fun _ => O ℓ') ![q, K ℓ'] := by
  simp only [nestB, nestedF, Fin.tail_cons, Fin.cons_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one]

variable {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
  (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
  (hε : 0 < P.ε)

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **The bubble in closed form**: its one-loop energy-first integral is `outerBub`. -/
theorem bubbleJ_nestB (O : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ) : bubbleJ (nestB P O K) = outerBub P O K := by
  funext ℓ'
  simp only [bubbleJ, nestB_cons]
  exact QED.ChainProof.HCSide.energyFirstIntegral_nestedF hm hM₁ hM₂ hPV₁ hPV₂ hε _ _

include hε in
/-- The energy integral of the bubble at fixed spatial momenta. -/
theorem bubbleT_nestB (O : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ) (t' : Fin 2 → ℝ) (v' : Fin 2 → Fin 3 → ℝ)
    (w : Fin 3 → ℝ) :
    bubbleT (nestB P O K) t' v' w =
      ∑ ρ : Fin 4, ∑ σ : Fin 4, O (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ *
        spatialG P P.ε (K fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ w := by
  simp only [bubbleT, nestB_cons]
  exact QED.ChainProof.HCSide.integral_nestedF_time hε _ _ w

/-- **The decay of the outer factor**: at every outer spatial momentum `v'`, each entry of `O`,
times `(1 + ‖K‖)^{17/2}`, is dominated by an integrable function of the outer energies. -/
def OuterDecay (O : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∀ (v' : Fin 2 → Fin 3 → ℝ) (ρ σ : Fin 4), ∃ h : (Fin 2 → ℝ) → ℝ, Integrable h ∧
    ∀ t' : Fin 2 → ℝ, ‖O (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ‖ *
      (1 + ‖K fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)‖) ^ (17 / 2 : ℝ) ≤ h t'

theorem continuous_consFam (v' : Fin 2 → Fin 3 → ℝ) :
    Continuous fun t' : Fin 2 → ℝ => (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) :=
  continuous_pi fun s => Continuous.finCons (A := fun _ : Fin 4 => ℝ) (continuous_apply s)
    continuous_const

include hε in
/-- Joint measurability of the bubble energy integral along a continuous photon momentum. -/
theorem aestronglyMeasurable_spatialG_comp {k : (Fin 2 → ℝ) → Fin 4 → ℝ} (hk : Continuous k)
    (ρ σ : Fin 4) : AEStronglyMeasurable
      (fun x : (Fin 2 → ℝ) × (Fin 3 → ℝ) => spatialG P P.ε (k x.1) ρ σ x.2) volume := by
  have hc : Continuous fun z : ((Fin 2 → ℝ) × (Fin 3 → ℝ)) × ℝ =>
      kappa P.e * timeSum P P.ε (k z.1.1) ρ σ z.2 z.1.2 := by
    have h2 : Continuous fun z : ((Fin 2 → ℝ) × (Fin 3 → ℝ)) × ℝ =>
        (k z.1.1, z.1.2, z.2) :=
      (hk.comp (continuous_fst.comp continuous_fst)).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    have h3 := (continuous_timeSum_joint hε P ρ σ).comp h2
    exact continuous_const.mul h3
  exact (hc.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).aestronglyMeasurable

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **The Fubini condition for `nestB`**, at every outer spatial momentum, from continuity of the
outer factor and of the photon momentum and the decay `OuterDecay`. -/
theorem integrable_bubbleT_nestB {O : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    {K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hO : ∀ ρ σ, Continuous fun ℓ' => O ℓ' ρ σ)
    (hK : Continuous K) (hd : OuterDecay O K) (v' : Fin 2 → Fin 3 → ℝ) :
    Integrable fun p : (Fin 2 → ℝ) × (Fin 3 → ℝ) => bubbleT (nestB P O K) p.1 v' p.2 := by
  simp only [bubbleT_nestB hε]
  refine integrable_finsetSum _ fun ρ _ => integrable_finsetSum _ fun σ _ => ?_
  obtain ⟨h, hh, hb⟩ := hd v' ρ σ
  obtain ⟨Ci, hCi0, hCi⟩ := exists_norm_spatialG_le_poly hm hM₁ hM₂ hPV₁ hPV₂ hε ρ σ
  have hint : Integrable (fun p : (Fin 2 → ℝ) × (Fin 3 → ℝ) =>
      Ci * (h p.1 * (1 + ‖p.2‖) ^ (-(7 / 2 : ℝ)))) :=
    (hh.mul_prod (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 7 / 2)
      (by simp; norm_num))).const_mul Ci
  have hc := continuous_consFam v'
  refine hint.mono' (((hO ρ σ).comp (hc.comp continuous_fst)).aestronglyMeasurable.mul
    (aestronglyMeasurable_spatialG_comp hε (hK.comp hc) ρ σ))
    (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨t', w⟩ := p
  simp only
  rw [norm_mul]
  set k := K fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)
  have h1 := hb t'
  have h2 := hCi k w
  have hO0 := norm_nonneg (O (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ)
  calc ‖O (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ‖ * ‖spatialG P P.ε k ρ σ w‖
      ≤ ‖O (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ‖ *
          (Ci * (1 + ‖k‖) ^ (17 / 2 : ℝ) * (1 + ‖w‖) ^ (-(7 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 hO0
    _ = Ci * ((‖O (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ‖ *
          (1 + ‖k‖) ^ (17 / 2 : ℝ)) * (1 + ‖w‖) ^ (-(7 / 2 : ℝ))) := by ring
    _ ≤ Ci * (h t' * (1 + ‖w‖) ^ (-(7 / 2 : ℝ))) := by gcongr

include hm hM₁ hM₂ hPV₁ hPV₂ hε in
/-- **Nested equals joint for a bubble in a two-loop outer factor, the bubble in closed form.**
Given both stages of (T₉) at three loops for `nestB`, continuity of the outer factor and of the
photon momentum and the decay `OuterDecay`, the value at three loops is the joint energy-first
integral at two loops of `outerBub`, which is integrable in both stages. -/
theorem jointEnergyFirstIntegral_nestB {O : (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    {K : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hO : ∀ ρ σ, Continuous fun ℓ' => O ℓ' ρ σ)
    (hK : Continuous K) (hd : OuterDecay O K)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3 (nestB P O K)) :
    QED.TwoLoop.jointEnergyFirstIntegral 3 (nestB P O K) =
        QED.TwoLoop.jointEnergyFirstIntegral 2 (outerBub P O K) ∧
      QED.TwoLoop.jointEnergyFirstIntegrable 2 (outerBub P O K) := by
  have hB := integrable_bubbleT_nestB hm hM₁ hM₂ hPV₁ hPV₂ hε hO hK hd
  rw [← bubbleJ_nestB hm hM₁ hM₂ hPV₁ hPV₂ hε]
  exact ⟨jointEnergyFirstIntegral_three_eq_inner _ hF (Filter.Eventually.of_forall hB),
    jointEnergyFirstIntegrable_inner _ hF hB⟩

end QED.ChainProof.SetCMainB

end
