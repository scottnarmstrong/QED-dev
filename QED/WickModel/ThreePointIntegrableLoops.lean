/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointClassification
import QED.WickModel.Compatibility
import QED.Wick.ChainValue
import QED.Wick.ClassificationGauge3
import QED.OneLoop.VertexOffShellIntegrable
import QED.WickModel.SelfEnergyExistsUnique
import QED.WickModel.VacuumPolarizationEnergyFirst

/-!
# Integrability of the one-loop contractions of the three-point function

For the connected contractions of three gauge vertices with one external fermion pair and one
external photon (packet 6a, decision D-24), with outgoing momentum `p'`, incoming momentum `p`
and photon momentum `p' - p`, the loop integrand (the regulated amplitude) is integrable in both
stages of the energy-first prescription M1 at every `ε > 0`:

* the vertex correction (the 1PI contractions): `(2π)⁻⁴` times the integrand is the one-loop
  vertex integrand at a shifted loop momentum (`QED.Wick.IsChain.integrand_eq`), integrable for
  all momenta (`QED.OneLoop.VertexOffShell.integrable_energyFirst_of_pos`);
* the self-energy loops on the electron legs: a leg factor times the self-energy integrand at a
  shifted loop momentum (`SelfEnergyLimit.integrable_selfEnergyIntegrand_sub`);
* the vacuum polarization loop on the photon leg: a leg factor times the vacuum polarization
  integrand, possibly at a shifted loop momentum; this uses the Pauli–Villars conditions.

Both stages of M1 are invariant under a translation of the loop momentum
(`IntegrableEnergyFirst.comp_sub`).

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.WickModel

open Wick (gauge3)

/-! ### Translations and multiples -/

/-- **Integrability in both stages is invariant under a translation** `ℓ ↦ ℓ - c` of the loop
momentum. -/
theorem IntegrableEnergyFirst.comp_sub {F : (Fin 4 → ℝ) → ℂ} (hF : IntegrableEnergyFirst F)
    (c : Fin 4 → ℝ) : IntegrableEnergyFirst fun ℓ => F (ℓ - c) := by
  have h : ∀ (t : ℝ) (v : Fin 3 → ℝ),
      (Fin.cons t v : Fin 4 → ℝ) - c = Fin.cons (t - c 0) (v - Fin.tail c) := fun t v => by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]
  refine ⟨fun v => ?_, ?_⟩
  · simp only [h]
    exact (hF.1 (v - Fin.tail c)).comp_sub_right (c 0)
  · have h2 : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, F (Fin.cons (t - c 0) (v - Fin.tail c)) =
        ∫ t : ℝ, F (Fin.cons t (v - Fin.tail c)) := fun v =>
      integral_sub_right_eq_self (fun t : ℝ => F (Fin.cons t (v - Fin.tail c))) (c 0)
    simp only [h, h2]
    exact hF.2.comp_sub_right (Fin.tail c)

/-- Integrability in both stages, from that of a nonzero multiple. -/
theorem IntegrableEnergyFirst.of_mul {F G : (Fin 4 → ℝ) → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hG : IntegrableEnergyFirst G) (h : ∀ ℓ, c * F ℓ = G ℓ) : IntegrableEnergyFirst F := by
  have hF : F = fun ℓ => c⁻¹ * G ℓ := funext fun ℓ => by rw [← h ℓ, inv_mul_cancel_left₀ hc]
  rw [hF]
  exact hG.const_mul _

/-- The loop measure `(2π)⁻⁴` is nonzero. -/
theorem loopMeasure_ne_zero : (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ ≠ 0 :=
  inv_ne_zero (ofReal_ne_zero.mpr (by positivity))

/-! ### Self-energy loops -/

variable {C : Contraction 1 1 gauge3}

namespace IsSEin

variable {a b c : Fin 3}

/-- The integrand of an incoming-leg self-energy loop, times `(2π)⁻⁴`: the leg factor times the
self-energy integrand at `ℓ - p`. -/
theorem inv_mul_regulatedAmplitude_eq (P : Params) (hC : IsSEin C a b c) (p' p ℓ : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P C ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] =
      ∑ γ, ((I * P.e) • Dirac.gamma μ *
        ((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p)) α γ *
          selfEnergyIntegrand P P.ε p (ℓ - p) γ β := by
  rw [regulatedAmplitude_eq_of_forall_preserves P (fun φ hφ => hC.chain.eq_electronFlavoring hφ),
    hC.contractionAmplitude_eq]
  simp only [selfEnergyIntegrand, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    add_sub_cancel, sum_photonPropagator_swap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **The integrand of an incoming-leg self-energy loop is integrable in both stages** at
`ε > 0`. -/
theorem integrableEnergyFirst (P : Params) (hε : 0 < P.ε) (hC : IsSEin C a b c)
    (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    IntegrableEnergyFirst fun ℓ =>
      regulatedAmplitude P C ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] := by
  refine IntegrableEnergyFirst.of_mul loopMeasure_ne_zero ?_
    (fun ℓ => hC.inv_mul_regulatedAmplitude_eq P p' p ℓ α β μ)
  exact IntegrableEnergyFirst.finsetSum _ fun γ _ =>
    (show IntegrableEnergyFirst fun ℓ => selfEnergyIntegrand P P.ε p (ℓ - p) γ β from
      SelfEnergyLimit.integrable_selfEnergyIntegrand_sub hε P p p γ β).const_mul _

end IsSEin

namespace IsSEout

variable {a b c : Fin 3}

/-- The integrand of an outgoing-leg self-energy loop, times `(2π)⁻⁴`: the self-energy integrand
at `ℓ - p'` times the leg factor. -/
theorem inv_mul_regulatedAmplitude_eq (P : Params) (hC : IsSEout C a b c) (p' p ℓ : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P C ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] =
      ∑ γ, selfEnergyIntegrand P P.ε p' (ℓ - p') α γ *
        (((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p') *
          (I * P.e) • Dirac.gamma μ) γ β := by
  rw [regulatedAmplitude_eq_of_forall_preserves P (fun φ hφ => hC.chain.eq_electronFlavoring hφ),
    hC.contractionAmplitude_eq]
  simp only [selfEnergyIntegrand, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    add_sub_cancel, sum_photonPropagator_swap, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **The integrand of an outgoing-leg self-energy loop is integrable in both stages** at
`ε > 0`. -/
theorem integrableEnergyFirst (P : Params) (hε : 0 < P.ε) (hC : IsSEout C a b c)
    (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    IntegrableEnergyFirst fun ℓ =>
      regulatedAmplitude P C ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] := by
  refine IntegrableEnergyFirst.of_mul loopMeasure_ne_zero ?_
    (fun ℓ => hC.inv_mul_regulatedAmplitude_eq P p' p ℓ α β μ)
  exact IntegrableEnergyFirst.finsetSum _ fun γ _ =>
    (show IntegrableEnergyFirst fun ℓ => selfEnergyIntegrand P P.ε p' (ℓ - p') α γ from
      SelfEnergyLimit.integrable_selfEnergyIntegrand_sub hε P p' p' α γ).mul_const _

end IsSEout

/-! ### Vacuum polarization loops -/

namespace IsVP

variable {a v w : Fin 3}

/-- The integrand of a vacuum polarization loop for `v < w`, times `-(2π)⁻⁴`: the leg factor
times the vacuum polarization integrand. -/
theorem neg_inv_mul_regulatedAmplitude_eq_of_lt (P : Params) (hC : IsVP C a v w) (h : v < w)
    (p' p ℓ : Fin 4 → ℝ) (α β μ : Fin 4) :
    -1 * ((((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P C ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ]) =
      ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ) *
          vacuumPolarizationIntegrand P P.ε (p' - p) ℓ μ ρ := by
  have hl := hC.isLoopLine_lineV h
  obtain ⟨hW, hP⟩ := hC.lineMomentum_of_lt h p' p ℓ
  simp only [hC.regulatedAmplitude_eq,
    hC.contractionAmplitude_eq P (hC.preserves_vpFlavoring _)
      (lineMomentum_of_isLoopLine hl _ _ _ _) hW hP, hC.vpFlavoring_v,
    vacuumPolarizationIntegrand, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun f _ => ?_
  rw [trace_rotate (QED.OneLoop.electronPropagator _ _ (ℓ + (p' - p))), add_comm ℓ]
  ring

/-- The integrand of a vacuum polarization loop for `w < v`, times `-(2π)⁻⁴`: the leg factor
times the vacuum polarization integrand at `ℓ - (p' - p)`. -/
theorem neg_inv_mul_regulatedAmplitude_eq_of_gt (P : Params) (hC : IsVP C a v w) (h : w < v)
    (p' p ℓ : Fin 4 → ℝ) (α β μ : Fin 4) :
    -1 * ((((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude P C ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ]) =
      ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
        ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ) *
          vacuumPolarizationIntegrand P P.ε (p' - p) (ℓ - (p' - p)) μ ρ := by
  have hl := hC.isLoopLine_lineW h
  obtain ⟨hV, hP⟩ := hC.lineMomentum_of_gt h p' p ℓ
  simp only [hC.regulatedAmplitude_eq,
    hC.contractionAmplitude_eq P (hC.preserves_vpFlavoring _) hV
      (lineMomentum_of_isLoopLine hl _ _ _ _) hP, hC.vpFlavoring_v,
    vacuumPolarizationIntegrand, Finset.mul_sum, sub_add_cancel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun f _ => ?_
  rw [trace_rotate (QED.OneLoop.electronPropagator _ _ ℓ)]
  ring

/-- **The integrand of a vacuum polarization loop is integrable in both stages** at `ε > 0`,
for regulator fermions heavier than the electron and the Pauli–Villars conditions. -/
theorem integrableEnergyFirst {P : Params} (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hε : 0 < P.ε) (hC : IsVP C a v w) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    IntegrableEnergyFirst fun ℓ =>
      regulatedAmplitude P C ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] := by
  have hVP : ∀ ρ, IntegrableEnergyFirst fun ℓ =>
      vacuumPolarizationIntegrand P P.ε (p' - p) ℓ μ ρ := fun ρ =>
    ⟨fun v => VacuumPolarizationLimit.integrable_vacuumPolarizationIntegrand_time hε P
      (p' - p) μ ρ v, VacuumPolarizationLimit.integrable_integral_vacuumPolarizationIntegrand hm
      hM₁ hM₂ hPV₁ hPV₂ hε (p' - p) μ ρ⟩
  have hc : (-1 : ℂ) * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ ≠ 0 :=
    mul_ne_zero (by norm_num) loopMeasure_ne_zero
  rcases lt_or_gt_of_ne hC.hvw with h | h
  · refine IntegrableEnergyFirst.of_mul hc ?_ (fun ℓ => (mul_assoc _ _ _).trans
      (hC.neg_inv_mul_regulatedAmplitude_eq_of_lt P h p' p ℓ α β μ))
    exact IntegrableEnergyFirst.finsetSum _ fun ν _ => IntegrableEnergyFirst.finsetSum _
      fun ρ _ => (hVP ρ).const_mul _
  · refine IntegrableEnergyFirst.of_mul hc ?_ (fun ℓ => (mul_assoc _ _ _).trans
      (hC.neg_inv_mul_regulatedAmplitude_eq_of_gt P h p' p ℓ α β μ))
    exact IntegrableEnergyFirst.finsetSum _ fun ν _ => IntegrableEnergyFirst.finsetSum _
      fun ρ _ => ((hVP ρ).comp_sub (p' - p)).const_mul _

end IsVP

/-! ### The vertex correction -/

/-- A one-entry vector is constant. -/
theorem vecCons_one_eq {X : Type*} (x : X) : (![x] : Fin 1 → X) = fun _ => x :=
  funext fun i => by fin_cases i; rfl

/-- **The integrand of a 1PI contraction of three gauge vertices is integrable in both stages**
at `ε > 0`, for all momenta: it is a vertex correction, and `(2π)⁻⁴` times its integrand is the
one-loop vertex integrand at a shifted loop momentum. -/
theorem integrableEnergyFirst_of_isOnePI (P : Params) (hε : 0 < P.ε) (hC : IsOnePI C)
    (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    IntegrableEnergyFirst fun ℓ =>
      regulatedAmplitude P C ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] := by
  obtain ⟨C₀, rfl⟩ := (contractionEquiv gauge3).surjective C
  have h1 : Wick.IsOnePI C₀ := isOnePI_contractionEquiv_iff.mp hC
  obtain ⟨a, b, c, hch⟩ := h1.exists_isChain
  have hV : IntegrableEnergyFirst fun ℓ =>
      QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε p' p μ ℓ α β :=
    QED.OneLoop.VertexOffShell.integrable_energyFirst_of_pos hε P.e P.m P.mγ P.Λ p' p μ α β
  refine IntegrableEnergyFirst.of_mul loopMeasure_ne_zero (hV.comp_sub (if a < b then p' else p))
    (fun ℓ => ?_)
  rw [vecCons_one_eq p', vecCons_one_eq p, vecCons_one_eq (p' - p), vecCons_one_eq α,
    vecCons_one_eq β, vecCons_one_eq μ,
    regulatedAmplitude_eq_of_forall_preserves P
      (fun φ hφ => eq_electronFlavoring_of_preserves (by decide) h1 hφ),
    contractionAmplitude_contractionEquiv P h1, hch.integrand_eq]

end QED.WickModel

end
