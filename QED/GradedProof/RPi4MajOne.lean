/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajScalG
public import QED.GradedProof.RPi4FVBlock

/-!
# (R-Π₄) step L10, one loop: `MajGrowD` from bounds on single flavours

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, input
`MajGrowD`. The one-loop functional `D₁(4, ·) = decD₀ e 1 4` is, up to the factor `I / e²`, the
`s`-subtracted projection of `fLim (decCfg 1 4)`. On the region this limit is `fbVal`
(`fLim_eq_fbVal`), a finite sum over the flavours of `insVal` (the inserted bubble written as ten
parametric pieces). The projection is linear, so the bounds of `MajGrowD` follow from the same
bounds for each flavour's `insVal`. The Pauli–Villars sum is not used. Numerics
(scratchpad `r31maj/pieces_ray.py`) show each of the ten pieces bounded along the ray, with
projection decaying like `s⁻²`.

* `MajSRay g`: `‖g t - g 0‖ ≤ A` for `t ≥ 0` and `‖g t - g t'‖ ≤ A (t - t')/t'` for
  `0 < t' ≤ t`; closed under affine maps and finite sums;
* `maj_growD_of_sRay`: `MajSRay (decD₀ e 1 4) → MajGrowD e`;
* `maj_projS_congr`, `maj_projS_sum`: the projection respects equality on the region and finite
  linear combinations;
* `MajOneIns e`: `MajSRay` of the projected `insVal` of each flavour of `decCfg 1 4` (auxiliary
  line mass `1`, pure mass insertion);
* **`maj_growD_of_ins`**: `MajOneIns → MajGrowD`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2
open QED.GradedProof.SE2 (canonVec dot_canonVec nullVec dot_nullVec)

/-! ### Bounded and scale-Lipschitz on the ray -/

/-- **Bounded and scale-Lipschitz for `t ≥ 0`**, after subtraction of the value at `0`. -/
def MajSRay (g : ℝ → ℂ) : Prop :=
  ∃ A : ℝ, ∀ t : ℝ, 0 ≤ t → ‖g t - g 0‖ ≤ A ∧
    ∀ t' : ℝ, 0 < t' → t' ≤ t → ‖g t - g t'‖ ≤ A * ((t - t') / t')

namespace MajSRay

theorem zero : MajSRay fun _ => 0 :=
  ⟨0, fun t _ => ⟨by simp, fun t' _ _ => by simp⟩⟩

theorem add {g h : ℝ → ℂ} (hg : MajSRay g) (hh : MajSRay h) : MajSRay fun t => g t + h t := by
  obtain ⟨A, hA⟩ := hg
  obtain ⟨B, hB⟩ := hh
  refine ⟨A + B, fun t ht => ⟨?_, fun t' ht' htt => ?_⟩⟩
  · calc _ = ‖(g t - g 0) + (h t - h 0)‖ := by ring_nf
      _ ≤ ‖g t - g 0‖ + ‖h t - h 0‖ := norm_add_le _ _
      _ ≤ A + B := add_le_add (hA t ht).1 (hB t ht).1
  · calc _ = ‖(g t - g t') + (h t - h t')‖ := by ring_nf
      _ ≤ ‖g t - g t'‖ + ‖h t - h t'‖ := norm_add_le _ _
      _ ≤ A * ((t - t') / t') + B * ((t - t') / t') :=
          add_le_add ((hA t ht).2 t' ht' htt) ((hB t ht).2 t' ht' htt)
      _ = _ := by ring

/-- Affine images: `t ↦ c (g t - b)`. -/
theorem affine {g : ℝ → ℂ} (hg : MajSRay g) (c b : ℂ) : MajSRay fun t => c * (g t - b) := by
  obtain ⟨A, hA⟩ := hg
  refine ⟨‖c‖ * A, fun t ht => ⟨?_, fun t' ht' htt => ?_⟩⟩
  · calc _ = ‖c * (g t - g 0)‖ := by ring_nf
      _ = ‖c‖ * ‖g t - g 0‖ := norm_mul _ _
      _ ≤ ‖c‖ * A := mul_le_mul_of_nonneg_left (hA t ht).1 (norm_nonneg c)
  · calc _ = ‖c * (g t - g t')‖ := by ring_nf
      _ = ‖c‖ * ‖g t - g t'‖ := norm_mul _ _
      _ ≤ ‖c‖ * (A * ((t - t') / t')) :=
          mul_le_mul_of_nonneg_left ((hA t ht).2 t' ht' htt) (norm_nonneg c)
      _ = _ := by ring

theorem const_mul {g : ℝ → ℂ} (hg : MajSRay g) (c : ℂ) : MajSRay fun t => c * g t := by
  simpa using hg.affine c 0

theorem sum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℂ} (hg : ∀ i ∈ s, MajSRay (g i)) :
    MajSRay fun t => ∑ i ∈ s, g i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem congr {g h : ℝ → ℂ} (hg : MajSRay g) (e : ∀ t, 0 ≤ t → g t = h t) : MajSRay h := by
  obtain ⟨A, hA⟩ := hg
  refine ⟨A, fun t ht => ⟨?_, fun t' ht' htt => ?_⟩⟩
  · rw [← e t ht, ← e 0 le_rfl]
    exact (hA t ht).1
  · rw [← e t ht, ← e t' ht'.le]
    exact (hA t ht).2 t' ht' htt

end MajSRay

/-- **`MajGrowD` from `MajSRay`** (the value at `0` vanishes). -/
theorem maj_growD_of_sRay {e : ℝ} (h : MajSRay (decD₀ e 1 4)) : MajGrowD e := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun t ht => ⟨?_, (hA t ht).2⟩⟩
  simpa [decD₀_zero] using (hA t ht).1

/-! ### The projection: congruence on the region and linearity -/

/-- The projection reads its tensor only on the region `k² > -T`. -/
theorem maj_projS_congr {X Y : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} {T : ℝ}
    (h : ∀ k : Fin 4 → ℝ, -T < Minkowski.dot k k → ∀ μ ν, X k μ ν = Y k μ ν)
    {s : ℝ} (hT : 0 < T) (hs : -T < s) : projS X s = projS Y s := by
  unfold projS
  split_ifs with h0
  · simp only [nProj, h nullVec (by rw [dot_nullVec]; linarith) 0 1]
  · rw [show X (canonVec s) = Y (canonVec s) from
      funext fun μ => funext fun ν => h (canonVec s) (by rwa [dot_canonVec]) μ ν]

/-- The projection of a finite linear combination. -/
theorem maj_projS_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (X : ι → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (t : ℝ) :
    projS (fun k μ ν => ∑ i ∈ s, c i * X i k μ ν) t = ∑ i ∈ s, c i * projS (X i) t := by
  unfold projS
  split_ifs
  · show -(∑ i ∈ s, c i * X i nullVec 0 1) = ∑ i ∈ s, c i * -X i nullVec 0 1
    simp [mul_neg]
  · simp only [trProj, Finset.mul_sum]
    rw [Finset.sum_comm (s := s) (t := (Finset.univ : Finset (Fin 4)))]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_comm (s := s) (t := (Finset.univ : Finset (Fin 4)))]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun i _ => by ring

/-! ### The reduction to single flavours -/

/-- **(L10 input, one loop, per flavour)** the projected inserted bubble of each flavour of
`decCfg 1 4` (auxiliary line mass `1`, pure mass insertion `d₂ = 0`, any `d_m`, both index
orders and both momentum routings) is bounded and scale-Lipschitz along `s ≥ 0`. -/
def MajOneIns : Prop :=
  ∀ (sw bx bY : Bool) (dm : ℝ) (f : Fin 3),
    MajSRay (projS (insVal 1 sw 0 dm bx bY ((decCfg 1 4).mass f) (auxX (decCfg 1 4))
      (auxX (decCfg 1 4) + 1)))

/-- **(L10) `MajGrowD` from the single-flavour bounds**: no Pauli–Villars cancellation is
used. -/
theorem maj_growD_of_ins (P : Params) (he : P.e ≠ 0) (h : MajOneIns) : MajGrowD P.e := by
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  set Φ := decCfg 1 4 with hΦ
  set D := ctδ (ctOf P.e fun _ : Fin 3 => (1 : ℝ)) with hD
  -- the per-flavour bubble of one index order and routing
  set ins : Bool → Bool → Bool → Fin 3 → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
    fun sw bx bY f => insVal 1 sw (P.e ^ 2 * D.d₂ ((fun _ => 0) f) 0)
      (P.e ^ 2 * D.dm ((fun _ => 0) f) 0) bx bY (Φ.mass f) (auxX Φ) (auxX Φ + 1) with hins
  have hfb : ∀ sw bx bY, MajSRay (projS fun k μ ν => fbVal P Φ D (fun _ => 0) 1 sw bx bY k μ ν) :=
    by
    intro sw bx bY
    have e : (fun k μ ν => fbVal P Φ D (fun _ => 0) 1 sw bx bY k μ ν) =
        fun k μ ν => ∑ f, ((Φ.coeff f : ℂ) * kF P.e) * ins sw bx bY f k μ ν := rfl
    rw [e]
    refine (MajSRay.sum Finset.univ fun f _ => (?_ : MajSRay _).const_mul
      ((Φ.coeff f : ℂ) * kF P.e)).congr fun t _ => (maj_projS_sum _ _ _ t).symm
    refine (h sw bx bY (P.e ^ 2 * D.dm 0 0) f).congr fun t _ => ?_
    simp [hins, hD, ctδ, hΦ]
  have hreg : ∀ k : Fin 4 → ℝ, -(4 : ℝ) < Minkowski.dot k k → ∀ μ ν,
      fLim Φ (fun _ => 0) P.e (fun _ => 1) k μ ν =
        fbVal P Φ D (fun _ => 0) 1 true true false k μ ν +
          fbVal P Φ D (fun _ => 0) 1 false false true k μ ν := fun k hk μ ν =>
    fLim_eq_fbVal P Φ (fun _ => 0) one_pos hmass hrep hpv.1 hpv.2 he _ (by linarith) μ ν
  have hg : MajSRay (projS (fLim Φ (fun _ => 0) P.e fun _ => 1)) := by
    refine ((hfb true true false).add (hfb false false true)).congr fun t ht => ?_
    rw [maj_projS_congr hreg (by norm_num : (0 : ℝ) < 4) (by linarith)]
    exact (projS_add (X := fun k μ ν => fbVal P Φ D (fun _ => 0) 1 true true false k μ ν +
      fbVal P Φ D (fun _ => 0) 1 false false true k μ ν)
      (Y := fun k μ ν => fbVal P Φ D (fun _ => 0) 1 true true false k μ ν)
      (Z := fun k μ ν => fbVal P Φ D (fun _ => 0) 1 false false true k μ ν) one_pos
      (fun _ _ _ _ => rfl) (by linarith : (-1 : ℝ) < t)).symm
  refine maj_growD_of_sRay ((hg.affine (I / (P.e : ℂ) ^ 2)
    (projS (fLim Φ (fun _ => 0) P.e fun _ => 1) 0)).congr fun t _ => ?_)
  simp only [decD₀, hΦ]
  ring

end QED.GradedProof.RPi4

end
