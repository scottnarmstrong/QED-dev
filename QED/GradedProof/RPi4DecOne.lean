/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecDilQ

/-!
# (R-Π₄) step L9, D3c₁: the one-loop functional is dilation covariant

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
part D3c₁. The one-loop functional `decD₀ e 1 x s` (the `s`-subtracted projected limit of the
mass-derivative block of `decCfg 1 x` with unit weight) satisfies `DecDil`:

* `dec_fLim_cfg_comb`: at the tensor level, the block of the dilated configuration
  `decDil √Λ (decCfg 1 x)` is the combination `cfg(Λx) + (x - 2) cfg(Λ) + (1 - x) cfg(2Λ)` (the
  auxiliary points cancel; the weight is constant, so the counterterm flavour plays no role);
* the dilation itself is `dec_projS_fLim_dil` (D3a);
* **`dec_dil_decD₀ : DecDil (decD₀ P.e 1)`** for `P.e ≠ 0`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2

namespace QED.GradedProof.RPi4

/-- The configuration `decCfg 1 y` has a block of mass-derivative bubbles that is `VPF` with
the threshold `√(min 1 y)`. -/
theorem dec_cfg_vpf (P : Params) (he : P.e ≠ 0) {y : ℝ} (hy : 0 < y) :
    VPF (Real.sqrt (min 1 y) + Real.sqrt (min 1 y)) fun ε k q μ ν =>
      dBlockD (decCfg 1 y) (fun _ => 0) P.e (fun _ => 1) ε k q μ ν := by
  have hm : 0 < min 1 y := lt_min one_pos hy
  have hm₀ : 0 < Real.sqrt (min 1 y) := Real.sqrt_pos.2 hm
  have hpv := dec_cfg_pv (μ := 1) (x := y) one_ne_zero hy.le
  refine vpf_dBlockD (decCfg 1 y) (fun _ => 0) hm₀ (fun g => dec_cfg_mass_ge ?_ hm₀ ?_ g)
    (fun _ => rfl) hpv.1 hpv.2 P he _
  · calc Real.sqrt (min 1 y) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (min_le_left _ _)
      _ = 1 := Real.sqrt_one
  · rw [Real.sq_sqrt hm.le]
    exact min_le_right _ _

theorem dec_sq_sqrt_min {y : ℝ} (hy : 0 < y) :
    (Real.sqrt (min 1 y) + Real.sqrt (min 1 y)) ^ 2 = 4 * min 1 y := by
  rw [← two_mul, mul_pow, Real.sq_sqrt (lt_min one_pos hy).le]
  norm_num

/-- **The mass-derivative blocks of the configurations, combined.** -/
theorem dec_fLim_cfg_comb (P : Params) (he : P.e ≠ 0) {Λ x : ℝ} (hΛ : 0 < Λ) (hx : 0 < x)
    {k : Fin 4 → ℝ} (h1 : -(4 * min 1 (Λ * x)) < Minkowski.dot k k)
    (h2 : -(4 * min 1 Λ) < Minkowski.dot k k) (h3 : -(4 * min 1 (2 * Λ)) < Minkowski.dot k k)
    (μ ν : Fin 4) :
    fLim (decDil (Real.sqrt Λ) (decCfg 1 x)) (fun _ => 0) P.e (fun _ => 1) k μ ν =
      fLim (decCfg 1 (Λ * x)) (fun _ => 0) P.e (fun _ => 1) k μ ν +
        ((x - 2 : ℝ) : ℂ) * fLim (decCfg 1 Λ) (fun _ => 0) P.e (fun _ => 1) k μ ν +
        ((1 - x : ℝ) : ℂ) * fLim (decCfg 1 (2 * Λ)) (fun _ => 0) P.e (fun _ => 1) k μ ν := by
  have hΛx : 0 < Λ * x := mul_pos hΛ hx
  have h2Λ : 0 < 2 * Λ := by positivity
  have V1 := dec_cfg_vpf P he hΛx
  have V2 := dec_cfg_vpf P he hΛ
  have V3 := dec_cfg_vpf P he h2Λ
  have t1 := tendsto_limT_of_hasVPLim V1.hasVPLim (by rwa [dec_sq_sqrt_min hΛx]) μ ν
  have t2 := tendsto_limT_of_hasVPLim V2.hasVPLim (by rwa [dec_sq_sqrt_min hΛ]) μ ν
  have t3 := tendsto_limT_of_hasVPLim V3.hasVPLim (by rwa [dec_sq_sqrt_min h2Λ]) μ ν
  refine limT_eq (((t1.add (t2.const_mul ((x - 2 : ℝ) : ℂ))).add
    (t3.const_mul ((1 - x : ℝ) : ℂ))).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [← QED.OneLoop.energyFirstIntegral_const_mul, ← QED.OneLoop.energyFirstIntegral_const_mul,
    ← efi_add (V1.2 ε hε k μ ν) ((V2.2 ε hε k μ ν).const_mul _),
    ← efi_add ((V1.2 ε hε k μ ν).add ((V2.2 ε hε k μ ν).const_mul _))
      ((V3.2 ε hε k μ ν).const_mul _)]
  congr 1
  funext q
  have sx : Real.sqrt (Λ * x) = Real.sqrt Λ * Real.sqrt x := Real.sqrt_mul hΛ.le x
  have s2 : Real.sqrt (2 * Λ) = Real.sqrt 2 * Real.sqrt Λ := Real.sqrt_mul (by norm_num) Λ
  have sc : Real.sqrt Λ * Real.sqrt 2 = Real.sqrt 2 * Real.sqrt Λ := mul_comm _ _
  simp only [dBlockD, decDil, decCfg, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_one,
    one_mul, one_pow, div_one, sx, s2, sc]
  push_cast
  ring

/-- **(D3c₁) the one-loop functional is dilation covariant.** -/
theorem dec_dil_decD₀ (P : Params) (he : P.e ≠ 0) : DecDil (decD₀ P.e 1) := by
  intro Λ x s hΛ hx hs hΛs
  have hΛx : 0 < Λ * x := mul_pos hΛ hx
  set m := min 1 (min (Λ * x) Λ) with hm
  have hm0 : 0 < m := lt_min one_pos (lt_min hΛx hΛ)
  have hT : 0 < 4 * m := by positivity
  have le1 : m ≤ min 1 (Λ * x) := le_min (min_le_left _ _)
    ((min_le_right _ _).trans (min_le_left _ _))
  have le2 : m ≤ min 1 Λ := le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_right _ _))
  have le3 : m ≤ min 1 (2 * Λ) := le_min (min_le_left _ _)
    ((min_le_right _ _).trans ((min_le_right _ _).trans (by linarith)))
  -- the region contains `Λ s` and `0`
  have hsx : -(4 * x) < s := lt_of_le_of_lt (by nlinarith [min_le_right 1 x]) hs
  have hreg : -(4 * m) < Λ * s := by
    have : -(4 * (Λ * x)) < Λ * s := by nlinarith
    have h' : -(4 * min 1 Λ) < Λ * s := hΛs
    rcases min_choice 1 (min (Λ * x) Λ) with h | h <;> rw [hm, h]
    · have := min_le_left 1 Λ; linarith
    · rcases min_choice (Λ * x) Λ with h'' | h'' <;> rw [h''] <;> nlinarith [min_le_right 1 Λ]
  have hreg0 : -(4 * m) < 0 := by linarith
  -- the tensor identity on the region, projected
  have comb : ∀ t : ℝ, -(4 * m) < t →
      projS (fLim (decDil (Real.sqrt Λ) (decCfg 1 x)) (fun _ => 0) P.e (fun _ => 1)) t =
        ((x - 2 : ℝ) : ℂ) * projS (fLim (decCfg 1 Λ) (fun _ => 0) P.e (fun _ => 1)) t +
          (((1 - x : ℝ) : ℂ) * projS (fLim (decCfg 1 (2 * Λ)) (fun _ => 0) P.e (fun _ => 1)) t +
            projS (fLim (decCfg 1 (Λ * x)) (fun _ => 0) P.e (fun _ => 1)) t) := by
    intro t ht
    rw [dec_projS_lin hT ((x - 2 : ℝ) : ℂ)
      (Y := fLim (decCfg 1 Λ) (fun _ => 0) P.e (fun _ => 1)) (Z := fun k μ ν =>
        ((1 - x : ℝ) : ℂ) * fLim (decCfg 1 (2 * Λ)) (fun _ => 0) P.e (fun _ => 1) k μ ν +
          fLim (decCfg 1 (Λ * x)) (fun _ => 0) P.e (fun _ => 1) k μ ν) (fun k hk μ ν => by
        rw [dec_fLim_cfg_comb P he hΛ hx (by nlinarith) (by nlinarith) (by nlinarith)]
        ring) ht,
      dec_projS_lin hT ((1 - x : ℝ) : ℂ) (fun k _ μ ν => rfl) ht]
  -- the dilation
  have hl : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ
  have hsq : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hΛ.le
  have hx1 : 0 < min 1 x := lt_min one_pos hx
  have dil : ∀ t : ℝ, -(4 * min 1 x) < t →
      projS (fLim (decDil (Real.sqrt Λ) (decCfg 1 x)) (fun _ => 0) P.e (fun _ => 1)) (Λ * t) =
        projS (fLim (decCfg 1 x) (fun _ => 0) P.e (fun _ => 1)) t := by
    intro t ht
    have h := dec_projS_fLim_dil (decCfg 1 x) (fun _ => 0) P.e (fun _ => 1)
      (dec_cfg_vpf P he hx) (by positivity) hl (s := t) (by rwa [dec_sq_sqrt_min hx])
    rwa [hsq] at h
  have c1 := comb _ hreg
  have c0 := comb _ hreg0
  have d1 := dil s hs
  have d0 := dil 0 (by linarith)
  rw [mul_zero] at d0
  rw [d1] at c1
  rw [d0] at c0
  simp only [decD₀]
  linear_combination (-I / (P.e : ℂ) ^ 2) * c1 + (I / (P.e : ℂ) ^ 2) * c0

end QED.GradedProof.RPi4

end
