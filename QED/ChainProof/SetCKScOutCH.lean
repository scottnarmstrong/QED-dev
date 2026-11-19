/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutCDom
public import QED.ChainProof.SetCKCornInDomInt

/-!
# Set (c), Stage K, group G4: the outer-massive corner Stieltjes identity (G4C)

Helper level (no frozen statement). The dominating function
`scOutCDom t Y y₃ x = 200 (1 + 1/t) (Y^(-2/3) + (1-Y)^(-1/2)) y₃^(-5/6) x^(-2/3)` is integrable
on the cube (**`integrable_scOutCDom`**: a product of one-variable powers with exponents
`> -1`), so the domination hypothesis of `SetCKScOutCFub` holds (**`scOutC_bound`**) and

**`scOutCH_isScOutCHDensity : IsScOutCHDensity scOutCH`**, i.e. for every `t > 0`

`C(0, t) = ∫₀¹ H_C(X) Q'(X)/(Q(X) + t)² dX`, `H_C = scOutCH`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

/-- `x ↦ 1/(x^(1/12))ⁿ = x^(-n/12)` is integrable on `(0, 1)` for `n < 12`. -/
theorem integrableOn_inv_root_pow {n : ℕ} (hn : n < 12) :
    IntegrableOn (fun x : ℝ => 1 / (x ^ ((1 : ℝ) / 12)) ^ n) (Ioo 0 1) := by
  have hn' : (n : ℝ) < 12 := by exact_mod_cast hn
  have h := (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2
    (by linarith : (-1 : ℝ) < -((n : ℝ) / 12))
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioo
  simp only
  rw [rpow_neg hx.1.le, ← rpow_natCast, ← rpow_mul hx.1.le, one_div]
  ring_nf

/-- **The dominating function is integrable on the cube.** -/
theorem integrable_scOutCDom (t : ℝ) :
    Integrable (fun p : ℝ × ℝ × ℝ => scOutCDom t p.1 p.2.1 p.2.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  have i8 : Integrable (fun x : ℝ => 1 / (x ^ ((1 : ℝ) / 12)) ^ 8) μ :=
    integrableOn_inv_root_pow (by norm_num)
  have i10 : Integrable (fun x : ℝ => 1 / (x ^ ((1 : ℝ) / 12)) ^ 10) μ :=
    integrableOn_inv_root_pow (by norm_num)
  have iS0 : Integrable (fun x : ℝ => (√(1 - x))⁻¹) μ :=
    cornIn_integrableOn_one_sub integrableOn_inv_sqrt_Ioo
  have iS : Integrable (fun x : ℝ => 1 / √(1 - x)) μ := by
    simpa only [one_div] using iS0
  have iY : Integrable (fun Y : ℝ => 1 / (Y ^ ((1 : ℝ) / 12)) ^ 8 + 1 / √(1 - Y)) μ := i8.add iS
  have h := (iY.mul_prod (i10.mul_prod i8)).const_mul (200 * (1 + 1 / t))
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp only [scOutCDom]
  ring

/-- **The domination hypothesis of G4C holds.** -/
theorem scOutC_bound {t : ℝ} (ht : 0 < t) : ScOutCBound t := by
  refine ⟨fun p => scOutCDom t p.1 p.2.1 p.2.2, integrable_scOutCDom t, ?_⟩
  filter_upwards [ae_mem_cube, ae_scOutC_mass_ne t] with p hp hM
  refine ⟨?_, fun h => scOutC_abs_integral_le_dom ht hp.1 ⟨hp.2.1.1, h⟩ hp.2.2 hM⟩
  have h1 : 0 < √(1 - p.1) := sqrt_pos.2 (by linarith [hp.1.2])
  have h2 := rpow_pos_of_pos hp.1.1 ((1 : ℝ) / 12)
  have h3 := rpow_pos_of_pos hp.2.1.1 ((1 : ℝ) / 12)
  have h4 := rpow_pos_of_pos hp.2.2.1 ((1 : ℝ) / 12)
  unfold scOutCDom
  positivity

/-- **The G4C Stieltjes identity** (`Q`-derivative form), unconditionally. -/
theorem scOutCH_isScOutCHDensity : IsScOutCHDensity scOutCH :=
  scOutCH_isScOutCHDensity_of_bound fun _ ht => scOutC_bound ht

end QED.ChainProof.SetCK

end
