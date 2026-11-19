/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCornInKt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G2: the per-node identity of the corner unit

Helper level (no frozen statement). With `M = M_t(Y)` and the node weight
`G(y₃, x) = ∫₀^∞ K_tot(w)/(M + w) dw` (`cornInGn`), the `x`-integral of the unit integrand is
(`cornIn_x_level`, by `cornerGm_add_log_eq`, `cornInKt_integral` and `integral_cornInDel`)

`∫₀¹ cornerGm 0 (√t) y₃ (Y-y₃) x dx = ∫₀¹ G(y₃, x) dx - (log M)/4`,

and the `Y`-integrand of `C(t, 0)` is (**`cornInIntegrand_eq`**)

`cornInIntegrand t Y = e₁M/M + ∫∫_{(0,1)²} 1{y₃ < Y} G(y₃, x) dy₃ dx`,  `e₁M = -Y(Y² + 2Y - 2)/4`,

whenever `1{y₃ < Y} G` is integrable on the square (this hypothesis is discharged by the bounds
of the Fubini step). The counterterm's `log M` cancels the `-(log M)/4` exactly.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The node weight** `G(Y, y₃, x) = ∫₀^∞ K_tot(w)/(M_t(Y) + w) dw`. -/
noncomputable def cornInGn (t Y y3 x : ℝ) : ℝ :=
  ∫ w in Ioi 0, cornInKt Y y3 x w / (massIn t Y + w)

/-- The pole residue `e₁M = -Y(Y² + 2Y - 2)/4` of the per-node function in `M`. -/
noncomputable def cornInE1M (Y : ℝ) : ℝ := -(Y * (Y ^ 2 + 2 * Y - 2)) / 4

section

variable {t Y y3 : ℝ}

theorem integral_one_sub_div_two_mul (c : ℝ) :
    ∫ x in Ioo (0 : ℝ) 1, (1 - x) / 2 * c = c / 4 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => (x - x ^ 2 / 2) / 2 * c)
      ((1 - x) / 2 * c) x := fun x _ => by
    have := (((hasDerivAt_id' x).sub ((hasDerivAt_pow 2 x).div_const 2)).div_const 2).mul_const c
    refine this.congr_deriv ?_
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- **The `x`-level identity** `∫₀¹ cornerGm = ∫₀¹ G - (log M)/4`. -/
theorem cornIn_x_level (ht : 0 < t) (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1)
    (hG : IntegrableOn (cornInGn t Y y3) (Ioo 0 1)) :
    IntegrableOn (fun x => cornerGm 0 (√t) y3 (Y - y3) x) (Ioo 0 1) ∧
      ∫ x in Ioo (0 : ℝ) 1, cornerGm 0 (√t) y3 (Y - y3) x =
        (∫ x in Ioo (0 : ℝ) 1, cornInGn t Y y3 x) - log (massIn t Y) / 4 := by
  have hY0 : Y ∈ Ioo (0 : ℝ) 1 := ⟨h3.trans h34, hY⟩
  have hM := massIn_pos ht ⟨hY0.1.le, hY.le⟩
  set M := massIn t Y with hMdef
  have hxs := cornInXs_mem h3 h34 hY
  set xs := cornInXs Y y3
  obtain ⟨iD, iB, vD⟩ := integral_cornInDel hM h3 h34 hY
  set f : ℝ → ℝ := fun x => cornInDPhi Y y3 x * log (1 + cornInW0 Y y3 x / M) with hf
  -- the boundary piece as an indicator
  have hBe : ∀ x ∈ Ioo (0 : ℝ) 1, cornInBphi M Y y3 x = (Ioo xs 1).indicator f x := by
    intro x hx
    unfold cornInBphi cornInDPhiC
    by_cases h : cornInXs Y y3 < x
    · simp only [h, ↓reduceIte]
      rw [indicator_of_mem (show x ∈ Ioo xs 1 from ⟨h, hx.2⟩)]
    · simp only [h, ↓reduceIte, zero_mul]
      rw [indicator_of_notMem (show x ∉ Ioo xs 1 from fun h' => h h'.1)]
  have iB' : IntegrableOn (fun x => cornInBphi M Y y3 x) (Ioo 0 1) := by
    have : IntegrableOn f (Ioo xs 1) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hxs.2.le).1 iB
    exact (this.integrable_indicator measurableSet_Ioo).integrableOn.congr_fun
      (fun x hx => (hBe x hx).symm) measurableSet_Ioo
  have vB : ∫ x in Ioo (0 : ℝ) 1, cornInBphi M Y y3 x = ∫ x in xs..1, f x := by
    rw [setIntegral_congr_fun measurableSet_Ioo hBe, setIntegral_indicator measurableSet_Ioo,
      intervalIntegral.integral_of_le hxs.2.le, integral_Ioc_eq_integral_Ioo,
      inter_eq_right.2 (Ioo_subset_Ioo_left hxs.1.le)]
  have iD' : IntegrableOn (fun x => cornInDel Y y3 x / (M + cornInW0 Y y3 x)) (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 iD
  have vD' : ∫ x in Ioo (0 : ℝ) 1, cornInDel Y y3 x / (M + cornInW0 Y y3 x) =
      -∫ x in xs..1, f x := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, vD]
  have iL : IntegrableOn (fun x : ℝ => (1 - x) / 2 * log M) (Ioo 0 1) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
  -- the pointwise identity
  have hpt : ∀ x ∈ Ioo (0 : ℝ) 1, cornerGm 0 (√t) y3 (Y - y3) x =
      cornInGn t Y y3 x + cornInBphi M Y y3 x + cornInDel Y y3 x / (M + cornInW0 Y y3 x) -
        (1 - x) / 2 * log M := by
    intro x hx
    have h1 := cornerGm_add_log_eq ht hY0 h3 hx
    have h2 := (cornInKt_integral hM h3 hY hx).2
    rw [← hMdef] at h1
    unfold cornInGn
    rw [← hMdef, h2]
    linarith
  have i1 : IntegrableOn (fun x => cornInGn t Y y3 x + cornInBphi M Y y3 x) (Ioo 0 1) :=
    hG.add iB'
  have i2 : IntegrableOn (fun x => cornInGn t Y y3 x + cornInBphi M Y y3 x +
      cornInDel Y y3 x / (M + cornInW0 Y y3 x)) (Ioo 0 1) := i1.add iD'
  have iS : IntegrableOn (fun x => cornInGn t Y y3 x + cornInBphi M Y y3 x +
      cornInDel Y y3 x / (M + cornInW0 Y y3 x) - (1 - x) / 2 * log M) (Ioo 0 1) := i2.sub iL
  refine ⟨iS.congr_fun (fun x hx => (hpt x hx).symm) measurableSet_Ioo, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_sub i2 iL, integral_add i1 iD',
    integral_add hG iB', vB, vD', integral_one_sub_div_two_mul]
  ring

/-- **The per-node identity**: the `Y`-integrand of `C(t, 0)` is
`e₁M/M + ∫∫ 1{y₃ < Y} G(Y, y₃, x) dy₃ dx`. -/
theorem cornInIntegrand_eq (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hG : Integrable (fun q : ℝ × ℝ => if q.1 < Y then cornInGn t Y q.1 q.2 else 0)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) :
    cornInIntegrand t Y = cornInE1M Y / massIn t Y +
      ∫ q, (if q.1 < Y then cornInGn t Y q.1 q.2 else 0)
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hM := massIn_pos ht ⟨hY.1.le, hY.2.le⟩
  set M := massIn t Y with hMdef
  set I : ℝ → ℝ := fun y3 => ∫ x in Ioo (0 : ℝ) 1, cornerGm 0 (√t) y3 (Y - y3) x with hI
  set J : ℝ → ℝ := fun y3 => ∫ x, (if y3 < Y then cornInGn t Y y3 x else 0)
    ∂(volume.restrict (Ioo (0 : ℝ) 1)) with hJ
  have hJi : Integrable J (volume.restrict (Ioo (0 : ℝ) 1)) := hG.integral_prod_left
  -- `J = 1{y₃ < Y}(I + log M/4)` almost everywhere
  have hJe : ∀ᵐ y3 ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      J y3 = (Iio Y).indicator (fun y3 => I y3 + log M / 4) y3 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hG.prod_right_ae] with y3 hy3 hs
    by_cases h : y3 < Y
    · simp only [h, ↓reduceIte] at hs
      have := (cornIn_x_level ht hy3.1 h hY.2 hs).2
      simp only [hJ, hI, h, ↓reduceIte, indicator, mem_Iio]
      rw [this]
      ring
    · simp [hJ, h, indicator]
  -- integrability of `I` on `(0, Y)`
  have hIi : IntegrableOn I (Ioo 0 Y) := by
    have h1 : IntegrableOn (fun y3 => I y3 + log M / 4) (Ioo 0 Y) := by
      have h2 : Integrable ((Iio Y).indicator (fun y3 => I y3 + log M / 4))
          (volume.restrict (Ioo (0 : ℝ) 1)) := hJi.congr hJe
      rw [integrable_indicator_iff measurableSet_Iio, IntegrableOn,
        Measure.restrict_restrict measurableSet_Iio] at h2
      have e : Iio Y ∩ Ioo 0 1 = Ioo 0 Y := by
        ext y; simp only [mem_inter_iff, mem_Iio, mem_Ioo]
        constructor
        · rintro ⟨h, h0, -⟩; exact ⟨h0, h⟩
        · rintro ⟨h0, h⟩; exact ⟨h, h0, h.trans hY.2⟩
      rwa [e] at h2
    refine (h1.sub (integrableOn_const (C := log M / 4) (by simp))).congr_fun
      (fun y _ => by simp) measurableSet_Ioo
  rw [integral_prod _ hG, ← hJ, integral_congr_ae hJe, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  have e : Iio Y ∩ Ioo 0 1 = Ioo 0 Y := by
    ext y; simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨h, h0, -⟩; exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩; exact ⟨h, h0, h.trans hY.2⟩
  rw [e, integral_add hIi (integrableOn_const (C := log M / 4) (by simp)), setIntegral_const]
  have hII : ∫ y3 in (0 : ℝ)..Y, ∫ x in (0 : ℝ)..1, cornerGm 0 (√t) y3 (Y - y3) x =
      ∫ y3 in Ioo 0 Y, I y3 := by
    rw [intervalIntegral.integral_of_le hY.1.le, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun y3 _ => ?_
    rw [hI, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [cornInIntegrand, hII, ← hMdef]
  simp only [Real.volume_real_Ioo_of_le hY.1.le, smul_eq_mul,
    sub_zero]
  unfold cornInE1M
  field_simp
  ring

end

end QED.ChainProof.SetCK

end
