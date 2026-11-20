/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKLamOutC

/-!
# Set (c), Stage K: the outer-massive corner at finite Pauli–Villars mass

Helper level (no frozen statement). With the Pauli–Villars pair `(λ, Λ)` on the inner photon
line of the corner (outer photon of mass² `t > 0`), its two-loop part is (layer R2 of the M5
plan)

`scOutCReg t λ Λ = 2 ∫₀¹ dY ∫₀^Y dy₃ ∫₀¹ dx (cornerGm (√t) λ y₃ (Y - y₃) x
  - cornerGm (√t) Λ y₃ (Y - y₃) x)`.

* **`scOutCReg_eq`**: `scOutCReg t λ Λ = scOutCRep t λ - scOutCRep t Λ` (`λ² ≤ 1`, `Λ > 0`;
  integrability of each term at both masses, almost everywhere in `y₃`);
* **`lamOutC_scOutCRep_eq`**: at the large mass the inner subdivergence separates,
  `scOutCRep t Λ = 2 ∫ lamOutCY t Λ - F₂(√t) ∫₀¹ Y log M_Λ(Y) dY`, from
  `∫₀¹ ℓ_C dx = F₂(√t)/2` (`integral_cornerEll`) and `∫₀^Y dy₃ = Y`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitSCCorner

/-- **The outer-massive corner at finite Pauli–Villars mass** (two-loop part; pair `(λ, Λ)` on
the inner line). -/
noncomputable def scOutCReg (t lam Lam : ℝ) : ℝ :=
  2 * ∫ Y in (0 : ℝ)..1, ∫ y3 in (0 : ℝ)..Y, ∫ x in (0 : ℝ)..1,
    (cornerGm (√t) lam y3 (Y - y3) x - cornerGm (√t) Lam y3 (Y - y3) x)

/-! ### Integrability -/

theorem lamOutC_ell_intervalIntegrable (t : ℝ) :
    IntervalIntegrable (fun x => cornerC0 x / hOut t x) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr (integrableOn_cornerEll (√t))

/-- An a.e. bound by an integrable function gives integrability on `[0, b]`. -/
theorem lamOut_intervalIntegrable_of_ae_le {f g : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hf : Measurable f) (hg : IntervalIntegrable g volume 0 b)
    (h : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Ioc 0 b → |f y| ≤ g y) :
    IntervalIntegrable f volume 0 b := by
  refine hg.mono_fun' hf.aestronglyMeasurable ?_
  rw [uIoc_of_le hb]
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  filter_upwards [h] with y hy hy'
  rw [Real.norm_eq_abs]
  exact hy hy'

/-- The corner integrand at inner mass `λ`, `λ² ≤ 1`, is integrable in `x` (`M_λ ≠ 0`). -/
theorem lamOutC_intervalIntegrable_lam {t lam Y y3 : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) (h3 : y3 ∈ Ioo (0 : ℝ) Y)
    (hM : cornerMass (√t) lam y3 (Y - y3) ≠ 0) :
    IntervalIntegrable (cornerGm (√t) lam y3 (Y - y3)) volume 0 1 :=
  (intervalIntegrable_of_abs_le (measurable_regCornerGm (√t) lam y3 (Y - y3))
    ((regIntervalIntegrable_rootInv (n := 8) (by norm_num)).const_mul
      (200 * (1 + 1 / t) * regCOutA Y * regRootInv 10 y3))
    fun x hx => (abs_regCornerGm_out_le ht hl hY h3 hx hM).trans
      (le_of_eq (scOutCDom_eq ..))).1

/-- The `x`-integral at inner mass `λ`, `λ² ≤ 1`, is integrable in `y₃`. -/
theorem lamOutC_regCOutX_intervalIntegrable_lam {t lam Y : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1)
    (hY : Y ∈ Ioo (0 : ℝ) 1) : IntervalIntegrable (regCOutX t lam Y) volume 0 Y := by
  refine lamOut_intervalIntegrable_of_ae_le hY.1.le
    ((measurable_regCOutX t lam).of_uncurry_left)
    ((lamOutC_intervalIntegrable_rootInv_Y hY).const_mul
      (200 * (1 + 1 / t) * regCOutA Y) |>.mul_const (∫ x in (0 : ℝ)..1, regRootInv 8 x)) ?_
  filter_upwards [Measure.ae_ne volume Y, ae_regMass_ne (lam := lam) ht.le hY] with y3 hy3 hM hy
  exact abs_regCOutX_le ht hl hY ⟨hy.1, lt_of_le_of_ne hy.2 hy3⟩ hM

/-- The `(y₃, x)`-integral at inner mass `λ`, `λ² ≤ 1`, is integrable in `Y`. -/
theorem lamOutC_regCOutY_intervalIntegrable_lam {t lam : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1) :
    IntervalIntegrable (regCOutY t lam) volume 0 1 := by
  refine lamOut_intervalIntegrable_of_ae_le zero_le_one (measurable_regCOutY t lam)
    ((regIntervalIntegrable_regCOutA.const_mul (200 * (1 + 1 / t)) |>.mul_const
      (∫ y in (0 : ℝ)..1, regRootInv 10 y)).mul_const (∫ x in (0 : ℝ)..1, regRootInv 8 x)) ?_
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
  exact abs_regCOutY_le ht hl ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩

/-! ### The corner at inner mass `Λ` -/

theorem lamOutC_cornerGm_eq (t Lam Y y3 : ℝ) :
    cornerGm (√t) Lam y3 (Y - y3) = fun x =>
      lamOutCE t Lam Y y3 x - cornerC0 x / hOut t x * log (ladderInnerMass 1 Lam Y) := by
  funext x
  unfold lamOutCE
  ring

/-- **The `x`-integral at inner mass `Λ`**: `∫ cornerGm = ∫ lamOutCE - (F₂(√t)/2) log M_Λ`. -/
theorem lamOutC_regCOutX_eq {t Lam Y y3 : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (h3 : y3 ∈ Ioo (0 : ℝ) Y) (hM : cornerMass (√t) Lam y3 (Y - y3) ≠ 0) :
    IntervalIntegrable (cornerGm (√t) Lam y3 (Y - y3)) volume 0 1 ∧
      regCOutX t Lam Y y3 =
        lamOutCX t Lam Y y3 - oneLoopF2 1 (√t) / 2 * log (ladderInnerMass 1 Lam Y) := by
  have hi := (lamOutCX_bound ht hY h3 hM).1
  have hl := (lamOutC_ell_intervalIntegrable t).mul_const (log (ladderInnerMass 1 Lam Y))
  refine ⟨by rw [lamOutC_cornerGm_eq]; exact hi.sub hl, ?_⟩
  unfold regCOutX lamOutCX
  rw [lamOutC_cornerGm_eq, intervalIntegral.integral_sub hi hl,
    intervalIntegral.integral_mul_const]
  have e : ∫ x in (0 : ℝ)..1, cornerC0 x / hOut t x = oneLoopF2 1 (√t) / 2 :=
    integral_cornerEll (sqrt_pos.2 ht)
  rw [e]

/-- **The `(y₃, x)`-integral at inner mass `Λ`.** -/
theorem lamOutC_regCOutY_eq {t Lam Y : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (regCOutX t Lam Y) volume 0 Y ∧
      regCOutY t Lam Y =
        lamOutCY t Lam Y - Y * (oneLoopF2 1 (√t) / 2 * log (ladderInnerMass 1 Lam Y)) := by
  set c := oneLoopF2 1 (√t) / 2 * log (ladderInnerMass 1 Lam Y)
  have hi := (lamOutCY_bound (Lam := Lam) ht hY).1
  have hc : IntervalIntegrable (fun _ : ℝ => c) volume 0 Y := intervalIntegrable_const
  have hae : ∀ᵐ y3 ∂(volume : Measure ℝ), y3 ∈ Ioc 0 Y →
      regCOutX t Lam Y y3 = lamOutCX t Lam Y y3 - c := by
    filter_upwards [Measure.ae_ne volume Y, ae_regMass_ne (lam := Lam) ht.le hY] with y3 hy3 hM hy
    exact (lamOutC_regCOutX_eq ht hY ⟨hy.1, lt_of_le_of_ne hy.2 hy3⟩ hM).2
  refine ⟨lamOut_intervalIntegrable_of_ae_le hY.1.le ((measurable_regCOutX t Lam).of_uncurry_left)
    (hi.sub hc).abs ?_, ?_⟩
  · filter_upwards [hae] with y3 h hy
    rw [h hy]
  · unfold regCOutY lamOutCY
    rw [intervalIntegral.integral_congr_ae (g := fun y3 => lamOutCX t Lam Y y3 - c) ?_,
      intervalIntegral.integral_sub hi hc, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    filter_upwards [hae] with y3 h hy
    rw [uIoc_of_le hY.1.le] at hy
    exact h hy

/-- **The outer-massive corner at inner mass `Λ`**: `scOutCRep t Λ = 2 ∫ lamOutCY -
F₂(√t) ∫₀¹ Y log M_Λ(Y) dY`; the last term is the corner's inner subdivergence. -/
theorem lamOutC_scOutCRep_eq {t Lam : ℝ} (ht : 0 < t) (hLam : 0 < Lam) :
    IntervalIntegrable (regCOutY t Lam) volume 0 1 ∧
      scOutCRep t Lam = 2 * (∫ Y in (0 : ℝ)..1, lamOutCY t Lam Y) -
        oneLoopF2 1 (√t) * ∫ Y in (0 : ℝ)..1, Y * log (ladderInnerMass 1 Lam Y) := by
  set c := oneLoopF2 1 (√t) / 2
  have hi := lamOutCY_intervalIntegrable (Lam := Lam) ht
  have hL : IntervalIntegrable (fun Y => Y * (c * log (ladderInnerMass 1 Lam Y))) volume 0 1 := by
    have := intervalIntegrable_mul_logMass hLam (p := fun Y => Y * c) (by fun_prop)
    refine this.congr_uIoo fun Y _ => ?_
    ring
  have hae : ∀ᵐ Y ∂(volume : Measure ℝ), Y ∈ Ioc 0 1 →
      regCOutY t Lam Y = lamOutCY t Lam Y - Y * (c * log (ladderInnerMass 1 Lam Y)) := by
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    exact (lamOutC_regCOutY_eq ht ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩).2
  refine ⟨lamOut_intervalIntegrable_of_ae_le zero_le_one (measurable_regCOutY t Lam)
    (hi.sub hL).abs ?_, ?_⟩
  · filter_upwards [hae] with Y h hY
    rw [h hY]
  · change 2 * (∫ Y in (0 : ℝ)..1, regCOutY t Lam Y) = _
    rw [intervalIntegral.integral_congr_ae
      (g := fun Y => lamOutCY t Lam Y - Y * (c * log (ladderInnerMass 1 Lam Y))) ?_,
      intervalIntegral.integral_sub hi hL]
    · have e : ∫ Y in (0 : ℝ)..1, Y * (c * log (ladderInnerMass 1 Lam Y)) =
          c * ∫ Y in (0 : ℝ)..1, Y * log (ladderInnerMass 1 Lam Y) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext Y
        ring
      rw [e]
      ring
    · filter_upwards [hae] with Y h hY
      rw [uIoc_of_le zero_le_one] at hY
      exact h hY

/-- **The corner at finite `Λ` is the difference of the two inner masses.** -/
theorem scOutCReg_eq {t lam Lam : ℝ} (ht : 0 < t) (hl : lam ^ 2 ≤ 1) (hLam : 0 < Lam) :
    scOutCReg t lam Lam = scOutCRep t lam - scOutCRep t Lam := by
  have hYeq : ∀ Y ∈ Ioo (0 : ℝ) 1, (∫ y3 in (0 : ℝ)..Y, ∫ x in (0 : ℝ)..1,
      (cornerGm (√t) lam y3 (Y - y3) x - cornerGm (√t) Lam y3 (Y - y3) x)) =
      regCOutY t lam Y - regCOutY t Lam Y := fun Y hY => by
    rw [intervalIntegral.integral_congr_ae
      (g := fun y3 => regCOutX t lam Y y3 - regCOutX t Lam Y y3) ?_]
    · exact intervalIntegral.integral_sub (lamOutC_regCOutX_intervalIntegrable_lam ht hl hY)
        (lamOutC_regCOutY_eq ht hY).1
    · filter_upwards [Measure.ae_ne volume Y, ae_regMass_ne (lam := lam) ht.le hY,
        ae_regMass_ne (lam := Lam) ht.le hY] with y3 hy3 hMl hML hy
      rw [uIoc_of_le hY.1.le] at hy
      have h3 : y3 ∈ Ioo (0 : ℝ) Y := ⟨hy.1, lt_of_le_of_ne hy.2 hy3⟩
      exact intervalIntegral.integral_sub (lamOutC_intervalIntegrable_lam ht hl hY h3 hMl)
        (lamOutC_regCOutX_eq ht hY h3 hML).1
  unfold scOutCReg
  rw [intervalIntegral.integral_congr_ae (g := fun Y => regCOutY t lam Y - regCOutY t Lam Y) ?_,
    intervalIntegral.integral_sub (lamOutC_regCOutY_intervalIntegrable_lam ht hl)
      (lamOutC_scOutCRep_eq ht hLam).1]
  · change _ = 2 * (∫ Y in (0 : ℝ)..1, regCOutY t lam Y) - 2 * ∫ Y in (0 : ℝ)..1, regCOutY t Lam Y
    ring
  · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with Y hY1 hY
    rw [uIoc_of_le zero_le_one] at hY
    exact hYeq Y ⟨hY.1, lt_of_le_of_ne hY.2 hY1⟩

end QED.ChainProof.SetCK
