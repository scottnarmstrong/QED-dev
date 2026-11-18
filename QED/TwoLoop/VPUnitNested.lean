/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPUnitNestedD3
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The nested form of the VP unit: reduction to the bubble half

The nested-form identity `QED.TwoLoop.UnitVPLink.VPUnitNested P` of the VP unit,
`unitF2 .VP P = outerF2 ((Π_loop - δ₃) s D(s)²)`, splits into the two kinds of classes of the
unit, `unitZero .VP P = -vpZero P + 2 d3Zero P`:

* the two `δ₃` classes give `e³ outerF2 (-δ₃ s D(s)²)`, **proved**
  (`QED.TwoLoop.VPUnitNested.unit_d3Zero`, `QED/TwoLoop/VPUnitNestedD3.lean`), for all
  `m_γ, Λ > 0` and every `δ₃`;
* the bubble class `VP` should give `e³ outerF2 (Π_loop s D(s)²)` (`VPHalf`, **not proved**).

This file proves that, at `m = 1`, `e = 1` and admissible regulators, the nested form is
**equivalent** to the bubble half (`vpUnitNested_iff_vpHalf`): the remaining content of
`VPUnitNested` is exactly `VPHalf`. The outer integrands are integrable
(`intervalIntegrable_outer_sD2`, `intervalIntegrable_outer_loop`; the second through the spectral
form `QED.TwoLoop.UnitVPLink.vacuumPolarizationLoop_sub_zero` and
`QED.TwoLoop.UnitVPLink.vpFlavour_eq_outer`), so `outerF2` splits linearly.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPUnitNested

open QED.WickModel QED.TwoLoop.UnitVPLink QED.TwoLoop.UnitsRegulated

/-! ### Integrability of the outer integrands -/

theorem continuousOn_kernD3One {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (kernD3One a b) (Icc 0 1) := by
  have hpos : ∀ M : ℝ, 0 < M → ∀ y ∈ Icc (0 : ℝ) 1, 0 < (1 - y) * M ^ 2 + y ^ 2 := by
    intro M hM y hy
    rcases eq_or_lt_of_le hy.1 with h0 | h0
    · subst h0; simp; positivity
    · have : 0 ≤ (1 - y) * M ^ 2 := mul_nonneg (by linarith [hy.2]) (sq_nonneg M)
      positivity
  unfold kernD3One
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => ?_
  have := hpos a ha y hy
  have := hpos b hb y hy
  positivity

/-- The outer integrand of `s D(s)²` is integrable on `[0, 1]`. -/
theorem intervalIntegrable_outer_sD2 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : ℝ) :
    IntervalIntegrable (fun x => x ^ 2 * (c * photonVar x * photonD a b (photonVar x) ^ 2))
      volume 0 1 := by
  have hK : IntervalIntegrable (fun y => c * ((b ^ 2 - a ^ 2) ^ 2 * kernD3One a b y) / 2)
      volume 0 1 :=
    (((continuousOn_kernD3One ha hb).intervalIntegrable_of_Icc zero_le_one).const_mul
      ((b ^ 2 - a ^ 2) ^ 2)).const_mul c |>.div_const 2
  refine (intervalIntegrable_congr_uIoo fun y hy => ?_).mp hK
  rw [uIoo_of_le zero_le_one] at hy
  rw [kernD3One_mul ha hb hy]
  ring

/-- The outer integrand of `Π_loop(s) s D(s)²` is integrable on `[0, 1]`, for admissible
regulators at `m = 1`. -/
theorem intervalIntegrable_outer_loop (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁)
    (hM₂ : 1 < P.M₂) (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2) :
    IntervalIntegrable (fun x => x ^ 2 *
      (vacuumPolarizationLoop P (photonVar x) * photonVar x * photonD P.mγ P.Λ (photonVar x) ^ 2))
      volume 0 1 := by
  have hmass := mass_ne_zero_of hm hM₁ hM₂
  have hΛ : 0 < P.Λ := hmγ.trans hmΛ
  have hsq : P.mγ ^ 2 < 4 := by nlinarith
  have F0 := (vpFlavour_eq_outer (M := 1) one_ne_zero hmγ hmΛ (by norm_num; exact hsq)).1
  have F1 := (vpFlavour_eq_outer (M := P.M₁) (by linarith : P.M₁ ≠ 0).symm.symm hmγ hmΛ
    (by nlinarith)).1
  have F2 := (vpFlavour_eq_outer (M := P.M₂) (by linarith : P.M₂ ≠ 0).symm.symm hmγ hmΛ
    (by nlinarith)).1
  have hI := (intervalIntegrable_outer_sD2 hmγ hΛ (vacuumPolarizationLoop P 0)).add
    (((F0.add (F1.const_mul P.c₁)).add (F2.const_mul P.c₂)).const_mul (P.e ^ 2 / (4 * π ^ 2)))
  refine (intervalIntegrable_congr_uIoo fun x hx => ?_).mp hI
  rw [uIoo_of_le zero_le_one] at hx
  have hs : 0 ≤ photonVar x := photonVar_nonneg ⟨hx.1.le, hx.2.le⟩
  have hsub := vacuumPolarizationLoop_sub_zero P hmass hs
  rw [Fin.sum_univ_three] at hsub
  simp only [Params.loopCoeff, Params.mass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hm] at hsub
  have hPi : vacuumPolarizationLoop P (photonVar x) = vacuumPolarizationLoop P 0 +
      P.e ^ 2 / (4 * π ^ 2) * (1 * specJ 1 (photonVar x) + P.c₁ * specJ P.M₁ (photonVar x) +
        P.c₂ * specJ P.M₂ (photonVar x)) := by linarith
  simp only [flavOuter]
  rw [hPi]
  ring

/-! ### The bubble half and the reduction -/

/-- **The bubble half of the nested form** (open): the bubble class of the VP unit is `e³` times
the outer one-loop functional of the inserted loop function,
`-(1/(64 m⁵)) (1/i) vpZero P = e³ outerF2 (s ↦ Π_loop(s) s D(s)²)`. -/
def VPHalf (P : Params) : Prop :=
  1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * -QED.TwoLoop.PauliZeroExplicit.vpZero P) =
    ((P.e ^ 3 * outerF2 (fun s => vacuumPolarizationLoop P s * s * photonD P.mγ P.Λ s ^ 2) : ℝ) :
      ℂ)

/-- **The nested form of the VP unit is equivalent to its bubble half**, at `m = 1`, `e = 1`, for
regulator masses `M₁, M₂ > 1`, `0 < m_γ < Λ`, `m_γ < 2` and every `δ₃`: the `δ₃` classes are
accounted for by `unit_d3Zero`. -/
theorem vpUnitNested_iff_vpHalf (P : Params) (hm : P.m = 1) (he : P.e = 1) (hM₁ : 1 < P.M₁)
    (hM₂ : 1 < P.M₂) (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2) :
    VPUnitNested P ↔ VPHalf P := by
  have hΛ : 0 < P.Λ := hmγ.trans hmΛ
  have hd3 := unit_d3Zero P hm hmγ hΛ
  have hsplit : vpOuterF2 P =
      outerF2 (fun s => vacuumPolarizationLoop P s * s * photonD P.mγ P.Λ s ^ 2) +
        outerF2 (fun s => -P.δ₃ * s * photonD P.mγ P.Λ s ^ 2) := by
    unfold vpOuterF2 outerF2
    rw [← mul_add, ← intervalIntegral.integral_add
      (intervalIntegrable_outer_loop P hm hM₁ hM₂ hmγ hmΛ hm2)
      (intervalIntegrable_outer_sD2 hmγ hΛ (-P.δ₃))]
    congr 1
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  have hU : unitF2 .VP P =
      1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * -QED.TwoLoop.PauliZeroExplicit.vpZero P) +
        1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * (2 * QED.TwoLoop.PauliZeroExplicit.d3Zero P)) := by
    simp only [unitF2, unitZero]
    ring
  unfold VPUnitNested VPHalf
  rw [hU, hd3, hsplit, he]
  simp only [one_pow, one_mul]
  push_cast
  constructor
  · intro h
    exact add_right_cancel h
  · intro h
    rw [h]

end QED.TwoLoop.VPUnitNested

end
