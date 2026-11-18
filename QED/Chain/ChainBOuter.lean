/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.ChainBSpec
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The two-bubble outer functional at finite regulators (O3-10, analytic core)

Helper-level form of obligation O3-10 of `docs/HIGHER-LOOP-PLAN.md` for set (b). It is **not**
frozen and does not depend on any three-loop model: the bubble is the explicit flavour-summed
loop function `QED.Chain.HeavyVP.flavourPi`, so that a later model whose set (b) class unfolds to
the outer functional of `(Π_loop - δ₃)² s² D³` (obligations O3-6, O3-7) can use these statements.

The chain of `n` bubbles has the photon function `D (Π k² D)ⁿ`; for `n = 2` the outer integrand is
`(Π_loop(s) - δ₃)² s² D(s)³`, the model-level form of task T1 (`chain_reg` in
`scripts/numerics/phase5_chains.py`, section C).

## Objects

* `chainReg m_γ Λ M₁ M₂ = ∫₀¹ x² s² D(s)³ jSum(M₁, M₂, s)² dx`, `s = x²/(1-x)`: the set (b)
  two-bubble functional at finite regulators, electron loop and open line of mass `1`, with the
  spectral form `jSum = specJ(1,·) + c₁ specJ(M₁,·) + c₂ specJ(M₂,·)` of each bubble.
* `chainPair M M' m_γ Λ = ∫₀¹ x² s² D³ specJ(M, s) specJ(M', s) dx`: one pair of flavours.

## Main statements

* `outerF2_flavourPi_sub_sq` (**any finite flavour family**, no condition on the regulators):
  `64π⁶ outerF2 (s ↦ (Π(s) - Π(0))² s² D(s)³) = e⁴ ∫₀¹ x² s² D³ (∑_f c_f specJ(M_f, s))² dx`.
* `outerF2_flavourPi_delta3_sq`: the same with `δ₃ = Π(0)` (the photon condition).
* `chainOuter_eq_chainReg`: for the electron with its Pauli–Villars pair, `M₁, M₂ > 1` and the
  two conditions, `64π⁶ outerF2 (s ↦ (Π_e(s) - Π_e(0))² s² D³) = e⁴ chainReg m_γ Λ M₁ M₂`.
* `chainModel_eq_chainReg`: the frozen two-loop model's loop function in the set (b) form:
  `64π⁶ outerF2 (s ↦ (vacuumPolarizationLoop P s - P.δ₃)² s² D³) = P.e⁴ chainReg`.
* `chainReg_eq_sum_chainPair`: at `0 < m_γ < Λ`, `chainReg` is the sum over the nine flavour
  pairs `∑_{f,g} c_f c_g chainPair(M_f, M_g)`, each pair integrable
  (`intervalIntegrable_chainPair`).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.Chain.ChainB

open QED.WickModel QED.TwoLoop.VPUnit QED.TwoLoop.UnitVPLink QED.Chain.HeavyVP

variable {ι : Type*} [Fintype ι]

/-! ### Any finite flavour family -/

/-- **The two-bubble outer functional of a flavour-summed subtracted `Π`.** For nonzero masses,
`64π⁶ outerF2 (s ↦ (Π(s) - Π(0))² s² D(s)³) = e⁴ ∫₀¹ x² s² D(s)³ (∑_f c_f specJ(M_f, s))² dx`. -/
theorem outerF2_flavourPi_sub_sq {e mγ Λ : ℝ} {mass coeff : ι → ℝ} (hmass : ∀ f, mass f ≠ 0) :
    64 * π ^ 6 * outerF2 (fun s => (flavourPi e mass coeff s - flavourPi e mass coeff 0) ^ 2 *
        s ^ 2 * photonD mγ Λ s ^ 3) =
      e ^ 4 * ∫ x in (0 : ℝ)..1, x ^ 2 * (photonVar x ^ 2 * photonD mγ Λ (photonVar x) ^ 3 *
        (∑ f, coeff f * specJ (mass f) (photonVar x)) ^ 2) := by
  have hpt : ∀ x ∈ uIcc (0 : ℝ) 1,
      x ^ 2 * ((flavourPi e mass coeff (photonVar x) - flavourPi e mass coeff 0) ^ 2 *
        photonVar x ^ 2 * photonD mγ Λ (photonVar x) ^ 3) =
      (e ^ 2 / (4 * π ^ 2)) ^ 2 * (x ^ 2 * (photonVar x ^ 2 * photonD mγ Λ (photonVar x) ^ 3 *
        (∑ f, coeff f * specJ (mass f) (photonVar x)) ^ 2)) := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    rw [flavourPi_sub_zero hmass (photonVar_nonneg hx)]
    ring
  unfold outerF2
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The same with the counterterm written as `δ₃ = Π(0)` (the photon on-shell condition). -/
theorem outerF2_flavourPi_delta3_sq {e mγ Λ δ₃ : ℝ} {mass coeff : ι → ℝ}
    (hmass : ∀ f, mass f ≠ 0) (hδ₃ : δ₃ = flavourPi e mass coeff 0) :
    64 * π ^ 6 * outerF2 (fun s => (flavourPi e mass coeff s - δ₃) ^ 2 * s ^ 2 *
        photonD mγ Λ s ^ 3) =
      e ^ 4 * ∫ x in (0 : ℝ)..1, x ^ 2 * (photonVar x ^ 2 * photonD mγ Λ (photonVar x) ^ 3 *
        (∑ f, coeff f * specJ (mass f) (photonVar x)) ^ 2) := by
  subst hδ₃
  exact outerF2_flavourPi_sub_sq hmass

/-! ### The electron with its Pauli–Villars pair -/

/-- **The set (b) two-bubble functional at finite regulators** (electron loop and open line of
mass `1`): `∫₀¹ x² s² D(s)³ jSum(M₁, M₂, s)² dx` with `s = x²/(1-x)`. -/
noncomputable def chainReg (mγ Λ M₁ M₂ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ 2 * (photonVar x ^ 2 * photonD mγ Λ (photonVar x) ^ 3 *
    jSum M₁ M₂ (photonVar x) ^ 2)

/-- The flavour sum of one block with the Pauli–Villars conditions of loop mass `1` is `jSum`. -/
theorem sum_heavy_specJ {M₁ M₂ c₁ c₂ : ℝ} (hM₂ : 1 < M₂) (hPV₁ : 1 + c₁ + c₂ = 0)
    (hPV₂ : 1 ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) (s : ℝ) :
    ∑ f, heavyCoeff c₁ c₂ f * specJ (heavyMass 1 M₁ M₂ f) s = jSum M₁ M₂ s := by
  obtain ⟨hc₁, hc₂⟩ := pvL_unique (sq_ne_sq_of_pvL one_pos hM₂ hPV₁ hPV₂) hPV₁ hPV₂
  rw [Fin.sum_univ_three]
  simp only [heavyCoeff, heavyMass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul, jSum, deltaM, hc₁, hc₂,
    pvC1L_one, pvC2L_one, add_assoc]

/-- **O3-10 for the electron block.** With regulators `M₁, M₂ > 1` and coefficients satisfying
the two Pauli–Villars conditions of loop mass `1`, for all `m_γ, Λ`:
`64π⁶ outerF2 (s ↦ (Π_e(s) - Π_e(0))² s² D(s)³) = e⁴ chainReg m_γ Λ M₁ M₂`. -/
theorem chainOuter_eq_chainReg {e M₁ M₂ c₁ c₂ mγ Λ : ℝ} (hM₁ : 1 < M₁) (hM₂ : 1 < M₂)
    (hPV₁ : 1 + c₁ + c₂ = 0) (hPV₂ : 1 ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0) :
    64 * π ^ 6 * outerF2 (fun s => (heavyPi e 1 M₁ M₂ c₁ c₂ s - heavyPi e 1 M₁ M₂ c₁ c₂ 0) ^ 2 *
        s ^ 2 * photonD mγ Λ s ^ 3) =
      e ^ 4 * chainReg mγ Λ M₁ M₂ := by
  unfold heavyPi
  rw [outerF2_flavourPi_sub_sq (heavyMass_ne_zero one_pos hM₁ hM₂)]
  simp only [sum_heavy_specJ hM₂ hPV₁ hPV₂]
  rfl

/-- **O3-10 in the frozen two-loop model's variables.** For `P.m = 1`, `P.M₁, P.M₂ > 1`, the
Pauli–Villars conditions and `δ₃ = Π_loop(0)`:
`64π⁶ outerF2 (s ↦ (vacuumPolarizationLoop P s - P.δ₃)² s² D(s)³) = P.e⁴ chainReg`. -/
theorem chainModel_eq_chainReg (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hδ₃ : P.δ₃ = vacuumPolarizationLoop P 0) :
    64 * π ^ 6 * outerF2 (fun s => (vacuumPolarizationLoop P s - P.δ₃) ^ 2 * s ^ 2 *
        photonD P.mγ P.Λ s ^ 3) =
      P.e ^ 4 * chainReg P.mγ P.Λ P.M₁ P.M₂ := by
  rw [hm] at hPV₂
  rw [hδ₃, vacuumPolarizationLoop_eq_heavyPi, hm]
  exact chainOuter_eq_chainReg hM₁ hM₂ hPV₁ hPV₂

/-! ### The flavour-pair expansion -/

/-- The integrand of one flavour pair: `x² s² D(s)³ specJ(M, s) specJ(M', s)`, `s = x²/(1-x)`. -/
noncomputable def pairIntegrand (M M' mγ Λ x : ℝ) : ℝ :=
  x ^ 2 * (photonVar x ^ 2 * photonD mγ Λ (photonVar x) ^ 3 *
    (specJ M (photonVar x) * specJ M' (photonVar x)))

/-- One flavour pair of the two-bubble functional: `∫₀¹ x² s² D³ specJ(M, s) specJ(M', s) dx`. -/
noncomputable def chainPair (M M' mγ Λ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, pairIntegrand M M' mγ Λ x

theorem measurable_photonVar : Measurable photonVar := by
  unfold photonVar
  fun_prop

theorem measurable_photonD (mγ Λ : ℝ) : Measurable (photonD mγ Λ) := by
  unfold photonD
  fun_prop

/-- `0 ≤ s D(s) ≤ 1` for `s ≥ 0` and `0 < m_γ ≤ Λ`. -/
theorem photonD_bounds {mγ Λ s : ℝ} (hmγ : 0 < mγ) (hmΛ : mγ ≤ Λ) (hs : 0 ≤ s) :
    0 ≤ s * photonD mγ Λ s ∧ s * photonD mγ Λ s ≤ 1 := by
  have ha : 0 < s + mγ ^ 2 := by positivity
  have hb : s + mγ ^ 2 ≤ s + Λ ^ 2 := by nlinarith
  have hb' : 0 < s + Λ ^ 2 := ha.trans_le hb
  unfold photonD
  have h1 : 1 / (s + Λ ^ 2) ≤ 1 / (s + mγ ^ 2) := one_div_le_one_div_of_le ha hb
  have h2 : s * (1 / (s + mγ ^ 2)) ≤ 1 := by
    rw [mul_one_div, div_le_one ha]
    linarith [pow_pos hmγ 2]
  have h3 : 0 ≤ s * (1 / (s + Λ ^ 2)) := mul_nonneg hs (by positivity)
  constructor
  · exact mul_nonneg hs (by linarith)
  · rw [mul_sub]
    linarith

/-- `s⁴ D(s)³ ≤ Λ²` for `s ≥ 0` and `0 < m_γ ≤ Λ`. -/
theorem sq_sq_photonD_cube_le {mγ Λ s : ℝ} (hmγ : 0 < mγ) (hmΛ : mγ ≤ Λ) (hs : 0 ≤ s) :
    0 ≤ s ^ 4 * photonD mγ Λ s ^ 3 ∧ s ^ 4 * photonD mγ Λ s ^ 3 ≤ Λ ^ 2 := by
  obtain ⟨d0, d1⟩ := photonD_bounds hmγ hmΛ hs
  have ha : 0 < s + mγ ^ 2 := by positivity
  have hΛ : 0 < Λ := hmγ.trans_le hmΛ
  have hb' : 0 < s + Λ ^ 2 := by positivity
  -- `s D(s) ≤ Λ² s/((s + m_γ²)(s + Λ²)) · ...`; we use `s² D ≤ Λ²`.
  have hD : s ^ 2 * photonD mγ Λ s ≤ Λ ^ 2 := by
    have e : photonD mγ Λ s = (Λ ^ 2 - mγ ^ 2) / ((s + mγ ^ 2) * (s + Λ ^ 2)) := by
      unfold photonD
      field_simp
      ring
    rw [e, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hs (sq_nonneg Λ)) (sq_nonneg Λ),
      mul_nonneg (mul_nonneg hs (sq_nonneg mγ)) (sq_nonneg Λ),
      mul_nonneg (sq_nonneg mγ) (mul_nonneg (sq_nonneg Λ) (sq_nonneg Λ)),
      mul_nonneg (sq_nonneg s) (sq_nonneg mγ)]
  have hsD : 0 ≤ s * photonD mγ Λ s := d0
  have e4 : s ^ 4 * photonD mγ Λ s ^ 3 = (s * photonD mγ Λ s) ^ 2 * (s ^ 2 * photonD mγ Λ s) := by
    ring
  have hs2D : 0 ≤ s ^ 2 * photonD mγ Λ s := by
    have : s ^ 2 * photonD mγ Λ s = s * (s * photonD mγ Λ s) := by ring
    rw [this]
    exact mul_nonneg hs hsD
  rw [e4]
  constructor
  · positivity
  · calc (s * photonD mγ Λ s) ^ 2 * (s ^ 2 * photonD mγ Λ s) ≤ 1 * (s ^ 2 * photonD mγ Λ s) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hs2D
      _ ≤ Λ ^ 2 := by linarith

/-- Each flavour pair is integrable at `0 < m_γ ≤ Λ` (for `M, M' ≠ 0`): the integrand is bounded
by `x² Λ²/(225 M² M'²)`, from `specJ(M, s) ≤ s/(15M²)` and `s⁴D³ ≤ Λ²`. -/
theorem intervalIntegrable_chainPair {M M' mγ Λ : ℝ} (hM : M ≠ 0) (hM' : M' ≠ 0) (hmγ : 0 < mγ)
    (hmΛ : mγ ≤ Λ) :
    IntervalIntegrable (pairIntegrand M M' mγ Λ) volume 0 1 := by
  have hm : Measurable (pairIntegrand M M' mγ Λ) := by
    unfold pairIntegrand
    have h1 := (measurable_photonD mγ Λ).comp measurable_photonVar
    have h2 := (measurable_specJ M).comp measurable_photonVar
    have h3 := (measurable_specJ M').comp measurable_photonVar
    exact (measurable_id.pow_const 2).mul (((measurable_photonVar.pow_const 2).mul
      (h1.pow_const 3)).mul (h2.mul h3))
  refine ((continuous_const (y := Λ ^ 2 / (225 * M ^ 2 * M' ^ 2))).intervalIntegrable 0 1
    ).mono_fun hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => ?_)
  rw [uIoc_of_le zero_le_one] at hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
  set s := photonVar x with hsdef
  have hs : 0 ≤ s := photonVar_nonneg hx'
  have j0 := specJ_nonneg hM hs
  have j0' := specJ_nonneg hM' hs
  have j1 := specJ_le_div hM hs
  have j1' := specJ_le_div hM' hs
  obtain ⟨d0, d1⟩ := sq_sq_photonD_cube_le hmγ hmΛ hs
  have hM2 : 0 < M ^ 2 := by positivity
  have hM2' : 0 < M' ^ 2 := by positivity
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  have hD0 : 0 ≤ s ^ 2 * photonD mγ Λ s ^ 3 := by
    obtain ⟨e0, -⟩ := photonD_bounds hmγ hmΛ hs
    have hDs : 0 ≤ photonD mγ Λ s := by
      unfold photonD
      have ha : 0 < s + mγ ^ 2 := by positivity
      have hb : s + mγ ^ 2 ≤ s + Λ ^ 2 := by nlinarith
      linarith [one_div_le_one_div_of_le ha hb]
    positivity
  have key : s ^ 2 * photonD mγ Λ s ^ 3 * (specJ M s * specJ M' s) ≤
      Λ ^ 2 / (225 * M ^ 2 * M' ^ 2) := by
    calc s ^ 2 * photonD mγ Λ s ^ 3 * (specJ M s * specJ M' s)
        ≤ s ^ 2 * photonD mγ Λ s ^ 3 * (s / (15 * M ^ 2) * (s / (15 * M' ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul j1 j1' j0' (j0.trans j1)) hD0
      _ = s ^ 4 * photonD mγ Λ s ^ 3 / (225 * M ^ 2 * M' ^ 2) := by
          field_simp
          ring
      _ ≤ Λ ^ 2 / (225 * M ^ 2 * M' ^ 2) := div_le_div_of_nonneg_right d1 (by positivity)
  have i0 : 0 ≤ s ^ 2 * photonD mγ Λ s ^ 3 * (specJ M s * specJ M' s) :=
    mul_nonneg hD0 (mul_nonneg j0 j0')
  unfold pairIntegrand
  dsimp only
  rw [← hsdef, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg x) i0),
    abs_of_nonneg (by positivity)]
  calc x ^ 2 * (s ^ 2 * photonD mγ Λ s ^ 3 * (specJ M s * specJ M' s))
      ≤ 1 * (Λ ^ 2 / (225 * M ^ 2 * M' ^ 2)) := mul_le_mul hx2 key i0 zero_le_one
    _ = Λ ^ 2 / (225 * M ^ 2 * M' ^ 2) := one_mul _

/-- **The flavour-pair expansion.** For `M₁, M₂ ≠ 0` and `0 < m_γ ≤ Λ`, `chainReg` is the sum
over the nine flavour pairs, with coefficients `c_f c_g` (`c₀ = 1`). -/
theorem chainReg_eq_sum_chainPair {M₁ M₂ mγ Λ : ℝ} (hM₁ : M₁ ≠ 0) (hM₂ : M₂ ≠ 0)
    (hmγ : 0 < mγ) (hmΛ : mγ ≤ Λ) :
    chainReg mγ Λ M₁ M₂ =
      ∑ f : Fin 3, ∑ g : Fin 3, heavyCoeff (pvC1 M₁ M₂) (pvC2 M₁ M₂) f *
        heavyCoeff (pvC1 M₁ M₂) (pvC2 M₁ M₂) g *
        chainPair (heavyMass 1 M₁ M₂ f) (heavyMass 1 M₁ M₂ g) mγ Λ := by
  have hm : ∀ f, heavyMass 1 M₁ M₂ f ≠ 0 := by
    intro f
    fin_cases f
    · exact one_ne_zero
    · exact hM₁
    · exact hM₂
  have hI : ∀ f g, IntervalIntegrable (pairIntegrand (heavyMass 1 M₁ M₂ f)
      (heavyMass 1 M₁ M₂ g) mγ Λ) volume 0 1 := fun f g =>
    intervalIntegrable_chainPair (hm f) (hm g) hmγ hmΛ
  have hJ : ∀ s, jSum M₁ M₂ s = ∑ f : Fin 3, heavyCoeff (pvC1 M₁ M₂) (pvC2 M₁ M₂) f *
      specJ (heavyMass 1 M₁ M₂ f) s := by
    intro s
    rw [Fin.sum_univ_three]
    simp only [heavyCoeff, heavyMass, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul, jSum, deltaM, add_assoc]
  set C := heavyCoeff (pvC1 M₁ M₂) (pvC2 M₁ M₂) with hC
  set m := heavyMass 1 M₁ M₂ with hmdef
  have hsq : ∀ s, jSum M₁ M₂ s ^ 2 = ∑ f : Fin 3, ∑ g : Fin 3, C f * specJ (m f) s *
      (C g * specJ (m g) s) := by
    intro s
    rw [hJ, sq, Finset.sum_mul_sum]
  have hpt : ∀ x, x ^ 2 * (photonVar x ^ 2 * photonD mγ Λ (photonVar x) ^ 3 *
      jSum M₁ M₂ (photonVar x) ^ 2) =
      ∑ f : Fin 3, ∑ g : Fin 3, C f * C g * pairIntegrand (m f) (m g) mγ Λ x := by
    intro x
    rw [hsq]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
    unfold pairIntegrand
    ring
  have hIg : ∀ f ∈ (Finset.univ : Finset (Fin 3)), IntervalIntegrable
      (fun x => ∑ g : Fin 3, C f * C g * pairIntegrand (m f) (m g) mγ Λ x) volume 0 1 := by
    intro f _
    have h := IntervalIntegrable.sum (μ := volume) (a := 0) (b := 1) Finset.univ
      (fun g _ => (hI f g).const_mul (C f * C g))
    rw [Finset.sum_fn] at h
    exact h
  unfold chainReg
  simp only [hpt]
  rw [intervalIntegral.integral_finsetSum hIg]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [intervalIntegral.integral_finsetSum fun g _ => (hI f g).const_mul _]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [intervalIntegral.integral_const_mul]
  rfl

end QED.Chain.ChainB
