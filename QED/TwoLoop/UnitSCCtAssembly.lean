/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCtIntegral
public import QED.TwoLoop.UnitSCCtTrace
public import QED.TwoLoop.UnitSCReduce
public import QED.TwoLoop.UnitSCCloseIR
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The `δ₂, δ_m` half of the unit `S`, from the pointwise second-order coefficient

Sections 5.2 and 7 of `docs/TWO-LOOP-UNITS.md`. The `δ₂, δ_m` half of the self-energy unit is
`sCtHalf P = (1/(64 m⁵)) (1/i) (d2InZero P + d2OutZero P)`
(`QED.TwoLoop.UnitSCReduce.sCtHalf`), with `d2InZero`, `d2OutZero` the `q → 0` values
`kindsZero` of the product data of the two classes
(`QED.TwoLoop.PauliZeroExplicit.d2InZero`): `(∫_{Δ₇} c₂[N(x, ·)]/V(x)⁴ dx) / auxLimit m`.

The second-order coefficient `c₂[N]` at a point `z` of the open simplex is (at `m = e = 1`)

`ctPoint(z) = -((Λ² - m_γ²)/16) (6 A(ξ) + V B(ξ)/X₁) / (X₁² X₂²)`,
`A(ξ) = -256 ξ² (ξ - 1) (δ₂ (ξ - 1) - δ_m)`, `B(ξ) = 512 (ξ - 1) (4 δ₂ ξ + 2 δ₂ - 3 δ_m)`

(`ctA`, `ctB`, `ctPoint`), for both classes, with `ξ = e/X₁` the electron share of the first loop.
This identity is the statement `D2Pointwise` below, proved for both classes in
`QED/TwoLoop/UnitSCCtJet.lean` and `QED/TwoLoop/UnitSCCtJetOut.lean` (the Dirac traces and the
`u`-jets of the Pauli-projected chain). This file proves:

* `auxLimit_eq`: `auxLimit M = i π² / (2 M²)`;
* `kindsV_d2In_eq`, `kindsV_d2Out_eq`: the second Symanzik function at `q = 0` is
  `ctV (m_γ²) (Λ²)`, `V = m_γ² z₃ + Λ² z₄ + X₂ + e²/X₁`;
* `ctLine_eq`: the one-dimensional integrand of `QED.TwoLoop.UnitSCCt.integral_ctG` for this
  `A, B` is `128/(Λ² - m_γ²)` times the Pauli–Villars difference of
  `δ₂ V_k-integrand + δ_m V_m-integrand` (`QED.TwoLoop.UnitSCClose.vkIntegrand`, `vmIntegrand`);
* `d2InZero_eq_of_pointwise`: `d2InZero P = -8 Δ / auxLimit 1`,
  `Δ = δ₂ (V_k(m_γ) - V_k(Λ)) + δ_m (V_m(m_γ) - V_m(Λ))`;
* **`sixteen_pi_pow_four_mul_sCtHalf_of_pointwise`**: at `m = 1`, `0 < m_γ < Λ`, for every
  `d₁ d₂ d_m d₃`, given the pointwise identity for `P₁ = atUnitCharge P d₁ d₂ d_m d₃`,
  `16π⁴ sCtHalf P₁ = 8π² (d₂ (V_k(m_γ) - V_k(Λ)) + d_m (V_m(m_γ) - V_m(Λ)))`.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.TwoLoop.UnitSCCt

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.UnitSCReduce QED.TwoLoop.UnitSCClose QED.TwoLoop.UnitLLink
open QED.TwoLoop.UnitsRegulated
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.ChengWu (openSimplex)
open QED.Integration.TwoLoop (castLoopMatrix symanzikV symanzikU symanzikMatrix symanzikVector)

/-! ### The auxiliary loop -/

/-- **The limit of the auxiliary loop**: `auxLimit M = i π² / (2 M²)`. -/
theorem auxLimit_eq {M : ℝ} (hM : 0 < M) : auxLimit M = I * (π : ℂ) ^ 2 / (2 * (M : ℂ) ^ 2) := by
  have hpt : ∀ v : Fin 3 → ℝ, auxSpatial M 0 v =
      (-((3 * π / 8 : ℂ) * Complex.exp (π * I * (-(5 / 2 : ℂ))))) *
        (((∑ k, v k ^ 2 + M ^ 2) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) := by
    intro v
    have ha : 0 < ∑ k, v k ^ 2 + M ^ 2 := by
      have h0 : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
      positivity
    have h1 : -((((∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - ((0 : ℝ) : ℂ) * I) =
        ((-(∑ k, v k ^ 2 + M ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [auxSpatial, h1, ofReal_cpow_of_nonpos (by linarith), ofReal_neg, neg_neg,
      ofReal_cpow ha.le]
    push_cast
    ring
  have hexp : Complex.exp (π * I * (-(5 / 2 : ℂ))) = -I := by
    have e : (π : ℂ) * I * (-(5 / 2 : ℂ)) = -(π / 2 * I) + -(2 * π * I) := by ring
    rw [e, Complex.exp_add, Complex.exp_neg, Complex.exp_neg, Complex.exp_pi_div_two_mul_I,
      Complex.exp_two_pi_mul_I, inv_one, mul_one, Complex.inv_I]
  rw [auxLimit]
  simp only [hpt]
  rw [integral_const_mul, integral_complex_ofReal,
    QED.Integration.integral_sum_sq_add_rpow_neg_five_halves (by positivity), hexp]
  have hM' : (M : ℂ) ≠ 0 := ofReal_ne_zero.mpr hM.ne'
  push_cast
  field_simp
  ring_nf

/-! ### The second Symanzik function -/

/-- The second Symanzik function of the product data of either class, at `q = 0`. -/
theorem symanzikV_kinds_eq (P : Params) (hm : P.m = 1) (κ : Fin 8 → LineKind)
    (hκ : κ = kindsD2In ∨ κ = kindsD2Out) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0) (hX2 : ctX2 z ≠ 0) :
    symanzikV (castLoopMatrix fun i => (κ i).dir)
        (fun i => (κ i).mom (restMomentum P.m) (restMomentum P.m)) (massesD2In P) z =
      ctV (P.mγ ^ 2) (P.Λ ^ 2) z := by
  unfold symanzikV
  simp only [inv_symanzikMatrix_kinds κ hκ, Fin.sum_univ_two]
  simp only [ctX1, ctX2] at hX1 hX2
  rcases hκ with rfl | rfl <;>
  · simp [Fin.sum_univ_eight, symanzikVector, castLoopMatrix, kindsD2In, kindsD2Out, massesD2In,
      LineKind.dir, LineKind.mom, restMomentum, hm, QED.Minkowski.dot_eq, ctV, ctE, ctX1, ctX2]
    field_simp
    ring

/-- **The second Symanzik function at `q = 0`, incoming class.** -/
theorem kindsV_d2In_eq (P : Params) (hm : P.m = 1) {x : Fin 7 → ℝ}
    (hX1 : ctX1 (simplexPoint x) ≠ 0) (hX2 : ctX2 (simplexPoint x) ≠ 0) :
    kindsV kindsD2In (massesD2In P) P x = ctV (P.mγ ^ 2) (P.Λ ^ 2) (simplexPoint x) :=
  symanzikV_kinds_eq P hm kindsD2In (Or.inl rfl) hX1 hX2

/-- **The second Symanzik function at `q = 0`, outgoing class.** -/
theorem kindsV_d2Out_eq (P : Params) (hm : P.m = 1) {x : Fin 7 → ℝ}
    (hX1 : ctX1 (simplexPoint x) ≠ 0) (hX2 : ctX2 (simplexPoint x) ≠ 0) :
    kindsV kindsD2Out (massesD2In P) P x = ctV (P.mγ ^ 2) (P.Λ ^ 2) (simplexPoint x) :=
  symanzikV_kinds_eq P hm kindsD2Out (Or.inr rfl) hX1 hX2

/-! ### The pointwise second-order coefficient -/

/-- `A(ξ) = -256 ξ² (ξ - 1) (δ₂ (ξ - 1) - δ_m)`. -/
def ctA (d₂ dm ξ : ℝ) : ℝ := -256 * ξ ^ 2 * (ξ - 1) * (d₂ * (ξ - 1) - dm)

/-- `B(ξ) = 512 (ξ - 1) (4 δ₂ ξ + 2 δ₂ - 3 δ_m)`. -/
def ctB (d₂ dm ξ : ℝ) : ℝ := 512 * (ξ - 1) * (4 * d₂ * ξ + 2 * d₂ - 3 * dm)

/-- **The pointwise second-order coefficient** of the `δ₂, δ_m` classes (`m = e = 1`):
`-((Λ² - m_γ²)/16) (6 A(ξ) + V B(ξ)/X₁) / (X₁² X₂²)`. -/
noncomputable def ctPoint (P : Params) (z : Fin 8 → ℝ) : ℝ :=
  -((P.Λ ^ 2 - P.mγ ^ 2) / 16) *
    (6 * ctA P.δ₂ P.δm (ctE z / ctX1 z) +
      ctV (P.mγ ^ 2) (P.Λ ^ 2) z * ctB P.δ₂ P.δm (ctE z / ctX1 z) / ctX1 z) /
    (ctX1 z ^ 2 * ctX2 z ^ 2)

/-- **The pointwise identity** (the Dirac-trace stage): on the open simplex, the second-order
coefficient of the projected numerator of the product data `(κ, massesD2In P, num)` is
`ctPoint P`. -/
def D2Pointwise (P : Params) (κ : Fin 8 → LineKind)
    (num : (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ x ∈ openSimplex 7,
    secondCoeff (kindsNum κ (massesD2In P) P num x) = (ctPoint P (simplexPoint x) : ℂ)

/-- The Pauli–Villars difference `Δ = δ₂ (V_k(m_γ) - V_k(Λ)) + δ_m (V_m(m_γ) - V_m(Λ))`. -/
noncomputable def ctDelta (P : Params) : ℝ :=
  P.δ₂ * (selfVk P.mγ - selfVk P.Λ) + P.δm * (selfVm P.mγ - selfVm P.Λ)

/-! ### The one-dimensional integrand -/

theorem ctPoint_div (P : Params) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0)
    (hV : ctV (P.mγ ^ 2) (P.Λ ^ 2) z ≠ 0) :
    ctPoint P z / ctV (P.mγ ^ 2) (P.Λ ^ 2) z ^ 4 =
      -((P.Λ ^ 2 - P.mγ ^ 2) / 16) *
        ctG (fun ξ => 6 * ctA P.δ₂ P.δm ξ) (ctB P.δ₂ P.δm) (P.mγ ^ 2) (P.Λ ^ 2) z := by
  unfold ctPoint ctG
  field_simp

/-- **The one-dimensional integrand** is the Pauli–Villars difference of the `δ₂, δ_m`
insertions. -/
theorem ctLine_eq (d₂ dm : ℝ) {mγ Λ x : ℝ} (hmγ : 0 < mγ) (hΛ : mγ < Λ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ctLine (fun ξ => 6 * ctA d₂ dm ξ) (ctB d₂ dm) (mγ ^ 2) (Λ ^ 2) x =
      128 / (Λ ^ 2 - mγ ^ 2) *
        ((d₂ * vkIntegrand mγ x + dm * vmIntegrand mγ x) -
          (d₂ * vkIntegrand Λ x + dm * vmIntegrand Λ x)) := by
  have hΛ0 : 0 < Λ := hmγ.trans hΛ
  have ha := ladderInnerMass_pos one_pos hmγ hx
  have hb := ladderInnerMass_pos one_pos hΛ0 hx
  have hab : Λ ^ 2 - mγ ^ 2 ≠ 0 := by
    have : mγ ^ 2 < Λ ^ 2 := pow_lt_pow_left₀ hΛ hmγ.le (by norm_num)
    linarith
  have hab' : mγ ^ 2 - Λ ^ 2 ≠ 0 := by
    intro h; exact hab (by linarith)
  unfold ladderInnerMass at ha hb
  unfold ctLine ctA ctB vkIntegrand vmIntegrand ladderInnerMass
  simp only [one_pow, mul_one] at ha hb ⊢
  have ha' := ha.ne'
  have hb' := hb.ne'
  rw [show x ^ 2 + (1 - x) * mγ ^ 2 = x ^ 2 + (1 - x) * mγ ^ 2 from rfl]
  field_simp
  ring

theorem integral_ctLine (d₂ dm : ℝ) {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : mγ < Λ) :
    ∫ x in (0 : ℝ)..1, ctLine (fun ξ => 6 * ctA d₂ dm ξ) (ctB d₂ dm) (mγ ^ 2) (Λ ^ 2) x =
      128 / (Λ ^ 2 - mγ ^ 2) *
        (d₂ * (selfVk mγ - selfVk Λ) + dm * (selfVm mγ - selfVm Λ)) := by
  have hΛ0 : 0 < Λ := hmγ.trans hΛ
  rw [intervalIntegral.integral_congr (g := fun x => 128 / (Λ ^ 2 - mγ ^ 2) *
      ((d₂ * vkIntegrand mγ x + dm * vmIntegrand mγ x) -
        (d₂ * vkIntegrand Λ x + dm * vmIntegrand Λ x)))
    (fun x hx => ctLine_eq d₂ dm hmγ hΛ (by rwa [uIcc_of_le zero_le_one] at hx))]
  have ka := intervalIntegrable_vkIntegrand hmγ
  have ma := intervalIntegrable_vmIntegrand hmγ
  have kb := intervalIntegrable_vkIntegrand hΛ0
  have mb := intervalIntegrable_vmIntegrand hΛ0
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub ((ka.const_mul d₂).add (ma.const_mul dm))
      ((kb.const_mul d₂).add (mb.const_mul dm)),
    intervalIntegral.integral_add (ka.const_mul d₂) (ma.const_mul dm),
    intervalIntegral.integral_add (kb.const_mul d₂) (mb.const_mul dm),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [selfVk, selfVm]
  ring

/-! ### The `q → 0` values of the two classes -/

/-- **The `q → 0` value of either `δ₂, δ_m` class from the pointwise identity** (`m = 1`,
`0 < m_γ < Λ`): `kindsZero = -8 Δ / auxLimit 1`. -/
theorem kindsZero_eq_of_pointwise (P : Params) (hm : P.m = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ)
    (κ : Fin 8 → LineKind) (hκ : κ = kindsD2In ∨ κ = kindsD2Out)
    (num : (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hnum : κ = kindsD2In → num = fun p' μ k => numD2In P p' (restMomentum P.m) μ k)
    (hpt : D2Pointwise P κ num) :
    kindsZero κ (massesD2In P) P num = ((-8 * ctDelta P : ℝ) : ℂ) / auxLimit 1 := by
  have _ := hnum
  have hΛ0 : 0 < P.Λ := hmγ.trans hΛ
  have ha : 0 < P.mγ ^ 2 := by positivity
  have hb : 0 < P.Λ ^ 2 := by positivity
  have hab : P.mγ ^ 2 ≠ P.Λ ^ 2 := (pow_lt_pow_left₀ hΛ hmγ.le (by norm_num)).ne
  have hcont6 : Continuous fun ξ => 6 * ctA P.δ₂ P.δm ξ := by unfold ctA; fun_prop
  have hcontB : Continuous (ctB P.δ₂ P.δm) := by unfold ctB; fun_prop
  obtain ⟨-, hI⟩ := integral_ctG hcont6 hcontB ha hb hab
  unfold kindsZero
  rw [hm]
  congr 1
  have hae : (fun x => secondCoeff (kindsNum κ (massesD2In P) P num x) /
      ((kindsV κ (massesD2In P) P x : ℝ) : ℂ) ^ (7 - 3)) =ᵐ[volume.restrict (simplexSet 7)]
      fun x => ((-((P.Λ ^ 2 - P.mγ ^ 2) / 16) *
        ctG (fun ξ => 6 * ctA P.δ₂ P.δm ξ) (ctB P.δ₂ P.δm) (P.mγ ^ 2) (P.Λ ^ 2)
          (simplexPoint x) : ℝ) : ℂ) := by
    filter_upwards [ae_mem_openSimplex' (by norm_num : 0 < 7)] with x hx
    have hz := simplexPoint_pos_of_mem_openSimplex' hx
    have hz1 := sum_simplexPoint x
    have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
    have h4 := hz 4; have h5 := hz 5; have h6 := hz 6; have h7 := hz 7
    have hX1 : ctX1 (simplexPoint x) ≠ 0 := by unfold ctX1; positivity
    have hX2 : ctX2 (simplexPoint x) ≠ 0 := by unfold ctX2; positivity
    have hV := lt_of_lt_of_le (by have := lt_min ha (lt_min hb one_pos); positivity)
      (le_ctV ha hb hz hz1)
    have hkV : kindsV κ (massesD2In P) P x = ctV (P.mγ ^ 2) (P.Λ ^ 2) (simplexPoint x) := by
      rcases hκ with rfl | rfl
      · exact kindsV_d2In_eq P hm hX1 hX2
      · exact kindsV_d2Out_eq P hm hX1 hX2
    rw [hpt x hx, hkV, ← ctPoint_div P hX1 hV.ne']
    push_cast
    rfl
  rw [integral_congr_ae hae, integral_complex_ofReal, integral_const_mul, hI,
    integral_ctLine P.δ₂ P.δm hmγ hΛ]
  have hab' : ((P.Λ : ℂ) ^ 2 - (P.mγ : ℂ) ^ 2) ≠ 0 := by
    have : P.Λ ^ 2 - P.mγ ^ 2 ≠ 0 := sub_ne_zero.mpr hab.symm
    exact_mod_cast this
  unfold ctDelta
  push_cast
  field_simp
  ring

/-- **The `δ₂, δ_m` class on the incoming line from the pointwise identity.** -/
theorem d2InZero_eq_of_pointwise (P : Params) (hm : P.m = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ)
    (hpt : D2Pointwise P kindsD2In fun p' μ k => numD2In P p' (restMomentum P.m) μ k) :
    d2InZero P = ((-8 * ctDelta P : ℝ) : ℂ) / auxLimit 1 :=
  kindsZero_eq_of_pointwise P hm hmγ hΛ kindsD2In (Or.inl rfl) _ (fun _ => rfl) hpt

/-- **The `δ₂, δ_m` class on the outgoing line from the pointwise identity.** -/
theorem d2OutZero_eq_of_pointwise (P : Params) (hm : P.m = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ)
    (hpt : D2Pointwise P kindsD2Out fun p' μ k => numD2Out P p' (restMomentum P.m) μ k) :
    d2OutZero P = ((-8 * ctDelta P : ℝ) : ℂ) / auxLimit 1 :=
  kindsZero_eq_of_pointwise P hm hmγ hΛ kindsD2Out (Or.inr rfl) _
    (fun h => absurd h (by decide)) hpt

/-! ### The `δ₂, δ_m` half of the unit `S` -/

/-- **The `δ₂, δ_m` half of the unit `S`, from the pointwise identity** (`m = 1`,
`0 < m_γ < Λ`, any `d₁ d₂ d_m d₃`, `P₁ = atUnitCharge P d₁ d₂ d_m d₃`):
`16π⁴ sCtHalf P₁ = 8π² (d₂ (V_k(m_γ) - V_k(Λ)) + d_m (V_m(m_γ) - V_m(Λ)))`. -/
theorem sixteen_pi_pow_four_mul_sCtHalf_of_pointwise (P : Params) (hm : P.m = 1)
    (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) (d₁ d₂ dm d₃ : ℝ)
    (hIn : D2Pointwise (atUnitCharge P d₁ d₂ dm d₃) kindsD2In
      fun p' μ k => numD2In (atUnitCharge P d₁ d₂ dm d₃) p' (restMomentum P.m) μ k)
    (hOut : D2Pointwise (atUnitCharge P d₁ d₂ dm d₃) kindsD2Out
      fun p' μ k => numD2Out (atUnitCharge P d₁ d₂ dm d₃) p' (restMomentum P.m) μ k) :
    16 * (π : ℂ) ^ 4 * sCtHalf (atUnitCharge P d₁ d₂ dm d₃) =
      ((8 * π ^ 2 * (d₂ * (selfVk P.mγ - selfVk P.Λ) + dm * (selfVm P.mγ - selfVm P.Λ)) : ℝ) :
        ℂ) := by
  have hIn' := d2InZero_eq_of_pointwise (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ hIn
  have hOut' := d2OutZero_eq_of_pointwise (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ hOut
  have hm' : (atUnitCharge P d₁ d₂ dm d₃).m = 1 := hm
  unfold sCtHalf
  rw [hIn', hOut', hm', auxLimit_eq one_pos]
  simp only [ctDelta, atUnitCharge]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end QED.TwoLoop.UnitSCCt

end
