/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSIdent
public import QED.ChainProof.SetAPauliAssemblyR
import QED.Chain.SetAValue
import QED.Frozen.Graded.VacuumPolarizationPartTwoLeptonLimit

/-!
# The set (a) regulator limit at the photon function `setAR`

Helper level for (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`
(`QED/Frozen/ThreeLoop/VertexSetAPauliLimit.lean`, `DRAFT_SORRY`, not imported). It proves the
regulator limit `SetARegLimitPV (setAPauliValue P₀ (setAR P₀))` of
`QED/ChainProof/SetAPauliAssembly.lean`, conditional only on the two open Källén–Sabry inputs
`DecFaceGen e` (R-Π₄) and `SetAKSScal e` of `QED/ChainProof/SetAKSIdent.lean`.

At fixed regulators the value is (`setAPauliValue_setAR_eq`, `integrand_sub_eq`)
`a = 16π⁴ ∫₀¹ (1 - y) Re(Pol(K)/e⁴) (K D(K))² dy`, `K = m² y²/(1-y)`,
with `Pol = setAPol` the fixed-regulator form factor and `D` the Pauli–Villars photon factor. The
sealed anchor (R-Π₄) `QED.Graded.vacuumPolarizationPart_two_lepton_limit` gives a limit `Π_∞`
and a majorant `C (1 + log(1 + s/m²))²`; both clauses hold for `setAPol` over distinct regulator
masses (`setAPol_body`), and the majorant passes to `Π_∞` (`norm_pinf_le`). Under the
Källén–Sabry inputs `16π⁴ Π_∞(s) = Π̂⁽⁴⁾(s/m²)`
(`QED.ChainProof.SetAKS.setAKS_pinf_eq_of_nonneg`), and
`∫₀¹ (1 - y) Π̂⁽⁴⁾(y²/(1-y)) dy = A₁⁽⁶⁾(a)` (`QED.Chain.integral_setA_eq_aSetA`, `setA_integral`).

The bridge splits `[0, 1]` into `(0, y₀]`, `(y₀, 1 - y₀]`, `(1 - y₀, 1]`
(`abs_integral_le_three`): on the outer pieces both integrands are bounded by
`160 π⁴ |C|`, since `(1 - y)(1 + log(1 + y²/(1-y)))² ≤ 10` (`one_sub_mul_log_sq_le`); on the middle
piece `K` ranges over a compact interval of `(0, ∞)`, where `Pol/e⁴ → Π_∞` uniformly and
`K D(K) → 1` (`one_sub_mul_photonD_le`).

## Main statements

* `setARegLimitPV_setAR`: `DecFaceGen e → SetAKSScal e →
  SetARegLimitPV (setAPauliValue P₀ (setAR P₀))`, for `e ≠ 0`, `m > 0`.
* `isFormFactorPair_vertexSetA_pauli_limit_of_N_KS`: the proposition of (HA₆) from obligation
  (N) `SetANestClasses P₀` and the two Källén–Sabry inputs.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetARegLim

open QED.TwoLoop.UnitVPLink
open QED.ChainProof.SetAKS QED.ChainProof.SetANestedAt QED.ChainProof.SetAPauli

/-! ### Real-variable estimates -/

/-- `(1-y)(1 + log(1 + y²/(1-y)))² ≤ 10` on `[0, 1)`. -/
theorem one_sub_mul_log_sq_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    (1 - y) * (1 + Real.log (1 + y ^ 2 / (1 - y))) ^ 2 ≤ 10 := by
  set t := 1 - y with ht
  have ht0 : 0 < t := by linarith
  have ht1 : t ≤ 1 := by linarith
  have hv : 1 + y ^ 2 / t ≤ 1 / t := by
    have e : 1 / t - (1 + y ^ 2 / t) = (y - y ^ 2) / t := by
      rw [ht]; field_simp; ring
    have : 0 ≤ (y - y ^ 2) / t := div_nonneg (by nlinarith) ht0.le
    linarith
  have hv0 : 0 < 1 + y ^ 2 / t := by positivity
  have hL0 : 0 ≤ Real.log (1 + y ^ 2 / t) :=
    Real.log_nonneg (by have : 0 ≤ y ^ 2 / t := by positivity
                        linarith)
  have hL : Real.log (1 + y ^ 2 / t) ≤ -Real.log t := by
    rw [← Real.log_inv, ← one_div]
    exact Real.log_le_log hv0 hv
  -- `t log² t < 4` via `√t |log √t| < 1`
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.2 ht1
  have hk := Real.abs_log_mul_self_lt _ hs0 hs1
  have hlog : Real.log (Real.sqrt t) = Real.log t / 2 := by
    rw [Real.log_sqrt ht0.le]
  rw [hlog] at hk
  have hk2 : (Real.log t / 2 * Real.sqrt t) ^ 2 < 1 := by
    have := abs_lt.1 hk
    nlinarith [abs_nonneg (Real.log t / 2 * Real.sqrt t)]
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have htl : t * Real.log t ^ 2 < 4 := by
    have : (Real.log t / 2 * Real.sqrt t) ^ 2 = t * Real.log t ^ 2 / 4 := by
      rw [mul_pow, hsq]; ring
    rw [this] at hk2
    linarith
  set L := Real.log (1 + y ^ 2 / t)
  have hLL : L ^ 2 ≤ Real.log t ^ 2 := by nlinarith
  have hL1 : t * L ^ 2 ≤ 4 := by nlinarith
  have : (1 + L) ^ 2 ≤ 2 + 2 * L ^ 2 := by nlinarith [sq_nonneg (1 - L)]
  nlinarith

/-- **The three-piece estimate**: a function on `[0, 1]` bounded by `B` on `(0, 1]` and by `b` on
`(y₀, y₁]` has integral at most `B y₀ + b (y₁ - y₀) + B (1 - y₁)`. -/
theorem abs_integral_le_three {H : ℝ → ℝ} {B b y₀ y₁ : ℝ} (hy₀ : 0 ≤ y₀) (h01 : y₀ ≤ y₁)
    (hy₁ : y₁ ≤ 1) (hH : IntervalIntegrable H volume 0 1)
    (hout : ∀ y ∈ Ioc (0 : ℝ) 1, |H y| ≤ B) (hmid : ∀ y ∈ Ioc y₀ y₁, |H y| ≤ b) :
    |∫ y in (0 : ℝ)..1, H y| ≤ B * y₀ + b * (y₁ - y₀) + B * (1 - y₁) := by
  have i1 : IntervalIntegrable H volume 0 y₀ :=
    hH.mono_set (uIcc_subset_uIcc (by simp) (by simp [hy₀, h01.trans hy₁]))
  have i2 : IntervalIntegrable H volume y₀ y₁ :=
    hH.mono_set (uIcc_subset_uIcc (by simp [hy₀, h01.trans hy₁]) (by simp [hy₀.trans h01, hy₁]))
  have i3 : IntervalIntegrable H volume y₁ 1 :=
    hH.mono_set (uIcc_subset_uIcc (by simp [hy₀.trans h01, hy₁]) (by simp))
  rw [← intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3,
    ← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  have e1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := y₀) (C := B)
    (f := H) fun y hy => by
      rw [uIoc_of_le hy₀] at hy
      exact hout y ⟨hy.1, hy.2.trans (h01.trans hy₁)⟩
  have e2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := y₀) (b := y₁) (C := b)
    (f := H) fun y hy => by
      rw [uIoc_of_le h01] at hy
      exact hmid y hy
  have e3 := intervalIntegral.norm_integral_le_of_norm_le_const (a := y₁) (b := 1) (C := B)
    (f := H) fun y hy => by
      rw [uIoc_of_le hy₁] at hy
      exact hout y ⟨(hy₀.trans h01).trans_lt hy.1, hy.2⟩
  simp only [Real.norm_eq_abs] at e1 e2 e3
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y₀ - 0), abs_of_nonneg (by linarith : 0 ≤ y₁ - y₀),
    abs_of_nonneg (by linarith : 0 ≤ 1 - y₁)] at *
  calc _ ≤ |(∫ y in (0 : ℝ)..y₀, H y) + ∫ y in y₀..y₁, H y| + |∫ y in y₁..1, H y| :=
        abs_add_le _ _
    _ ≤ |∫ y in (0 : ℝ)..y₀, H y| + |∫ y in y₀..y₁, H y| + |∫ y in y₁..1, H y| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by rw [sub_zero] at e1; linarith


/-! ### (R-Π₄) at the fixed-regulator form factor -/

/-- **The body of (R-Π₄) at the fixed-regulator form factor `setAPol`**: over distinct regulator
masses, the limit and majorant clauses of (R-Π₄) hold for `setAPol` itself, with admissible
photon regulators (`m_γ < Λ`). -/
theorem setAPol_body {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m) {mH : Fin 0 → ℝ}
    {Pinf : ℝ → ℂ} {C : ℝ} (hB : RPi4Body P₀ mH Pinf C) {S₀ S η : ℝ}
    (hS₀ : -(4 * P₀.m ^ 2) < S₀) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ : ℝ, RM < M₁ → RM < M₂ → M₁ ≠ M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → Λ₀ < Λ → mγ < Λ ∧
        (∀ s, S₀ ≤ s → s ≤ S →
          ‖setAPol P₀ mγ Λ M₁ M₂ s / (P₀.e : ℂ) ^ 4 - Pinf s‖ < η) ∧
        ∀ s, 0 ≤ s → ‖setAPol P₀ mγ Λ M₁ M₂ s / (P₀.e : ℂ) ^ 4‖ ≤
          C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2 := by
  obtain ⟨RM, hRM⟩ := hB S₀ S η hS₀ hη
  refine ⟨max RM P₀.m, fun M₁ M₂ h₁ h₂ hne => ?_⟩
  have hM₁ : P₀.m < M₁ := (le_max_right _ _).trans_lt h₁
  have hM₂ : P₀.m < M₂ := (le_max_right _ _).trans_lt h₂
  have hR₁ : RM < M₁ := (le_max_left _ _).trans_lt h₁
  have hR₂ : RM < M₂ := (le_max_left _ _).trans_lt h₂
  have hsq : M₁ ^ 2 - M₂ ^ 2 ≠ 0 := by
    intro h
    have h' : (M₁ - M₂) * (M₁ + M₂) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h' | h'
    · exact hne (by linarith)
    · linarith
  set c₁ := pvC₁ P₀.m M₁ M₂
  have hc₁ := pvC_sum P₀.m M₁ M₂
  have hc₂ := pvC_mass (m := P₀.m) hsq
  obtain ⟨δ, hδ, R, hR⟩ := hRM M₁ M₂ c₁ (-1 - c₁) hM₁ hM₂ hR₁ hR₂ hc₁ hc₂ mH mH mH mH
    (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0)
    (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0)
  have h2m : 0 < 2 * P₀.m := by linarith
  refine ⟨min δ (2 * P₀.m), lt_min hδ h2m, max R (min δ (2 * P₀.m)),
    fun mγ Λ h0 h1 h2 => ?_⟩
  have hmΛ : mγ < Λ := h1.trans ((le_max_right _ _).trans_lt h2)
  have hΛ : 0 < Λ := h0.trans hmΛ
  have hfun : (fun ℓ : Fin 0 => (⟨mH ℓ, mH ℓ, mH ℓ, mH ℓ, mH ℓ⟩ : Lepton.HeavyLepton)) =
      Fin.elim0 := funext fun ℓ => ℓ.elim0
  obtain ⟨⟨D, hD⟩, hall⟩ := hR mγ Λ h0 hΛ (h1.trans_le (min_le_left _ _))
    ((le_max_left _ _).trans_lt h2)
  rw [hfun] at hD hall
  have hA : SetAAdm P₀ M₁ M₂ c₁ (-1 - c₁) mγ Λ D :=
    ⟨hM₁, hM₂, hc₁, hc₂, h0, hΛ, hmΛ, h1.trans_le (min_le_right _ _), hD⟩
  obtain ⟨Pol, hPol⟩ := exists_isPol hm hA
  obtain ⟨hlim, hmaj⟩ := (hall D hD).2 Pol hPol
  refine ⟨hmΛ, fun s hs₀ hs => ?_, fun s hs => ?_⟩
  · rw [setAPol_eq he hm hA hPol (hS₀.trans_le hs₀)]
    exact hlim s hs₀ hs
  · rw [setAPol_eq he hm hA hPol (by nlinarith)]
    exact hmaj s hs

/-- **The limit `Π_∞` of (R-Π₄) obeys the majorant** on `s ≥ 0`. -/
theorem norm_pinf_le {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m) {mH : Fin 0 → ℝ}
    {Pinf : ℝ → ℂ} {C : ℝ} (hB : RPi4Body P₀ mH Pinf C) {s : ℝ} (hs : 0 ≤ s) :
    ‖Pinf s‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2 := by
  refine le_of_forall_pos_lt_add fun η hη => ?_
  obtain ⟨RM, hRM⟩ := setAPol_body he hm hB (S₀ := s) (S := s) (by nlinarith) hη
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hRM (|RM| + 1) (|RM| + 2) (by linarith [le_abs_self RM])
    (by linarith [le_abs_self RM]) (by linarith)
  obtain ⟨-, h1, h2⟩ := hΛ₀ (δ / 2) (|Λ₀| + 1) (by positivity) (by linarith)
    (by linarith [le_abs_self Λ₀])
  have a := h1 s le_rfl le_rfl
  have b := h2 s hs
  have := norm_sub_le_norm_sub_add_norm_sub (Pinf s)
    (setAPol P₀ (δ / 2) (|Λ₀| + 1) (|RM| + 1) (|RM| + 2) s / (P₀.e : ℂ) ^ 4) 0
  rw [norm_sub_rev] at a
  simp only [sub_zero] at this
  linarith


/-! ### The photon factor `K D(K)` -/

theorem mul_photonD_mem {mγ Λ K : ℝ} (hmγ : 0 < mγ) (hmΛ : mγ < Λ) (hK : 0 < K) :
    0 ≤ K * photonD mγ Λ K ∧ K * photonD mγ Λ K ≤ 1 ∧
      1 - K * photonD mγ Λ K ≤ mγ ^ 2 / K + K / Λ ^ 2 := by
  have hΛ : 0 < Λ := hmγ.trans hmΛ
  have e : 1 - K * photonD mγ Λ K = mγ ^ 2 / (K + mγ ^ 2) + K / (K + Λ ^ 2) := by
    unfold photonD
    field_simp
    ring
  have h1 : mγ ^ 2 / (K + mγ ^ 2) ≤ mγ ^ 2 / K :=
    div_le_div_of_nonneg_left (by positivity) hK (by nlinarith)
  have h2 : K / (K + Λ ^ 2) ≤ K / Λ ^ 2 :=
    div_le_div_of_nonneg_left hK.le (by positivity) (by nlinarith)
  have h3 : 0 ≤ mγ ^ 2 / (K + mγ ^ 2) + K / (K + Λ ^ 2) := by positivity
  refine ⟨mul_nonneg hK.le (QED.ChainProof.HCValue.photonD_nonneg hmγ hmΛ.le hK.le), ?_, ?_⟩
  · linarith
  · linarith

/-! ### Pointwise bounds -/

theorem abs_out_le {P Q w y C : ℝ} (hy0 : 0 ≤ 1 - y) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hP : (1 - y) * |P| ≤ C) (hQ : (1 - y) * |Q| ≤ C) :
    |(1 - y) * (P * w ^ 2 - Q)| ≤ 2 * C := by
  have hw2 : w ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
  rw [abs_mul, abs_of_nonneg hy0]
  have : |P * w ^ 2 - Q| ≤ |P| + |Q| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg w)]
    nlinarith [abs_nonneg P]
  nlinarith

theorem abs_mid_le {P Q w y C η₁ ε₁ : ℝ} (hy0 : 0 ≤ 1 - y) (hy1 : 1 - y ≤ 1) (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) (hQ : (1 - y) * |Q| ≤ C) (hPQ : |P - Q| ≤ η₁) (hwε : 1 - w ≤ ε₁) :
    |(1 - y) * (P * w ^ 2 - Q)| ≤ η₁ + 2 * C * ε₁ := by
  have hw2 : w ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
  have e : (1 - y) * (P * w ^ 2 - Q) = (1 - y) * (P - Q) * w ^ 2 - (1 - y) * Q * (1 - w ^ 2) := by
    ring
  have h1w : 1 - w ^ 2 ≤ 2 * ε₁ := by nlinarith
  have h1w0 : 0 ≤ 1 - w ^ 2 := by linarith
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hy0, abs_of_nonneg (sq_nonneg w),
    abs_of_nonneg h1w0]
  have hC : 0 ≤ C := (mul_nonneg hy0 (abs_nonneg Q)).trans hQ
  have a1 : (1 - y) * |P - Q| * w ^ 2 ≤ η₁ := by
    have : (1 - y) * |P - Q| ≤ |P - Q| := mul_le_of_le_one_left (abs_nonneg _) hy1
    nlinarith [abs_nonneg (P - Q), mul_nonneg hy0 (abs_nonneg (P - Q))]
  have a2 : (1 - y) * |Q| * (1 - w ^ 2) ≤ C * (2 * ε₁) :=
    mul_le_mul hQ h1w h1w0 hC
  linarith

/-! ### The fixed-regulator value as an integral -/

/-- `a = ∫₀¹ (16π⁴ m²/e⁴) y² R(m² y²/(1-y)) dy` at the photon function `setAR`. -/
theorem setAPauliValue_setAR_eq {P₀ : Params} (he : P₀.e ≠ 0) (mγ Λ M₁ M₂ : ℝ) :
    setAPauliValue P₀ (setAR P₀) mγ Λ M₁ M₂ = ∫ y in (0 : ℝ)..1,
      16 * π ^ 4 * P₀.m ^ 2 / P₀.e ^ 4 *
        (y ^ 2 * setAR P₀ mγ Λ M₁ M₂ (P₀.m ^ 2 * photonVar y)) := by
  rw [intervalIntegral.integral_const_mul]
  unfold setAPauliValue
  rw [QED.ChainProof.HCValue.outerAt_zero]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The integrand difference on `(0, 1)`. -/
theorem integrand_sub_eq {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m) {mγ Λ M₁ M₂ y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    16 * π ^ 4 * P₀.m ^ 2 / P₀.e ^ 4 *
        (y ^ 2 * setAR P₀ mγ Λ M₁ M₂ (P₀.m ^ 2 * photonVar y)) -
      (1 - y) * QED.Chain.piHat4 (y ^ 2 / (1 - y)) =
    (1 - y) * (16 * π ^ 4 * (setAPol P₀ mγ Λ M₁ M₂ (P₀.m ^ 2 * photonVar y) /
        (P₀.e : ℂ) ^ 4).re * (P₀.m ^ 2 * photonVar y * photonD mγ Λ (P₀.m ^ 2 * photonVar y)) ^ 2 -
      QED.Chain.piHat4 (y ^ 2 / (1 - y))) := by
  have h1 : 1 - y ≠ 0 := by linarith [hy.2]
  have hK : 0 < P₀.m ^ 2 * photonVar y := by
    unfold photonVar
    have : 0 < 1 - y := by linarith [hy.2]
    have := hy.1
    positivity
  simp only [setAR, hK, ↓reduceIte]
  rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
  unfold photonVar
  field_simp

/-! ### The pointwise bounds at fixed regulators -/

/-- The photon variable `K = m² y²/(1-y)`. -/
noncomputable def kY (m y : ℝ) : ℝ := m ^ 2 * photonVar y

theorem kY_pos {m y : ℝ} (hm : 0 < m) (hy : y ∈ Ioo (0 : ℝ) 1) : 0 < kY m y := by
  have : 0 < 1 - y := by linarith [hy.2]
  have := hy.1
  unfold kY photonVar
  positivity

theorem kY_div {m y : ℝ} (hm : 0 < m) : kY m y / m ^ 2 = y ^ 2 / (1 - y) := by
  unfold kY photonVar
  field_simp

/-- On `(y₀, 1 - y₀]`: `m² y₀² ≤ K ≤ m²/y₀`. -/
theorem kY_mem {m y y₀ : ℝ} (hm : 0 < m) (hy₀ : 0 < y₀) (hy : y ∈ Ioc y₀ (1 - y₀)) :
    m ^ 2 * y₀ ^ 2 ≤ kY m y ∧ kY m y ≤ m ^ 2 / y₀ := by
  obtain ⟨hya, hyb⟩ := hy
  have hy1 : y₀ ≤ 1 - y := by linarith
  have hy0 : 0 < 1 - y := hy₀.trans_le hy1
  have hm2 : 0 < m ^ 2 := by positivity
  have hyy : y₀ ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hy₀.le hya.le 2
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  unfold kY photonVar
  rw [mul_div_assoc']
  refine ⟨?_, div_le_div₀ hm2.le (by nlinarith) hy₀ hy1⟩
  rw [le_div_iff₀ hy0]
  have : y₀ ^ 2 * (1 - y) ≤ y ^ 2 := by nlinarith
  nlinarith

/-- `(1 - y) |16π⁴ Re(z)| ≤ 160 π⁴ |C|` from the majorant `‖z‖ ≤ C (1 + log(1 + K/m²))²`. -/
theorem one_sub_mul_abs_le {m y C : ℝ} {z : ℂ} (hm : 0 < m) (hy : y ∈ Ioo (0 : ℝ) 1)
    (hz : ‖z‖ ≤ C * (1 + Real.log (1 + kY m y / m ^ 2)) ^ 2) :
    (1 - y) * |16 * π ^ 4 * z.re| ≤ 16 * π ^ 4 * (10 * |C|) := by
  have hlog := one_sub_mul_log_sq_le hy.1.le hy.2
  rw [← kY_div hm] at hlog
  have hy1 : 0 ≤ 1 - y := by linarith [hy.2]
  have hc : 0 < 16 * π ^ 4 := by positivity
  have h1 : |16 * π ^ 4 * z.re| ≤
      16 * π ^ 4 * (|C| * (1 + Real.log (1 + kY m y / m ^ 2)) ^ 2) := by
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm z).trans (hz.trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)))) hc.le
  calc (1 - y) * |16 * π ^ 4 * z.re| ≤
        (1 - y) * (16 * π ^ 4 * (|C| * (1 + Real.log (1 + kY m y / m ^ 2)) ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 hy1
    _ = 16 * π ^ 4 * |C| * ((1 - y) * (1 + Real.log (1 + kY m y / m ^ 2)) ^ 2) := by ring
    _ ≤ 16 * π ^ 4 * |C| * 10 := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 16 * π ^ 4 * (10 * |C|) := by ring

/-- `1 - K D(K) ≤ ε₁` on `[K₀, K₁]` once `m_γ < 1`, `m_γ < ε₁ K₀/2`, `Λ > 1` and
`Λ > 2K₁/ε₁`. -/
theorem one_sub_mul_photonD_le {mγ Λ K K₀ K₁ ε₁ : ℝ} (hmγ : 0 < mγ) (hmΛ : mγ < Λ)
    (hK₀ : 0 < K₀) (hK0 : K₀ ≤ K) (hK1 : K ≤ K₁) (hε : 0 < ε₁) (hmγ1 : mγ < 1)
    (hmγε : mγ < ε₁ * K₀ / 2) (hΛ1 : 1 < Λ) (hΛK : 2 * K₁ / ε₁ < Λ) :
    1 - K * photonD mγ Λ K ≤ ε₁ := by
  have hK : 0 < K := hK₀.trans_le hK0
  have hw := (mul_photonD_mem hmγ hmΛ hK).2.2
  have a1 : mγ ^ 2 / K ≤ mγ ^ 2 / K₀ := div_le_div_of_nonneg_left (by positivity) hK₀ hK0
  have a2 : mγ ^ 2 / K₀ < ε₁ / 2 := by
    rw [div_lt_iff₀ hK₀]
    nlinarith
  have a3 : K / Λ ^ 2 ≤ K₁ / Λ ^ 2 := div_le_div_of_nonneg_right hK1 (by positivity)
  have a4 : K₁ / Λ ^ 2 < ε₁ / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hΛK
    nlinarith
  linarith

/-- The closing arithmetic. -/
theorem three_lt {C' η y₀ ε₁ : ℝ} (hC' : 0 ≤ C') (hη : 0 < η) (hy₀ : 0 < y₀)
    (hy₀η : y₀ * (8 * (2 * C' + 1)) ≤ η) (hε : ε₁ = η / (16 * (2 * C' + 1))) :
    2 * C' * y₀ + (η / 8 + 2 * C' * ε₁) * (1 - y₀ - y₀) + 2 * C' * (1 - (1 - y₀)) < η := by
  have hA0 : 0 < 2 * C' + 1 := by positivity
  have hε0 : 0 < ε₁ := by rw [hε]; positivity
  have hAε : (2 * C' + 1) * ε₁ = η / 16 := by rw [hε]; field_simp
  have t1 : 4 * C' * y₀ ≤ η / 4 := by nlinarith
  have t2 : 2 * C' * ε₁ ≤ η / 16 := by nlinarith
  have hb : 0 ≤ η / 8 + 2 * C' * ε₁ := by positivity
  have t3 : (η / 8 + 2 * C' * ε₁) * (1 - y₀ - y₀) ≤ η / 8 + 2 * C' * ε₁ := by nlinarith
  nlinarith

/-! ### The regulator limit -/

/-- The set (a) integral `∫₀¹ (1 - y) Π̂⁽⁴⁾(y²/(1-y)) dy` is `A₁⁽⁶⁾(a)`, and its integrand is
interval integrable (the integral is nonzero). -/
theorem setA_integral :
    IntervalIntegrable (fun y => (1 - y) * QED.Chain.piHat4 (y ^ 2 / (1 - y))) volume 0 1 ∧
      ∫ y in (0 : ℝ)..1, (1 - y) * QED.Chain.piHat4 (y ^ 2 / (1 - y)) =
        ThreeLoop.a1SixSetA := by
  have hval : ∫ y in (0 : ℝ)..1, (1 - y) * QED.Chain.piHat4 (y ^ 2 / (1 - y)) =
      ThreeLoop.a1SixSetA := QED.Chain.integral_setA_eq_aSetA
  have hpos : (0.05287065247 : ℝ) < ThreeLoop.a1SixSetA := QED.Chain.aSetA_bounds.1
  refine ⟨?_, hval⟩
  by_contra h
  rw [intervalIntegral.integral_undef h] at hval
  linarith

/-- The regulated integrand is interval integrable. -/
theorem intervalIntegrable_setAR {P₀ : Params} (hm : 0 < P₀.m) {mγ Λ M₁ M₂ : ℝ}
    (hM₁ : P₀.m < M₁) (hM₂ : P₀.m < M₂) (h0 : 0 < mγ) (hmΛ : mγ < Λ) (a : ℝ) :
    IntervalIntegrable (fun y => a * (y ^ 2 * setAR P₀ mγ Λ M₁ M₂ (P₀.m ^ 2 * photonVar y)))
      volume 0 1 := by
  obtain ⟨hRmeas, -, CR, hCR⟩ := setAPhotonReg hm M₁ M₂ mγ Λ hM₁ hM₂ h0 hmΛ
  have hv : Measurable photonVar := by unfold photonVar; fun_prop
  have hmeas : Measurable fun y => a * (y ^ 2 * setAR P₀ mγ Λ M₁ M₂ (P₀.m ^ 2 * photonVar y)) :=
    measurable_const.mul ((measurable_id.pow_const 2).mul (hRmeas.comp (measurable_const.mul hv)))
  refine (intervalIntegrable_const (c := |a| * CR)).mono_fun hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun y hy => ?_)
  rw [uIoc_of_le zero_le_one] at hy
  have hK : 0 ≤ P₀.m ^ 2 * photonVar y := by
    unfold photonVar
    rcases hy.2.lt_or_eq with h | h
    · have : 0 < 1 - y := by linarith
      positivity
    · simp [h]
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  simp only [Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg y)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := hCR _ hK
  have h0' := abs_nonneg (setAR P₀ mγ Λ M₁ M₂ (P₀.m ^ 2 * photonVar y))
  nlinarith

/-- **The set (a) regulator limit at `setAR`, conditional on the Källén–Sabry inputs**
`DecFaceGen e` (R-Π₄) and `SetAKSScal e`: `SetARegLimitPV (setAPauliValue P₀ (setAR P₀))`. -/
theorem setARegLimitPV_setAR {P₀ : Params} (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hDF : QED.GradedProof.RPi4.DecFaceGen P₀.e) (hKS : SetAKSScal P₀.e) :
    QED.ChainProof.SetAPauliAssembly.SetARegLimitPV (setAPauliValue P₀ (setAR P₀)) := by
  obtain ⟨Pinf, C, hB⟩ := QED.Graded.vacuumPolarizationPart_two_lepton_limit P₀
    (Fin.elim0 : Fin 0 → ℝ) he hm (fun ℓ => ℓ.elim0)
  have hB' : RPi4Body P₀ (Fin.elim0 : Fin 0 → ℝ) Pinf C := hB
  clear hB
  have hKSid : ∀ s, 0 ≤ s →
      Pinf s = ((QED.Chain.piHat4 (s / P₀.m ^ 2) / (16 * π ^ 4) : ℝ) : ℂ) :=
    fun s hs => setAKS_pinf_eq_of_nonneg P₀ _ he hm hDF hKS hB' hs
  obtain ⟨hGi, hGv⟩ := setA_integral
  have hm2 : 0 < P₀.m ^ 2 := by positivity
  have hc0 : 0 < 16 * π ^ 4 := by positivity
  obtain ⟨C', hC'⟩ : ∃ C', C' = 16 * π ^ 4 * (10 * |C|) := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by rw [hC']; positivity
  intro η hη
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = min (η / (8 * (2 * C' + 1))) (1 / 4) := ⟨_, rfl⟩
  have hy₀0 : 0 < y₀ := by rw [hy₀]; exact lt_min (by positivity) (by norm_num)
  have hy₀4 : y₀ ≤ 1 / 4 := by rw [hy₀]; exact min_le_right _ _
  have hy₀η : y₀ * (8 * (2 * C' + 1)) ≤ η := by
    have := min_le_left (η / (8 * (2 * C' + 1))) (1 / 4)
    rw [← hy₀, le_div_iff₀ (by positivity)] at this
    exact this
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁, ε₁ = η / (16 * (2 * C' + 1)) := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; positivity
  obtain ⟨η', hη'⟩ : ∃ η', η' = η / (8 * (16 * π ^ 4)) := ⟨_, rfl⟩
  have hη'0 : 0 < η' := by rw [hη']; positivity
  have hK₀0 : 0 < P₀.m ^ 2 * y₀ ^ 2 := by positivity
  obtain ⟨RM, hRM⟩ := setAPol_body he hm hB' (S₀ := 0) (S := P₀.m ^ 2 / y₀) (by nlinarith)
    hη'0
  refine ⟨max RM P₀.m, fun M₁ M₂ h₁ h₂ hne => ?_⟩
  have hM₁ : P₀.m < M₁ := (le_max_right _ _).trans_lt h₁
  have hM₂ : P₀.m < M₂ := (le_max_right _ _).trans_lt h₂
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hRM M₁ M₂ ((le_max_left _ _).trans_lt h₁)
    ((le_max_left _ _).trans_lt h₂) hne
  refine ⟨min δ (min 1 (ε₁ * (P₀.m ^ 2 * y₀ ^ 2) / 2)),
    lt_min hδ (lt_min one_pos (by positivity)),
    max Λ₀ (max 1 (2 * (P₀.m ^ 2 / y₀) / ε₁)), fun mγ Λ h0 h1 h2 => ?_⟩
  have hmγδ : mγ < δ := h1.trans_le (min_le_left _ _)
  have hmγ1 : mγ < 1 := h1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hmγε : mγ < ε₁ * (P₀.m ^ 2 * y₀ ^ 2) / 2 :=
    h1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hΛ₀Λ : Λ₀ < Λ := (le_max_left _ _).trans_lt h2
  have hΛ1 : 1 < Λ := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt h2
  have hΛK : 2 * (P₀.m ^ 2 / y₀) / ε₁ < Λ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt h2
  obtain ⟨hmΛ, hlim, hmaj⟩ := hΛ₀ mγ Λ h0 hmγδ hΛ₀Λ
  have hFi := intervalIntegrable_setAR hm hM₁ hM₂ h0 hmΛ (16 * π ^ 4 * P₀.m ^ 2 / P₀.e ^ 4)
  rw [setAPauliValue_setAR_eq he, ← hGv, ← intervalIntegral.integral_sub hFi hGi]
  -- the pointwise form on `(0, 1)`
  have key : ∀ y ∈ Ioo (0 : ℝ) 1,
      16 * π ^ 4 * P₀.m ^ 2 / P₀.e ^ 4 * (y ^ 2 * setAR P₀ mγ Λ M₁ M₂ (P₀.m ^ 2 * photonVar y)) -
        (1 - y) * QED.Chain.piHat4 (y ^ 2 / (1 - y)) =
      (1 - y) * (16 * π ^ 4 * (setAPol P₀ mγ Λ M₁ M₂ (kY P₀.m y) / (P₀.e : ℂ) ^ 4).re *
        (kY P₀.m y * photonD mγ Λ (kY P₀.m y)) ^ 2 -
        16 * π ^ 4 * (Pinf (kY P₀.m y)).re) := by
    intro y hy
    rw [integrand_sub_eq he hm hy, hKSid _ (kY_pos hm hy).le, Complex.ofReal_re, kY_div hm]
    unfold kY
    field_simp
  have hle := abs_integral_le_three (B := 2 * C') (b := η / 8 + 2 * C' * ε₁) hy₀0.le
    (by linarith : y₀ ≤ 1 - y₀) (by linarith) (hFi.sub hGi) (fun y hy => ?_) (fun y hy => ?_)
  · exact hle.trans_lt (three_lt hC'0 hη hy₀0 hy₀η hε₁)
  · rcases hy.2.lt_or_eq with h | h
    · have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy.1, h⟩
      have hK := kY_pos hm hy'
      obtain ⟨hw0, hw1, -⟩ := mul_photonD_mem h0 hmΛ hK
      rw [key y hy', hC']
      exact abs_out_le (by linarith) hw0 hw1 (one_sub_mul_abs_le hm hy' (hmaj _ hK.le))
        (one_sub_mul_abs_le hm hy' (norm_pinf_le he hm hB' hK.le))
    · subst h
      simp [photonVar, setAR]
      positivity
  · have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy₀0.trans hy.1, by linarith [hy.2]⟩
    have hK := kY_pos hm hy'
    obtain ⟨hw0, hw1, -⟩ := mul_photonD_mem h0 hmΛ hK
    obtain ⟨hK0, hK1⟩ := kY_mem hm hy₀0 hy
    rw [key y hy']
    refine abs_mid_le (by linarith [hy'.2]) (by linarith [hy'.1]) hw0 hw1
      (hC' ▸ one_sub_mul_abs_le hm hy' (norm_pinf_le he hm hB' hK.le)) ?_
      (one_sub_mul_photonD_le h0 hmΛ hK₀0 hK0 hK1 hε₁0 hmγ1 hmγε hΛ1 hΛK)
    rw [← mul_sub, abs_mul, abs_of_pos hc0, ← Complex.sub_re]
    have := (Complex.abs_re_le_norm _).trans (hlim _ hK.le hK1).le
    calc 16 * π ^ 4 * |(setAPol P₀ mγ Λ M₁ M₂ (kY P₀.m y) / (P₀.e : ℂ) ^ 4 -
          Pinf (kY P₀.m y)).re| ≤ 16 * π ^ 4 * η' := mul_le_mul_of_nonneg_left this hc0.le
      _ = η / 8 := by rw [hη']; field_simp

/-! ### The headline proposition -/

/-- **(HA₆) from obligation (N) and the Källén–Sabry inputs.** The conclusion is, verbatim, the
proposition of the frozen `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`. -/
theorem isFormFactorPair_vertexSetA_pauli_limit_of_N_KS (P₀ : Params)
    (hC : QED.ChainProof.SetAPauliAssembly.SetANestClasses P₀)
    (hDF : QED.GradedProof.RPi4.DecFaceGen P₀.e) (hKS : SetAKSScal P₀.e)
    (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (η : ℝ) (hη : 0 < η) :
    ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
      1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
      ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
        (∃ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2) ∧
        ∀ D : Graded.Counterterms (Fin 3 ⊕ Fin 0 × Fin 3),
          Graded.IsRenormalizedThrough
            { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
            (Lepton.leptonFlavors
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D Graded.leptonRep 2 →
          ∃ q₀ > 0, ∀ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -P₀.m ^ 2 →
            Minkowski.dot p p = -P₀.m ^ 2 → 0 < p' 0 → 0 < p 0 →
            0 < Minkowski.dot (p' - p) (p' - p) → Minkowski.dot (p' - p) (p' - p) < q₀ →
            (∃ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D
              (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p V) ∧
            ∀ V, Graded.IsFamilyVertexLimit
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                (Fin.elim0 : Fin 0 → Lepton.HeavyLepton)) D
              (fun C _ => IsOnePI C ∧ ThreeLoop.IsSetA C) 7 p' p V →
              (∃ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F) ∧
              ∀ F : ℂ × ℂ, QED.OneLoop.IsFormFactorPair P₀.e P₀.m p' p V F →
                ‖64 * (Real.pi : ℂ) ^ 6 * F.2 / (P₀.e : ℂ) ^ 6 -
                  (ThreeLoop.a1SixSetA : ℂ)‖ < η :=
  QED.ChainProof.SetAPauliAssembly.isFormFactorPair_vertexSetA_pauli_limit_of_N_reg P₀ hC
    (setARegLimitPV_setAR he hm hDF hKS) he hm η hη

end QED.ChainProof.SetARegLim

end
