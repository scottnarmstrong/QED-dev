/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajLip
public import QED.GradedProof.RPi4MajUV

/-!
# (R-Π₄) step L10: increments on one scale, uniform in the photon pair, from per-class inputs

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The increment
counterpart of `QED.GradedProof.RPi4.maj_rayVal_of_inputs`: the bound
`‖Q(a, b; s) - Q(a, b; s')‖ ≤ K w(s) (s - s')/s'` for `1 ≤ s' ≤ s ≤ 2s'` (`MajRayInc`) splits at
the photon mass `1` (`QED.GradedProof.RPi4.qPair_add`) into

* a light half, summed dyadically over comparable pairs: along the ray `Q = -i W(s)/s` with `W`
  the three class entries and the mass insertions; `MajLRay` bounds `W(s')`, `MajLRayInc` bounds
  `W(s) - W(s')`, and `QED.GradedProof.RPi4.MajTiltRay` does both for the mass insertions;
* a heavy half, the integral over the squared photon mass `u ∈ [1, b²]` of the density increment
  `qDens(√s, s, u) - qDens(√s', s', u)` (each at its own tilt): `O((s - s')/s')/u` from the class
  densities (`MajDRay`, `MajDRayInc`) and `O((s/u)^η (s - s')/s')/u` for `u ≥ s`
  (`MajFaceRateInc`, the increment form of the face rate).

* `majLip_norm_div_sub_le`: `‖W(s)/s - W(s')/s'‖ ≤ (X + Y)(s - s')/s'` from
  `‖W(s) - W(s')‖ ≤ X (s - s')` and `‖W(s')‖ ≤ Y s'`;
* `MajLRayInc`, `MajDRayInc`, `MajFaceRateInc`: the new inputs;
* `majLip_qPair_comparable_inc`, `majLip_irInc_of_lray`: the light half;
* `majLip_densInc_of_dRay`, `majLip_uvInc_of_dens`: the heavy half;
* **`majLip_rayInc_of_inputs`**: `MajRayInc`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-! ### The model-free quotient bound -/

/-- `‖W(s)/s - W(s')/s'‖ ≤ (X + Y)(s - s')/s'` if `‖W(s) - W(s')‖ ≤ X (s - s')`,
`‖W(s')‖ ≤ Y s'`, `0 < s' ≤ s`, `X, Y ≥ 0`. -/
theorem majLip_norm_div_sub_le {z z' : ℂ} {s s' X Y : ℝ} (hs' : 0 < s') (hss : s' ≤ s)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hX : ‖z - z'‖ ≤ X * (s - s')) (hY : ‖z'‖ ≤ Y * s') :
    ‖z / (s : ℂ) - z' / (s' : ℂ)‖ ≤ (X + Y) * ((s - s') / s') := by
  have hs : 0 < s := hs'.trans_le hss
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hsc' : (s' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs'.ne'
  have e : z / (s : ℂ) - z' / (s' : ℂ) =
      (z - z') / (s : ℂ) - z' * (((s - s' : ℝ) : ℂ) / ((s * s' : ℝ) : ℂ)) := by
    push_cast
    field_simp
    ring
  have hd : 0 ≤ s - s' := by linarith
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hs.le, Real.norm_of_nonneg hd, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖z - z'‖ / s ≤ X * ((s - s') / s') := by
    rw [div_le_iff₀ hs]
    calc ‖z - z'‖ ≤ X * (s - s') := hX
      _ = X * ((s - s') / s') * s' := by field_simp
      _ ≤ X * ((s - s') / s') * s :=
          mul_le_mul_of_nonneg_left hss (mul_nonneg hX0 (div_nonneg hd hs'.le))
  have h2 : ‖z'‖ * ((s - s') / (s * s')) ≤ Y * ((s - s') / s') := by
    calc ‖z'‖ * ((s - s') / (s * s')) ≤ Y * s' * ((s - s') / (s * s')) :=
          mul_le_mul_of_nonneg_right hY (div_nonneg hd (by positivity))
      _ = Y * ((s - s') / s) := by field_simp
      _ ≤ Y * ((s - s') / s') :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hd hs' hss) hY0
  linarith

/-! ### The inputs -/

/-- **Increments of one light-pair entry along the ray**: `‖G a b (k(s)) - G a b (k(s'))‖ ≤
C √b w(s) (s - s')` for `1 ≤ s' ≤ s ≤ 2s'` and light comparable pairs `0 < a ≤ b ≤ min(2a, 1)`. -/
def MajLRayInc (G : ℝ → ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C : ℝ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a →
    b ≤ 1 → ‖G a b (majRayVec s) - G a b (majRayVec s')‖ ≤ C * Real.sqrt b * majW s * (s - s')

/-- **Increments of one class density along the ray**:
`‖u (G(u, k(s)) - G(u, k(s')))‖ ≤ C (s - s')` for `1 ≤ s' ≤ s ≤ 2s'`, `u ≥ 1`, at the tilts
`√s`, `√s'`. -/
def MajDRayInc (G : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C : ℝ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' → ∀ u : ℝ, 1 ≤ u →
    ‖(u : ℂ) * (G u (tiltVec (Real.sqrt s) s) - G u (tiltVec (Real.sqrt s') s'))‖ ≤ C * (s - s')

section Inputs

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **The face rate on one scale** (the increment form of `MajFaceRate`):
`‖u (qDens(√s, s, u) - qDens(√s', s', u))‖ ≤ C (s/u)^η (s - s')/s'` for `1 ≤ s' ≤ s ≤ 2s'`,
`u ≥ s`. -/
def MajFaceRateInc (e m₀ : ℝ) : Prop :=
  ∃ C η : ℝ, 0 < η ∧ ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' → ∀ u : ℝ, s ≤ u →
    ‖(u : ℂ) * (qDens Φ rep e m₀ (Real.sqrt s) s u - qDens Φ rep e m₀ (Real.sqrt s') s' u)‖ ≤
      C * (s / u) ^ η * ((s - s') / s')

end Inputs

section Light

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)

include hrep hPV₁ hPV₂ hm₀ hmass

/-- **The class sum on a light pair along the ray**: `Q(a, b; s) = -i W(s)/s` with `W` the three
class entries and the single-flavour mass insertions at `majRayVec s`, `s ≥ 1`. -/
theorem majLip_qPair_ray_eq (he : P.e ≠ 0) {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : 1 ≤ s) :
    qPair Φ rep P.e a b s = -I * ((vVal aVA baseVA cVA Φ P.e m₀ a b (majRayVec s) 2 3 +
      vVal aVB baseVB cVB Φ P.e m₀ a b (majRayVec s) 2 3 +
      vVal aVC baseVC cVC Φ P.e m₀ a b (majRayVec s) 2 3 +
      ∑ g, ((ctPair P.e (Φ.mass g) a b : ℝ) : ℂ) *
        fLim Φ rep P.e (Pi.single g 1) (majRayVec s) 2 3) / (s : ℂ)) := by
  have hs0 : 0 < s := by linarith
  have hb : 0 < b := ha.trans_le hab
  set c : ℝ := Real.sqrt s with hc_def
  have hc : 0 < c := Real.sqrt_pos.mpr hs0
  have hc2 : c ^ 2 = s := Real.sq_sqrt hs0.le
  have hm2 := pow_pos hm₀ 2
  have hs' : -(4 * m₀ ^ 2) < s := by linarith
  have hs2 : s < 2 * c ^ 2 := by rw [hc2]; linarith
  have hk : -(4 * m₀ ^ 2) < Minkowski.dot (tiltVec c s) (tiltVec c s) := by
    rw [dot_tiltVec hs2.le]; exact hs'
  have hray : tiltVec c s = majRayVec s := rfl
  rw [qPair_eq_tilt Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hb hc hs' hs2,
    wV_eq_vVal_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hk,
    wV_eq_vVal_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hk,
    wV_eq_vVal_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hk,
    fLim_eq_sum_single Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he _ hk, hray, hc2]
  ring

/-- **Increments of the class sum on light comparable pairs along the ray**:
`‖Q(a, b; s) - Q(a, b; s')‖ ≤ C w(s) (s - s')/s' √b` for `1 ≤ s' ≤ s ≤ 2s'`. -/
theorem majLip_qPair_comparable_inc (he : P.e ≠ 0)
    (hA : MajLRay fun a b k => vVal aVA baseVA cVA Φ P.e m₀ a b k 2 3)
    (hB : MajLRay fun a b k => vVal aVB baseVB cVB Φ P.e m₀ a b k 2 3)
    (hC : MajLRay fun a b k => vVal aVC baseVC cVC Φ P.e m₀ a b k 2 3)
    (hA' : MajLRayInc fun a b k => vVal aVA baseVA cVA Φ P.e m₀ a b k 2 3)
    (hB' : MajLRayInc fun a b k => vVal aVB baseVB cVB Φ P.e m₀ a b k 2 3)
    (hC' : MajLRayInc fun a b k => vVal aVC baseVC cVC Φ P.e m₀ a b k 2 3)
    (hF : ∀ g, MajTiltRay (fLim Φ rep P.e (Pi.single g 1))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' → ∀ a b : ℝ, 0 < a → a ≤ b →
      b ≤ 2 * a → b ≤ 1 →
        ‖qPair Φ rep P.e a b s - qPair Φ rep P.e a b s'‖ ≤
          C * majW s * ((s - s') / s') * Real.sqrt b := by
  obtain ⟨CA, hCA⟩ := hA
  obtain ⟨CB, hCB⟩ := hB
  obtain ⟨CC, hCC⟩ := hC
  obtain ⟨CA', hCA'⟩ := hA'
  obtain ⟨CB', hCB'⟩ := hB'
  obtain ⟨CC', hCC'⟩ := hC'
  choose CF hCF using hF
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set D : ℝ := ∑ g, 3 * P.e ^ 2 / Real.pi ^ 2 / Real.sqrt (Φ.mass g) * |CF g| with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun g _ => by positivity
  set X₀ : ℝ := |CA'| + |CB'| + |CC'| + D with hX₀
  set Y₀ : ℝ := |CA| + |CB| + |CC| + D with hY₀
  have hX₀0 : 0 ≤ X₀ := by positivity
  have hY₀0 : 0 ≤ Y₀ := by positivity
  refine ⟨X₀ + Y₀, by positivity, fun s s' hs' hss hs2 a b ha hab hb2 hb1 => ?_⟩
  have hs1 : 1 ≤ s := hs'.trans hss
  have hb : 0 < b := ha.trans_le hab
  have hw := maj_one_le_majW (by linarith : (0 : ℝ) ≤ s)
  have hww := majW_mono (by linarith : (0 : ℝ) ≤ s') hss
  have hsb := Real.sqrt_nonneg b
  set W : ℝ → ℂ := fun t => vVal aVA baseVA cVA Φ P.e m₀ a b (majRayVec t) 2 3 +
      vVal aVB baseVB cVB Φ P.e m₀ a b (majRayVec t) 2 3 +
      vVal aVC baseVC cVC Φ P.e m₀ a b (majRayVec t) 2 3 +
      ∑ g, ((ctPair P.e (Φ.mass g) a b : ℝ) : ℂ) *
        fLim Φ rep P.e (Pi.single g 1) (majRayVec t) 2 3 with hW
  -- the mass-insertion coefficients
  have hct : ∀ g, |ctPair P.e (Φ.mass g) a b| ≤
      3 * P.e ^ 2 / Real.pi ^ 2 / Real.sqrt (Φ.mass g) * Real.sqrt b := fun g => by
    have h := abs_ctPair_le P.e (hpos g) ha hab
    rw [Real.sqrt_div' b (hpos g).le] at h
    refine h.trans (le_of_eq ?_)
    have := Real.sqrt_pos.mpr (hpos g)
    field_simp
  have hX : ‖W s - W s'‖ ≤ X₀ * Real.sqrt b * majW s * (s - s') := by
    have hM : ‖∑ g, ((ctPair P.e (Φ.mass g) a b : ℝ) : ℂ) *
        (fLim Φ rep P.e (Pi.single g 1) (majRayVec s) 2 3 -
          fLim Φ rep P.e (Pi.single g 1) (majRayVec s') 2 3)‖ ≤
        D * Real.sqrt b * majW s * (s - s') := by
      refine (norm_sum_le _ _).trans ?_
      rw [hD, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun g _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : ‖fLim Φ rep P.e (Pi.single g 1) (majRayVec s) 2 3 -
          fLim Φ rep P.e (Pi.single g 1) (majRayVec s') 2 3‖ ≤ |CF g| * majW s * (s - s') :=
        ((hCF g s hs1).2 s' hs' hss).trans (by
          rw [mul_assoc]
          refine mul_le_mul (le_abs_self _) ?_ (by linarith) (abs_nonneg _)
          nlinarith)
      calc _ ≤ (3 * P.e ^ 2 / Real.pi ^ 2 / Real.sqrt (Φ.mass g) * Real.sqrt b) *
            (|CF g| * majW s * (s - s')) := mul_le_mul (hct g) h1 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have e : W s - W s' =
        (vVal aVA baseVA cVA Φ P.e m₀ a b (majRayVec s) 2 3 -
          vVal aVA baseVA cVA Φ P.e m₀ a b (majRayVec s') 2 3) +
        (vVal aVB baseVB cVB Φ P.e m₀ a b (majRayVec s) 2 3 -
          vVal aVB baseVB cVB Φ P.e m₀ a b (majRayVec s') 2 3) +
        (vVal aVC baseVC cVC Φ P.e m₀ a b (majRayVec s) 2 3 -
          vVal aVC baseVC cVC Φ P.e m₀ a b (majRayVec s') 2 3) +
        ∑ g, ((ctPair P.e (Φ.mass g) a b : ℝ) : ℂ) *
          (fLim Φ rep P.e (Pi.single g 1) (majRayVec s) 2 3 -
            fLim Φ rep P.e (Pi.single g 1) (majRayVec s') 2 3) := by
      simp only [hW, mul_sub, Finset.sum_sub_distrib]
      ring
    have hab' : ∀ (C : ℝ) (z : ℂ), ‖z‖ ≤ C * Real.sqrt b * majW s * (s - s') →
        ‖z‖ ≤ |C| * Real.sqrt b * majW s * (s - s') := fun C z h =>
      h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C) hsb) (by linarith)) (by linarith))
    rw [e]
    refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        (hab' _ _ (hCA' s s' hs' hss hs2 a b ha hab hb2 hb1))
        (hab' _ _ (hCB' s s' hs' hss hs2 a b ha hab hb2 hb1))))
      (hab' _ _ (hCC' s s' hs' hss hs2 a b ha hab hb2 hb1)))) hM)).trans (le_of_eq ?_)
    rw [hX₀]
    ring
  have hY : ‖W s'‖ ≤ Y₀ * Real.sqrt b * majW s * s' := by
    have hs'0 : (0 : ℝ) ≤ s' := by linarith
    have hw1 : (0 : ℝ) ≤ majW s - 1 := by linarith
    have hw'0 : (0 : ℝ) ≤ majW s' := by linarith [maj_one_le_majW hs'0]
    have hM : ‖∑ g, ((ctPair P.e (Φ.mass g) a b : ℝ) : ℂ) *
        fLim Φ rep P.e (Pi.single g 1) (majRayVec s') 2 3‖ ≤ D * Real.sqrt b * majW s * s' := by
      refine (norm_sum_le _ _).trans ?_
      rw [hD, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun g _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : ‖fLim Φ rep P.e (Pi.single g 1) (majRayVec s') 2 3‖ ≤ |CF g| * majW s * s' :=
        ((hCF g s' hs').1.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
          (by linarith))).trans (by
          nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (CF g)) hs'0) hw1])
      calc _ ≤ (3 * P.e ^ 2 / Real.pi ^ 2 / Real.sqrt (Φ.mass g) * Real.sqrt b) *
            (|CF g| * majW s * s') := mul_le_mul (hct g) h1 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hab' : ∀ (C : ℝ) (z : ℂ), ‖z‖ ≤ C * Real.sqrt b * (s' * majW s') →
        ‖z‖ ≤ |C| * Real.sqrt b * majW s * s' := fun C z h =>
      h.trans (by
        calc C * Real.sqrt b * (s' * majW s') ≤ |C| * Real.sqrt b * (s' * majW s) :=
              mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) hsb)
                (mul_le_mul_of_nonneg_left hww (by linarith))
                (mul_nonneg hs'0 hw'0) (by positivity)
          _ = _ := by ring)
    refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        (hab' _ _ (hCA s' hs' a b ha hab hb2 hb1))
        (hab' _ _ (hCB s' hs' a b ha hab hb2 hb1))))
      (hab' _ _ (hCC s' hs' a b ha hab hb2 hb1)))) hM)).trans (le_of_eq ?_)
    rw [hY₀]
    ring
  rw [majLip_qPair_ray_eq P Φ rep hrep hPV₁ hPV₂ hm₀ hmass he ha hab hs1,
    majLip_qPair_ray_eq P Φ rep hrep hPV₁ hPV₂ hm₀ hmass he ha hab hs', ← mul_sub, norm_mul,
    norm_neg, Complex.norm_I, one_mul]
  have h := majLip_norm_div_sub_le (z := W s) (z' := W s') (by linarith : (0 : ℝ) < s') hss
    (by positivity) (by positivity) hX hY
  refine h.trans (le_of_eq ?_)
  ring

/-- **(T2.IR, increments) The light half at `R₀ = 1`**: `‖Q(a, 1; s) - Q(a, 1; s')‖ ≤
K w(s) (s - s')/s'` for `0 < a < 1`, `1 ≤ s' ≤ s ≤ 2s'`, by dyadic summation. -/
theorem majLip_irInc_of_lray (he : P.e ≠ 0)
    (hA : MajLRay fun a b k => vVal aVA baseVA cVA Φ P.e m₀ a b k 2 3)
    (hB : MajLRay fun a b k => vVal aVB baseVB cVB Φ P.e m₀ a b k 2 3)
    (hC : MajLRay fun a b k => vVal aVC baseVC cVC Φ P.e m₀ a b k 2 3)
    (hA' : MajLRayInc fun a b k => vVal aVA baseVA cVA Φ P.e m₀ a b k 2 3)
    (hB' : MajLRayInc fun a b k => vVal aVB baseVB cVB Φ P.e m₀ a b k 2 3)
    (hC' : MajLRayInc fun a b k => vVal aVC baseVC cVC Φ P.e m₀ a b k 2 3)
    (hF : ∀ g, MajTiltRay (fLim Φ rep P.e (Pi.single g 1))) :
    ∃ K : ℝ, ∀ a : ℝ, 0 < a → a < 1 → ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' →
      ‖qPair Φ rep P.e a 1 s - qPair Φ rep P.e a 1 s'‖ ≤ K * majW s * ((s - s') / s') := by
  obtain ⟨C, hC0, hCmp⟩ := majLip_qPair_comparable_inc P Φ rep hrep hPV₁ hPV₂ hm₀ hmass he hA hB
    hC hA' hB' hC' hF
  set ρ : ℝ := 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) with hρ
  refine ⟨C / ρ, fun a ha ha1 s s' hs' hss hs2 => ?_⟩
  have hm2 := pow_pos hm₀ 2
  have hT : ∀ t : ℝ, 1 ≤ t → -(4 * m₀ ^ 2) < t := fun t ht => by linarith
  have hs1 : 1 ≤ s := hs'.trans hss
  have hw := maj_one_le_majW (by linarith : (0 : ℝ) ≤ s)
  have hq : 0 ≤ (s - s') / s' := div_nonneg (by linarith) (by linarith)
  have hCw : 0 ≤ C * majW s * ((s - s') / s') := by positivity
  have h := norm_le_of_comparable_rpow
    (Q := fun a b => qPair Φ rep P.e a b s - qPair Φ rep P.e a b s') (r₀ := 1)
    hCw (by norm_num : (0 : ℝ) < 1 / 2)
    (fun a b d ha hab hbd _ => by
      have hb := ha.trans_le hab
      have hd := hb.trans_le hbd
      rw [qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hb hd (hT s hs1),
        qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hb hd (hT s' hs')]
      ring)
    (fun a b ha hab hb2 hb1 => by
      rw [← Real.sqrt_eq_rpow]
      exact hCmp s s' hs' hss hs2 a b ha hab hb2 hb1) a 1 ha ha1.le le_rfl
  rw [Real.one_rpow, mul_one] at h
  refine h.trans (le_of_eq ?_)
  rw [hρ]
  ring

end Light

section Heavy

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass in
/-- **Density increments from the classes**: `MajDRay` and `MajDRayInc` of the three class
densities and `MajTiltRay` of the single-flavour blocks give
`‖u (qDens(√s, s, u) - qDens(√s', s', u))‖ ≤ C (s - s')/s'` for `1 ≤ s' ≤ s ≤ 2s'`, `u ≥ 1`. -/
theorem majLip_densInc_of_dRay (P : Params)
    (hA : MajDRay fun u k => vDens aVA baseVA cVA Φ P.e m₀ u k 2 3)
    (hB : MajDRay fun u k => vDens aVB baseVB cVB Φ P.e m₀ u k 2 3)
    (hC : MajDRay fun u k => vDens aVC baseVC cVC Φ P.e m₀ u k 2 3)
    (hA' : MajDRayInc fun u k => vDens aVA baseVA cVA Φ P.e m₀ u k 2 3)
    (hB' : MajDRayInc fun u k => vDens aVB baseVB cVB Φ P.e m₀ u k 2 3)
    (hC' : MajDRayInc fun u k => vDens aVC baseVC cVC Φ P.e m₀ u k 2 3)
    (hFl : ∀ g, MajTiltRay (fLim Φ rep P.e (Pi.single g 1))) :
    ∃ C : ℝ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' → ∀ u : ℝ, 1 ≤ u →
      ‖(u : ℂ) * (qDens Φ rep P.e m₀ (Real.sqrt s) s u -
        qDens Φ rep P.e m₀ (Real.sqrt s') s' u)‖ ≤ C * ((s - s') / s') := by
  obtain ⟨CA, hCA⟩ := hA
  obtain ⟨CB, hCB⟩ := hB
  obtain ⟨CC, hCC⟩ := hC
  obtain ⟨CA', hCA'⟩ := hA'
  obtain ⟨CB', hCB'⟩ := hB'
  obtain ⟨CC', hCC'⟩ := hC'
  choose CF hCF using hFl
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set Sg : F → ℝ := fun g =>
    3 * P.e ^ 2 / (16 * Real.pi ^ 2) + P.e ^ 2 * |Φ.mass g| / (2 * Real.pi ^ 2) with hSg
  have hS0 : ∀ g, 0 ≤ Sg g := fun g => by simp only [hSg]; positivity
  set D : ℝ := ∑ g, Sg g * |CF g| with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun g _ => mul_nonneg (hS0 g) (abs_nonneg _)
  set X₀ : ℝ := |CA'| + |CB'| + |CC'| + D with hX₀
  set Y₀ : ℝ := |CA| + |CB| + |CC| + D with hY₀
  refine ⟨X₀ + Y₀, fun s s' hs' hss hs2 u hu => ?_⟩
  have hs1 : 1 ≤ s := hs'.trans hss
  have hn : ‖(u : ℂ)‖ = u := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  set W : ℝ → ℂ := fun t => (u : ℂ) *
      (vDens aVA baseVA cVA Φ P.e m₀ u (tiltVec (Real.sqrt t) t) 2 3 +
        vDens aVB baseVB cVB Φ P.e m₀ u (tiltVec (Real.sqrt t) t) 2 3 +
        vDens aVC baseVC cVC Φ P.e m₀ u (tiltVec (Real.sqrt t) t) 2 3 +
        ∑ g, (sigma P.e (Φ.mass g) u : ℂ) *
          fLim Φ rep P.e (Pi.single g 1) (tiltVec (Real.sqrt t) t) 2 3) with hW
  have hsig : ∀ g, ‖(u : ℂ) * (sigma P.e (Φ.mass g) u : ℂ)‖ ≤ Sg g := fun g => by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
    exact maj_abs_mul_sigma_le P.e (hpos g).ne' hu
  have hX : ‖W s - W s'‖ ≤ X₀ * (s - s') := by
    have hM : ‖∑ g, ((u : ℂ) * (sigma P.e (Φ.mass g) u : ℂ)) *
        (fLim Φ rep P.e (Pi.single g 1) (majRayVec s) 2 3 -
          fLim Φ rep P.e (Pi.single g 1) (majRayVec s') 2 3)‖ ≤ D * (s - s') := by
      refine (norm_sum_le _ _).trans ?_
      rw [hD, Finset.sum_mul]
      refine Finset.sum_le_sum fun g _ => ?_
      rw [norm_mul, mul_assoc]
      exact mul_le_mul (hsig g) (((hCF g s hs1).2 s' hs' hss).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))) (norm_nonneg _) (hS0 g)
    have e : W s - W s' =
        (u : ℂ) * (vDens aVA baseVA cVA Φ P.e m₀ u (tiltVec (Real.sqrt s) s) 2 3 -
          vDens aVA baseVA cVA Φ P.e m₀ u (tiltVec (Real.sqrt s') s') 2 3) +
        (u : ℂ) * (vDens aVB baseVB cVB Φ P.e m₀ u (tiltVec (Real.sqrt s) s) 2 3 -
          vDens aVB baseVB cVB Φ P.e m₀ u (tiltVec (Real.sqrt s') s') 2 3) +
        (u : ℂ) * (vDens aVC baseVC cVC Φ P.e m₀ u (tiltVec (Real.sqrt s) s) 2 3 -
          vDens aVC baseVC cVC Φ P.e m₀ u (tiltVec (Real.sqrt s') s') 2 3) +
        ∑ g, ((u : ℂ) * (sigma P.e (Φ.mass g) u : ℂ)) *
          (fLim Φ rep P.e (Pi.single g 1) (majRayVec s) 2 3 -
            fLim Φ rep P.e (Pi.single g 1) (majRayVec s') 2 3) := by
      simp only [hW, majRayVec, mul_add, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib,
        mul_assoc]
      ring
    have hab' : ∀ (C : ℝ) (z : ℂ), ‖z‖ ≤ C * (s - s') → ‖z‖ ≤ |C| * (s - s') := fun C z h =>
      h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith))
    rw [e]
    refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        (hab' _ _ (hCA' s s' hs' hss hs2 u hu)) (hab' _ _ (hCB' s s' hs' hss hs2 u hu))))
      (hab' _ _ (hCC' s s' hs' hss hs2 u hu)))) hM)).trans (le_of_eq ?_)
    rw [hX₀]
    ring
  have hY : ‖W s'‖ ≤ Y₀ * s' := by
    have hM : ‖∑ g, ((u : ℂ) * (sigma P.e (Φ.mass g) u : ℂ)) *
        fLim Φ rep P.e (Pi.single g 1) (majRayVec s') 2 3‖ ≤ D * s' := by
      refine (norm_sum_le _ _).trans ?_
      rw [hD, Finset.sum_mul]
      refine Finset.sum_le_sum fun g _ => ?_
      rw [norm_mul, mul_assoc]
      exact mul_le_mul (hsig g) ((hCF g s' hs').1.trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))) (norm_nonneg _) (hS0 g)
    have e : W s' =
        (u : ℂ) * vDens aVA baseVA cVA Φ P.e m₀ u (tiltVec (Real.sqrt s') s') 2 3 +
        (u : ℂ) * vDens aVB baseVB cVB Φ P.e m₀ u (tiltVec (Real.sqrt s') s') 2 3 +
        (u : ℂ) * vDens aVC baseVC cVC Φ P.e m₀ u (tiltVec (Real.sqrt s') s') 2 3 +
        ∑ g, ((u : ℂ) * (sigma P.e (Φ.mass g) u : ℂ)) *
          fLim Φ rep P.e (Pi.single g 1) (majRayVec s') 2 3 := by
      simp only [hW, majRayVec, mul_add, Finset.mul_sum, mul_assoc]
    have hab' : ∀ (C : ℝ) (z : ℂ), ‖z‖ ≤ C * s' → ‖z‖ ≤ |C| * s' := fun C z h =>
      h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith))
    rw [e]
    refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        (hab' _ _ (hCA s' hs' u hu).1) (hab' _ _ (hCB s' hs' u hu).1)))
      (hab' _ _ (hCC s' hs' u hu).1))) hM)).trans (le_of_eq ?_)
    rw [hY₀]
    ring
  have hq : ∀ t : ℝ, 1 ≤ t → (u : ℂ) * qDens Φ rep P.e m₀ (Real.sqrt t) t u =
      -I * (W t / (t : ℂ)) := fun t ht => by
    have h2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt (by linarith)
    simp only [qDens, hW, h2]
    ring
  rw [mul_sub, hq s hs1, hq s' hs', ← mul_sub, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact majLip_norm_div_sub_le (by linarith) hss (by positivity) (by positivity) hX hY

include hm₀ hmass hrep hPV₁ hPV₂

/-- **(T2.UV, increments) The heavy half at `R₀ = 1`**: the density increments and the face rate
on one scale give `‖Q(1, b; s) - Q(1, b; s')‖ ≤ K w(s) (s - s')/s'` for `b > 1`,
`1 ≤ s' ≤ s ≤ 2s'`. -/
theorem majLip_uvInc_of_dens (P : Params) (he : P.e ≠ 0)
    (hD : ∃ C : ℝ, ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' → ∀ u : ℝ, 1 ≤ u →
      ‖(u : ℂ) * (qDens Φ rep P.e m₀ (Real.sqrt s) s u -
        qDens Φ rep P.e m₀ (Real.sqrt s') s' u)‖ ≤ C * ((s - s') / s'))
    (hR : MajFaceRateInc Φ rep P.e m₀) :
    ∃ K : ℝ, ∀ b : ℝ, 1 < b → ∀ s s' : ℝ, 1 ≤ s' → s' ≤ s → s ≤ 2 * s' →
      ‖qPair Φ rep P.e 1 b s - qPair Φ rep P.e 1 b s'‖ ≤ K * majW s * ((s - s') / s') := by
  obtain ⟨CD, hCD⟩ := hD
  obtain ⟨CR, η, hη, hCR⟩ := hR
  refine ⟨|CD| + |CR| / η, fun b hb s s' hs' hss hs2 => ?_⟩
  have hs1 : 1 ≤ s := hs'.trans hss
  have hs0 : 0 < s := by linarith
  have hm2 := pow_pos hm₀ 2
  have hq : 0 ≤ (s - s') / s' := div_nonneg (by linarith) (by linarith)
  have hrep' : ∀ t : ℝ, 1 ≤ t → 0 < Real.sqrt t ∧ -(4 * m₀ ^ 2) < t ∧
      t < 2 * Real.sqrt t ^ 2 := fun t ht => by
    refine ⟨Real.sqrt_pos.mpr (by linarith), by linarith, ?_⟩
    rw [Real.sq_sqrt (by linarith)]
    linarith
  obtain ⟨c1, c2, c3⟩ := hrep' s hs1
  obtain ⟨c1', c2', c3'⟩ := hrep' s' hs'
  obtain ⟨iS, eS⟩ := qPair_eq_integral Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he one_pos hb c1 c2 c3
  obtain ⟨iS', eS'⟩ := qPair_eq_integral Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he one_pos hb c1' c2'
    c3'
  rw [eS, eS', ← intervalIntegral.integral_sub iS iS', one_pow]
  rw [one_pow] at iS iS'
  have hX : 1 ≤ b ^ 2 := by nlinarith
  have hlog : Real.log s ≤ majW s := by
    have := Real.log_le_log hs0 (by linarith : s ≤ 1 + s)
    simp only [majW]
    linarith
  have hA0 : 0 ≤ |CD| * ((s - s') / s') := mul_nonneg (abs_nonneg _) hq
  have hB0 : 0 ≤ |CR| * ((s - s') / s') := mul_nonneg (abs_nonneg _) hq
  refine (maj_norm_integral_dens_le hA0 hB0 hη hs1 hX (iS.sub iS') (fun u hu => ?_)
    (fun u hu => ?_)).trans ?_
  · have hu0 : 0 < u := by linarith
    have h := hCD s s' hs' hss hs2 u hu
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0.le] at h
    rw [le_mul_inv_iff₀ hu0, mul_comm]
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hq)
  · have hu0 : 0 < u := by linarith
    have h := hCR s s' hs' hss hs2 u hu
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0.le] at h
    have hr : (s / u) ^ η = s ^ η * u ^ (-η) := by
      rw [Real.div_rpow hs0.le hu0.le, Real.rpow_neg hu0.le, div_eq_mul_inv]
    have hr' : u ^ (-η - 1) = u ^ (-η) * u⁻¹ := by
      rw [Real.rpow_sub hu0, Real.rpow_one, div_eq_mul_inv]
    rw [hr', ← mul_assoc, le_mul_inv_iff₀ hu0, mul_comm _ u]
    rw [hr] at h
    have hsu : 0 ≤ s ^ η * u ^ (-η) :=
      mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg hu0.le _)
    calc _ ≤ CR * (s ^ η * u ^ (-η)) * ((s - s') / s') := h
      _ ≤ |CR| * (s ^ η * u ^ (-η)) * ((s - s') / s') :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hsu) hq
      _ = _ := by ring
  · have hw := maj_one_le_majW hs0.le
    have hCRη : 0 ≤ |CR| / η := div_nonneg (abs_nonneg _) hη.le
    have e : |CD| * ((s - s') / s') * Real.log s + |CR| * ((s - s') / s') / η =
        ((s - s') / s') * (|CD| * Real.log s + |CR| / η) := by ring
    rw [e]
    have : |CD| * Real.log s + |CR| / η ≤ (|CD| + |CR| / η) * majW s := by
      nlinarith [mul_le_mul_of_nonneg_left hlog (abs_nonneg CD),
        mul_le_mul_of_nonneg_left hw hCRη]
    nlinarith

/-- **(T2, increments) `MajRayInc` from its inputs**: the light half (`MajLRay`, `MajLRayInc` of
the three class entries), the heavy half (`MajDRay`, `MajDRayInc` of the three class densities,
`MajFaceRateInc`) and the single-flavour one-loop blocks along the ray. -/
theorem majLip_rayInc_of_inputs (P : Params) (he : P.e ≠ 0)
    (hA : MajLRay fun a b k => vVal aVA baseVA cVA Φ P.e m₀ a b k 2 3)
    (hB : MajLRay fun a b k => vVal aVB baseVB cVB Φ P.e m₀ a b k 2 3)
    (hC : MajLRay fun a b k => vVal aVC baseVC cVC Φ P.e m₀ a b k 2 3)
    (hA' : MajLRayInc fun a b k => vVal aVA baseVA cVA Φ P.e m₀ a b k 2 3)
    (hB' : MajLRayInc fun a b k => vVal aVB baseVB cVB Φ P.e m₀ a b k 2 3)
    (hC' : MajLRayInc fun a b k => vVal aVC baseVC cVC Φ P.e m₀ a b k 2 3)
    (hDA : MajDRay fun u k => vDens aVA baseVA cVA Φ P.e m₀ u k 2 3)
    (hDB : MajDRay fun u k => vDens aVB baseVB cVB Φ P.e m₀ u k 2 3)
    (hDC : MajDRay fun u k => vDens aVC baseVC cVC Φ P.e m₀ u k 2 3)
    (hDA' : MajDRayInc fun u k => vDens aVA baseVA cVA Φ P.e m₀ u k 2 3)
    (hDB' : MajDRayInc fun u k => vDens aVB baseVB cVB Φ P.e m₀ u k 2 3)
    (hDC' : MajDRayInc fun u k => vDens aVC baseVC cVC Φ P.e m₀ u k 2 3)
    (hR : MajFaceRateInc Φ rep P.e m₀)
    (hFl : ∀ g, MajTiltRay (fLim Φ rep P.e (Pi.single g 1))) : MajRayInc Φ rep P.e := by
  obtain ⟨K₁, hK₁⟩ := majLip_irInc_of_lray P Φ rep hrep hPV₁ hPV₂ hm₀ hmass he hA hB hC hA' hB'
    hC' hFl
  obtain ⟨K₂, hK₂⟩ := majLip_uvInc_of_dens Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he
    (majLip_densInc_of_dRay Φ rep hm₀ hmass P hDA hDB hDC hDA' hDB' hDC' hFl) hR
  refine ⟨K₁ + K₂, 1, 1, one_pos, fun a b ha ha1 hb s s' hs' hss hs2 => ?_⟩
  have hm2 := pow_pos hm₀ 2
  have hT : ∀ t : ℝ, 1 ≤ t → -(4 * m₀ ^ 2) < t := fun t ht => by linarith
  have hs1 : 1 ≤ s := hs'.trans hss
  have hb0 : 0 < b := one_pos.trans hb
  rw [qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha one_pos hb0 (hT s hs1),
    qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha one_pos hb0 (hT s' hs')]
  have e : qPair Φ rep P.e a 1 s + qPair Φ rep P.e 1 b s -
      (qPair Φ rep P.e a 1 s' + qPair Φ rep P.e 1 b s') =
      (qPair Φ rep P.e a 1 s - qPair Φ rep P.e a 1 s') +
        (qPair Φ rep P.e 1 b s - qPair Φ rep P.e 1 b s') := by ring
  rw [e, add_mul, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hK₁ a ha ha1 s s' hs' hss hs2)
    (hK₂ b hb s s' hs' hss hs2))

end Heavy

end QED.GradedProof.RPi4

end
