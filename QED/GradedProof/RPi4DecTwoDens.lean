/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecTwoDiff

/-!
# (R-Π₄) step L9: the second-difference bound from the photon-mass density

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling).
`QED.GradedProof.RPi4.DecTwoDiff` follows from a pointwise bound on the second differences in
`s` of the photon-mass density: `‖Δ²_h qDens(s, t)‖ ≤ B (t^{q/2} + t^{-q/2}) h² / t` for all
`t > 0` (`q < 1/2`), since `Q(a, b) = ∫_{a²}^{b²} qDens` and `b² - a² ≤ 3a²` at comparable
pairs. The bound is needed for `t → 0` (light) and `t → ∞` (heavy) alike, with no decay: it is
`t · Δ²_h qDens = O(h²)`, class by class.

* **`dec_twoDiff_of_dens`**.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real Interval

namespace QED.GradedProof.RPi4

open QED.WickModel (Params)

section TwoDens

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **`DecTwoDiff` from a second-difference bound on the photon-mass density** (tilt `c`). -/
theorem dec_twoDiff_of_dens (P : Params) (he : P.e ≠ 0) {c δ B q : ℝ} (hc : 0 < c)
    (hδ : 0 < δ) (hδm : δ < 4 * m₀ ^ 2) (hδc : δ < 2 * c ^ 2) (hB : 0 ≤ B) (hq0 : 0 ≤ q)
    (hq : q < 1 / 2)
    (hΔ : ∀ s h : ℝ, |s| ≤ δ → |s + 2 * h| ≤ δ → ∀ t : ℝ, 0 < t →
      ‖qDens Φ rep P.e m₀ c (s + 2 * h) t - 2 * qDens Φ rep P.e m₀ c (s + h) t +
        qDens Φ rep P.e m₀ c s t‖ ≤ B * (t ^ (q / 2) + t ^ (-(q / 2))) / t * h ^ 2) :
    DecTwoDiff Φ rep P.e := by
  refine ⟨δ, 6 * B, q, hδ, by positivity, hq0, hq, fun a b ha hab hb2 s h hs hs2 => ?_⟩
  have hb : 0 < b := ha.trans_le hab
  have hs1 : |s + h| ≤ δ := by
    have e : s + h = (s + (s + 2 * h)) / 2 := by ring
    rw [e, abs_div, abs_two]
    linarith [abs_add_le s (s + 2 * h)]
  have hreg : ∀ r : ℝ, |r| ≤ δ → -(4 * m₀ ^ 2) < r ∧ r < 2 * c ^ 2 := fun r hr =>
    ⟨by linarith [neg_abs_le r], by linarith [le_abs_self r]⟩
  have hW : 0 ≤ B * (b ^ q + b ^ (-q)) * h ^ 2 := by positivity
  rcases eq_or_lt_of_le hab with rfl | hlt
  · have z := fun r (hr : |r| ≤ δ) => qPair_self_eq_zero Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he ha
      (hreg r hr).1
    rw [z _ hs2, z _ hs1, z _ hs]
    simp only [mul_zero, sub_zero, add_zero, norm_zero]
    positivity
  obtain ⟨i2, e2⟩ := qPair_eq_integral Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hlt hc
    (hreg _ hs2).1 (hreg _ hs2).2
  obtain ⟨i1, e1⟩ := qPair_eq_integral Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hlt hc
    (hreg _ hs1).1 (hreg _ hs1).2
  obtain ⟨i0, e0⟩ := qPair_eq_integral Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hlt hc
    (hreg _ hs).1 (hreg _ hs).2
  rw [e2, e1, e0, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub i2 (i1.const_mul 2),
    ← intervalIntegral.integral_add (i2.sub (i1.const_mul 2)) i0]
  -- the pointwise bound on `(a², b²]`
  have ha2 : 0 < a ^ 2 := by positivity
  have hab2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have hbq : ∀ t : ℝ, 0 < t → t ≤ b ^ 2 → t ^ (q / 2) ≤ b ^ q := fun t ht htb => by
    have h1 := Real.rpow_le_rpow ht.le htb (by linarith : 0 ≤ q / 2)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hb.le, Nat.cast_ofNat,
      show (2 : ℝ) * (q / 2) = q by ring] at h1
  have haq : ∀ t : ℝ, a ^ 2 ≤ t → t ^ (-(q / 2)) ≤ 2 * b ^ (-q) := fun t hat => by
    have h1 := Real.rpow_le_rpow_of_nonpos ha2 hat (by linarith : -(q / 2) ≤ 0)
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le, Nat.cast_ofNat,
      show (2 : ℝ) * -(q / 2) = -q by ring] at h1
    have h2 : a ^ (-q) ≤ (b / 2) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have h3 : (b / 2) ^ (-q) = 2 ^ q * b ^ (-q) := by
      rw [Real.div_rpow hb.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    have h4 : (2 : ℝ) ^ q ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith : q ≤ 1)
      rwa [Real.rpow_one] at this
    have h5 : 0 ≤ b ^ (-q) := Real.rpow_nonneg hb.le _
    nlinarith
  set K : ℝ := B * (b ^ q + 2 * b ^ (-q)) / a ^ 2 * h ^ 2
  have hpt : ∀ t ∈ Ι (a ^ 2) (b ^ 2), ‖qDens Φ rep P.e m₀ c (s + 2 * h) t -
      2 * qDens Φ rep P.e m₀ c (s + h) t + qDens Φ rep P.e m₀ c s t‖ ≤ K := fun t ht => by
    rw [uIoc_of_le hab2] at ht
    have ht0 : 0 < t := ha2.trans ht.1
    refine (hΔ s h hs hs2 t ht0).trans ?_
    have hn : 0 ≤ t ^ (q / 2) + t ^ (-(q / 2)) := by positivity
    have hsum : t ^ (q / 2) + t ^ (-(q / 2)) ≤ b ^ q + 2 * b ^ (-q) :=
      add_le_add (hbq t ht0 ht.2) (haq t ht.1.le)
    have h1 : B * (t ^ (q / 2) + t ^ (-(q / 2))) / t ≤ B * (b ^ q + 2 * b ^ (-q)) / a ^ 2 :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hsum hB) ha2 ht.1.le
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg h)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans ?_
  have hlen : |b ^ 2 - a ^ 2| ≤ 3 * a ^ 2 := by
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  have hK : 0 ≤ K := by positivity
  calc K * |b ^ 2 - a ^ 2| ≤ K * (3 * a ^ 2) := mul_le_mul_of_nonneg_left hlen hK
    _ = 3 * B * (b ^ q + 2 * b ^ (-q)) * h ^ 2 := by simp only [K]; field_simp
    _ ≤ 6 * B * (b ^ q + b ^ (-q)) * h ^ 2 := by
        have : 0 ≤ b ^ q := Real.rpow_nonneg hb.le _
        have : 0 ≤ B * h ^ 2 := by positivity
        nlinarith

end TwoDens

end QED.GradedProof.RPi4

end
