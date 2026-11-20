/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecLipT
public import QED.GradedProof.RPi4DecInterp
public import QED.GradedProof.RPi4Light
public import QED.GradedProof.RPi4DensBound

/-!
# (R-Π₄) step L9: the heavy and light Lipschitz inputs from a second-difference bound

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
inputs `DecLipHeavy`, `DecLipLight` of `QED.GradedProof.RPi4.dec_scalAff_of_lipQ`.

The value bounds at comparable photon pairs are known: `‖Q(a, b; s)‖ ≤ C √b` for light pairs
(`QED.GradedProof.RPi4.exists_norm_qPair_comparable_le`) and, given the face-limit identity,
`‖Q(b, d; s) - Q(b, d; 0)‖ ≤ C/b` for heavy pairs
(`QED.GradedProof.RPi4.exists_norm_qPair_sub_heavy_le`). By the interpolation inequality
`QED.GradedProof.RPi4.dec_norm_sub_le_of_twoDiff`, a **bound on the second differences in `s`
at comparable pairs, with no decay** (`DecTwoDiff`, growth `b^{±q}`, `q < 1/2`, allowed) turns
them into Lipschitz bounds decaying like `b^{1/4 - q/2}` (light) and `b^{-(1 - q)/2}` (heavy);
the heavy ones are summed dyadically (`QED.GradedProof.RPi4.dec_norm_le_of_comparable_heavy`).
Unlike a Lipschitz rate for `qDens`, `DecTwoDiff` holds class by class (no cancellation of the
`s`-dependent heavy-photon limits is needed).

* `DecTwoDiff Φ rep e`: the second-difference bound at comparable pairs;
* **`dec_lipLight_of_twoDiff`**: `DecTwoDiff → DecLipLight`;
* **`dec_lipHeavy_of_twoDiff`**: face-limit identity → `DecTwoDiff → DecLipHeavy`;
* **`dec_scalAff_of_twoDiff`**: `DecScalAff` modulo `DecFaceGen` and `DecTwoDiff` at the
  configurations `decCfg 1 4`, `decCfg 1 8`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.WickModel (Params)

section TwoDiff

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **Second differences in `s` at comparable photon pairs**, bounded uniformly in the pair up
to a factor `b^q + b^{-q}`, `0 ≤ q < 1/2`. -/
def DecTwoDiff (e : ℝ) : Prop :=
  ∃ δ B q : ℝ, 0 < δ ∧ 0 ≤ B ∧ 0 ≤ q ∧ q < 1 / 2 ∧ ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a →
    ∀ s h : ℝ, |s| ≤ δ → |s + 2 * h| ≤ δ →
      ‖qPair Φ rep e a b (s + 2 * h) - 2 * qPair Φ rep e a b (s + h) + qPair Φ rep e a b s‖ ≤
        B * (b ^ q + b ^ (-q)) * h ^ 2

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **`DecLipLight` from the second-difference bound** (exponent `p = 1/4 - q/2`). -/
theorem dec_lipLight_of_twoDiff (P : Params) (he : P.e ≠ 0) (h2 : DecTwoDiff Φ rep P.e) :
    DecLipLight Φ rep P.e := by
  obtain ⟨δ₂, B, q, hδ₂, hB, hq0, hq, h2⟩ := h2
  have hm2 : 0 < m₀ ^ 2 := by positivity
  set δ : ℝ := min δ₂ (m₀ ^ 2) / 2
  have hδ : 0 < δ := half_pos (lt_min hδ₂ hm2)
  have hδ2 : 2 * δ ≤ δ₂ := by simp only [δ]; linarith [min_le_left δ₂ (m₀ ^ 2)]
  have hδm : 2 * δ ≤ m₀ ^ 2 := by simp only [δ]; linarith [min_le_right δ₂ (m₀ ^ 2)]
  obtain ⟨C, hC, hCb⟩ := exists_norm_qPair_comparable_le P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he
    (S₀ := -(2 * δ)) (S := 2 * δ) (by linarith) (by linarith)
  set p : ℝ := 1 / 4 - q / 2
  set ex : ℝ := 1 / 4 + q / 2
  refine ⟨δ, 4 * C / δ + 4 * C + 2 * B, p, hδ, by positivity, by simp only [p]; linarith,
    fun a b ha hab hb2 hb1 s s' hs hs' => ?_⟩
  have hb : 0 < b := ha.trans_le hab
  have hy : 0 < b ^ ex := Real.rpow_pos_of_pos hb _
  set ρ : ℝ := min δ (b ^ ex)
  have hρ : 0 < ρ := lt_min hδ hy
  have hint := dec_norm_sub_le_of_twoDiff (f := fun r => qPair Φ rep P.e a b r)
    (A := C * Real.sqrt b) (B := B * (b ^ q + b ^ (-q))) hρ (min_le_left _ _)
    (mul_nonneg hB (add_nonneg (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg hb.le _)))
    (fun r hr => hCb a b r ha hab hb2 hb1 (by linarith [neg_abs_le r])
      (by linarith [le_abs_self r]))
    (fun r h hr hr2 => h2 a b ha hab hb2 r h (hr.trans hδ2) (hr2.trans hδ2)) hs' hs
  refine hint.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  -- the exponent bookkeeping
  have hsq : Real.sqrt b = b ^ p * b ^ ex := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb]
    congr 1
    simp only [p, ex]
    ring
  have hsqp : Real.sqrt b ≤ b ^ p := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hb hb1 (by simp only [p]; linarith)
  have hqq : b ^ q ≤ b ^ (-q) := Real.rpow_le_rpow_of_exponent_ge hb hb1 (by linarith)
  have hqe : b ^ (-q) * b ^ ex = b ^ p := by
    rw [← Real.rpow_add hb]
    congr 1
    simp only [p, ex]
    ring
  have hinv := dec_inv_min_le hδ hy
  have hX : 0 ≤ b ^ p := Real.rpow_nonneg hb.le _
  have hA : 4 * (C * Real.sqrt b) / ρ ≤ 4 * C / δ * b ^ p + 4 * C * b ^ p := by
    have e1 : 4 * (C * Real.sqrt b) / ρ = 4 * C * Real.sqrt b * (1 / ρ) := by ring
    have e2 : 4 * C * Real.sqrt b * (1 / b ^ ex) = 4 * C * b ^ p := by
      rw [hsq]
      field_simp
    have h1 : 4 * C * Real.sqrt b * (1 / ρ) ≤ 4 * C * Real.sqrt b * (1 / δ + 1 / b ^ ex) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    have h2 : 4 * C * Real.sqrt b * (1 / δ) ≤ 4 * C / δ * b ^ p := by
      have := mul_le_mul_of_nonneg_left hsqp (show 0 ≤ 4 * C / δ by positivity)
      calc 4 * C * Real.sqrt b * (1 / δ) = 4 * C / δ * Real.sqrt b := by ring
        _ ≤ _ := this
    rw [e1]
    nlinarith
  have hBb : B * (b ^ q + b ^ (-q)) * ρ ≤ 2 * B * b ^ p := by
    have h1 : B * (b ^ q + b ^ (-q)) ≤ B * (2 * b ^ (-q)) :=
      mul_le_mul_of_nonneg_left (by linarith) hB
    have h2 : ρ ≤ b ^ ex := min_le_right _ _
    calc B * (b ^ q + b ^ (-q)) * ρ ≤ B * (2 * b ^ (-q)) * b ^ ex :=
          mul_le_mul h1 h2 hρ.le (by positivity)
      _ = 2 * B * (b ^ (-q) * b ^ ex) := by ring
      _ = 2 * B * b ^ p := by rw [hqe]
  calc 4 * (C * Real.sqrt b) / ρ + B * (b ^ q + b ^ (-q)) * ρ
      ≤ 4 * C / δ * b ^ p + 4 * C * b ^ p + 2 * B * b ^ p := by linarith
    _ = (4 * C / δ + 4 * C + 2 * B) * b ^ p := by ring

/-- **Lipschitz at comparable heavy pairs**, with the factor `b^{-(1 - q)/2}`. -/
theorem dec_lip_comparable_heavy (P : Params) (he : P.e ≠ 0)
    (hId : ∀ s : ℝ, min (-(2 * m₀ ^ 2)) 0 ≤ s → s ≤ max (m₀ ^ 2) 0 →
      FaceLimitId Φ rep P.e m₀ (1 + |max (m₀ ^ 2) 0|) s)
    {δ₂ B q : ℝ} (hδ₂ : 0 < δ₂) (hB : 0 ≤ B) (hq0 : 0 ≤ q) (hq : q < 1 / 2)
    (h2 : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a → ∀ s h : ℝ, |s| ≤ δ₂ → |s + 2 * h| ≤ δ₂ →
      ‖qPair Φ rep P.e a b (s + 2 * h) - 2 * qPair Φ rep P.e a b (s + h) +
        qPair Φ rep P.e a b s‖ ≤ B * (b ^ q + b ^ (-q)) * h ^ 2) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ m₀ ^ 2 / 2 ∧ 0 ≤ K ∧ ∀ s s' : ℝ, |s| ≤ δ → |s'| ≤ δ →
      ∀ b d : ℝ, 1 ≤ b → b ≤ d → d ≤ 2 * b →
        ‖qPair Φ rep P.e b d s - qPair Φ rep P.e b d s'‖ ≤
          K * b ^ (-((1 - q) / 2)) * |s - s'| := by
  have hm2 : 0 < m₀ ^ 2 := by positivity
  set δ : ℝ := min δ₂ (m₀ ^ 2) / 2
  have hδ : 0 < δ := half_pos (lt_min hδ₂ hm2)
  have hδ2 : 2 * δ ≤ δ₂ := by simp only [δ]; linarith [min_le_left δ₂ (m₀ ^ 2)]
  have hδm : 2 * δ ≤ m₀ ^ 2 := by simp only [δ]; linarith [min_le_right δ₂ (m₀ ^ 2)]
  set c : ℝ := 1 + |max (m₀ ^ 2) 0|
  have hc : 0 < c := by positivity
  have hcm : m₀ ^ 2 ≤ |max (m₀ ^ 2) 0| := (le_max_left _ _).trans (le_abs_self _)
  have hS : m₀ ^ 2 < 2 * c ^ 2 := by simp only [c]; nlinarith [abs_nonneg (max (m₀ ^ 2) 0)]
  obtain ⟨C, hC⟩ := exists_norm_qPair_sub_heavy_le Φ rep P hm₀ hmass hrep hPV₁ hPV₂ he hc
    (S₀ := -(2 * m₀ ^ 2)) (S := m₀ ^ 2) (by linarith) (by linarith) hm2.le hS
    (fun s h₀ h₁ => hId s ((min_le_left _ _).trans h₀) (h₁.trans (le_max_left _ _)))
  set pH : ℝ := (1 - q) / 2
  set ex : ℝ := (1 + q) / 2
  refine ⟨δ, 4 * |C| / δ + 4 * |C| + 4 * B, hδ, by linarith, by positivity,
    fun s s' hs hs' b d hb hbd hd2 => ?_⟩
  have hb0 : 0 < b := one_pos.trans_le hb
  have hd1 : 1 ≤ d := hb.trans hbd
  have hd0 : 0 < d := one_pos.trans_le hd1
  have hy : 0 < b ^ (-ex) := Real.rpow_pos_of_pos hb0 _
  set ρ : ℝ := min δ (b ^ (-ex))
  have hρ : 0 < ρ := lt_min hδ hy
  have hw : d ^ q + d ^ (-q) ≤ 4 * b ^ q := by
    have h1 : d ^ (-q) ≤ d ^ q := Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
    have h2 : d ^ q ≤ (2 * b) ^ q := Real.rpow_le_rpow hd0.le hd2 hq0
    have h3 : (2 * b) ^ q ≤ 2 * b ^ q := by
      rw [Real.mul_rpow (by norm_num) hb0.le]
      have : (2 : ℝ) ^ q ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by linarith)
      rw [Real.rpow_one] at this
      exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hb0.le _)
    linarith
  have hint := dec_norm_sub_le_of_twoDiff
    (f := fun r => qPair Φ rep P.e b d r - qPair Φ rep P.e b d 0)
    (A := |C| / b) (B := B * (d ^ q + d ^ (-q))) hρ (min_le_left _ _)
    (mul_nonneg hB (add_nonneg (Real.rpow_nonneg hd0.le _) (Real.rpow_nonneg hd0.le _)))
    (fun r hr => (hC r (by linarith [neg_abs_le r]) (by linarith [le_abs_self r]) b d hb
      hbd).trans (div_le_div_of_nonneg_right (le_abs_self C) hb0.le))
    (fun r h hr hr2 => by
      have e : qPair Φ rep P.e b d (r + 2 * h) - qPair Φ rep P.e b d 0 -
          2 * (qPair Φ rep P.e b d (r + h) - qPair Φ rep P.e b d 0) +
          (qPair Φ rep P.e b d r - qPair Φ rep P.e b d 0) =
          qPair Φ rep P.e b d (r + 2 * h) - 2 * qPair Φ rep P.e b d (r + h) +
          qPair Φ rep P.e b d r := by ring
      rw [e]
      exact h2 b d hb0 hbd hd2 r h (hr.trans hδ2) (hr2.trans hδ2)) hs' hs
  simp only [sub_sub_sub_cancel_right] at hint
  refine hint.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  -- the exponent bookkeeping
  have hX : 0 ≤ b ^ (-pH) := Real.rpow_nonneg hb0.le _
  have hinv := dec_inv_min_le hδ hy
  have hbi : b⁻¹ ≤ b ^ (-pH) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hb (by simp only [pH]; linarith)
  have hbe : b⁻¹ * (1 / b ^ (-ex)) = b ^ (-pH) := by
    rw [← Real.rpow_neg_one, one_div, ← Real.rpow_neg hb0.le, neg_neg, ← Real.rpow_add hb0]
    congr 1
    simp only [pH, ex]
    ring
  have hqe : b ^ q * b ^ (-ex) = b ^ (-pH) := by
    rw [← Real.rpow_add hb0]
    congr 1
    simp only [pH, ex]
    ring
  have hA : 4 * (|C| / b) / ρ ≤ 4 * |C| / δ * b ^ (-pH) + 4 * |C| * b ^ (-pH) := by
    have e1 : 4 * (|C| / b) / ρ = 4 * |C| * b⁻¹ * (1 / ρ) := by ring
    have h1 : 4 * |C| * b⁻¹ * (1 / ρ) ≤ 4 * |C| * b⁻¹ * (1 / δ + 1 / b ^ (-ex)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    have h2 : 4 * |C| * b⁻¹ * (1 / δ) ≤ 4 * |C| / δ * b ^ (-pH) := by
      have := mul_le_mul_of_nonneg_left hbi (show 0 ≤ 4 * |C| / δ by positivity)
      calc 4 * |C| * b⁻¹ * (1 / δ) = 4 * |C| / δ * b⁻¹ := by ring
        _ ≤ _ := this
    have h3 : 4 * |C| * b⁻¹ * (1 / b ^ (-ex)) = 4 * |C| * b ^ (-pH) := by
      rw [mul_assoc, hbe]
    rw [e1]
    nlinarith
  have hBb : B * (d ^ q + d ^ (-q)) * ρ ≤ 4 * B * b ^ (-pH) := by
    have h1 : B * (d ^ q + d ^ (-q)) ≤ B * (4 * b ^ q) := mul_le_mul_of_nonneg_left hw hB
    have h2 : ρ ≤ b ^ (-ex) := min_le_right _ _
    calc B * (d ^ q + d ^ (-q)) * ρ ≤ B * (4 * b ^ q) * b ^ (-ex) :=
          mul_le_mul h1 h2 hρ.le (by positivity)
      _ = 4 * B * (b ^ q * b ^ (-ex)) := by ring
      _ = 4 * B * b ^ (-pH) := by rw [hqe]
  calc 4 * (|C| / b) / ρ + B * (d ^ q + d ^ (-q)) * ρ
      ≤ 4 * |C| / δ * b ^ (-pH) + 4 * |C| * b ^ (-pH) + 4 * B * b ^ (-pH) := by linarith
    _ = (4 * |C| / δ + 4 * |C| + 4 * B) * b ^ (-pH) := by ring

/-- **`DecLipHeavy` from the second-difference bound**, given the face-limit identity. -/
theorem dec_lipHeavy_of_twoDiff (P : Params) (he : P.e ≠ 0)
    (hId : ∀ s : ℝ, min (-(2 * m₀ ^ 2)) 0 ≤ s → s ≤ max (m₀ ^ 2) 0 →
      FaceLimitId Φ rep P.e m₀ (1 + |max (m₀ ^ 2) 0|) s)
    (h2 : DecTwoDiff Φ rep P.e) : DecLipHeavy Φ rep P.e := by
  obtain ⟨δ₂, B, q, hδ₂, hB, hq0, hq, h2⟩ := h2
  obtain ⟨δ, K, hδ, hδm, hK, hcomp⟩ := dec_lip_comparable_heavy Φ rep hm₀ hmass hrep hPV₁ hPV₂
    P he hId hδ₂ hB hq0 hq h2
  set pH : ℝ := (1 - q) / 2
  have hpH : 0 < pH := by simp only [pH]; linarith
  refine ⟨δ, K / (1 - (2 : ℝ) ^ (-pH)), hδ, fun b d hb hbd s s' hs hs' => ?_⟩
  have hreg : ∀ r : ℝ, |r| ≤ δ → -(4 * m₀ ^ 2) < r := fun r hr => by
    have hm2 : 0 < m₀ ^ 2 := by positivity
    linarith [neg_abs_le r]
  have h := dec_norm_le_of_comparable_heavy
    (Q := fun b d => qPair Φ rep P.e b d s - qPair Φ rep P.e b d s')
    (C := K * |s - s'|) (p := pH) (mul_nonneg hK (abs_nonneg _)) hpH
    (fun a b d ha hab hbd => by
      have ha0 : 0 < a := one_pos.trans_le ha
      have hb0 : 0 < b := ha0.trans_le hab
      have hd0 : 0 < d := hb0.trans_le hbd
      rw [qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha0 hb0 hd0 (hreg s hs),
        qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha0 hb0 hd0 (hreg s' hs')]
      ring)
    (fun a b ha hab hb2 => (hcomp s s' hs hs' a b ha hab hb2).trans (le_of_eq (by ring)))
    b d hb hbd
  refine h.trans (le_of_eq ?_)
  ring

end TwoDiff

/-- **`DecScalAff` modulo `DecFaceGen` and the second-difference bound** at the
configurations `decCfg 1 4` and `decCfg 1 8` (counterterms at the flavour `0`). -/
theorem dec_scalAff_of_twoDiff (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (h2 : ∀ x : ℝ, x = 4 ∨ x = 8 → DecTwoDiff (decCfg 1 x) (fun _ => 0) P.e) :
    DecScalAff P.e := by
  have key : ∀ x : ℝ, x = 4 ∨ x = 8 →
      DecLipHeavy (decCfg 1 x) (fun _ => 0) P.e ∧ DecLipLight (decCfg 1 x) (fun _ => 0) P.e := by
    intro x hx
    have hx0 : 0 < x := by rcases hx with rfl | rfl <;> norm_num
    have hx1 : (1 : ℝ) ≤ x := by rcases hx with rfl | rfl <;> norm_num
    have hm₀ : (0 : ℝ) < 1 := one_pos
    have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 x).mass g := dec_cfg_mass_ge le_rfl hm₀
      (by rw [one_pow]; exact hx1)
    have hpv := dec_cfg_pv (μ := 1) one_ne_zero hx0.le
    have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
      fun _ => rfl
    exact ⟨dec_lipHeavy_of_twoDiff (decCfg 1 x) (fun _ => 0) hm₀ hmass hrep hpv.1 hpv.2 P he
      (fun s h₀ h₁ => hF (Fin 3) (decCfg 1 x) (fun _ => 0) 1 hm₀ hmass hrep hpv.1
        hpv.2 _ s (by positivity) ((lt_min (by norm_num) (by norm_num)).trans_le h₀)
        (h₁.trans_lt (asm_max_lt_two_mul_sq _))) (h2 x hx),
      dec_lipLight_of_twoDiff (decCfg 1 x) (fun _ => 0) hm₀ hmass hrep hpv.1 hpv.2 P he
        (h2 x hx)⟩
  exact dec_scalAff_of_lipQ P he hF (fun x hx => (key x hx).1) (fun x hx => (key x hx).2)

end QED.GradedProof.RPi4

end
