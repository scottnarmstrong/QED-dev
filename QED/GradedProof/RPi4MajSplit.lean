/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajGrowD
public import QED.GradedProof.RPi4MajRay
public import QED.GradedProof.RPi4Light
public import QED.GradedProof.RPi4FLin
public import QED.GradedProof.RPi4CtBound

/-!
# (R-Π₄) step L10, two loops: the photon pair split at a fixed mass, and the light half

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2). The
large-`s` value bound `MajRayVal` is uniform in the photon pair `(a, b)`, `a → 0`, `b → ∞`. By
additivity `QED.GradedProof.RPi4.qPair_add`, `Q(a, b) = Q(a, R₀) + Q(R₀, b)`, so it splits into
a light half (`a → 0`, `b = R₀`) and a heavy half (`a = R₀`, `b → ∞`).

* `MajIRVal Φ rep e R₀`, `MajUVVal Φ rep e R₀`: the two halves;
* **`maj_rayVal_of_split`**: `MajIRVal` and `MajUVVal` at the same `R₀ > 0` give `MajRayVal`;
* `MajLRay G`: `‖G a b (k(s))‖ ≤ C √b s w(s)` along the ray `k(s) = majRayVec s`, `s ≥ 1`, for
  light comparable pairs `0 < a ≤ b ≤ min(2a, 1)`; closed under sums and constants;
* `maj_tiltRay_fLim_gen`: the one-loop block `fLim … δ` is `MajTiltRay` for any weights, all
  masses `≥ 1`;
* `maj_qPair_comparable_ray`: `MajLRay` of the three class entries and `MajTiltRay` of the mass
  insertions give `‖Q(a, b; s)‖ ≤ C w(s) √b` on light comparable pairs, `s ≥ 1`;
* **`maj_irVal_of_lray`**: then the light half `MajIRVal Φ rep e 1` holds: dyadic summation
  (`QED.GradedProof.RPi4.norm_le_of_comparable_rpow`) for `s ≥ 1`, the light-pair bound of step
  L7 (`QED.GradedProof.RPi4.exists_norm_qPair_light_le`) for `s ≤ 1` and at `s = 0`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

section Halves

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **The light half at the split mass `R₀`**: `‖Q(a, R₀; s) - Q(a, R₀; 0)‖ ≤ K w(s)` for
`0 < a < δ`, `s ≥ 0`. -/
def MajIRVal (e R₀ : ℝ) : Prop :=
  ∃ K δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 < a → a < δ → ∀ s : ℝ, 0 ≤ s →
    ‖qPair Φ rep e a R₀ s - qPair Φ rep e a R₀ 0‖ ≤ K * majW s

/-- **The heavy half at the split mass `R₀`**: `‖Q(R₀, b; s) - Q(R₀, b; 0)‖ ≤ K w(s)` for
`b > R`, `s ≥ 0`. -/
def MajUVVal (e R₀ : ℝ) : Prop :=
  ∃ K R : ℝ, ∀ b : ℝ, R < b → ∀ s : ℝ, 0 ≤ s →
    ‖qPair Φ rep e R₀ b s - qPair Φ rep e R₀ b 0‖ ≤ K * majW s

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **(T2.0) The split**: the light and heavy halves at a common `R₀ > 0` give `MajRayVal`. -/
theorem maj_rayVal_of_split (P : Params) (he : P.e ≠ 0) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hIR : MajIRVal Φ rep P.e R₀) (hUV : MajUVVal Φ rep P.e R₀) : MajRayVal Φ rep P.e := by
  obtain ⟨K₁, δ, hδ, h₁⟩ := hIR
  obtain ⟨K₂, R, h₂⟩ := hUV
  refine ⟨K₁ + K₂, δ, max R R₀, hδ, fun a b ha haδ hb s hs => ?_⟩
  have hbR : R < b := (le_max_left _ _).trans_lt hb
  have hb0 : 0 < b := hR₀.trans ((le_max_right _ _).trans_lt hb)
  have hT : ∀ t : ℝ, 0 ≤ t → -(4 * m₀ ^ 2) < t := fun t ht => by
    have := pow_pos hm₀ 2
    linarith
  rw [qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hR₀ hb0 (hT s hs),
    qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hR₀ hb0 (hT 0 le_rfl)]
  have e : qPair Φ rep P.e a R₀ s + qPair Φ rep P.e R₀ b s -
      (qPair Φ rep P.e a R₀ 0 + qPair Φ rep P.e R₀ b 0) =
      (qPair Φ rep P.e a R₀ s - qPair Φ rep P.e a R₀ 0) +
        (qPair Φ rep P.e R₀ b s - qPair Φ rep P.e R₀ b 0) := by ring
  rw [e, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h₁ a ha haδ s hs) (h₂ b hbR s hs))

end Halves

/-! ### Light comparable pairs along the ray -/

/-- `G a b` is at most `C √b s w(s)` along the ray `majRayVec s`, `s ≥ 1`, for all light
comparable photon pairs `0 < a ≤ b ≤ min(2a, 1)`. -/
def MajLRay (G : ℝ → ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a → b ≤ 1 →
    ‖G a b (majRayVec s)‖ ≤ C * Real.sqrt b * (s * majW s)

namespace MajLRay

variable {G H : ℝ → ℝ → (Fin 4 → ℝ) → ℂ}

theorem zero : MajLRay fun _ _ _ => 0 :=
  ⟨0, fun s _ a b _ _ _ _ => by simp⟩

theorem add (hG : MajLRay G) (hH : MajLRay H) : MajLRay fun a b k => G a b k + H a b k := by
  obtain ⟨C, hC⟩ := hG
  obtain ⟨D, hD⟩ := hH
  refine ⟨C + D, fun s hs a b ha hab hb2 hb1 => ?_⟩
  refine (norm_add_le _ _).trans ?_
  have e : (C + D) * Real.sqrt b * (s * majW s) =
      C * Real.sqrt b * (s * majW s) + D * Real.sqrt b * (s * majW s) := by ring
  rw [e]
  exact add_le_add (hC s hs a b ha hab hb2 hb1) (hD s hs a b ha hab hb2 hb1)

theorem const_mul (hG : MajLRay G) (r : ℂ) : MajLRay fun a b k => r * G a b k := by
  obtain ⟨C, hC⟩ := hG
  refine ⟨‖r‖ * C, fun s hs a b ha hab hb2 hb1 => ?_⟩
  rw [norm_mul, mul_assoc, mul_assoc]
  rw [← mul_assoc C]
  exact mul_le_mul_of_nonneg_left (hC s hs a b ha hab hb2 hb1) (norm_nonneg _)

theorem sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → ℝ → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, MajLRay (G i)) : MajLRay fun a b k => ∑ i ∈ s, G i a b k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : MajLRay fun _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : MajLRay G)
    (e : ∀ s : ℝ, 1 ≤ s → ∀ a b : ℝ, 0 < a → a ≤ b →
      G a b (majRayVec s) = H a b (majRayVec s)) : MajLRay H := by
  obtain ⟨C, hC⟩ := hG
  exact ⟨C, fun s hs a b ha hab hb2 hb1 => e s hs a b ha hab ▸ hC s hs a b ha hab hb2 hb1⟩

end MajLRay

section Light

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hrep hPV₁ hPV₂

/-- **The one-loop block along the ray, any weights**: `fLim … δ` is `MajTiltRay` when all
masses are at least `1`. -/
theorem maj_tiltRay_fLim_gen (hmass : ∀ g, 1 ≤ Φ.mass g) (he : P.e ≠ 0) (δ : F → ℝ) :
    MajTiltRay (fLim Φ rep P.e δ) := by
  refine ((maj_tiltRay_fbVal P Φ (ctOf P.e δ) rep hmass true
    (by decide : true ≠ false)).add (maj_tiltRay_fbVal P Φ (ctOf P.e δ) rep hmass false
      (by decide : false ≠ true))).congr fun s hs => ?_
  have hk : -(4 * (1 : ℝ) ^ 2) < Minkowski.dot (majRayVec s) (majRayVec s) := by
    rw [dot_majRayVec (by linarith)]
    linarith
  exact (fLim_eq_fbVal P Φ rep one_pos hmass hrep hPV₁ hPV₂ he δ hk 2 3).symm

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)

include hm₀ hmass

/-- **The class sum on light comparable pairs along the ray**: `‖Q(a, b; s)‖ ≤ C w(s) √b` for
`s ≥ 1` and `0 < a ≤ b ≤ min(2a, 1)`, from `MajLRay` of the three class entries and
`MajTiltRay` of the single-flavour mass insertions. -/
theorem maj_qPair_comparable_ray (he : P.e ≠ 0)
    (hA : MajLRay fun a b k => vVal aVA baseVA cVA Φ P.e m₀ a b k 2 3)
    (hB : MajLRay fun a b k => vVal aVB baseVB cVB Φ P.e m₀ a b k 2 3)
    (hC : MajLRay fun a b k => vVal aVC baseVC cVC Φ P.e m₀ a b k 2 3)
    (hF : ∀ g, MajTiltRay (fLim Φ rep P.e (Pi.single g 1))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 ≤ s → ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2 * a → b ≤ 1 →
      ‖qPair Φ rep P.e a b s‖ ≤ C * majW s * Real.sqrt b := by
  obtain ⟨CA, hCA⟩ := hA
  obtain ⟨CB, hCB⟩ := hB
  obtain ⟨CC, hCC⟩ := hC
  choose CF hCF using hF
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set D : ℝ := ∑ g, 3 * P.e ^ 2 / Real.pi ^ 2 / Real.sqrt (Φ.mass g) * |CF g| with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun g _ => by positivity
  refine ⟨|CA| + |CB| + |CC| + D, by positivity, fun s hs a b ha hab hb2 hb1 => ?_⟩
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
    fLim_eq_sum_single Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he _ hk, hray]
  have hw := maj_one_le_majW hs0.le
  have hsb := Real.sqrt_nonneg b
  have hX : ∀ (C : ℝ) (z : ℂ), ‖z‖ ≤ C * Real.sqrt b * (s * majW s) →
      ‖z‖ ≤ |C| * Real.sqrt b * (s * majW s) := fun C z h =>
    h.trans (by gcongr; exact le_abs_self C)
  -- the mass insertions
  have hM : ‖∑ g, ((ctPair P.e (Φ.mass g) a b : ℝ) : ℂ) *
      fLim Φ rep P.e (Pi.single g 1) (majRayVec s) 2 3‖ ≤ D * Real.sqrt b * (s * majW s) := by
    refine (norm_sum_le _ _).trans ?_
    rw [hD, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun g _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hct := abs_ctPair_le P.e (hpos g) ha hab
    rw [Real.sqrt_div' b (hpos g).le] at hct
    have hsg := Real.sqrt_pos.mpr (hpos g)
    have hF1 : ‖fLim Φ rep P.e (Pi.single g 1) (majRayVec s) 2 3‖ ≤ |CF g| * (s * majW s) :=
      (hCF g s hs).1.trans (by
        have : s ≤ s * majW s := le_mul_of_one_le_right hs0.le hw
        gcongr
        · exact le_abs_self _)
    calc |ctPair P.e (Φ.mass g) a b| * ‖fLim Φ rep P.e (Pi.single g 1) (majRayVec s) 2 3‖
        ≤ (3 * P.e ^ 2 * (Real.sqrt b / Real.sqrt (Φ.mass g)) / Real.pi ^ 2) *
            (|CF g| * (s * majW s)) := mul_le_mul hct hF1 (norm_nonneg _) (by positivity)
      _ = 3 * P.e ^ 2 / Real.pi ^ 2 / Real.sqrt (Φ.mass g) * |CF g| * Real.sqrt b *
            (s * majW s) := by field_simp
  have hsum := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add (hX _ _ (hCA s hs a b ha hab hb2 hb1))
      (hX _ _ (hCB s hs a b ha hab hb2 hb1)))) (hX _ _ (hCC s hs a b ha hab hb2 hb1)))) hM)
  rw [norm_mul, norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity), hc2]
  calc 1 / s * ‖_‖ ≤ 1 / s * (|CA| * Real.sqrt b * (s * majW s) +
        |CB| * Real.sqrt b * (s * majW s) + |CC| * Real.sqrt b * (s * majW s) +
        D * Real.sqrt b * (s * majW s)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

/-- **(T2.IR, assembly) The light half at `R₀ = 1`** from `MajLRay` of the three class entries
and `MajTiltRay` of the single-flavour mass insertions. -/
theorem maj_irVal_of_lray (he : P.e ≠ 0)
    (hA : MajLRay fun a b k => vVal aVA baseVA cVA Φ P.e m₀ a b k 2 3)
    (hB : MajLRay fun a b k => vVal aVB baseVB cVB Φ P.e m₀ a b k 2 3)
    (hC : MajLRay fun a b k => vVal aVC baseVC cVC Φ P.e m₀ a b k 2 3)
    (hF : ∀ g, MajTiltRay (fLim Φ rep P.e (Pi.single g 1))) : MajIRVal Φ rep P.e 1 := by
  obtain ⟨C, hC0, hCmp⟩ := maj_qPair_comparable_ray P Φ rep hrep hPV₁ hPV₂ hm₀ hmass he hA hB
    hC hF
  have hm2 := pow_pos hm₀ 2
  obtain ⟨C₀, hC₀⟩ := exists_norm_qPair_light_le P Φ rep hm₀ hmass hrep hPV₁ hPV₂ he
    (S₀ := 0) (S := 1) (by linarith) zero_le_one
  set ρ : ℝ := 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) with hρ
  have hρ0 : 0 < ρ := by
    have : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith
  refine ⟨2 * |C₀| + C / ρ, 1, one_pos, fun a ha ha1 s hs => ?_⟩
  have hw := maj_one_le_majW hs
  have hCρ : 0 ≤ C / ρ := div_nonneg hC0 hρ0.le
  have h0 : ‖qPair Φ rep P.e a 1 0‖ ≤ |C₀| := by
    have := hC₀ a 1 0 ha ha1.le le_rfl le_rfl zero_le_one
    rw [Real.sqrt_one, mul_one] at this
    exact this.trans (le_abs_self _)
  refine (norm_sub_le _ _).trans ?_
  rcases le_or_gt s 1 with hs1 | hs1
  · have h1 : ‖qPair Φ rep P.e a 1 s‖ ≤ |C₀| := by
      have := hC₀ a 1 s ha ha1.le le_rfl hs hs1
      rw [Real.sqrt_one, mul_one] at this
      exact this.trans (le_abs_self _)
    have : 2 * |C₀| ≤ 2 * |C₀| * majW s := le_mul_of_one_le_right (by positivity) hw
    nlinarith [mul_nonneg hCρ (by linarith : (0 : ℝ) ≤ majW s - 1)]
  · have hs0 : -(4 * m₀ ^ 2) < s := by linarith
    have hCw : 0 ≤ C * majW s := mul_nonneg hC0 (by linarith)
    have h := norm_le_of_comparable_rpow (Q := fun a b => qPair Φ rep P.e a b s) (r₀ := 1)
      hCw (by norm_num : (0 : ℝ) < 1 / 2)
      (fun a b d ha hab hbd _ => qPair_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha
        (ha.trans_le hab) ((ha.trans_le hab).trans_le hbd) hs0)
      (fun a b ha hab hb2 hb1 => by
        rw [← Real.sqrt_eq_rpow]
        exact hCmp s hs1.le a b ha hab hb2 hb1) a 1 ha ha1.le le_rfl
    rw [Real.one_rpow, mul_one] at h
    have h1 : ‖qPair Φ rep P.e a 1 s‖ ≤ C / ρ * majW s := by
      refine h.trans (le_of_eq ?_)
      rw [hρ]
      ring
    have : |C₀| ≤ 2 * |C₀| * majW s := by nlinarith [abs_nonneg C₀]
    nlinarith
end Light

/-- **The light half at `decCfg 1 4`** from `MajLRay` of the three class entries. -/
theorem maj_irVal_cfg4 (P : Params) (he : P.e ≠ 0)
    (hA : MajLRay fun a b k => vVal aVA baseVA cVA (decCfg 1 4) P.e 1 a b k 2 3)
    (hB : MajLRay fun a b k => vVal aVB baseVB cVB (decCfg 1 4) P.e 1 a b k 2 3)
    (hC : MajLRay fun a b k => vVal aVC baseVC cVC (decCfg 1 4) P.e 1 a b k 2 3) :
    MajIRVal (decCfg 1 4) (fun _ => 0) P.e 1 := by
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero (by norm_num : (0 : ℝ) ≤ 4)
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  exact maj_irVal_of_lray P (decCfg 1 4) (fun _ => 0) hrep hpv.1 hpv.2 one_pos hmass he hA hB hC
    fun g => maj_tiltRay_fLim_gen P (decCfg 1 4) (fun _ => 0) hrep hpv.1 hpv.2 hmass he _

end QED.GradedProof.RPi4

end
