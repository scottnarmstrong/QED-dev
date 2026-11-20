/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecTwoF
public import QED.GradedProof.RPi4DecTwoDens

/-!
# (R-Π₄) step L9: the density second-difference bound from the class bounds

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (second
differences in `s`), item D2s. The density `qDens = -(i/c²)(vDens_VA + vDens_VB + vDens_VC +
decMassDens)`; the mass part is done (`QED.GradedProof.RPi4.dec_massDens_two`), so the hypothesis
of `QED.GradedProof.RPi4.dec_twoDiff_of_dens` reduces to one bound per class,
`QED.GradedProof.RPi4.DecVTwo`: `t ‖Δ²ₕ vDens(t, k'(s))‖ ≤ B (t^{q/2} + t^{-q/2}) h²`.

* `DecVTwo`; `dec_rpow_pair_le`, `dec_one_le_rpow_pair`;
* **`dec_twoDiff_of_vTwo`**: the three class bounds give `DecTwoDiff`;
* **`dec_scalAff_of_vTwo`**: `DecFaceGen` and the class bounds at `decCfg 1 4`, `decCfg 1 8`
  give `DecScalAff`.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2
open QED.WickModel (Params)

/-- **The second-difference bound of one class density** at the tilted vectors, for
`|s|, |s + 2h| ≤ δ` and every photon mass `t > 0`. -/
def DecVTwo (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (cv : Fin 5 → ℝ) {F : Type} [Fintype F]
    (Φ : Lepton.Flavors F) (e m₀ c δ : ℝ) : Prop :=
  ∃ B q : ℝ, 0 ≤ B ∧ 0 ≤ q ∧ q < 1 / 2 ∧ ∀ s h : ℝ, |s| ≤ δ → |s + 2 * h| ≤ δ →
    ∀ t : ℝ, 0 < t →
      ‖vDens A base cv Φ e m₀ t (tiltVec c (s + 2 * h)) 2 3 -
        2 * vDens A base cv Φ e m₀ t (tiltVec c (s + h)) 2 3 +
          vDens A base cv Φ e m₀ t (tiltVec c s) 2 3‖ ≤
        B * (t ^ (q / 2) + t ^ (-(q / 2))) / t * h ^ 2

theorem dec_rpow_pair_le {t q q' : ℝ} (ht : 0 < t) (hq : 0 ≤ q) (hqq : q ≤ q') :
    t ^ (q / 2) + t ^ (-(q / 2)) ≤ 2 * (t ^ (q' / 2) + t ^ (-(q' / 2))) := by
  have h0 : 0 ≤ t ^ (q' / 2) := Real.rpow_nonneg ht.le _
  have h0' : 0 ≤ t ^ (-(q' / 2)) := Real.rpow_nonneg ht.le _
  rcases le_total 1 t with h1 | h1
  · have a := Real.rpow_le_rpow_of_exponent_le h1 (by linarith : q / 2 ≤ q' / 2)
    have b := Real.rpow_le_rpow_of_exponent_le h1 (by linarith : -(q / 2) ≤ q' / 2)
    linarith
  · have a := Real.rpow_le_rpow_of_exponent_ge ht h1 (by linarith : -(q' / 2) ≤ -(q / 2))
    have b := Real.rpow_le_rpow_of_exponent_ge ht h1 (by linarith : -(q' / 2) ≤ q / 2)
    linarith

theorem dec_one_le_rpow_pair {t q : ℝ} (ht : 0 < t) (hq : 0 ≤ q) :
    1 ≤ t ^ (q / 2) + t ^ (-(q / 2)) := by
  have h0 : 0 ≤ t ^ (q / 2) := Real.rpow_nonneg ht.le _
  have h0' : 0 ≤ t ^ (-(q / 2)) := Real.rpow_nonneg ht.le _
  rcases le_total 1 t with h1 | h1
  · have := Real.one_le_rpow h1 (by linarith : 0 ≤ q / 2)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge ht h1 (by linarith : -(q / 2) ≤ 0)
    rw [Real.rpow_zero] at this
    linarith

section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
  {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **`DecTwoDiff` from the second-difference bounds of the three class densities.** -/
theorem dec_twoDiff_of_vTwo (P : Params) (he : P.e ≠ 0) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hδm : δ < 4 * m₀ ^ 2) (hδc : δ < 2 * c ^ 2)
    (hVA : DecVTwo aVA baseVA cVA Φ P.e m₀ c δ) (hVB : DecVTwo aVB baseVB cVB Φ P.e m₀ c δ)
    (hVC : DecVTwo aVC baseVC cVC Φ P.e m₀ c δ) :
    DecTwoDiff Φ rep P.e := by
  obtain ⟨BA, qA, hBA, hqA0, hqA, hA⟩ := hVA
  obtain ⟨BB, qB, hBB, hqB0, hqB, hB⟩ := hVB
  obtain ⟨BC, qC, hBC, hqC0, hqC, hC⟩ := hVC
  obtain ⟨BM, hBM, hM⟩ := dec_massDens_two Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he
    (by linarith : -(4 * m₀ ^ 2) < -δ) (by linarith : -δ < δ) hδc
  set q := max (max qA qB) qC
  have hq0 : 0 ≤ q := le_max_of_le_right hqC0
  have hq : q < 1 / 2 := max_lt (max_lt hqA hqB) hqC
  set k : ℂ := -I / ((c ^ 2 : ℝ) : ℂ)
  refine dec_twoDiff_of_dens Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he hc hδ hδm hδc
    (B := ‖k‖ * (2 * BA + 2 * BB + 2 * BC + BM)) (by positivity) hq0 hq
    fun s h hs hs2 t ht => ?_
  set X := t ^ (q / 2) + t ^ (-(q / 2))
  have hX1 : 1 ≤ X := dec_one_le_rpow_pair ht hq0
  have hh := sq_nonneg h
  have cls : ∀ (B q' : ℝ) (v : ℝ → ℂ), 0 ≤ B → 0 ≤ q' → q' ≤ q →
      ‖v (s + 2 * h) - 2 * v (s + h) + v s‖ ≤ B * (t ^ (q' / 2) + t ^ (-(q' / 2))) / t * h ^ 2 →
      ‖v (s + 2 * h) - 2 * v (s + h) + v s‖ ≤ 2 * B * X / t * h ^ 2 := by
    intro B q' v hB hq' hqq hv
    refine hv.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ ht.le) hh)
    have := dec_rpow_pair_le ht hq' hqq
    nlinarith
  have tA := cls BA qA (fun s => vDens aVA baseVA cVA Φ P.e m₀ t (tiltVec c s) 2 3) hBA hqA0
    ((le_max_left _ _).trans (le_max_left _ _)) (hA s h hs hs2 t ht)
  have tB := cls BB qB (fun s => vDens aVB baseVB cVB Φ P.e m₀ t (tiltVec c s) 2 3) hBB hqB0
    ((le_max_right _ _).trans (le_max_left _ _)) (hB s h hs hs2 t ht)
  have tC := cls BC qC (fun s => vDens aVC baseVC cVC Φ P.e m₀ t (tiltVec c s) 2 3) hBC hqC0
    (le_max_right _ _) (hC s h hs hs2 t ht)
  have tM := hM s h (abs_le.mp hs) (abs_le.mp hs2) t ht
  have tM' : BM / t * h ^ 2 ≤ BM * X / t * h ^ 2 :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_mul_of_one_le_right hBM hX1)
      ht.le) hh
  have e : qDens Φ rep P.e m₀ c (s + 2 * h) t - 2 * qDens Φ rep P.e m₀ c (s + h) t +
      qDens Φ rep P.e m₀ c s t = k *
      (((vDens aVA baseVA cVA Φ P.e m₀ t (tiltVec c (s + 2 * h)) 2 3 -
          2 * vDens aVA baseVA cVA Φ P.e m₀ t (tiltVec c (s + h)) 2 3 +
          vDens aVA baseVA cVA Φ P.e m₀ t (tiltVec c s) 2 3) +
        (vDens aVB baseVB cVB Φ P.e m₀ t (tiltVec c (s + 2 * h)) 2 3 -
          2 * vDens aVB baseVB cVB Φ P.e m₀ t (tiltVec c (s + h)) 2 3 +
          vDens aVB baseVB cVB Φ P.e m₀ t (tiltVec c s) 2 3)) +
        (vDens aVC baseVC cVC Φ P.e m₀ t (tiltVec c (s + 2 * h)) 2 3 -
          2 * vDens aVC baseVC cVC Φ P.e m₀ t (tiltVec c (s + h)) 2 3 +
          vDens aVC baseVC cVC Φ P.e m₀ t (tiltVec c s) 2 3) +
        (decMassDens Φ rep P.e c (s + 2 * h) t - 2 * decMassDens Φ rep P.e c (s + h) t +
          decMassDens Φ rep P.e c s t)) := by
    simp only [qDens, decMassDens, k]
    ring
  rw [e, norm_mul]
  have hk := norm_nonneg k
  refine (mul_le_mul_of_nonneg_left (norm_add₄_le.trans
    (add_le_add (add_le_add (add_le_add tA tB) tC) (tM.trans tM'))) hk).trans (le_of_eq ?_)
  ring

end Classes

/-- **`DecScalAff` modulo `DecFaceGen` from the class bounds** at `decCfg 1 4`, `decCfg 1 8`
(flavour map `fun _ => 0`, `m₀ = 1`). -/
theorem dec_scalAff_of_vTwo (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hV : ∀ x : ℝ, x = 4 ∨ x = 8 → ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ < 4 ∧ δ < 2 * c ^ 2 ∧
      DecVTwo aVA baseVA cVA (decCfg 1 x) P.e 1 c δ ∧
      DecVTwo aVB baseVB cVB (decCfg 1 x) P.e 1 c δ ∧
      DecVTwo aVC baseVC cVC (decCfg 1 x) P.e 1 c δ) :
    DecScalAff P.e := by
  refine dec_scalAff_of_twoDiff P he hF fun x hx => ?_
  have hx0 : 0 < x := by rcases hx with rfl | rfl <;> norm_num
  have hx1 : (1 : ℝ) ≤ x := by rcases hx with rfl | rfl <;> norm_num
  have hm₀ : (0 : ℝ) < 1 := one_pos
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 x).mass g := dec_cfg_mass_ge le_rfl hm₀
    (by rw [one_pow]; exact hx1)
  have hpv := dec_cfg_pv (μ := 1) one_ne_zero hx0.le
  have hrep : ∀ f : Fin 3, (fun _ : Fin 3 => (0 : Fin 3)) ((fun _ => 0) f) = (fun _ => 0) f :=
    fun _ => rfl
  obtain ⟨c, δ, hc, hδ, hδm, hδc, hA, hB, hC⟩ := hV x hx
  exact dec_twoDiff_of_vTwo (decCfg 1 x) (fun _ => 0) hm₀ hmass hrep hpv.1 hpv.2 P he hc hδ
    (by rw [one_pow, mul_one]; exact hδm) hδc hA hB hC

end QED.GradedProof.RPi4

end
