/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegXPartialFractions
public import QED.Integration.SimplexMerge
public import QED.ChainProof.SetCRegBndSplit
public import QED.TwoLoop.UnitLGraphReduce

/-!
# The two photon pairs and the dressed partial fractions

Merging slots `(4, 6)` and `(5, 7)` leaves the electron parameters intact.
The divided differences from `QED/ChainProof/SetCRegXPartialFractions.lean`
then collect the contributions at the three single and two double poles.
-/

@[expose] public section

open MeasureTheory
open QED.Integration.Feynman (simplexPoint simplexSet)
open QED.Integration.SimplexMerge

namespace QED.ChainProof.SetCUnitM

/-- Split the last two group weights between their light and heavy slots. -/
def photonPairSplit (w : Fin 6 → ℝ) (t u : ℝ) : Fin 8 → ℝ :=
  ![w 0, w 1, w 2, w 3, t, u, w 4 - t, w 5 - u]

private theorem splitAt_photonPair (w : Fin 6 → ℝ) (t u : ℝ) :
    splitAt 5 (splitAt 4 w t) u = photonPairSplit w t u := by
  funext j
  fin_cases j <;> rfl

/-- The two photon fiber integrals preserve integrability and the simplex integral. -/
theorem integral_simplex_photonPairSplit {f : (Fin 8 → ℝ) → ℝ}
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet 7)) :
    let g := fun w => ∫ t in (0 : ℝ)..w 4, ∫ u in (0 : ℝ)..w 5, f (photonPairSplit w t u)
    IntegrableOn (fun x => g (simplexPoint x)) (simplexSet 5) ∧
      (∫ x in simplexSet 7, f (simplexPoint x)) = ∫ x in simplexSet 5, g (simplexPoint x) := by
  intro g
  let h := fun v : Fin 7 → ℝ => ∫ u in (0 : ℝ)..v 5, f (splitAt 5 v u)
  obtain ⟨hI, eI⟩ := integral_simplex_splitAt (m := 6) (by decide) 5 hf
  change IntegrableOn (fun x => h (simplexPoint x)) _ at hI
  obtain ⟨hJ, eJ⟩ := integral_simplex_splitAt (m := 5) (by decide) 4 hI
  have hwidth (w : Fin 6 → ℝ) (t : ℝ) : splitAt 4 w t 5 = w 5 := by
    simp [splitAt, Fin.snoc, Function.update]
    rfl
  have e (w : Fin 6 → ℝ) : (∫ t in (0 : ℝ)..w 4, h (splitAt 4 w t)) = g w := by
    simp only [h, hwidth, splitAt_photonPair, g]
  simp only [e] at hJ eJ
  exact ⟨hJ, eI.trans eJ⟩

open QED.ChainProof.SetCRegX QED.ChainProof.SetCRegBubble

/-- The eight-line expression after the original dressed pair is merged.
The values at its equal masses are the two repeated-slot integrals `ra, rb`. -/
theorem photonPair_four_terms_eq_partialFractions {a b c : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (fa fb fc ra rb : ℝ) :
    let D := massDividedDifference
    let ua := D a b fa fb
    let uc := D c b fc fb
    let wa := D a b ra ua
    let f := D a c ua uc
    let g := D b c rb uc
    let ff := D a c wa f
    let fg := D a b f g
    (b - a) ^ 2 * (f - a * ff - b * (fg - a * D a b ff fg)) =
      bubCoefC a b c * fc + bubCoefA a b c * fa + bubCoefB a b c * fb +
        bubCoefA2 a c * ra + bubCoefB2 b c * rb := by
  dsimp only
  have e₁ : b - a = -(a - b) := by ring
  have e₂ : c - a = -(a - c) := by ring
  have e₃ : c - b = -(b - c) := by ring
  simp only [massDividedDifference, e₁, e₂, e₃, bubCoefC, bubCoefA, bubCoefB,
    bubCoefA2, bubCoefB2]
  field_simp [sub_ne_zero.mpr hab, sub_ne_zero.mpr hac, sub_ne_zero.mpr hbc]
  ring


open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.PauliZero
open QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace
open QED.TwoLoop.UnitLGraphReduce QED.ChainProof.SetCUnit QED.Integration.TwoLoop

private theorem symanzikV_L_unitMasses {P : Params} (hm : P.m = 1)
    (a A b B : ℝ) (z : Fin 8 → ℝ) (hU : lU z ≠ 0) :
    symanzikV ladderAlpha (pvMomentaE .L (restMomentum P.m) (restMomentum P.m))
      (unitMasses P.m a A b B) z =
      gE (lzA z) (lzB z) (lza z) (lzb z) +
        z 4 * a ^ 2 + z 5 * b ^ 2 + z 6 * A ^ 2 + z 7 * B ^ 2 := by
  let P₀ := { P with mγ := 0, Λ := 0 }
  have e :
      symanzikV ladderAlpha (pvMomentaE .L (restMomentum P.m) (restMomentum P.m))
        (pvMasses P₀) z = gE (lzA z) (lzB z) (lza z) (lzb z) := by
    simpa [ladderV, P₀] using symanzikV_ladder P₀ hm hU
  rw [← e]
  unfold symanzikV
  simp [pvMasses, unitMasses, P₀, classPVMasses, Fin.sum_univ_succ]
  ring

/-- On a ladder fiber the two Pauli coefficients depend only on the group sums.
The four photon masses enter in the affine denominator with their own widths. -/
theorem groupedParam_L_ladderSplit {P : Params} (hm : P.m = 1) (he : P.e = 1) (s : Fin 8)
    (a A b B : ℝ) (w : Fin 4 → ℝ) (hw : ∀ i, 0 < w i) (x y t u : ℝ) :
    let U := gU (w 0) (w 1) (w 2) (w 3)
    let E := gE (w 0) (w 1) (w 2) (w 3)
    let k := ((((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2) / kConst).im
    groupedParam .L P s (fun z => (secondCoeff (ladderT1 P z)).im / 6)
      (fun z => -(secondCoeff (ladderT2 P z)).im / 2)
      a A b B Fin.elim0 (ladderSplit w x y t u) =
      factorialResolventPair 2
        (k * (w 2 * gQ (w 0) (w 1) (w 2) (w 3) / (2 * U ^ 5)))
        (-k * (w 2 * (9 * gc (w 1) (w 3) + ga (w 0) (w 1) (w 3)) / (2 * U ^ 4)))
        (E + a ^ 2 * t + A ^ 2 * (w 2 - t) + b ^ 2 * u + B ^ 2 * (w 3 - u)) := by
  intro U E k
  let z := ladderSplit w x y t u
  have hza : groupExtra (r := 0) s z = z := by
    funext j
    have hj : mEmb 0 j = j := Fin.ext rfl
    simp [groupExtra, hj]
  have hU : lU z ≠ 0 := by
    rw [lU_eq, ladderSplit_lzA, ladderSplit_lzB, ladderSplit_lza, ladderSplit_lzb]
    exact (gU_pos (hw 0) (hw 1) (hw 2) (hw 3)).ne'
  unfold groupedParam unitMMasses
  rw [symanzikV_unitM_group, hza]
  dsimp only
  rw [secondCoeff_ladderT1 hm he hU, secondCoeff_ladderT2 hm he hU]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change factorialResolventPair 2 _ _
    (symanzikV ladderAlpha (pvMomentaE .L (restMomentum P.m) (restMomentum P.m))
      (unitMasses P.m a A b B) z) = _
  rw [symanzikV_L_unitMasses hm a A b B z hU]
  dsimp only [z]
  simp only [lU_eq, lQ_eq, la_eq, lc_eq, ladderSplit_lzA, ladderSplit_lzB,
    ladderSplit_lza, ladderSplit_lzb]
  have e₁ (d : ℝ) :
      ((((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst)) * (d : ℂ)).im / 6 =
        k * d := by
    have e : ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (6 / kConst) =
        6 * (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst) := by ring
    rw [e]
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, zero_add]
    dsimp [k]
    ring
  have e₂ (d : ℝ) :
      -((((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst)) * (d : ℂ)).im / 2 =
        -k * d := by
    have e : ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (2 / kConst) =
        2 * (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst) := by ring
    rw [e]
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, zero_add]
    dsimp [k]
    ring
  rw [e₁, e₂]
  congr 1
  change E + t * a ^ 2 + u * b ^ 2 + (w 2 - t) * A ^ 2 + (w 3 - u) * B ^ 2 = _
  ring

end QED.ChainProof.SetCUnitM

end
