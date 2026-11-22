/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndRepeat
public import QED.ChainProof.SetCRegBndPhotonMerge
public import QED.ChainProof.SetCRegBndTransport

/-!
# Two photon-pair fibers

The two affine mass parameters can be removed by successive divided
differences. A repeated light mass has the positive width weight from
`QED/ChainProof/SetCRegBndRepeat.lean`.
-/

@[expose] public section

open MeasureTheory Set
open QED.ChainProof.SetCRegX (massDividedDifference)
open QED.Integration.SimplexMerge

namespace QED.ChainProof.SetCUnitM

/-- The adjacent pair of factorial resolvents at the two merged masses. -/
noncomputable def photonFiberValue (n : ℕ) (F G E W H x y : ℝ) : ℝ :=
  factorialResolventPair n F G (E + x * W + y * H)

private theorem fiber_base_pos {E W H x X y t : ℝ}
    (hE : 0 ≤ E) (hW : 0 < W) (hH : 0 < H) (hx : 0 < x) (hX : 0 < X)
    (hy : 0 < y) (ht : t ∈ uIcc 0 W) :
    0 < E + x * t + X * (W - t) + y * H := by
  rw [uIcc_of_le hW.le] at ht
  have h1 := mul_nonneg hx.le ht.1
  have h2 := mul_nonneg hX.le (sub_nonneg.mpr ht.2)
  linarith only [hE, h1, h2, mul_pos hy hH]

private theorem continuousOn_photonFiber {E W H x X y : ℝ}
    (hE : 0 ≤ E) (hW : 0 < W) (hH : 0 < H) (hx : 0 < x) (hX : 0 < X)
    (hy : 0 < y) (n : ℕ) (F G : ℝ) :
    ContinuousOn
      (fun t => factorialResolventPair n F G (E + x * t + X * (W - t) + y * H))
      (uIcc 0 W) := by
  have hV : Continuous (fun t => E + x * t + X * (W - t) + y * H) := by fun_prop
  have hn (t : ℝ) (ht : t ∈ uIcc 0 W) :=
    (fiber_base_pos hE hW hH hx hX hy ht).ne'
  unfold factorialResolventPair
  exact (continuousOn_const.div (hV.continuousOn.pow _) fun t ht =>
      pow_ne_zero _ (hn t ht)).sub
    (continuousOn_const.div (hV.continuousOn.pow _) fun t ht => pow_ne_zero _ (hn t ht))

private theorem integral_photonFiber_inner {K H y Y : ℝ}
    (hH : 0 < H) (hK : 0 ≤ K) (hy : 0 < y) (hY : 0 < Y) (hyY : y ≠ Y)
    (n : ℕ) (F G : ℝ) :
    (∫ u in (0 : ℝ)..H, factorialResolventPair (n + 1) F G (K + y * u + Y * (H - u))) =
      massDividedDifference y Y
        (factorialResolventPair n F G (K + y * H))
        (factorialResolventPair n F G (K + Y * H)) :=
  integral_factorialResolventPair_split n F G hyY
    (add_pos_of_nonneg_of_pos hK (mul_pos hy hH))
    (add_pos_of_nonneg_of_pos hK (mul_pos hY hH))

/-- Integrating two distinct mass pairs gives nested divided differences. -/
theorem integral_photonFiber {n : ℕ} {F G E W H x X y Y : ℝ}
    (hE : 0 ≤ E) (hW : 0 < W) (hH : 0 < H)
    (hx : 0 < x) (hX : 0 < X) (hy : 0 < y) (hY : 0 < Y)
    (hxX : x ≠ X) (hyY : y ≠ Y) :
    let D := massDividedDifference
    let f := photonFiberValue n F G E W H
    (∫ t in (0 : ℝ)..W, ∫ u in (0 : ℝ)..H,
      factorialResolventPair (n + 2) F G
        (E + x * t + X * (W - t) + y * u + Y * (H - u))) =
      D x X (D y Y (f x y) (f x Y)) (D y Y (f X y) (f X Y)) := by
  dsimp only
  have hI := continuousOn_photonFiber hE hW hH hx hX hy (n + 1) F G
  have hJ := continuousOn_photonFiber hE hW hH hx hX hY (n + 1) F G
  have e (t : ℝ) (ht : t ∈ uIcc 0 W) := integral_photonFiber_inner (K :=
    E + x * t + X * (W - t)) hH (by
      rw [uIcc_of_le hW.le] at ht
      exact add_nonneg (add_nonneg hE (mul_nonneg hx.le ht.1))
        (mul_nonneg hX.le (sub_nonneg.mpr ht.2))) hy hY hyY (n + 1) F G
  rw [intervalIntegral.integral_congr e]
  unfold massDividedDifference
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (hI.intervalIntegrable) (hJ.intervalIntegrable)]
  have ev (z : ℝ) (hz : 0 < z) :
      (∫ t in (0 : ℝ)..W, factorialResolventPair (n + 1) F G
        (E + x * t + X * (W - t) + z * H)) =
      massDividedDifference x X
        (photonFiberValue n F G E W H x z) (photonFiberValue n F G E W H X z) := by
    simp_rw [show ∀ t : ℝ, E + x * t + X * (W - t) + z * H =
      E + z * H + x * t + X * (W - t) by intro t; ring]
    unfold massDividedDifference photonFiberValue
    rw [integral_factorialResolventPair_split n F G hxX (by positivity) (by positivity)]
    rw [show E + z * H + x * W = E + x * W + z * H by ring,
      show E + z * H + X * W = E + X * W + z * H by ring]
  rw [ev y hy, ev Y hY]
  simp only [massDividedDifference, div_sub_div_same]
  ring

/-- Integrating a repeated light mass in the first pair gives a weighted endpoint. -/
theorem integral_mul_photonFiber {n : ℕ} {F G E W H x X y Y : ℝ}
    (hE : 0 ≤ E) (hW : 0 < W) (hH : 0 < H)
    (hx : 0 < x) (hX : 0 < X) (hy : 0 < y) (hY : 0 < Y)
    (hxX : x ≠ X) (hyY : y ≠ Y) :
    let D := massDividedDifference
    let f := photonFiberValue n F G E W H
    let r := photonFiberValue (n + 1) F G E W H
    (∫ t in (0 : ℝ)..W, ∫ u in (0 : ℝ)..H,
      t * factorialResolventPair (n + 3) F G
        (E + x * t + X * (W - t) + y * u + Y * (H - u))) =
      D x X (D y Y (W * r x y) (W * r x Y))
        (D x X (D y Y (f x y) (f x Y)) (D y Y (f X y) (f X Y))) := by
  dsimp only
  have hI := continuous_id.continuousOn.mul
    (continuousOn_photonFiber hE hW hH hx hX hy (n + 2) F G)
  have hJ := continuous_id.continuousOn.mul
    (continuousOn_photonFiber hE hW hH hx hX hY (n + 2) F G)
  have e (t : ℝ) (ht : t ∈ uIcc 0 W) :
      (∫ u in (0 : ℝ)..H, t * factorialResolventPair (n + 3) F G
        (E + x * t + X * (W - t) + y * u + Y * (H - u))) =
      (t * factorialResolventPair (n + 2) F G (E + x * t + X * (W - t) + y * H) -
        t * factorialResolventPair (n + 2) F G (E + x * t + X * (W - t) + Y * H)) /
        (Y - y) := by
    rw [intervalIntegral.integral_const_mul, integral_photonFiber_inner hH _ hy hY hyY]
    · unfold massDividedDifference
      ring
    · rw [uIcc_of_le hW.le] at ht
      exact add_nonneg (add_nonneg hE (mul_nonneg hx.le ht.1))
        (mul_nonneg hX.le (sub_nonneg.mpr ht.2))
  have hII : IntervalIntegrable (fun t => t *
      factorialResolventPair (n + 2) F G (E + x * t + X * (W - t) + y * H)) volume 0 W :=
    hI.intervalIntegrable
  have hJJ : IntervalIntegrable (fun t => t *
      factorialResolventPair (n + 2) F G (E + x * t + X * (W - t) + Y * H)) volume 0 W :=
    hJ.intervalIntegrable
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_div,
    intervalIntegral.integral_sub hII hJJ]
  have ev (z : ℝ) (hz : 0 < z) :
      (∫ t in (0 : ℝ)..W, t * factorialResolventPair (n + 2) F G
        (E + x * t + X * (W - t) + z * H)) =
      massDividedDifference x X (W * photonFiberValue (n + 1) F G E W H x z)
        (massDividedDifference x X
          (photonFiberValue n F G E W H x z) (photonFiberValue n F G E W H X z)) := by
    simp_rw [show ∀ t : ℝ, E + x * t + X * (W - t) + z * H =
      E + z * H + x * t + X * (W - t) by intro t; ring]
    unfold massDividedDifference photonFiberValue
    rw [integral_mul_factorialResolventPair_split n F G hxX (by positivity) (by positivity)]
    rw [show E + z * H + x * W = E + x * W + z * H by ring,
      show E + z * H + X * W = E + X * W + z * H by ring]
  rw [ev y hy, ev Y hY]
  simp only [massDividedDifference, div_sub_div_same]
  ring

/-- Two equal masses in the first pair contribute its width. -/
theorem integral_photonFiber_eq {n : ℕ} {F G E W H x y Y : ℝ}
    (hE : 0 ≤ E) (hW : 0 < W) (hH : 0 < H)
    (hx : 0 < x) (hy : 0 < y) (hY : 0 < Y) (hyY : y ≠ Y) :
    let r := photonFiberValue (n + 1) F G E W H x
    (∫ t in (0 : ℝ)..W, ∫ u in (0 : ℝ)..H,
      factorialResolventPair (n + 2) F G
        (E + x * t + x * (W - t) + y * u + Y * (H - u))) =
      massDividedDifference y Y (W * r y) (W * r Y) := by
  dsimp only
  simp_rw [show ∀ t : ℝ, E + x * t + x * (W - t) = E + x * W by intro t; ring]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    integral_photonFiber_inner hH (K := E + x * W) (by positivity) hy hY hyY]
  unfold photonFiberValue massDividedDifference
  ring

private theorem intervalIntegral_integral_swap_of_continuousOn {W H : ℝ}
    (hW : 0 ≤ W) (hH : 0 ≤ H) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 W ×ˢ Icc 0 H)) :
    (∫ t in (0 : ℝ)..W, ∫ u in (0 : ℝ)..H, f t u) =
      ∫ u in (0 : ℝ)..H, ∫ t in (0 : ℝ)..W, f t u := by
  have hI : IntegrableOn (Function.uncurry f) (Icc 0 W ×ˢ Icc 0 H)
      ((volume : Measure ℝ).prod volume) :=
    hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hJ : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc 0 W)).prod (volume.restrict (Ioc 0 H))) := by
    rw [Measure.prod_restrict]
    exact hI.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simp_rw [intervalIntegral.integral_of_le hW, intervalIntegral.integral_of_le hH]
  exact integral_integral_swap hJ

private theorem continuousOn_photonBox {E W H x X y Y : ℝ}
    (hE : 0 ≤ E) (hW : 0 < W)
    (hx : 0 < x) (hX : 0 < X) (hy : 0 < y) (hY : 0 < Y)
    (n : ℕ) (F G : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => factorialResolventPair n F G
      (E + x * p.1 + X * (W - p.1) + y * p.2 + Y * (H - p.2))) (Icc 0 W ×ˢ Icc 0 H) := by
  have hV : Continuous (fun p : ℝ × ℝ =>
      E + x * p.1 + X * (W - p.1) + y * p.2 + Y * (H - p.2)) := by fun_prop
  have hn (p : ℝ × ℝ) (hp : p ∈ Icc 0 W ×ˢ Icc 0 H) :
      E + x * p.1 + X * (W - p.1) + y * p.2 + Y * (H - p.2) ≠ 0 := by
    have hy' := mul_nonneg hy.le hp.2.1
    have hY' := mul_nonneg hY.le (sub_nonneg.mpr hp.2.2)
    have hpos : 0 < x * p.1 + X * (W - p.1) := by
      rcases hp.1.1.eq_or_lt with ht | ht
      · rw [← ht, mul_zero, sub_zero, zero_add]
        exact mul_pos hX hW
      · exact add_pos_of_pos_of_nonneg (mul_pos hx ht)
          (mul_nonneg hX.le (sub_nonneg.mpr hp.1.2))
    exact (by linarith only [hE, hy', hY', hpos] :
      0 < E + x * p.1 + X * (W - p.1) + y * p.2 + Y * (H - p.2)).ne'
  unfold factorialResolventPair
  exact (continuousOn_const.div (hV.continuousOn.pow _) fun p hp =>
      pow_ne_zero _ (hn p hp)).sub
    (continuousOn_const.div (hV.continuousOn.pow _) fun p hp => pow_ne_zero _ (hn p hp))

/-- At positive masses, either photon pair can be integrated first, including
a polynomial numerator in the two split parameters. -/
theorem integral_photonBox_swap {E W H x X y Y : ℝ}
    (hE : 0 ≤ E) (hW : 0 < W) (hH : 0 < H)
    (hx : 0 < x) (hX : 0 < X) (hy : 0 < y) (hY : 0 < Y)
    (n : ℕ) (F G : ℝ) {g : ℝ → ℝ → ℝ}
    (hg : Continuous (Function.uncurry g)) :
    (∫ t in (0 : ℝ)..W, ∫ u in (0 : ℝ)..H, g t u * factorialResolventPair n F G
      (E + x * t + X * (W - t) + y * u + Y * (H - u))) =
      ∫ u in (0 : ℝ)..H, ∫ t in (0 : ℝ)..W, g t u * factorialResolventPair n F G
        (E + x * t + X * (W - t) + y * u + Y * (H - u)) := by
  exact intervalIntegral_integral_swap_of_continuousOn hW.le hH.le
    (hf := hg.continuousOn.mul (continuousOn_photonBox hE hW hx hX hy hY n F G))

section Ladder

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.UnitLGraphReduce
open QED.ChainProof.SetCUnit QED.ChainProof.SetCRegBubble
open QED.ChainProof.SetCRegDisp (kerT)
open QED.Integration.Feynman (simplexPoint simplexSet)
open QED.TwoLoop.Bridge QED.Integration.TwoLoop
open scoped Real

private theorem symanzikV_ladderPhoton {P : Params} (hm : P.m = 1)
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

private theorem groupedParamRepeat_L_ladderSplit {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (s : Fin 8) (a A b B : ℝ) (w : Fin 4 → ℝ) (hw : ∀ i, 0 < w i) (x y t u : ℝ) :
    let U := gU (w 0) (w 1) (w 2) (w 3)
    let E := gE (w 0) (w 1) (w 2) (w 3)
    let k := ((((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2) / kConst).im
    groupedParamRepeat .L P s (fun z => (secondCoeff (ladderT1 P z)).im / 6)
      (fun z => -(secondCoeff (ladderT2 P z)).im / 2)
      a A b B Fin.elim0 (ladderSplit w x y t u) =
      (ladderSplit w x y t u) s * factorialResolventPair 3
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
  unfold groupedParamRepeat unitMMasses
  rw [symanzikV_unitM_group, hza]
  dsimp only
  rw [secondCoeff_ladderT1 hm he hU, secondCoeff_ladderT2 hm he hU]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [show mEmb 0 s = s from Fin.ext rfl]
  change z s * factorialResolventPair 3 _ _
    (symanzikV ladderAlpha (pvMomentaE .L (restMomentum P.m) (restMomentum P.m))
      (unitMasses P.m a A b B) z) = _
  rw [symanzikV_ladderPhoton hm a A b B z hU]
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
  congr 2
  change E + t * a ^ 2 + u * b ^ 2 + (w 2 - t) * A ^ 2 + (w 3 - u) * B ^ 2 = _
  ring

/-- The ladder Pauli integrand with both photon pairs merged. The first mass
argument belongs to the dressed slot, whose repeat contributes its width. -/
noncomputable def ladderPhotonNode (P : Params) (outer : Bool) (repeatMass : Bool)
    (w : Fin 4 → ℝ) (x y : ℝ) : ℝ :=
  let U := gU (w 0) (w 1) (w 2) (w 3)
  let E := gE (w 0) (w 1) (w 2) (w 3)
  let k := ((((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2) / kConst).im
  let F := k * (w 2 * gQ (w 0) (w 1) (w 2) (w 3) / (2 * U ^ 5))
  let G := -k * (w 2 * (9 * gc (w 1) (w 3) + ga (w 0) (w 1) (w 3)) / (2 * U ^ 4))
  let W := if outer then w 2 else w 3
  let H := if outer then w 3 else w 2
  w 0 * w 1 * (if repeatMass then W else 1) *
    photonFiberValue (if repeatMass then 1 else 0) F G E W H x y

private noncomputable def ladderPhotonTrace (P : Params) (outer repeatMass : Bool)
    (a A b B : ℝ) : (Fin 8 → ℝ) → ℝ :=
  let s : Fin 8 := if outer then 4 else 5
  let F := fun w => (secondCoeff (ladderT1 P w)).im / 6
  let G := fun w => -(secondCoeff (ladderT2 P w)).im / 2
  let l := if outer then a else b
  let L := if outer then A else B
  let r := if outer then b else a
  let R := if outer then B else A
  if repeatMass then groupedParamRepeat .L P s F G l L r R Fin.elim0
  else groupedParam .L P s F G l L r R Fin.elim0

private theorem ladderMerged_ladderPhotonTrace {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (outer repeatMass : Bool) {a A b B : ℝ}
    (ha : 0 < a) (hA : 0 < A) (hb : 0 < b) (hB : 0 < B)
    (w : Fin 4 → ℝ) (hw : ∀ i, 0 < w i) :
    let U := gU (w 0) (w 1) (w 2) (w 3)
    let E := gE (w 0) (w 1) (w 2) (w 3)
    let k := ((((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2) / kConst).im
    let F := k * (w 2 * gQ (w 0) (w 1) (w 2) (w 3) / (2 * U ^ 5))
    let G := -k * (w 2 * (9 * gc (w 1) (w 3) + ga (w 0) (w 1) (w 3)) / (2 * U ^ 4))
    let W := if outer then w 2 else w 3
    let H := if outer then w 3 else w 2
    ladderMerged (ladderPhotonTrace P outer repeatMass a A b B) w =
      w 0 * w 1 * (∫ t in (0 : ℝ)..W, ∫ u in (0 : ℝ)..H,
        (if repeatMass then t else 1) * factorialResolventPair
          (if repeatMass then 3 else 2) F G
          (E + a ^ 2 * t + A ^ 2 * (W - t) + b ^ 2 * u + B ^ 2 * (H - u))) := by
  intro U E k F G W H
  let s : Fin 8 := if outer then 4 else 5
  let l := if outer then a else b
  let L := if outer then A else B
  let r := if outer then b else a
  let R := if outer then B else A
  have hE : 0 ≤ E := gE_nonneg (hw 0) (hw 1) (hw 2) (hw 3)
  have e (x y t u : ℝ) :
      ladderPhotonTrace P outer repeatMass a A b B (ladderSplit w x y t u) =
        (if repeatMass then (ladderSplit w x y t u) s else 1) *
          factorialResolventPair (if repeatMass then 3 else 2) F G
            (E + l ^ 2 * t + L ^ 2 * (w 2 - t) + r ^ 2 * u + R ^ 2 * (w 3 - u)) := by
    have hv := groupedParam_L_ladderSplit hm he s l L r R w hw x y t u
    dsimp only at hv
    cases repeatMass
    · simpa only [ladderPhotonTrace, Bool.false_eq_true, ite_false, one_mul] using hv
    · simpa only [ladderPhotonTrace, Bool.true_eq, ite_true] using
        groupedParamRepeat_L_ladderSplit hm he s l L r R w hw x y t u
  unfold ladderMerged
  simp_rw [e]
  have hxy (x y t u : ℝ) :
      (ladderSplit w x y t u) s = if outer then t else u := by
    cases outer <;> rfl
  simp_rw [hxy]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  cases outer
  · have hh := integral_photonBox_swap (W := w 2) (H := w 3)
      (x := b ^ 2) (X := B ^ 2) (y := a ^ 2) (Y := A ^ 2)
      hE (hw 2) (hw 3) (pow_pos hb _) (pow_pos hB _) (pow_pos ha _) (pow_pos hA _)
      (if repeatMass then 3 else 2) F G
      (g := fun _ u => if repeatMass then u else 1) (by
        cases repeatMass
        · exact continuous_const
        · exact continuous_snd)
    simp only [W, H, l, L, r, R, Bool.false_eq_true, ite_false]
    rw [hh]
    simp_rw [show ∀ t u : ℝ,
      E + b ^ 2 * t + B ^ 2 * (w 2 - t) + a ^ 2 * u + A ^ 2 * (w 3 - u) =
      E + a ^ 2 * u + A ^ 2 * (w 3 - u) + b ^ 2 * t + B ^ 2 * (w 2 - t) by
        intro t u
        ring]
  · rfl

/-- A ladder partial-fraction node with the ordinary photon difference retained. -/
noncomputable def ladderPhotonDifference (P : Params) (outer repeatMass : Bool)
    (w : Fin 4 → ℝ) (x y Y : ℝ) : ℝ :=
  massDividedDifference y Y (ladderPhotonNode P outer repeatMass w x y)
    (ladderPhotonNode P outer repeatMass w x Y)

private theorem ladderMerged_ladderPhotonTrace_of_ne {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (outer repeatMass : Bool) {a A b B : ℝ}
    (ha : 0 < a) (hA : 0 < A) (hb : 0 < b) (hB : 0 < B)
    (haA : a ^ 2 ≠ A ^ 2) (hbB : b ^ 2 ≠ B ^ 2)
    (w : Fin 4 → ℝ) (hw : ∀ i, 0 < w i) :
    let D := massDividedDifference
    let f := fun x => ladderPhotonDifference P outer false w x (b ^ 2) (B ^ 2)
    let r := ladderPhotonDifference P outer true w (a ^ 2) (b ^ 2) (B ^ 2)
    ladderMerged (ladderPhotonTrace P outer repeatMass a A b B) w =
      if repeatMass then D (a ^ 2) (A ^ 2) r (D (a ^ 2) (A ^ 2) (f (a ^ 2)) (f (A ^ 2)))
      else D (a ^ 2) (A ^ 2) (f (a ^ 2)) (f (A ^ 2)) := by
  dsimp only
  rw [ladderMerged_ladderPhotonTrace hm he outer repeatMass ha hA hb hB w hw]
  have hE := gE_nonneg (hw 0) (hw 1) (hw 2) (hw 3)
  have hW : 0 < (if outer then w 2 else w 3) := by cases outer; exact hw 3; exact hw 2
  have hH : 0 < (if outer then w 3 else w 2) := by cases outer; exact hw 2; exact hw 3
  cases repeatMass
  · simp only [Bool.false_eq_true, ite_false, one_mul]
    rw [integral_photonFiber (n := 0) hE hW hH
      (pow_pos ha _) (pow_pos hA _) (pow_pos hb _) (pow_pos hB _) haA hbB]
    unfold ladderPhotonDifference ladderPhotonNode massDividedDifference
    simp only [Bool.false_eq_true, ite_false]
    ring
  · simp only [ite_true]
    rw [integral_mul_photonFiber (n := 0) hE hW hH
      (pow_pos ha _) (pow_pos hA _) (pow_pos hb _) (pow_pos hB _) haA hbB]
    unfold ladderPhotonDifference ladderPhotonNode massDividedDifference
    simp only [ite_true, Bool.false_eq_true, ite_false]
    ring

private theorem ladderMerged_ladderPhotonTrace_eq {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (outer : Bool) {a b B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hB : 0 < B) (hbB : b ^ 2 ≠ B ^ 2)
    (w : Fin 4 → ℝ) (hw : ∀ i, 0 < w i) :
    ladderMerged (ladderPhotonTrace P outer false a a b B) w =
      ladderPhotonDifference P outer true w (a ^ 2) (b ^ 2) (B ^ 2) := by
  rw [ladderMerged_ladderPhotonTrace hm he outer false ha ha hb hB w hw]
  have hE := gE_nonneg (hw 0) (hw 1) (hw 2) (hw 3)
  have hW : 0 < (if outer then w 2 else w 3) := by cases outer; exact hw 3; exact hw 2
  have hH : 0 < (if outer then w 3 else w 2) := by cases outer; exact hw 2; exact hw 3
  simp only [Bool.false_eq_true, ite_false, one_mul]
  rw [integral_photonFiber_eq (n := 0) hE hW hH (pow_pos ha _) (pow_pos hb _) (pow_pos hB _) hbB]
  unfold ladderPhotonDifference ladderPhotonNode massDividedDifference
  simp only [ite_true]
  ring

private theorem integrableOn_ladderPhotonTrace {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (outer repeatMass : Bool) {a A b B : ℝ}
    (ha : 0 < a) (hA : 0 < A) (hb : 0 < b) (hB : 0 < B) :
    IntegrableOn (fun x => ladderPhotonTrace P outer repeatMass a A b B (simplexPoint x))
      (simplexSet 7) := by
  let s : Fin 8 := if outer then 4 else 5
  let l := if outer then a else b
  let L := if outer then A else B
  let r := if outer then b else a
  let R := if outer then B else A
  let F := fun w => (secondCoeff (ladderT1 P w)).im / 6
  let G := fun w => -(secondCoeff (ladderT2 P w)).im / 2
  let μ := min (min a A) (min b B)
  have hμ : 0 < μ := lt_min (lt_min ha hA) (lt_min hb hB)
  have hμa : μ ≤ a := (min_le_left _ _).trans (min_le_left _ _)
  have hμA : μ ≤ A := (min_le_left _ _).trans (min_le_right _ _)
  have hμb : μ ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hμB : μ ≤ B := (min_le_right _ _).trans (min_le_right _ _)
  have hM : MassesGe μ l L r R := by
    cases outer
    · exact ⟨hμb, hμB, hμa, hμA⟩
    · exact ⟨hμa, hμA, hμb, hμB⟩
  have hs : 4 ≤ s.val := by cases outer <;> decide
  cases repeatMass
  · exact (unitMPauliZero_L_im_eq_pair hm he hs hμ hM
      (cs := Fin.elim0) (fun j => j.elim0)).1
  · have hcs (j : Fin 1) : μ ≤ (![a] : Fin 1 → ℝ) j := by
      fin_cases j
      exact hμa
    have heq : (![a] : Fin 1 → ℝ) (Fin.last 0) ^ 2 = unitMasses P.m l L r R s ^ 2 := by
      cases outer <;> rfl
    have hI := (unitMPauliZero_L_im_eq_pair hm he hs hμ hM hcs).1
    have h := (integral_groupedParam_repeat .L P s F G hI heq).1
    have e : Fin.init (![a] : Fin 1 → ℝ) = Fin.elim0 := Subsingleton.elim _ _
    rw [e] at h
    exact h

/-- The five dressed partial fractions on the ladder simplex, with the
ordinary Pauli–Villars difference represented by a divided difference. -/
noncomputable def ladderPhotonPF (P : Params) (outer : Bool) (w : Fin 4 → ℝ)
    (a b c : ℝ) : ℝ :=
  let f := fun x => ladderPhotonDifference P outer false w x a b
  let r := fun x => ladderPhotonDifference P outer true w x a b
  bubCoefC a b c * f c + bubCoefA a b c * f a + bubCoefB a b c * f b +
    bubCoefA2 a c * r a + bubCoefB2 b c * r b

private theorem integral_massDividedDifference {u v : (Fin 3 → ℝ) → ℝ}
    (hu : IntegrableOn u (simplexSet 3)) (hv : IntegrableOn v (simplexSet 3))
    (a b : ℝ) :
    IntegrableOn (fun x => massDividedDifference a b (u x) (v x)) (simplexSet 3) ∧
    massDividedDifference a b (∫ x in simplexSet 3, u x) (∫ x in simplexSet 3, v x) =
      ∫ x in simplexSet 3, massDividedDifference a b (u x) (v x) := by
  unfold massDividedDifference
  exact ⟨(hu.sub hv).div_const _, by rw [integral_div, integral_sub hu hv]⟩

/-- The actual ladder transverse trace after merging both photon pairs.
The result holds for both dressed placements, away from the two spectral
coincidences. Integrability is for the combined five-term integrand. -/
theorem kerT_L_im_eq_integral_ladderPhotonPF {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (outer : Bool) {p q T : ℝ} (hp : 0 < p) (hpq : p < q) (hT : 0 < T)
    (hpT : p ^ 2 ≠ T) (hqT : q ^ 2 ≠ T) :
    let s : Fin 8 := if outer then 4 else 5
    let f := fun x => ladderPhotonPF P outer (simplexPoint x) (p ^ 2) (q ^ 2) T
    IntegrableOn f (simplexSet 3) ∧
      (q ^ 2 - p ^ 2) ^ 2 * (kerT .L P s p q T).im = ∫ x in simplexSet 3, f x := by
  intro s f
  let M := √T
  have hM : 0 < M := Real.sqrt_pos.2 hT
  have hM2 : M ^ 2 = T := Real.sq_sqrt hT.le
  have hq := hp.trans hpq
  have hab : p ^ 2 ≠ q ^ 2 := (pow_lt_pow_left₀ hpq hp.le (by decide)).ne
  have hac : p ^ 2 ≠ M ^ 2 := hM2.symm ▸ hpT
  have hbc : q ^ 2 ≠ M ^ 2 := hM2.symm ▸ hqT
  have hs : s = 4 ∨ s = 5 := by cases outer; exact Or.inr rfl; exact Or.inl rfl
  let a := p ^ 2
  let b := q ^ 2
  let c := M ^ 2
  let D := massDividedDifference
  let J := fun (rep : Bool) (m n : ℝ) (x : Fin 3 → ℝ) =>
    ladderMerged (ladderPhotonTrace P outer rep m n p q) (simplexPoint x)
  have hJ (rep : Bool) {m n : ℝ} (hm' : 0 < m) (hn' : 0 < n) :=
    integral_simplex_ladderSplit (integrableOn_ladderPhotonTrace hm he outer rep hm' hn' hp hq)
  let u := J false p q
  let v := J false q q
  let w := J false M q
  let r := J true p q
  let S := fun x => D a c (u x) (w x)
  let B := fun x => D b c (v x) (w x)
  let SS := fun x => D a c (r x) (S x)
  let SB := fun x => D a b (S x) (B x)
  let SSB := fun x => D a b (SS x) (SB x)
  let K := fun x => S x - a * SS x - b * (SB x - a * SSB x)
  have hS := integral_massDividedDifference (hJ false hp hq).1 (hJ false hM hq).1 a c
  have hB := integral_massDividedDifference (hJ false hq hq).1 (hJ false hM hq).1 b c
  have hSS := integral_massDividedDifference (hJ true hp hq).1 hS.1 a c
  have hSB := integral_massDividedDifference hS.1 hB.1 a b
  have hSSB := integral_massDividedDifference hSS.1 hSB.1 a b
  have hG := hSB.1.sub (hSSB.1.const_mul a)
  have hK : IntegrableOn K (simplexSet 3) :=
    (hS.1.sub (hSS.1.const_mul a)).sub (hG.const_mul b)
  have eK : (kerT .L P s p q T).im = ∫ x in simplexSet 3, K x := by
    rw [kerT_L_im_eq_four_terms hm he hs hp hpq hT hpT hqT]
    have e (t : ℝ) :
        (fun z => groupedParam .L P s (fun w => (secondCoeff (ladderT1 P w)).im / 6)
          (fun w => -(secondCoeff (ladderT2 P w)).im / 2) (slotMa s t p) (slotMA s t q)
          (slotMb s t p) (slotMB s t q) Fin.elim0 z) =
          ladderPhotonTrace P outer false t q p q := by cases outer <;> rfl
    have er :
        (fun z => groupedParamRepeat .L P s (fun w => (secondCoeff (ladderT1 P w)).im / 6)
          (fun w => -(secondCoeff (ladderT2 P w)).im / 2) (slotMa s p p) (slotMA s p q)
          (slotMb s p p) (slotMB s p q) Fin.elim0 z) =
          ladderPhotonTrace P outer true p q p q := by cases outer <;> rfl
    unfold groupedParamFourTerms
    dsimp only
    simp_rw [show ∀ t z, _ = _ from fun t z => congrFun (e t) z,
      show ∀ z, _ = _ from congrFun er]
    rw [(hJ false hp hq).2, (hJ false hM hq).2, (hJ false hq hq).2, (hJ true hp hq).2]
    rw [hS.2, hB.2, hSS.2, hSB.2, hSSB.2]
    symm
    calc
      (∫ x in simplexSet 3, K x) =
          (∫ x in simplexSet 3, S x - a * SS x) -
            ∫ x in simplexSet 3, b * (SB x - a * SSB x) :=
        integral_sub (hS.1.sub (hSS.1.const_mul a)) (hG.const_mul b)
      _ = (∫ x in simplexSet 3, S x) - a * (∫ x in simplexSet 3, SS x) -
          b * ((∫ x in simplexSet 3, SB x) - a * (∫ x in simplexSet 3, SSB x)) := by
        rw [integral_sub (f := S) (g := fun x => a * SS x) hS.1 (hSS.1.const_mul a),
          integral_const_mul, integral_const_mul,
          integral_sub (f := SB) (g := fun x => a * SSB x) hSB.1 (hSSB.1.const_mul a),
          integral_const_mul]
  have hae : (fun x => (b - a) ^ 2 * K x) =ᵐ[volume.restrict (simplexSet 3)] f := by
    filter_upwards [ae_simplexPoint_pos (by decide : 0 < 3)] with x hx
    let z := simplexPoint x
    let F := fun m => ladderPhotonDifference P outer false z m a b
    let R := fun m => ladderPhotonDifference P outer true z m a b
    have eu : u x = D a b (F a) (F b) :=
      ladderMerged_ladderPhotonTrace_of_ne hm he outer false hp hq hp hq hab hab z hx
    have ev : v x = R b :=
      ladderMerged_ladderPhotonTrace_eq hm he outer hq hp hq hab z hx
    have ew : w x = D c b (F c) (F b) :=
      ladderMerged_ladderPhotonTrace_of_ne hm he outer false hM hq hp hq hbc.symm hab z hx
    have er : r x = D a b (R a) (D a b (F a) (F b)) :=
      ladderMerged_ladderPhotonTrace_of_ne hm he outer true hp hq hp hq hab hab z hx
    dsimp only [K, S, B, SS, SB, SSB]
    rw [eu, ev, ew, er]
    change _ = ladderPhotonPF P outer z a b T
    rw [← hM2]
    exact photonPair_four_terms_eq_partialFractions hab hac hbc (F a) (F b) (F c) (R a) (R b)
  refine ⟨(hK.const_mul _).congr hae, ?_⟩
  rw [eK, ← integral_const_mul, integral_congr_ae hae]

open QED.TwoLoop.MassScaling QED.ChainProof.SetCRegDisp
open Filter Topology

/-- Both ladder placements in the normalized real kernel, in electron-mass
units and with the fixed-regulator trace integrals already merged. -/
theorem uBDT_ladder_eq_integral_ladderPhotonPF (P : Params) (he : P.e ≠ 0) (hm : 0 < P.m)
    (outer : Bool) {p q T : ℝ} (hp : 0 < p) (hpq : p < q) (hT : 0 < T)
    (hpT : (p / P.m) ^ 2 ≠ T) (hqT : (q / P.m) ^ 2 ≠ T) :
    let i : Fin 12 := if outer then 0 else 1
    let a := p / P.m
    let b := q / P.m
    let N := { massScale (1 / P.m) { P with e := 1 } with mγ := a, Λ := b }
    let f := fun x => π ^ 4 / (4 * (b ^ 2 - a ^ 2)) *
      ladderPhotonPF N outer (simplexPoint x) (a ^ 2) (b ^ 2) T
    IntegrableOn f (simplexSet 3) ∧
      64 * π ^ 6 / P.e ^ 6 * ((1 / Complex.I) * uBDT P i p q T).re =
        ∫ x in simplexSet 3, f x := by
  intro i a b N f
  have hq := hp.trans hpq
  have hpa : 0 < a := div_pos hp hm
  have hpab : a < b := div_lt_div_of_pos_right hpq hm
  have hgap : b ^ 2 - a ^ 2 ≠ 0 :=
    sub_ne_zero.mpr (pow_lt_pow_left₀ hpab hpa.le two_ne_zero).ne.symm
  let N₀ := massScale (1 / P.m) { P with e := 1 }
  have hNm : N₀.m = 1 := by change (1 / P.m) * P.m = 1; field_simp
  have hNe : N₀.e = 1 := rfl
  have hC : repBClass i = .L := by cases outer <;> rfl
  have hS : repBSlot i = (if outer then 4 else 5 : Fin 8) := by cases outer <;> rfl
  obtain ⟨hI, hEq⟩ :=
    kerT_L_im_eq_integral_ladderPhotonPF (P := N) hNm hNe outer hpa hpab hT hpT hqT
  refine ⟨hI.const_mul _, ?_⟩
  rw [uBDT_normalized_real_of_ne_X P hm he i (by rw [hC]; decide) hp hq hT]
  change 64 * π ^ 6 * ((1 / Complex.I) * uBDT N₀ i a b T).re = _
  have eq := uBDT_normalized_real N₀ (by rw [hNe]; exact one_ne_zero)
    (by rw [hNm]; exact one_ne_zero) i a b T
  have ePow : N₀.e ^ 6 = 1 := by rw [hNe, one_pow]
  have eDen : 4 * N₀.e ^ 5 * N₀.m ^ 5 = 4 := by rw [hNe, hNm, one_pow, mul_one, mul_one]
  rw [ePow, div_one, eDen, hC, hS] at eq
  rw [eq]
  dsimp only [f]
  rw [integral_const_mul, ← hEq]
  field_simp [hgap]
  rfl

private theorem deriv_vpPhotonT_partialFractions {p q T s : ℝ}
    (hs : 0 < s) (hp : 0 ≤ p ^ 2) (hq : 0 ≤ q ^ 2) (hT : 0 ≤ T)
    (hab : p ^ 2 ≠ q ^ 2) (hac : p ^ 2 ≠ T) (hbc : q ^ 2 ≠ T) :
    let a := p ^ 2
    let b := q ^ 2
    deriv (vpPhotonT 1 p q T) s =
      -(bubCoefC a b T / (s + T) ^ 2) - bubCoefA a b T / (s + a) ^ 2 -
        bubCoefB a b T / (s + b) ^ 2 - 2 * bubCoefA2 a T / (s + a) ^ 3 -
        2 * bubCoefB2 b T / (s + b) ^ 3 := by
  intro a b
  have lin (d : ℝ) : HasDerivAt (fun x => x + d) 1 s := (hasDerivAt_id s).add_const d
  have pole (k : ℝ) {d : ℝ} (hd : 0 ≤ d) :
      HasDerivAt (fun x => k / (x + d)) (-(k / (s + d) ^ 2)) s := by
    convert (hasDerivAt_const s k).div (lin d) (add_pos_of_pos_of_nonneg hs hd).ne' using 1
    simp only [zero_mul, mul_one, zero_sub, neg_div]
  have double (k : ℝ) {d : ℝ} (hd : 0 ≤ d) :
      HasDerivAt (fun x => k / (x + d) ^ 2) (-(2 * k / (s + d) ^ 3)) s := by
    have hne := (add_pos_of_pos_of_nonneg hs hd).ne'
    convert (hasDerivAt_const s k).div ((lin d).pow 2) (pow_ne_zero 2 hne) using 1
    simp only [Pi.pow_apply, zero_mul, zero_sub, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    field_simp [hne]
  have h := ((((pole (bubCoefC a b T) hT).add (pole (bubCoefA a b T) hp)).add
    (pole (bubCoefB a b T) hq)).add (double (bubCoefA2 a T) hp)).add
      (double (bubCoefB2 b T) hq)
  have he : vpPhotonT 1 p q T =ᶠ[nhds s] (fun x =>
      bubCoefC a b T / (x + T) + bubCoefA a b T / (x + a) + bubCoefB a b T / (x + b) +
        bubCoefA2 a T / (x + a) ^ 2 + bubCoefB2 b T / (x + b) ^ 2) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    rw [← crossedDressedPhoton_eq_vpPhotonT]
    exact bubble_partialFractions hab hac hbc (add_pos_of_pos_of_nonneg hx hp).ne'
      (add_pos_of_pos_of_nonneg hx hq).ne' (add_pos_of_pos_of_nonneg hx hT).ne'
  rw [(h.congr_of_eventuallyEq he).deriv]
  ring

/-- The single and repeated resolvents resum to the dressed photon and its
derivative at the positive affine argument. -/
theorem photonFiberValue_partialFractions_eq {p q T K W : ℝ}
    (hK : 0 < K) (hW : 0 < W) (hT : 0 ≤ T)
    (hab : p ^ 2 ≠ q ^ 2) (hac : p ^ 2 ≠ T) (hbc : q ^ 2 ≠ T) (F G : ℝ) :
    let a := p ^ 2
    let b := q ^ 2
    let s := K / W
    let f := fun x => factorialResolventPair 0 F G (K + x * W)
    let r := fun x => W * factorialResolventPair 1 F G (K + x * W)
    bubCoefC a b T * f T + bubCoefA a b T * f a + bubCoefB a b T * f b +
        bubCoefA2 a T * r a + bubCoefB2 b T * r b =
      -(F / W ^ 2) * deriv (vpPhotonT 1 p q T) s - (G / W) * vpPhotonT 1 p q T s := by
  intro a b s f r
  have hs : 0 < s := div_pos hK hW
  rw [deriv_vpPhotonT_partialFractions hs (sq_nonneg p) (sq_nonneg q) hT hab hac hbc]
  have hR : vpPhotonT 1 p q T s =
      bubCoefC a b T / (s + T) + bubCoefA a b T / (s + a) + bubCoefB a b T / (s + b) +
        bubCoefA2 a T / (s + a) ^ 2 + bubCoefB2 b T / (s + b) ^ 2 := by
    rw [← crossedDressedPhoton_eq_vpPhotonT]
    exact bubble_partialFractions hab hac hbc (add_pos_of_pos_of_nonneg hs (sq_nonneg p)).ne'
      (add_pos_of_pos_of_nonneg hs (sq_nonneg q)).ne' (add_pos_of_pos_of_nonneg hs hT).ne'
  rw [hR]
  have hv (x : ℝ) : K + x * W = W * (s + x) := by dsimp only [s]; field_simp
  have ef (x : ℝ) (hx : 0 ≤ x) :
      f x = (F / W ^ 2) / (s + x) ^ 2 - (G / W) / (s + x) := by
    simp only [f, factorialResolventPair, hv, Nat.reduceAdd, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_one, mul_one, pow_one]
    field_simp [hW.ne', (add_pos_of_pos_of_nonneg hs hx).ne']
  have er (x : ℝ) (hx : 0 ≤ x) :
      r x = (2 * (F / W ^ 2)) / (s + x) ^ 3 - (G / W) / (s + x) ^ 2 := by
    simp only [r, factorialResolventPair, hv, Nat.reduceAdd, Nat.factorial_one,
      show (2 : ℕ).factorial = 2 by decide, Nat.cast_one, Nat.cast_ofNat, mul_one]
    field_simp [hW.ne', (add_pos_of_pos_of_nonneg hs hx).ne']
  rw [ef T hT, ef a (sq_nonneg _), ef b (sq_nonneg _), er a (sq_nonneg _), er b (sq_nonneg _)]
  change _ = -(F / W ^ 2) * (_ - bubCoefA a b T / (s + a) ^ 2 -
    bubCoefB a b T / (s + b) ^ 2 - 2 * bubCoefA2 a T / (s + a) ^ 3 -
    2 * bubCoefB2 b T / (s + b) ^ 3) - (G / W) * _
  ring

/-- In either ladder placement, the five poles combine into the dressed
photon and its derivative before taking the ordinary photon difference. -/
theorem ladderPhotonPF_eq_vpPhotonT (P : Params) (outer : Bool)
    {p q T : ℝ} (hp : 0 < p) (hq : 0 < q) (hT : 0 ≤ T)
    (hab : p ^ 2 ≠ q ^ 2) (hac : p ^ 2 ≠ T) (hbc : q ^ 2 ≠ T)
    {w : Fin 4 → ℝ} (hw : ∀ i, 0 < w i) :
    let U := gU (w 0) (w 1) (w 2) (w 3)
    let E := gE (w 0) (w 1) (w 2) (w 3)
    let k := ((((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2) / kConst).im
    let F := k * (w 2 * gQ (w 0) (w 1) (w 2) (w 3) / (2 * U ^ 5))
    let G := -k * (w 2 * (9 * gc (w 1) (w 3) + ga (w 0) (w 1) (w 3)) / (2 * U ^ 4))
    let W := if outer then w 2 else w 3
    let H := if outer then w 3 else w 2
    let R := vpPhotonT 1 p q T
    let L := fun μ => -(F / W ^ 2) * deriv R ((E + μ * H) / W) -
      (G / W) * R ((E + μ * H) / W)
    ladderPhotonPF P outer w (p ^ 2) (q ^ 2) T =
      w 0 * w 1 * massDividedDifference (p ^ 2) (q ^ 2) (L (p ^ 2)) (L (q ^ 2)) := by
  intro U E k F G W H R L
  let a := p ^ 2
  let b := q ^ 2
  let f := ladderPhotonNode P outer false w
  let r := ladderPhotonNode P outer true w
  let S := fun μ => bubCoefC a b T * f T μ + bubCoefA a b T * f a μ +
    bubCoefB a b T * f b μ + bubCoefA2 a T * r a μ + bubCoefB2 b T * r b μ
  have hW : 0 < W := by cases outer; exact hw 3; exact hw 2
  have hH : 0 < H := by cases outer; exact hw 2; exact hw 3
  have hE : 0 ≤ E := gE_nonneg (hw 0) (hw 1) (hw 2) (hw 3)
  have hS (μ : ℝ) (hμ : 0 < μ) : S μ = w 0 * w 1 * L μ := by
    have he := photonFiberValue_partialFractions_eq
      (add_pos_of_nonneg_of_pos hE (mul_pos hμ hH)) hW hT hab hac hbc F G
    change _ = L μ at he
    rw [← he]
    have e (x : ℝ) : E + x * W + μ * H = E + μ * H + x * W := by ring
    have ef (x : ℝ) :
        f x μ = w 0 * w 1 * factorialResolventPair 0 F G (E + μ * H + x * W) := by
      change (w 0 * w 1 * 1) * factorialResolventPair 0 F G (E + x * W + μ * H) = _
      rw [mul_one, e]
    have er (x : ℝ) :
        r x μ = (w 0 * w 1 * W) * factorialResolventPair 1 F G (E + μ * H + x * W) := by
      change (w 0 * w 1 * W) * factorialResolventPair 1 F G (E + x * W + μ * H) = _
      rw [e]
    simp only [S, ef, er, a, b]
    ring
  calc
    _ = massDividedDifference a b (S a) (S b) := by
      unfold ladderPhotonPF ladderPhotonDifference
      dsimp only [S, f, r]
      change _ = massDividedDifference (p ^ 2) (q ^ 2) _ _
      unfold massDividedDifference
      ring
    _ = _ := by
      rw [hS a (sq_pos_of_pos hp), hS b (sq_pos_of_pos hq)]
      unfold massDividedDifference
      ring

end Ladder

end QED.ChainProof.SetCUnitM

end
