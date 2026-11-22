/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegXApply
public import QED.ChainProof.SetCRegXPartialFractions
public import QED.ChainProof.SetCRegBndAE
import QED.ChainProof.SetCRegXNorm
import QED.ChainProof.SetCRegXFixedT
import QED.ChainProof.SetCRegXPower
import QED.ChainProof.SetCRegXHomogeneity
import QED.ChainProof.SetCRegBndDeriv

/-!
# The transverse crossed kernel and its regulator estimate

The splits in `QED/ChainProof/SetCRegXApply.lean` reduce the crossed engine to the
dressed-photon partial fractions. A photon-pair permutation handles repeated masses.
The dressed resolvent bounds and an integrable simplex majorant give the crossed
contribution to `IsRegPieceAE` in `QED/ChainProof/SetCRegBndAE.lean`.
-/

@[expose] public section

open MeasureTheory QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.UnitXGraph
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.ChainProof.SetCUnit QED.Integration.TwoLoop QED.Integration.SimplexMerge
open QED.Integration.Feynman (simplexPoint simplexSet)

namespace QED.ChainProof.SetCUnitM

variable {r : ℕ}

private theorem crossedParam_mass_term (P : Params) (hm : P.m = 1) (s : Fin 8)
    (a A b B : ℝ) (cs : Fin r → ℝ) (z : Fin (r + 8) → ℝ) :
    let w := groupExtra s z
    crossedParam P s a A b B cs z =
      crossedResolvent r w
        (gXE (xA w) (xM w) (xc w) (xa w) (xb w) +
          w 4 * a ^ 2 + w 5 * b ^ 2 + w 6 * A ^ 2 + w 7 * B ^ 2 +
          ∑ j, z (mExtra r j) * (cs j ^ 2 - unitMasses P.m a A b B s ^ 2)) := by
  unfold crossedParam unitMMasses
  rw [symanzikV_unitM_group]
  exact congrArg (crossedResolvent r _) (congrArg (· + _) (symanzikV_X_unitMasses hm ..))

private theorem swap_fixed_extra (i j : Fin 8) (k : Fin r) :
    Equiv.swap (mEmb r i) (mEmb r j) (mExtra r k) = mExtra r k := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have e := congrArg Fin.val h
    change k.val + 8 = i.val at e
    omega
  · intro h
    have e := congrArg Fin.val h
    change k.val + 8 = j.val at e
    omega

private theorem groupExtra_swap (i j s k : Fin 8) (z : Fin (r + 8) → ℝ) :
    groupExtra s (z ∘ Equiv.swap (mEmb r i) (mEmb r j)) k =
      z (mEmb r (Equiv.swap i j k)) + if k = s then ∑ l, z (mExtra r l) else 0 := by
  have he : Equiv.swap (mEmb r i) (mEmb r j) (mEmb r k) = mEmb r (Equiv.swap i j k) := by
    by_cases hi : k = i
    · subst k
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    by_cases hj : k = j
    · subst k
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    rw [Equiv.swap_apply_of_ne_of_ne hi hj,
      Equiv.swap_apply_of_ne_of_ne (fun h => hi ((mEmb r).injective h))
        (fun h => hj ((mEmb r).injective h))]
  simp only [groupExtra, Function.comp_apply, he, swap_fixed_extra]

/-- Exchange the two base masses on the right photon of a crossed unit. -/
theorem integral_crossedParam_swap_right (P : Params) (hm : P.m = 1)
    (a A b B : ℝ) (cs : Fin r → ℝ) :
    (∫ x in simplexSet (r + 7), crossedParam P 5 a A b B cs (simplexPoint x)) =
      ∫ x in simplexSet (r + 7), crossedParam P 5 a A B b cs (simplexPoint x) := by
  let σ := Equiv.swap (mEmb r 5) (mEmb r 7)
  rw [← integral_simplex_comp_perm σ (crossedParam P 5 a A b B cs)]
  apply integral_congr_ae
  filter_upwards with x
  let z := simplexPoint x
  let w := groupExtra 5 z
  let v := groupExtra 5 (z ∘ σ)
  let S := ∑ k, z (mExtra r k)
  change crossedParam P 5 a A b B cs (z ∘ σ) = crossedParam P 5 a A B b cs z
  rw [crossedParam_mass_term P hm, crossedParam_mass_term P hm]
  have hsum (u : ℝ) :
      (∑ k, z (mExtra r k) * (cs k ^ 2 - u ^ 2)) =
        (∑ k, z (mExtra r k) * cs k ^ 2) - S * u ^ 2 := by
    simp only [S, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  have hi : v 5 = w 7 + S := by
    simp only [v, σ, groupExtra_swap, Equiv.swap_apply_left, ite_true, w, groupExtra,
      ite_eq_right (show (7 : Fin 8) ≠ 5 by decide), add_zero, S]
  have hj : v 7 = w 5 - S := by
    simp only [v, σ, groupExtra_swap, Equiv.swap_apply_right,
      ite_eq_right (show (7 : Fin 8) ≠ 5 by decide), add_zero, w, groupExtra, ite_true, S,
      add_sub_cancel_right]
  have hf (k : Fin 8) (h₁ : k ≠ 5) (h₂ : k ≠ 7) : v k = w k := by
    simp only [v, σ, groupExtra_swap, Equiv.swap_apply_of_ne_of_ne h₁ h₂, w, groupExtra]
  have h0 := hf 0 (by decide) (by decide)
  have h1 := hf 1 (by decide) (by decide)
  have h2 := hf 2 (by decide) (by decide)
  have h3 := hf 3 (by decide) (by decide)
  have h4 := hf 4 (by decide) (by decide)
  have h6 := hf 6 (by decide) (by decide)
  have he : xb v = xb w := by
    rw [xb, xb, hi, hj]
    ring
  have hmass (K : ℝ) :
      K + v 4 * a ^ 2 + v 5 * b ^ 2 + v 6 * A ^ 2 + v 7 * B ^ 2 +
        (∑ k, (z ∘ σ) (mExtra r k) * (cs k ^ 2 - b ^ 2)) =
      K + w 4 * a ^ 2 + w 5 * B ^ 2 +
        w 6 * A ^ 2 + w 7 * b ^ 2 +
        (∑ k, z (mExtra r k) * (cs k ^ 2 - B ^ 2)) := by
    simp only [Function.comp_apply, σ, swap_fixed_extra, hsum, hi, hj,
      h4, h6]
    ring
  change crossedResolvent r v
      (gXE (xA v) (xM v) (xc v) (xa v) (xb v) +
        v 4 * a ^ 2 + v 5 * b ^ 2 + v 6 * A ^ 2 + v 7 * B ^ 2 +
        ∑ k, (z ∘ σ) (mExtra r k) * (cs k ^ 2 - b ^ 2)) =
    crossedResolvent r w
      (gXE (xA w) (xM w) (xc w) (xa w) (xb w) +
        w 4 * a ^ 2 + w 5 * B ^ 2 + w 6 * A ^ 2 + w 7 * b ^ 2 +
        ∑ k, z (mExtra r k) * (cs k ^ 2 - B ^ 2))
  have hA : xA v = xA w := h0
  have ht : xt v = xt w := h1
  have hM : xM v = xM w := congrArg₂ (· + ·) h1 h2
  have hc : xc v = xc w := h3
  have ho : xa v = xa w :=
    congrArg₂ (· + ·) h4 h6
  rw [hA, hM, hc, ho, he, hmass]
  simp only [crossedResolvent, xPsi1, xPsi2, xan, xbn, xCn, xU, hA, hM, hc, ho, he, ht]

/-- Exchange the two base masses on the left photon of a crossed unit. -/
theorem integral_crossedParam_swap_left (P : Params) (hm : P.m = 1)
    (a A b B : ℝ) (cs : Fin r → ℝ) :
    (∫ x in simplexSet (r + 7), crossedParam P 4 a A b B cs (simplexPoint x)) =
      ∫ x in simplexSet (r + 7), crossedParam P 4 A a b B cs (simplexPoint x) := by
  let σ := Equiv.swap (mEmb r 4) (mEmb r 6)
  rw [← integral_simplex_comp_perm σ (crossedParam P 4 a A b B cs)]
  apply integral_congr_ae
  filter_upwards with x
  let z := simplexPoint x
  let w := groupExtra 4 z
  let v := groupExtra 4 (z ∘ σ)
  let S := ∑ k, z (mExtra r k)
  change crossedParam P 4 a A b B cs (z ∘ σ) = crossedParam P 4 A a b B cs z
  rw [crossedParam_mass_term P hm, crossedParam_mass_term P hm]
  have hsum (u : ℝ) :
      (∑ k, z (mExtra r k) * (cs k ^ 2 - u ^ 2)) =
        (∑ k, z (mExtra r k) * cs k ^ 2) - S * u ^ 2 := by
    simp only [S, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  have hi : v 4 = w 6 + S := by
    simp only [v, σ, groupExtra_swap, Equiv.swap_apply_left, ite_true, w, groupExtra,
      ite_eq_right (show (6 : Fin 8) ≠ 4 by decide), add_zero, S]
  have hj : v 6 = w 4 - S := by
    simp only [v, σ, groupExtra_swap, Equiv.swap_apply_right,
      ite_eq_right (show (6 : Fin 8) ≠ 4 by decide), add_zero, w, groupExtra, ite_true, S,
      add_sub_cancel_right]
  have hf (k : Fin 8) (h₁ : k ≠ 4) (h₂ : k ≠ 6) : v k = w k := by
    simp only [v, σ, groupExtra_swap, Equiv.swap_apply_of_ne_of_ne h₁ h₂, w, groupExtra]
  have h0 := hf 0 (by decide) (by decide)
  have h1 := hf 1 (by decide) (by decide)
  have h2 := hf 2 (by decide) (by decide)
  have h3 := hf 3 (by decide) (by decide)
  have h5 := hf 5 (by decide) (by decide)
  have h7 := hf 7 (by decide) (by decide)
  have he : xa v = xa w := by
    rw [xa, xa, hi, hj]
    ring
  have hmass (K : ℝ) :
      K + v 4 * a ^ 2 + v 5 * b ^ 2 + v 6 * A ^ 2 + v 7 * B ^ 2 +
        (∑ k, (z ∘ σ) (mExtra r k) * (cs k ^ 2 - a ^ 2)) =
      K + w 4 * A ^ 2 + w 5 * b ^ 2 +
        w 6 * a ^ 2 + w 7 * B ^ 2 +
        (∑ k, z (mExtra r k) * (cs k ^ 2 - A ^ 2)) := by
    simp only [Function.comp_apply, σ, swap_fixed_extra, hsum, hi, hj,
      h5, h7]
    ring
  change crossedResolvent r v
      (gXE (xA v) (xM v) (xc v) (xa v) (xb v) +
        v 4 * a ^ 2 + v 5 * b ^ 2 + v 6 * A ^ 2 + v 7 * B ^ 2 +
        ∑ k, (z ∘ σ) (mExtra r k) * (cs k ^ 2 - a ^ 2)) =
    crossedResolvent r w
      (gXE (xA w) (xM w) (xc w) (xa w) (xb w) +
        w 4 * A ^ 2 + w 5 * b ^ 2 + w 6 * a ^ 2 + w 7 * B ^ 2 +
        ∑ k, z (mExtra r k) * (cs k ^ 2 - A ^ 2))
  have hA : xA v = xA w := h0
  have ht : xt v = xt w := h1
  have hM : xM v = xM w := congrArg₂ (· + ·) h1 h2
  have hc : xc v = xc w := h3
  have ho : xb v = xb w :=
    congrArg₂ (· + ·) h5 h7
  rw [hA, hM, hc, ho, he, hmass]
  simp only [crossedResolvent, xPsi1, xPsi2, xan, xbn, xCn, xU, hA, hM, hc, ho, he, ht]

open QED.ChainProof.SetCK QED.ChainProof.SetCRegX

/-- Crossed resolvent integral with the spectator pair listed first. -/
noncomputable def crossedPairIntegral (P : Params) (left : Bool)
    (a A p q : ℝ) (cs : Fin r → ℝ) : ℝ :=
  if left then
    ∫ x in simplexSet (r + 7), crossedParam P 4 p q a A cs (simplexPoint x)
  else
    ∫ x in simplexSet (r + 7), crossedParam P 5 a A p q cs (simplexPoint x)

private theorem crossedPairIntegral_swap (P : Params) (hm : P.m = 1)
    (left : Bool) (a A p q : ℝ) (cs : Fin r → ℝ) :
    crossedPairIntegral P left a A p q cs = crossedPairIntegral P left a A q p cs := by
  cases left
  · exact integral_crossedParam_swap_right P hm a A p q cs
  · exact integral_crossedParam_swap_left P hm p q a A cs

private theorem crossedPairIntegral_split (P : Params) (hm : P.m = 1)
    (left : Bool) {μ a A p q : ℝ} (hμ : 0 < μ) (ha : μ ≤ a) (hA : μ ≤ A)
    (hp : μ ≤ p) (hq : μ ≤ q) {cs : Fin (r + 1) → ℝ} (hcs : ∀ j, μ ≤ cs j)
    (hne : p ^ 2 ≠ cs (Fin.last r) ^ 2) :
    let t := cs (Fin.last r)
    crossedPairIntegral P left a A p q cs = massDividedDifference (p ^ 2) (t ^ 2)
      (crossedPairIntegral P left a A p q (Fin.init cs))
      (crossedPairIntegral P left a A t q (Fin.init cs)) := by
  have hm0 : 0 < P.m := by rw [hm]; exact one_pos
  cases left
  · exact integral_crossedParam_split P hm0 (s := 5) (by decide)
      hμ ⟨ha, hA, hp, hq⟩ hcs hne
  · exact integral_crossedParam_split P hm0 (s := 4) (by decide)
      hμ ⟨hp, hq, ha, hA⟩ hcs hne

private theorem crossedPairIntegral_zero (P : Params) (hm : P.m = 1)
    (left : Bool) {μ a A p q : ℝ} (hμ : 0 < μ) (ha : μ ≤ a) (hA : μ ≤ A)
    (hp : μ ≤ p) (hq : μ ≤ q) (haA : a ^ 2 ≠ A ^ 2) (hpq : p ^ 2 ≠ q ^ 2) :
    let f := fun t => massDividedDifference (a ^ 2) (A ^ 2)
      (crossUnit (a ^ 2) t) (crossUnit (A ^ 2) t)
    crossedPairIntegral P left a A p q (fun i : Fin 0 => Fin.elim0 i) =
      massDividedDifference (p ^ 2) (q ^ 2) (f (p ^ 2)) (f (q ^ 2)) := by
  have h₁ := sub_ne_zero.mpr haA.symm
  have h₂ := sub_ne_zero.mpr hpq.symm
  cases left
  · change (∫ x in simplexSet 7,
      crossedParam P 5 a A p q (fun i : Fin 0 => Fin.elim0 i) (simplexPoint x)) = _
    rw [integral_crossedParam_zero P hm (by decide) hμ ⟨ha, hA, hp, hq⟩ haA hpq]
    dsimp only [massDividedDifference]
    field_simp
    ring
  · change (∫ x in simplexSet 7,
      crossedParam P 4 p q a A (fun i : Fin 0 => Fin.elim0 i) (simplexPoint x)) = _
    rw [integral_crossedParam_zero P hm (by decide) hμ ⟨hp, hq, ha, hA⟩ hpq haA,
      crossUnit_mirror (p ^ 2) (a ^ 2), crossUnit_mirror (p ^ 2) (A ^ 2),
      crossUnit_mirror (q ^ 2) (a ^ 2), crossUnit_mirror (q ^ 2) (A ^ 2)]
    dsimp only [massDividedDifference]
    field_simp

private theorem crossedPairIntegral_repeat (P : Params) (hm : P.m = 1)
    (left : Bool) {μ a A p : ℝ} (hμ : 0 < μ) (ha : μ ≤ a) (hA : μ ≤ A)
    (hp : μ ≤ p) (haA : a ^ 2 ≠ A ^ 2) :
    let f := fun t => massDividedDifference (a ^ 2) (A ^ 2)
      (crossUnit (a ^ 2) t) (crossUnit (A ^ 2) t)
    crossedPairIntegral P left a A p p (fun i : Fin 0 => Fin.elim0 i) =
      -deriv f (p ^ 2) := by
  have hp' : 0 < p ^ 2 := sq_pos_of_pos (hμ.trans_le hp)
  have hda := hasDerivAt_crossUnit_right (a := a ^ 2) (sq_nonneg _) hp'
  have hdA := hasDerivAt_crossUnit_right (a := A ^ 2) (sq_nonneg _) hp'
  have hd := ((hda.sub hdA).div_const (A ^ 2 - a ^ 2)).deriv
  change deriv (fun t => (crossUnit (a ^ 2) t - crossUnit (A ^ 2) t) /
    (A ^ 2 - a ^ 2)) (p ^ 2) = _ at hd
  dsimp only [massDividedDifference]
  rw [hd]
  rw [← hda.deriv, ← hdA.deriv]
  cases left
  · change (∫ x in simplexSet 7,
      crossedParam P 5 a A p p (fun i : Fin 0 => Fin.elim0 i) (simplexPoint x)) = _
    rw [integral_crossedParam_zero_right_repeat P hm (by decide) hμ ⟨ha, hA, hp, hp⟩ haA]
    rw [← neg_div, neg_sub]
  · change (∫ x in simplexSet 7,
      crossedParam P 4 p p a A (fun i : Fin 0 => Fin.elim0 i) (simplexPoint x)) = _
    rw [integral_crossedParam_zero_left_repeat P hm (by decide) hμ ⟨hp, hp, ha, hA⟩ haA]
    rw [← neg_div, neg_sub]

private theorem init_singleton (t : ℝ) :
    Fin.init (![t] : Fin 1 → ℝ) = (fun i : Fin 0 => Fin.elim0 i) := by
  funext i
  exact Fin.elim0 i

private theorem init_pair (t u : ℝ) : Fin.init (![t, u] : Fin 2 → ℝ) = ![t] := by
  funext i
  fin_cases i
  rfl

private theorem init_triple (t u v : ℝ) : Fin.init (![t, u, v] : Fin 3 → ℝ) = ![t, u] := by
  funext i
  fin_cases i <;> rfl

private theorem lower_singleton {μ t : ℝ} (ht : μ ≤ t) : ∀ j : Fin 1, μ ≤ (![t] : _ → ℝ) j := by
  intro j
  fin_cases j
  exact ht

private theorem lower_pair {μ t u : ℝ} (ht : μ ≤ t) (hu : μ ≤ u) :
    ∀ j : Fin 2, μ ≤ (![t, u] : _ → ℝ) j := by
  intro j
  fin_cases j
  · exact ht
  · exact hu

private theorem lower_triple {μ t u v : ℝ} (ht : μ ≤ t) (hu : μ ≤ u) (hv : μ ≤ v) :
    ∀ j : Fin 3, μ ≤ (![t, u, v] : _ → ℝ) j := by
  intro j
  fin_cases j
  · exact ht
  · exact hu
  · exact hv


private theorem crossed_dressed_divided_difference {a b c : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (fa fb fc da db : ℝ) :
    let D := massDividedDifference
    let S := D a c (D a b fa fb) (D c b fc fb)
    let Ap := D a c (-da) (D c a fc fa)
    let Bq := D b c (-db) (D c b fc fb)
    S - a * D b a S Ap - b * (D a b S Bq - a * D b a (D a b S Bq) (D a b Ap S)) =
      bubbleDividedDifference a b c fa fb fc da db := by
  simp only [bubbleDividedDifference, massDividedDifference]
  rw [show a - b = -(b - a) by ring, show a - c = -(c - a) by ring,
    show b - c = -(c - b) by ring]
  field_simp [sub_ne_zero.mpr hab.symm, sub_ne_zero.mpr hac.symm, sub_ne_zero.mpr hbc.symm]
  ring

/-- Reduce all four numerator terms to the divided differences of the crossed unit. -/
theorem crossedPairIntegral_dressed (P : Params) (hm : P.m = 1)
    (left : Bool) {μ a A p q c : ℝ} (hμ : 0 < μ)
    (ha : μ ≤ a) (hA : μ ≤ A) (hp : μ ≤ p) (hq : μ ≤ q) (hc : μ ≤ c)
    (haA : a ^ 2 ≠ A ^ 2) (hpq : p ^ 2 ≠ q ^ 2) (hpc : p ^ 2 ≠ c ^ 2) (hqc : q ^ 2 ≠ c ^ 2) :
    let E r := crossedPairIntegral (r := r) P left a A p q
    let f := fun t => massDividedDifference (a ^ 2) (A ^ 2)
      (crossUnit (a ^ 2) t) (crossUnit (A ^ 2) t)
    E 1 ![c] - p ^ 2 * E 2 ![c, p] - q ^ 2 * (E 2 ![c, q] - p ^ 2 * E 3 ![c, q, p]) =
      bubbleDividedDifference (p ^ 2) (q ^ 2) (c ^ 2)
        (f (p ^ 2)) (f (q ^ 2)) (f (c ^ 2)) (deriv f (p ^ 2)) (deriv f (q ^ 2)) := by
  dsimp only
  let D := massDividedDifference
  let E {r} := crossedPairIntegral (r := r) P left a A
  let f := fun t => D (a ^ 2) (A ^ 2) (crossUnit (a ^ 2) t) (crossUnit (A ^ 2) t)
  let nil : Fin 0 → ℝ := fun i => Fin.elim0 i
  have hsplit {r : ℕ} {u v : ℝ} (hu : μ ≤ u) (hv : μ ≤ v) {cs : Fin (r + 1) → ℝ}
      (hs : ∀ j, μ ≤ cs j) (hne : u ^ 2 ≠ cs (Fin.last r) ^ 2) :
      E u v cs = D (u ^ 2) (cs (Fin.last r) ^ 2)
        (E u v (Fin.init cs)) (E (cs (Fin.last r)) v (Fin.init cs)) :=
    crossedPairIntegral_split P hm left hμ ha hA hu hv hs hne
  have hbase {u v : ℝ} (hu : μ ≤ u) (hv : μ ≤ v) (hne : u ^ 2 ≠ v ^ 2) :
      E u v nil = D (u ^ 2) (v ^ 2) (f (u ^ 2)) (f (v ^ 2)) :=
    crossedPairIntegral_zero P hm left hμ ha hA hu hv haA hne
  have hp0 : E p p nil = -deriv f (p ^ 2) :=
    crossedPairIntegral_repeat P hm left hμ ha hA hp haA
  have hq0 : E q q nil = -deriv f (q ^ 2) :=
    crossedPairIntegral_repeat P hm left hμ ha hA hq haA
  have hswap {r : ℕ} (u v : ℝ) (cs : Fin r → ℝ) : E u v cs = E v u cs :=
    crossedPairIntegral_swap P hm left a A u v cs
  have h1 {u : ℝ} (hu : μ ≤ u) {v t : ℝ} (hv : μ ≤ v) (ht : μ ≤ t)
      (hne : u ^ 2 ≠ t ^ 2) :
      E u v ![t] = D (u ^ 2) (t ^ 2) (E u v nil) (E t v nil) := by
    have h := hsplit hu hv (lower_singleton ht) (show u ^ 2 ≠ (![t] : Fin 1 → ℝ)
      (Fin.last 0) ^ 2 from hne)
    rw [init_singleton] at h
    exact h
  have h2 {u v t w : ℝ} (hu : μ ≤ u) (hv : μ ≤ v) (ht : μ ≤ t) (hw : μ ≤ w)
      (hne : u ^ 2 ≠ w ^ 2) :
      E u v ![t, w] = D (u ^ 2) (w ^ 2) (E u v ![t]) (E w v ![t]) := by
    have h := hsplit hu hv (lower_pair ht hw) (show u ^ 2 ≠ (![t, w] : Fin 2 → ℝ)
      (Fin.last 1) ^ 2 from hne)
    rw [init_pair] at h
    exact h
  have h3 {u v t w y : ℝ} (hu : μ ≤ u) (hv : μ ≤ v) (ht : μ ≤ t) (hw : μ ≤ w) (hy : μ ≤ y)
      (hne : u ^ 2 ≠ y ^ 2) :
      E u v ![t, w, y] = D (u ^ 2) (y ^ 2) (E u v ![t, w]) (E y v ![t, w]) := by
    have h := hsplit hu hv (lower_triple ht hw hy) (show u ^ 2 ≠ (![t, w, y] : Fin 3 → ℝ)
      (Fin.last 2) ^ 2 from hne)
    rw [init_triple] at h
    exact h
  change E p q ![c] - p ^ 2 * E p q ![c, p] -
    q ^ 2 * (E p q ![c, q] - p ^ 2 * E p q ![c, q, p]) =
    bubbleDividedDifference (p ^ 2) (q ^ 2) (c ^ 2)
      (f (p ^ 2)) (f (q ^ 2)) (f (c ^ 2)) (deriv f (p ^ 2)) (deriv f (q ^ 2))

  have hpc0 := hbase hp hq hpq
  have hcq0 := hbase hc hq hqc.symm
  have hcp0 := hbase hc hp hpc.symm
  let S := D (p ^ 2) (c ^ 2)
    (D (p ^ 2) (q ^ 2) (f (p ^ 2)) (f (q ^ 2)))
    (D (c ^ 2) (q ^ 2) (f (c ^ 2)) (f (q ^ 2)))
  let Ap := D (p ^ 2) (c ^ 2) (-deriv f (p ^ 2))
    (D (c ^ 2) (p ^ 2) (f (c ^ 2)) (f (p ^ 2)))
  let Bq := D (q ^ 2) (c ^ 2) (-deriv f (q ^ 2))
    (D (c ^ 2) (q ^ 2) (f (c ^ 2)) (f (q ^ 2)))
  have hs : E p q ![c] = S := by rw [h1 hp hq hc hpc, hpc0, hcq0]
  have hap : E p p ![c] = Ap := by rw [h1 hp hp hc hpc, hp0, hcp0]
  have hbq : E q q ![c] = Bq := by rw [h1 hq hq hc hqc, hq0, hcq0]
  have hsp : E p q ![c, p] = D (q ^ 2) (p ^ 2) S Ap := by
    rw [hswap p q ![c, p], h2 hq hp hc hp hpq.symm, hswap q p ![c], hs, hap]
  have hsq : E p q ![c, q] = D (p ^ 2) (q ^ 2) S Bq := by
    rw [h2 hp hq hc hq hpq, hs, hbq]
  have hsqp : E p q ![c, q, p] = D (q ^ 2) (p ^ 2)
      (D (p ^ 2) (q ^ 2) S Bq) (D (p ^ 2) (q ^ 2) Ap S) := by
    rw [hswap p q ![c, q, p], h3 hq hp hc hq hp hpq.symm, hswap q p ![c, q], hsq,
      h2 hp hp hc hq hpq, hswap q p ![c], hap, hs]
  rw [hs, hsp, hsq, hsqp]
  exact crossed_dressed_divided_difference hpq hpc hqc
    (f (p ^ 2)) (f (q ^ 2)) (f (c ^ 2)) (deriv f (p ^ 2)) (deriv f (q ^ 2))

open QED.TwoLoop.Enumeration QED.TwoLoop.ClassIntegrable QED.TwoLoop.UnitLGraphTrace
open QED.TwoLoop.MassScaling QED.ChainProof.SetCRegBubble QED.ChainProof.SetCMain
open scoped Real

private theorem crossedPairIntegral_eq_crossPF (P : Params) (hm : P.m = 1)
    (left : Bool) {μ p q c : ℝ} (hμ : 0 < μ) (hp : μ ≤ p) (hq : μ ≤ q) (hc : μ ≤ c)
    (hpq : p ^ 2 ≠ q ^ 2) (hpc : p ^ 2 ≠ c ^ 2) (hqc : q ^ 2 ≠ c ^ 2) :
    let E r := crossedPairIntegral (r := r) P left p q p q
    (q ^ 2 - p ^ 2) ^ 3 *
      (E 1 ![c] - p ^ 2 * E 2 ![c, p] - q ^ 2 * (E 2 ![c, q] - p ^ 2 * E 3 ![c, q, p])) =
      crossPF (p ^ 2) (p ^ 2) (q ^ 2) (c ^ 2) -
        crossPF (q ^ 2) (p ^ 2) (q ^ 2) (c ^ 2) := by
  dsimp only
  rw [crossedPairIntegral_dressed P hm left hμ hp hq hp hq hc hpq hpq hpc hqc]
  let g := q ^ 2 - p ^ 2
  let f := fun (t : ℝ) => massDividedDifference (p ^ 2) (q ^ 2)
    (crossUnit (p ^ 2) t) (crossUnit (q ^ 2) t)
  have hg : g ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hdf {t : ℝ} (ht : 0 < t) :
      deriv f t = (deriv (crossUnit (p ^ 2)) t - deriv (crossUnit (q ^ 2)) t) / g := by
    have hp' := hasDerivAt_crossUnit_right (a := p ^ 2) (sq_nonneg _) ht
    have hq' := hasDerivAt_crossUnit_right (a := q ^ 2) (sq_nonneg _) ht
    have hd := ((hp'.sub hq').div_const g).deriv
    rw [hp'.deriv, hq'.deriv]
    exact hd
  change g ^ 3 * bubbleDividedDifference (p ^ 2) (q ^ 2) (c ^ 2)
    (f (p ^ 2)) (f (q ^ 2)) (f (c ^ 2)) (deriv f (p ^ 2)) (deriv f (q ^ 2)) = _
  rw [pow_succ, mul_comm (g ^ 2) g, mul_assoc]
  rw [show g ^ 2 * bubbleDividedDifference (p ^ 2) (q ^ 2) (c ^ 2)
      (f (p ^ 2)) (f (q ^ 2)) (f (c ^ 2)) (deriv f (p ^ 2)) (deriv f (q ^ 2)) = _ from
    bubbleDividedDifference_eq_partialFractions hpq hpc hqc _ _ _ _ _]
  rw [hdf (sq_pos_of_pos (hμ.trans_le hp)), hdf (sq_pos_of_pos (hμ.trans_le hq))]
  simp only [f, massDividedDifference, crossPF, ← show g = q ^ 2 - p ^ 2 from rfl]
  field_simp
  ring

private theorem unitMPauliZero_pow_crossPF (P : Params) (hm : P.m = 1) (he : P.e = 1)
    (left : Bool) {μ p q c : ℝ} (hμ : 0 < μ) (hp : μ ≤ p) (hq : μ ≤ q) (hc : μ ≤ c)
    (hpq : p ^ 2 ≠ q ^ 2) (hpc : p ^ 2 ≠ c ^ 2) (hqc : q ^ 2 ≠ c ^ 2)
    (hγ : P.mγ = p) (hΛ : P.Λ = q) :
    unitMPauliZeroPow .X P (if left then 4 else 5) (fun _ : Fin 3 => 1)
      (unitMMasses P.m p q p q ![c, p, q]) 2 =
      ((crossPF (p ^ 2) (p ^ 2) (q ^ 2) (c ^ 2) -
        crossPF (q ^ 2) (p ^ 2) (q ^ 2) (c ^ 2) : ℝ) : ℂ) /
        (((q ^ 2 - p ^ 2 : ℝ) : ℂ) * kConst) := by
  let s : Fin 8 := if left then 4 else 5
  have hs : 4 ≤ s.val := by cases left <;> decide
  have hm0 : 0 < P.m := by rw [hm]; exact one_pos
  have hX : Class5.X ∈ openClasses := by decide
  have hM : MassesGe μ p q p q := ⟨hp, hq, hp, hq⟩
  let E {r} := crossedPairIntegral (r := r) P left p q p q
  let g := q ^ 2 - p ^ 2
  have hzero {r : ℕ} (cs : Fin r → ℝ) :
      unitMPauliZero .X P s (fun _ => 1) (unitMMasses P.m p q p q cs) =
        ((g : ℂ) ^ 2 / kConst) * (E cs : ℂ) := by
    unfold unitMMasses
    rw [unitMPauliZero_X_eq_integral hm he, hγ, hΛ]
    cases left <;> rfl
  change unitMPauliZeroPow .X P s _ _ _ = _
  rw [unitMPauliZeroPow_three_two hX P hm0 hs hμ hM hc hp hq,
    hzero, hzero, hzero, hzero]
  let v := E ![c] - p ^ 2 * E ![c, p] - q ^ 2 * (E ![c, q] - p ^ 2 * E ![c, q, p])
  have hv : g ^ 3 * v = _ := crossedPairIntegral_eq_crossPF P hm left hμ hp hq hc hpq hpc hqc
  rw [← hv]
  change _ = ((g ^ 3 * v : ℝ) : ℂ) / ((g : ℂ) * kConst)
  have hk : kConst ≠ 0 := by
    unfold kConst
    exact div_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hg : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hpq.symm)
  push_cast
  field_simp [hk]
  simp only [v, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow]

private theorem unitMMasses_inv_mass_smul {r : ℕ} {m : ℝ}
    (a A b B : ℝ) (cs : Fin r → ℝ) :
    (1 / m) • unitMMasses m a A b B cs =
      unitMMasses (1 / m * m) (a / m) (A / m) (b / m) (B / m) (fun j => cs j / m) := by
  funext i
  obtain ⟨j, rfl⟩ | ⟨j, rfl⟩ := mem_mEmb_or_mExtra i
  · simp only [Pi.smul_apply, smul_eq_mul, unitMMasses, mExt_mEmb]
    fin_cases j <;> simp [unitMasses, classPVMasses, Fin.isValue, div_eq_mul_inv, mul_comm]
  · simp only [Pi.smul_apply, smul_eq_mul, unitMMasses, mExt_mExtra]
    ring

private theorem unitMPauliZero_X_normalize (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ s.val) {μ a A b B : ℝ} (hμ : 0 < μ)
    (hM : MassesGe μ a A b B) {cs : Fin r → ℝ} (hcs : ∀ j, μ ≤ cs j) :
    let N := massScale (1 / P.m) { P with e := 1 }
    unitMPauliZero .X P s (fun _ => 1) (unitMMasses P.m a A b B cs) =
      ((P.e : ℂ) ^ 5 * (P.m : ℂ) ^ 13 / ((P.m : ℂ) ^ 2) ^ (r + 4)) *
        unitMPauliZero .X N s (fun _ => 1)
          (unitMMasses N.m (a / P.m) (A / P.m) (b / P.m) (B / P.m) (fun j => cs j / P.m)) := by
  intro N
  rw [unitMPauliZero_X_chargeOne P hm hs hμ hM hcs]
  have hX : Class5.X ∈ openClasses := by decide
  have hS := unitMPauliZero_massScale hX { P with e := 1 } hm hs hμ hM
    (fun j => ⟨one_pos, le_rfl, hcs j⟩) (one_div_ne_zero hm.ne')
  rw [unitMMasses_inv_mass_smul] at hS
  change unitMPauliZero .X N s _ (unitMMasses N.m _ _ _ _ _) = _ at hS
  rw [hS]
  have hm' : (P.m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  simp only [Complex.ofReal_div, Complex.ofReal_one, div_pow]
  field_simp
  ring


private theorem kerT_crossPF (P : Params) (hm : 0 < P.m)
    (left : Bool) {p q T : ℝ} (hp : 0 < p) (hpq : p < q) (hT : 0 < T)
    (hpT : (p / P.m) ^ 2 ≠ T) (hqT : (q / P.m) ^ 2 ≠ T)
    (hγ : P.mγ = p) (hΛ : P.Λ = q) :
    QED.ChainProof.SetCRegDisp.kerT .X P (if left then 4 else 5) p q T =
      ((P.e : ℂ) ^ 5 * (P.m : ℂ) ^ 5) *
      ((crossPF ((p / P.m) ^ 2) ((p / P.m) ^ 2) ((q / P.m) ^ 2) T -
        crossPF ((q / P.m) ^ 2) ((p / P.m) ^ 2) ((q / P.m) ^ 2) T : ℝ) : ℂ) /
      (((q ^ 2 - p ^ 2 : ℝ) : ℂ) * kConst) := by
  let s : Fin 8 := if left then 4 else 5
  let c := Real.sqrt (P.m ^ 2 * T)
  let N := massScale (1 / P.m) { P with e := 1 }
  let p' := p / P.m
  let q' := q / P.m
  let c' := c / P.m
  have hc : 0 < c := Real.sqrt_pos.2 (mul_pos (sq_pos_of_pos hm) hT)
  have hp' : 0 < p' := div_pos hp hm
  have hq' : p' < q' := div_lt_div_of_pos_right hpq hm
  have hc' : 0 < c' := div_pos hc hm
  have hs : 4 ≤ s.val := by cases left <;> decide
  have hX : Class5.X ∈ openClasses := by decide
  have hN : N.m = 1 := by change 1 / P.m * P.m = 1; field_simp
  have hNe : N.e = 1 := rfl
  have hNp : N.mγ = p' := by change 1 / P.m * P.mγ = _; rw [hγ]; ring
  have hNq : N.Λ = q' := by change 1 / P.m * P.Λ = _; rw [hΛ]; ring
  have hcT : c' ^ 2 = T := by
    rw [show c' = c / P.m from rfl, div_pow,
      Real.sq_sqrt (mul_nonneg (sq_nonneg _) hT.le)]
    field_simp
  let μ := min p c
  have hμ : 0 < μ := lt_min hp hc
  have hμp : μ ≤ p := min_le_left _ _
  have hμq : μ ≤ q := hμp.trans hpq.le
  have hμc : μ ≤ c := min_le_right _ _
  have hM : MassesGe μ p q p q := ⟨hμp, hμq, hμp, hμq⟩
  let ν := μ / P.m
  have hν : 0 < ν := div_pos hμ hm
  have hνp : ν ≤ p' := div_le_div_of_nonneg_right hμp hm.le
  have hνq : ν ≤ q' := div_le_div_of_nonneg_right hμq hm.le
  have hνc : ν ≤ c' := div_le_div_of_nonneg_right hμc hm.le
  have hνM : MassesGe ν p' q' p' q' := ⟨hνp, hνq, hνp, hνq⟩
  have hpq' : p' ^ 2 ≠ q' ^ 2 := (pow_lt_pow_left₀ hq' hp'.le (by decide : 2 ≠ 0)).ne
  have hpc' : p' ^ 2 ≠ c' ^ 2 := hcT ▸ hpT
  have hqc' : q' ^ 2 ≠ c' ^ 2 := hcT ▸ hqT
  have hm' : (P.m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  let U {r} (cs : Fin r → ℝ) :=
    unitMPauliZero .X N s (fun _ => 1) (unitMMasses N.m p' q' p' q' cs)
  have e1 : (fun j : Fin 1 => (![c] : Fin 1 → ℝ) j / P.m) = ![c'] := by
    funext j
    fin_cases j
    rfl
  have e2 (z : ℝ) :
      (fun j : Fin 2 => (![c, z] : Fin 2 → ℝ) j / P.m) = ![c', z / P.m] := by
    funext j
    fin_cases j <;> rfl
  have e3 : (fun j : Fin 3 => (![c, q, p] : Fin 3 → ℝ) j / P.m) = ![c', q', p'] := by
    funext j
    fin_cases j <;> rfl
  have h1 := unitMPauliZero_X_normalize P hm hs hμ hM (lower_singleton hμc)
  have h2p := unitMPauliZero_X_normalize P hm hs hμ hM (lower_pair hμc hμp)
  have h2q := unitMPauliZero_X_normalize P hm hs hμ hM (lower_pair hμc hμq)
  have h3 := unitMPauliZero_X_normalize P hm hs hμ hM (lower_triple hμc hμq hμp)
  dsimp only at h1 h2p h2q h3
  rw [e1] at h1
  rw [e2] at h2p h2q
  rw [e3] at h3
  have hNorm := unitMPauliZero_pow_crossPF N hN hNe left hν hνp hνq hνc
    hpq' hpc' hqc' hNp hNq
  change unitMPauliZeroPow .X N s _ _ _ = _ at hNorm
  rw [unitMPauliZeroPow_three_two hX N (hN ▸ one_pos) hs hν hνM hνc hνp hνq] at hNorm
  change U ![c'] - ((p' ^ 2 : ℝ) : ℂ) * U ![c', p'] -
    ((q' ^ 2 : ℝ) : ℂ) * (U ![c', q'] - ((p' ^ 2 : ℝ) : ℂ) * U ![c', q', p']) = _ at hNorm
  have hScale :
      QED.ChainProof.SetCRegDisp.kerT .X P s p q T =
        ((P.e : ℂ) ^ 5 * (P.m : ℂ) ^ 3) *
          (U ![c'] - ((p' ^ 2 : ℝ) : ℂ) * U ![c', p'] -
            ((q' ^ 2 : ℝ) : ℂ) * (U ![c', q'] - ((p' ^ 2 : ℝ) : ℂ) * U ![c', q', p'])) := by
    change unitMPauliZeroPow .X P s (fun _ : Fin 3 => 1) (unitMMasses P.m p q p q ![c,p,q]) 2 = _
    rw [unitMPauliZeroPow_three_two hX P hm hs hμ hM hμc hμp hμq, h1, h2p, h2q, h3]
    change _ * U ![c'] - _ * (_ * U ![c', p']) -
      _ * (_ * U ![c', q'] - _ * (_ * U ![c', q', p'])) = _
    simp only [p', q', Complex.ofReal_pow, Complex.ofReal_div]
    field_simp
    ring
  change QED.ChainProof.SetCRegDisp.kerT .X P s p q T = _
  rw [hScale, hNorm, hcT]
  have hgap : (q' ^ 2 - p' ^ 2 : ℝ) = (q ^ 2 - p ^ 2) / P.m ^ 2 := by
    simp only [p', q', div_pow, sub_div]
  let f := crossPF (p' ^ 2) (p' ^ 2) (q' ^ 2) T - crossPF (q' ^ 2) (p' ^ 2) (q' ^ 2) T
  change ((P.e : ℂ) ^ 5 * (P.m : ℂ) ^ 3) *
      ((f : ℂ) / (((q' ^ 2 - p' ^ 2 : ℝ) : ℂ) * kConst)) =
      ((P.e : ℂ) ^ 5 * (P.m : ℂ) ^ 5) * (f : ℂ) /
        (((q ^ 2 - p ^ 2 : ℝ) : ℂ) * kConst)
  rw [hgap, Complex.ofReal_div, Complex.ofReal_pow, div_mul_eq_mul_div, div_div_eq_mul_div]
  ring

end QED.ChainProof.SetCUnitM

namespace QED.ChainProof.SetCRegDisp

open Complex Real QED.ChainProof.SetCUnitM QED.ChainProof.SetCK
open QED.TwoLoop.UnitLGraphTrace
open Filter Set Topology

/-- The normalized transverse crossed placements are the two frozen-kernel photon terms. -/
theorem uBDT_crossed_pair_eq_xExact (P : Params) (he : P.e ≠ 0) (hm : 0 < P.m)
    {mγ Λ T : ℝ} (hγ : 0 < mγ) (hγΛ : mγ < Λ) (hT : 0 < T)
    (haT : (mγ / P.m) ^ 2 ≠ T) (hbT : (Λ / P.m) ^ 2 ≠ T) :
    64 * π ^ 6 / P.e ^ 6 *
      ((1 / I) * (uBDT P 2 mγ Λ T + uBDT P 3 mγ Λ T)).re =
      xExact T (mγ / P.m) (Λ / P.m) := by
  let R := { P with mγ := mγ, Λ := Λ }
  have h5 := kerT_crossPF R hm false hγ hγΛ hT haT hbT rfl rfl
  have h4 := kerT_crossPF R hm true hγ hγΛ hT haT hbT rfl rfl
  change kerT .X R 5 mγ Λ T = _ at h5
  change kerT .X R 4 mγ Λ T = _ at h4
  rw [uBDT_crossed_pair P he hm.ne', h5, h4]
  have hg : Λ ^ 2 - mγ ^ 2 ≠ 0 :=
    sub_ne_zero.mpr (pow_lt_pow_left₀ hγΛ hγ.le (by decide : 2 ≠ 0)).ne.symm
  have hk : kConst = -((π ^ 4 / 4 : ℝ) : ℂ) * I := by
    rw [kConst, div_eq_mul_inv, mul_inv_rev, inv_I]
    push_cast
    ring
  have hgrp (c : ℝ) :
      (((P.e : ℂ) ^ 5 * (P.m : ℂ) ^ 5) * (c : ℂ) /
        (((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ) * kConst)).im =
      P.e ^ 5 * P.m ^ 5 * c / ((Λ ^ 2 - mγ ^ 2) * (π ^ 4 / 4)) := by
    rw [hk]
    let d : ℝ := (Λ ^ 2 - mγ ^ 2) * (π ^ 4 / 4)
    have ee :
        ((P.e : ℂ) ^ 5 * (P.m : ℂ) ^ 5 * (c : ℂ)) /
          (((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ) * (-((π ^ 4 / 4 : ℝ) : ℂ) * I)) =
        ((P.e ^ 5 * P.m ^ 5 * c / d : ℝ) : ℂ) * I := by
      simp only [d, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
        Complex.ofReal_ofNat]
      rw [div_eq_mul_inv, mul_inv_rev, mul_inv_rev, inv_I]
      ring
    rw [ee]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, I_im, I_re,
      mul_one, mul_zero, add_zero, d]
  change (π ^ 4 * (Λ ^ 2 - mγ ^ 2) / (4 * P.e ^ 5 * P.m ^ 5)) * im (_ + _) = _
  rw [Complex.add_im, hgrp]
  unfold xExact
  field_simp [Real.pi_ne_zero, hm.ne', he, hg]
  ring

/-- The crossed transverse contribution has its regulator limit at fixed spectral mass. -/
theorem tendsto_uBDT_crossed_pair (P : Params) (he : P.e ≠ 0) (hm : 0 < P.m)
    {T : ℝ} (hT : 4 ≤ T) :
    Tendsto (fun p : ℝ × ℝ => 64 * π ^ 6 / P.e ^ 6 *
      ((1 / I) * (uBDT P 2 p.1 p.2 T + uBDT P 3 p.1 p.2 T)).re)
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (crossUnit 0 T + crossUnit T 0)) := by
  refine (tendsto_xExact_div_mass hm hT).congr' ?_
  filter_upwards [eventually_xExact_mass_separation hm hT] with p hp
  have ht : 0 < T := by linarith
  exact (uBDT_crossed_pair_eq_xExact P he hm hp.1 hp.2.1 ht
    (by linarith [hp.2.2.1]) (by linarith [hp.2.2.2])).symm

end QED.ChainProof.SetCRegDisp

namespace QED.ChainProof.SetCUnitM

open QED.TwoLoop.UnitXClose

/- These weights are multiples of 1/10000. They use the monomial exponents of
`QED/TwoLoop/UnitXCloseCert.lean` with the extra spectral factor built into
the denominator. The kernel checks the weights and exponent inequalities below. -/
private def spectralCerts : List Cert := [
  (![0, 0, 1778, 3111, 3111, 1111, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 889, 889, 3333, 3111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 3111, 889, 1111, 3111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 3111, 889, 2222, 3111, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 0, 2667, 4000, 1778, 222, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 2889, 4222, 889, 0, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 3111, 667, 889, 4000, 0, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 889, 2889, 889, 4000, 0, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 667, 4222, 3111, 0, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 5333, 889, 1111, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 3111, 889, 3333, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 889, 889, 0, 3111, 4222, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 2222, 667, 889, 5333, 0, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2889, 889, 5333, 0, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 889, 3111, 2222, 3111, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![667, 0, 0, 222, 222, 5111, 3778, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 4000, 3111, 889, 1111, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 667, 4222, 889, 0, 3111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 889, 3111, 1111, 3111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 5333, 889, 0, 3111, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![3555, 3111, 667, 889, 1778, 0, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![3555, 889, 2889, 889, 1778, 0, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 2000, 667, 4222, 1778, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 3333, 667, 4222, 889, 0, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 3333, 667, 2000, 3111, 0, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 2889, 2000, 3111, 0, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 667, 6444, 889, 0, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 0, 3111, 2000, 1778, 1333], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 0, 889, 2000, 4000, 1333], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 889, 5333, 0, 3111, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 0, 5333, 889, 1778, 1333], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 0, 3111, 3111, 1778, 1333], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 0, 889, 5333, 1778, 1333], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 3111, 889, 0, 5333, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 889, 3111, 0, 5333, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 1778, 889, 0, 1778, 4222, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 2000, 2889, 2000, 1778, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 4000, 889, 3111, 1111, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 4000, 889, 889, 1111, 3111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 889, 889, 0, 889, 6444, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 667, 2000, 3111, 0, 3111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 0, 889, 4222, 1778, 1333], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 889, 889, 1111, 5333, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 889, 0, 3333, 4000, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 0, 0, 4222, 2667, 1333], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2889, 3111, 3111, 0, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 889, 2889, 3111, 0], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 3111, 2889, 3111, 0], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 889, 5111, 3111, 0], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 0, 2889, 4000, 0], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 889, 2889, 5333, 0], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 5111, 4000, 0], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 889, 3778, 4000, 1333], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 2889, 6222, 0], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 4889, 1333], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 2667, 3555], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 3111, 3111, 0, 3111, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 0, 2889, 4000, 0], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 889, 2889, 5333, 0], ![2000, 0, 0, 8000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 5111, 4000, 0], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 3111, 1556, 4000, 1333], ![2000, 0, 0, 8000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 889, 3778, 4000, 1333], ![2000, 0, 0, 8000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 6000, 2667, 1333], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 889, 889, 0, 7555, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 2889, 6222, 0], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 4889, 1333], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 1556, 7111, 1333], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 1556, 4889, 3555], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1556, 0, 0, 1111, 7333], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 4222, 667, 2000, 1778, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 889, 3111, 0, 889, 4222, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 3333, 667, 2000, 889, 0, 3111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 3333, 2889, 2000, 889, 0, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 2889, 2000, 889, 0, 3111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![889, 222, 5111, 2000, 0, 0, 1778, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 4000, 889, 0, 3333, 1778, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 4000, 0, 889, 2000, 1778, 1333], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1333, 2889, 4000, 0, 0, 1778, 0], ![0, 9333, 0, 0, 0, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![1333, 889, 2889, 3111, 1778, 0, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 3111, 0, 3333, 1778, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2000, 889, 0, 5333, 1778, 0], ![0, 9333, 0, 0, 0, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 1778, 889, 222, 0, 5333], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 2222, 667, 3111, 3111, 0, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2889, 5333, 889, 0, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 5333, 889, 667, 3111, 0], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 5333, 0, 2889, 1778, 0], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 3111, 667, 3111, 0], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 0, 5111, 1778, 0], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 7333, 1778, 0], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 3111, 3778, 1778, 1333], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 5333, 0, 667, 4000, 0], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 889, 667, 5333, 0], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 6000, 2667, 1333], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 667, 2000, 889, 0, 5333, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 445, 0, 3333, 0, 6222], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 5333, 0, 2889, 1778, 0], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 0, 5111, 1778, 0], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 5333, 0, 667, 4000, 0], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1778, 889, 2000, 0, 5333], ![2000, 0, 0, 8000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 444, 0, 5556, 0, 4000], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 0, 667, 6222, 0], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 889, 1556, 6222, 1333], ![2000, 0, 0, 8000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 889, 1556, 4000, 3555], ![2000, 0, 0, 8000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 2667, 3555], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 445, 0, 3333, 0, 6222], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 667, 8444, 0], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 445, 0, 1111, 0, 8444], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 222, 2889, 3778, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 222, 5111, 3778, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 222, 2889, 6000, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 3778, 4667, 1333], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 4000, 0, 3111, 2889], ![0, 0, 0, 5333, 0, 0, 0, 2667, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 2444, 1556, 2444, 3556], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 1778, 0, 3111, 5111], ![0, 0, 0, 5333, 0, 0, 0, 2667, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 0, 4889, 5111], ![1333, 0, 0, 2667, 0, 0, 0, 4000, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 0, 2667, 7333], ![1333, 0, 0, 2667, 0, 0, 0, 4000, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 889, 3778, 4000, 1333], ![6000, 0, 0, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 0, 4889, 1778, 1778, 222, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 5555, 667, 2000, 889, 0, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 3333, 667, 4222, 0, 0, 1778, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 2889, 4222, 0, 0, 1778, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 4000, 3111, 0, 1111, 1778, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 6222, 889, 889, 1111, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 4222, 889, 0, 3111, 1778, 0], ![0, 9333, 0, 0, 0, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![1333, 3111, 667, 3111, 1778, 0, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 667, 6444, 0, 0, 1778, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 5333, 0, 1111, 1778, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 889, 0, 5555, 1778, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 667, 4222, 0, 0, 4000, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 3111, 0, 1111, 4000, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2000, 3111, 0, 3111, 1778, 0], ![0, 9333, 0, 0, 0, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2000, 0, 0, 6222, 445, 1333], ![0, 9333, 0, 0, 0, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 445, 1333, 0, 0, 4222, 0, 4000], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2000, 889, 0, 3111, 4000, 0], ![0, 9333, 0, 0, 0, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2000, 0, 0, 4000, 2667, 1333], ![0, 9333, 0, 0, 0, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 2222, 667, 5333, 889, 0, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2889, 3111, 889, 2222, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 7555, 0, 667, 1778, 0], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 889, 6000, 1778, 1333], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 8222, 445, 1333], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1778, 889, 2000, 0, 5333], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 444, 0, 5556, 0, 4000], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 0, 667, 6222, 0], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 7555, 0, 667, 1778, 0], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 7333, 1778, 0], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 8222, 445, 1333], ![0, 2000, 0, 6000, 2000, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1556, 3111, 0, 222, 5111], ![2000, 0, 0, 8000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1556, 889, 0, 222, 7333], ![2000, 0, 0, 8000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 5333, 222, 667, 3778, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 0, 6222, 0, 3111, 0], ![0, 0, 0, 3333, 0, 0, 0, 2667, 4000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 4667, 1556, 2444, 1333], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 2445, 3778, 2444, 1333], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 6000, 2445, 1333], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 889, 0, 0, 6222, 0, 0, 2889], ![0, 0, 0, 2667, 0, 0, 0, 2667, 4666, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 4667, 1556, 222, 3555], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 2444, 3778, 222, 3556], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 222, 222, 5778, 0, 3778], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 222, 667, 6000, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 0, 4000, 0, 5333, 0], ![0, 0, 0, 3333, 0, 0, 0, 2667, 4000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 2444, 1556, 4667, 1333], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 3778, 2444, 3556], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 889, 0, 0, 4000, 0, 0, 5111], ![0, 0, 0, 2667, 0, 0, 0, 2667, 4666, 0, 0, 0, 0]),
  (![0, 0, 0, 222, 2445, 1333, 0, 6000], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 222, 222, 3556, 0, 6000], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 1778, 0, 5333, 2889], ![0, 0, 0, 5333, 0, 0, 0, 2667, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 1556, 4667, 3555], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 1556, 2444, 5778], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 889, 0, 0, 1778, 0, 0, 7333], ![0, 0, 0, 2667, 0, 0, 0, 2667, 4666, 0, 0, 0, 0]),
  (![0, 0, 0, 222, 222, 1334, 0, 8222], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 0, 7111, 2889], ![1333, 0, 0, 2667, 0, 0, 0, 4000, 2000, 0, 0, 0, 0]),
  (![1333, 445, 0, 1333, 1778, 5111, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 889, 2889, 5333, 0], ![6000, 0, 0, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 3111, 1556, 4000, 1333], ![6000, 0, 0, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1556, 3111, 0, 222, 5111], ![6000, 0, 0, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 889, 3778, 1778, 3555], ![6000, 0, 0, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![5778, 889, 666, 889, 1778, 0, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![3555, 1778, 667, 0, 4000, 0, 0, 0], ![4000, 0, 0, 6000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 2000, 667, 2000, 4000, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 0, 2667, 1778, 4000, 222, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 4000, 0, 0, 4222, 445, 1333], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 3333, 667, 2000, 0, 0, 4000, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 2889, 2000, 0, 0, 4000, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 4000, 0, 0, 2000, 2667, 1333], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 4222, 0, 0, 4000, 445, 1333], ![0, 9333, 0, 0, 0, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![3555, 889, 667, 3111, 1778, 0, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![3555, 889, 667, 889, 4000, 0, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 1778, 667, 0, 6222, 0, 0, 0], ![4000, 0, 0, 6000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![3556, 0, 1555, 1778, 1778, 1333, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 667, 2000, 5333, 0, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 889, 5333, 1111, 889, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 0, 0, 6445, 444, 1333], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2889, 3111, 889, 0, 3111, 0], ![0, 6667, 0, 0, 0, 0, 3333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 889, 0, 1111, 6222, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 0, 0, 2000, 4889, 1333], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 2000, 0, 0, 667, 5555], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 889, 667, 5333, 1778, 0, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 889, 667, 3111, 4000, 0, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 0, 1556, 4000, 1778, 1333, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 889, 667, 889, 6222, 0, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 0, 1556, 1778, 4000, 1333, 0, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2889, 889, 3111, 2222, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 5333, 667, 3111, 0], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 5333, 1556, 1778, 1333], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2889, 889, 889, 4444, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 5333, 222, 2889, 1556, 0], ![0, 8667, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 222, 5111, 1556, 0], ![0, 8667, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 3111, 667, 5333, 0], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 222, 7333, 1556, 0], ![0, 8667, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 3111, 1556, 4000, 1333], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 8222, 222, 1334], ![0, 8667, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 222, 2889, 3778, 0], ![0, 8667, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 889, 667, 7555, 0], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 222, 5111, 3778, 0], ![0, 8667, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 889, 1556, 6222, 1333], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 6000, 2445, 1333], ![0, 8667, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1556, 889, 0, 2444, 5111], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 6000, 222, 3556], ![0, 8667, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1556, 889, 0, 222, 7333], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 1556, 7111, 1333], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 3778, 4667, 1333], ![0, 8667, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1556, 0, 0, 3333, 5111], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 3778, 2444, 3556], ![0, 8667, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1556, 0, 0, 1111, 7333], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 222, 222, 3556, 0, 6000], ![0, 8667, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 445, 0, 1111, 0, 8444], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 7555, 889, 0, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 5333, 3111, 0, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 5333, 889, 2222, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 3111, 5333, 0, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 3111, 3111, 2222, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 3111, 889, 4444, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 889, 5333, 2222, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 667, 0, 222, 889, 7333, 889, 0], ![0, 0, 0, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 5333, 0, 2889, 1778, 0], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 0, 5111, 1778, 0], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 7333, 1778, 0], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 0, 5333, 0, 4000, 0], ![4000, 0, 0, 2000, 0, 0, 0, 0, 4000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 8222, 445, 1333], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 5333, 0, 1778, 2889], ![4000, 0, 0, 4000, 0, 0, 0, 0, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 0, 2889, 4000, 0], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 5111, 4000, 0], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 0, 3111, 0, 6222, 0], ![4000, 0, 0, 2000, 0, 0, 0, 0, 4000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 6000, 2667, 1333], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 3111, 0, 4000, 2889], ![4000, 0, 0, 4000, 0, 0, 0, 0, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 6000, 444, 3556], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 2889, 6222, 0], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 0, 889, 0, 8444, 0], ![4000, 0, 0, 2000, 0, 0, 0, 0, 4000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 4889, 1333], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 889, 0, 6222, 2889], ![4000, 0, 0, 4000, 0, 0, 0, 0, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 2667, 3555], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 889, 0, 4000, 5111], ![4000, 0, 0, 4000, 0, 0, 0, 0, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 444, 5778], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 889, 0, 1778, 7333], ![4000, 0, 0, 4000, 0, 0, 0, 0, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 1556, 7111, 1333], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 1556, 4889, 3555], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 0, 4889, 5111], ![0, 4000, 0, 4000, 0, 0, 0, 0, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 1556, 0, 0, 1111, 7333], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 0, 2667, 7333], ![0, 4000, 0, 4000, 0, 0, 0, 0, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 445, 0, 1111, 0, 8444], ![0, 2000, 0, 0, 7333, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 5333, 0, 2889, 1778, 0], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 2444, 667, 3778, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 0, 5111, 1778, 0], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 2444, 2889, 3778, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 4667, 666, 3778, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 0, 2889, 4000, 0], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 2444, 667, 6000, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 5111, 4000, 0], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 6000, 2667, 1333], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 6000, 444, 3556], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 222, 667, 8222, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 2889, 6222, 0], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 1556, 6889, 1333], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 4889, 1333], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 0, 1778, 0, 7555, 0], ![0, 0, 0, 3333, 0, 0, 0, 2667, 4000, 0, 0, 0, 0]),
  (![0, 0, 667, 0, 0, 0, 9333, 0], ![1333, 0, 0, 667, 0, 0, 0, 4000, 4000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 1556, 7111, 1333], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 1556, 4889, 3555], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 1555, 2667, 5778], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 445, 0, 1111, 0, 8444], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 444, 0, 0, 0, 0, 0, 9556], ![1334, 0, 0, 1333, 0, 0, 0, 4000, 3333, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 0, 2667, 7333], ![0, 0, 0, 0, 2667, 0, 2667, 2666, 2000, 0, 0, 0, 0]),
  (![3333, 1852, 741, 0, 4074, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1111, 4074, 741, 0, 4074, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1111, 1852, 2963, 0, 4074, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 5185, 741, 0, 2963, 0, 1111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 741, 5185, 0, 2963, 0, 1111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1111, 1852, 741, 0, 6296, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 2963, 741, 0, 5185, 0, 1111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 741, 2963, 0, 5185, 0, 1111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 2963, 741, 0, 2963, 0, 3333, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 5111, 3111, 889, 0, 889, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 3704, 0, 2963, 0, 1852, 1481], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 741, 741, 0, 7407, 0, 1111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2889, 5333, 889, 0, 889, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 741, 741, 0, 5185, 0, 3333, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1482, 0, 5185, 0, 1852, 1481], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 741, 741, 0, 2963, 0, 5555, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1481, 0, 2963, 0, 1852, 3704], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 5333, 0, 2889, 1778, 0], ![0, 6000, 0, 0, 2000, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 0, 5111, 1778, 0], ![0, 6000, 0, 0, 2000, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 7333, 1778, 0], ![0, 6000, 0, 0, 2000, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 0, 2889, 4000, 0], ![0, 6000, 0, 0, 2000, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 5111, 4000, 0], ![0, 6000, 0, 0, 2000, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 6000, 2445, 1333], ![0, 6000, 0, 0, 0, 0, 4000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 2889, 6222, 0], ![0, 6000, 0, 0, 2000, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 889, 1556, 6222, 1333], ![6000, 0, 0, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 4889, 1333], ![0, 6000, 0, 0, 2000, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1556, 889, 0, 2444, 5111], ![6000, 0, 0, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 2667, 3555], ![0, 6000, 0, 0, 2000, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1556, 889, 0, 222, 7333], ![6000, 0, 0, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![5778, 1778, 666, 0, 1778, 0, 0, 0], ![4000, 0, 0, 6000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![3555, 2000, 667, 2000, 1778, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![3555, 0, 2667, 1778, 1778, 222, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 5555, 667, 2000, 0, 0, 1778, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 5333, 667, 889, 1778, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 3333, 2889, 2000, 0, 0, 1778, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 5111, 3111, 889, 0, 889, 0], ![0, 6667, 0, 0, 0, 0, 3333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 6222, 889, 0, 1111, 1778, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 3111, 667, 3111, 1778, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2889, 5333, 889, 0, 889, 0], ![0, 6667, 0, 0, 0, 0, 3333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2000, 0, 0, 6222, 1333, 445], ![0, 0, 9333, 0, 0, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 4444, 667, 889, 3111, 0, 889, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 1111, 667, 2000, 0, 0, 6222, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 4000, 889, 0, 1111, 4000, 0], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2000, 0, 0, 4000, 444, 3556], ![0, 9333, 0, 0, 0, 0, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 889, 667, 0, 7555, 0, 889, 0], ![4000, 0, 0, 6000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1333, 889, 667, 5333, 1778, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 1556, 3111, 0, 222, 5111], ![8667, 0, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 8222, 889, 667], ![0, 0, 8667, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 2222, 667, 3111, 3111, 0, 889, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 222, 5111, 0, 3778], ![0, 0, 8667, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 222, 2889, 6000, 0], ![0, 8667, 0, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1778, 444, 0, 1556, 0, 6222], ![6000, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 222, 2889, 0, 6000], ![0, 0, 8667, 0, 0, 0, 1333, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 7555, 1778, 667, 0, 0], ![2000, 0, 0, 0, 0, 0, 8000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 8222, 0, 1778], ![0, 0, 2000, 0, 4000, 3333, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 5333, 3111, 0, 889, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 6000, 0, 4000], ![0, 0, 2000, 0, 4000, 3333, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 3111, 3111, 0, 3111, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 0, 6222], ![0, 0, 2000, 0, 4000, 3333, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 667, 8444, 0], ![4667, 4000, 0, 1333, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 889, 3111, 0, 5333, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 0, 0, 0, 9333, 0], ![0, 4000, 0, 2000, 0, 0, 0, 0, 4000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 0, 7111, 2889], ![0, 4000, 0, 4000, 0, 0, 0, 0, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 0, 444, 9556], ![0, 4000, 0, 4000, 0, 0, 0, 0, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 1556, 0, 8444], ![0, 0, 2000, 0, 4000, 3333, 667, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 7556, 222, 667, 1555, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![1333, 0, 445, 6222, 1778, 222, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10000, 0, 0]),
  (![0, 0, 0, 5333, 2444, 667, 1556, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 5333, 222, 2889, 1556, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 2444, 2889, 1556, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 3111, 222, 5111, 1556, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 0, 7333, 1778, 0], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 6889, 667, 1555, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 2444, 5111, 1556, 0], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 0, 7555, 0, 1778, 0], ![4000, 0, 0, 2000, 0, 0, 0, 0, 4000, 0, 0, 0, 0]),
  (![0, 889, 667, 0, 8444, 0, 0, 0], ![0, 0, 0, 667, 0, 0, 0, 2667, 6666, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 7301, 0, 1905, 794], ![2857, 0, 0, 0, 0, 0, 0, 0, 7143, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 6889, 1556, 222, 1333], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 4667, 3778, 222, 1333], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 2445, 6000, 222, 1333], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 222, 8222, 222, 1334], ![0, 0, 0, 5333, 0, 0, 0, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 8222, 445, 1333], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 8222, 0, 1778], ![0, 0, 0, 0, 0, 4667, 667, 4000, 0, 666, 0, 0, 0]),
  (![0, 0, 0, 5333, 1556, 667, 2444, 0], ![0, 0, 0, 0, 0, 0, 5333, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 5079, 0, 4127, 794], ![2857, 0, 0, 0, 0, 0, 0, 0, 7143, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 5079, 0, 1905, 3016], ![2857, 0, 0, 0, 0, 0, 0, 0, 7143, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 6000, 0, 4000], ![0, 0, 0, 0, 0, 4667, 667, 4000, 0, 666, 0, 0, 0]),
  (![0, 0, 0, 3111, 1555, 667, 4667, 0], ![0, 0, 0, 0, 0, 0, 5333, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 2857, 0, 6349, 794], ![2857, 0, 0, 0, 0, 0, 0, 0, 7143, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 2667, 3555], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 2857, 0, 4127, 3016], ![2857, 0, 0, 0, 0, 0, 0, 0, 7143, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 3111, 0, 1778, 5111], ![4000, 0, 0, 4000, 0, 0, 0, 0, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 2857, 0, 1905, 5238], ![2857, 0, 0, 0, 0, 0, 0, 0, 7143, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 444, 5778], ![0, 0, 0, 0, 4667, 0, 667, 4666, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 3778, 0, 6222], ![0, 0, 0, 0, 0, 4667, 667, 4000, 0, 666, 0, 0, 0]),
  (![0, 0, 0, 889, 1555, 667, 6889, 0], ![0, 0, 0, 0, 0, 0, 5333, 4667, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 635, 0, 8571, 794], ![2857, 0, 0, 0, 0, 0, 0, 0, 7143, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 635, 0, 6349, 3016], ![2857, 0, 0, 0, 0, 0, 0, 0, 7143, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 635, 0, 4127, 5238], ![2857, 0, 0, 0, 0, 0, 0, 0, 7143, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 635, 0, 1905, 7460], ![2857, 0, 0, 0, 0, 0, 0, 0, 7143, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 1556, 0, 8444], ![0, 0, 0, 0, 0, 4667, 667, 4000, 0, 666, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 0, 4889, 5111], ![0, 0, 0, 0, 2667, 0, 2667, 2666, 2000, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 0, 4762, 5238], ![2857, 0, 0, 0, 0, 0, 0, 0, 2381, 0, 0, 4762, 0]),
  (![0, 0, 0, 0, 0, 0, 2540, 7460], ![2857, 0, 0, 0, 0, 0, 0, 0, 2381, 0, 0, 4762, 0]),
  (![0, 0, 0, 0, 0, 0, 444, 9556], ![0, 0, 0, 0, 2667, 0, 2667, 2666, 2000, 0, 0, 0, 0]),
  (![5555, 1852, 741, 0, 1852, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![3333, 4074, 741, 0, 1852, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![3333, 1852, 2963, 0, 1852, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1111, 6296, 741, 0, 1852, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1111, 4074, 2963, 0, 1852, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 2963, 2963, 0, 2963, 0, 1111, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![1111, 1852, 5185, 0, 1852, 0, 0, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 3555, 667, 4000, 0, 0, 1778, 0], ![0, 8000, 0, 0, 0, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 1333, 667, 6222, 0, 0, 1778, 0], ![0, 8000, 0, 0, 0, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 1333, 667, 4000, 0, 0, 4000, 0], ![0, 8000, 0, 0, 0, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 2889, 3111, 889, 0, 3111, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 741, 2963, 0, 2963, 0, 3333, 0], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 1482, 0, 2963, 0, 4074, 1481], ![10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 7555, 889, 0, 889, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 7555, 667, 889, 0], ![6000, 0, 0, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 7301, 0, 1905, 794], ![8571, 0, 0, 0, 0, 0, 0, 0, 1429, 0, 0, 0, 0]),
  (![0, 0, 0, 889, 3111, 5111, 889, 0], ![6000, 0, 0, 4000, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 8222, 445, 1333], ![0, 6000, 0, 0, 2000, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 5333, 889, 0, 3111, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 5079, 0, 4127, 794], ![8571, 0, 0, 0, 0, 0, 0, 0, 1429, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 5079, 0, 1905, 3016], ![8571, 0, 0, 0, 0, 0, 0, 0, 1429, 0, 0, 0, 0]),
  (![0, 0, 0, 444, 0, 5556, 0, 4000], ![0, 6000, 0, 0, 2000, 0, 2000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 667, 3111, 889, 0, 5333, 0], ![0, 0, 0, 0, 0, 0, 10000, 0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 2857, 0, 6349, 794], ![8571, 0, 0, 0, 0, 0, 0, 0, 1429, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 2857, 0, 1905, 5238], ![8571, 0, 0, 0, 0, 0, 0, 0, 1429, 0, 0, 0, 0]),
  (![0, 0, 0, 445, 0, 3333, 0, 6222], ![0, 6000, 0, 0, 2000, 0, 2000, 0, 0, 0, 0, 0, 0]),
  ]

private def spectralIndices2 : List (Fin 5 → ℕ) := [
  ![310, 175, 20, 176, 21], ![311, 20, 22, 177, 4], ![312, 21, 4, 178, 35], ![69, 22, 23, 24, 5],
  ![36, 4, 5, 25, 16], ![117, 35, 16, 37, 70], ![118, 23, 119, 71, 120], ![72, 5, 120, 73, 121],
  ![74, 16, 121, 38, 75], ![122, 70, 75, 76, 179], ![313, 119, 314, 180, 77],
  ![315, 120, 77, 181, 316], ![317, 75, 123, 182, 183], ![20, 184, 124, 6, 78],
  ![176, 185, 6, 186, 7], ![21, 187, 78, 7, 170], ![22, 124, 26, 8, 9], ![177, 6, 8, 188, 0],
  ![4, 78, 9, 0, 10], ![178, 7, 0, 189, 11], ![35, 170, 10, 11, 39], ![23, 26, 125, 17, 126],
  ![24, 8, 17, 40, 2], ![5, 9, 126, 2, 79], ![25, 0, 2, 18, 1], ![16, 10, 79, 1, 127],
  ![37, 11, 1, 27, 41], ![119, 125, 318, 128, 319], ![73, 2, 129, 42, 43], ![121, 79, 130, 43, 80],
  ![38, 1, 43, 28, 44], ![75, 127, 80, 44, 131], ![76, 41, 44, 81, 132], ![179, 190, 131, 132, 320],
  ![180, 128, 321, 322, 191], ![181, 129, 191, 192, 133], ![323, 43, 133, 193, 134],
  ![182, 44, 134, 194, 324], ![124, 195, 135, 82, 83], ![6, 196, 82, 12, 45],
  ![78, 197, 83, 45, 136], ![186, 198, 12, 325, 13], ![7, 199, 45, 13, 200],
  ![26, 135, 137, 84, 85], ![8, 82, 84, 86, 46], ![9, 83, 85, 46, 87], ![188, 12, 86, 201, 47],
  ![0, 45, 46, 47, 48], ![10, 136, 87, 48, 88], ![189, 13, 47, 202, 89], ![11, 200, 48, 89, 138],
  ![39, 203, 88, 138, 139], ![125, 137, 326, 90, 204], ![17, 84, 90, 91, 49],
  ![126, 85, 204, 49, 205], ![40, 86, 91, 206, 50], ![2, 46, 49, 50, 51], ![79, 87, 205, 51, 207],
  ![18, 47, 50, 208, 52], ![1, 48, 51, 52, 92], ![127, 88, 207, 92, 209], ![27, 89, 52, 327, 140],
  ![190, 139, 209, 141, 328], ![128, 90, 329, 142, 210], ![93, 91, 142, 211, 53],
  ![129, 49, 210, 53, 212], ![42, 50, 53, 213, 54], ![43, 51, 212, 54, 214], ![28, 52, 54, 215, 55],
  ![44, 92, 214, 55, 216], ![81, 140, 55, 217, 94], ![132, 141, 216, 94, 330],
  ![192, 53, 331, 218, 219], ![193, 54, 219, 220, 221], ![194, 55, 221, 222, 223],
  ![332, 94, 223, 224, 333], ![135, 225, 143, 19, 95], ![82, 226, 19, 56, 3], ![83, 227, 95, 3, 96],
  ![12, 228, 56, 29, 14], ![45, 229, 3, 14, 15], ![136, 230, 96, 15, 144], ![13, 231, 14, 30, 31],
  ![203, 232, 144, 32, 145], ![137, 143, 334, 97, 233], ![84, 19, 97, 33, 57],
  ![85, 95, 233, 57, 234], ![86, 56, 33, 34, 58], ![46, 3, 57, 58, 59], ![87, 96, 234, 59, 235],
  ![201, 29, 34, 236, 60], ![47, 14, 58, 60, 61], ![48, 15, 59, 61, 62], ![88, 144, 235, 62, 237],
  ![202, 30, 60, 238, 146], ![89, 31, 61, 146, 98], ![138, 32, 62, 98, 99],
  ![139, 145, 237, 99, 335], ![90, 97, 336, 100, 239], ![91, 33, 100, 63, 64],
  ![49, 57, 239, 64, 240], ![206, 34, 63, 241, 101], ![50, 58, 64, 101, 65],
  ![51, 59, 240, 65, 242], ![208, 60, 101, 243, 102], ![52, 61, 65, 102, 103],
  ![92, 62, 242, 103, 244], ![140, 98, 103, 147, 104], ![141, 99, 244, 104, 337],
  ![142, 100, 338, 105, 245], ![211, 63, 105, 246, 66], ![53, 64, 245, 66, 247],
  ![213, 101, 66, 248, 67], ![54, 65, 247, 67, 249], ![215, 102, 67, 250, 68],
  ![55, 103, 249, 68, 251], ![217, 147, 68, 252, 106], ![94, 104, 251, 106, 339],
  ![340, 105, 341, 342, 253], ![218, 66, 253, 343, 254], ![220, 67, 254, 255, 256],
  ![222, 68, 256, 257, 258], ![224, 106, 258, 344, 345], ![143, 346, 347, 148, 259],
  ![19, 348, 148, 260, 107], ![95, 349, 259, 107, 261], ![3, 350, 107, 262, 108],
  ![96, 351, 261, 108, 352], ![29, 353, 263, 149, 150], ![15, 354, 108, 151, 152],
  ![355, 356, 149, 357, 153], ![30, 358, 150, 153, 154], ![31, 359, 151, 154, 155],
  ![32, 360, 152, 155, 156], ![145, 361, 362, 156, 363], ![97, 148, 364, 157, 264],
  ![33, 260, 157, 265, 109], ![57, 107, 264, 109, 266], ![34, 263, 265, 158, 159],
  ![58, 262, 109, 159, 110], ![59, 108, 266, 110, 267], ![236, 149, 158, 365, 111],
  ![60, 150, 159, 111, 112], ![61, 151, 110, 112, 160], ![62, 152, 267, 160, 268],
  ![238, 153, 111, 366, 161], ![146, 154, 112, 161, 162], ![98, 155, 160, 162, 163],
  ![99, 156, 268, 163, 367], ![100, 157, 368, 269, 270], ![64, 109, 270, 271, 272],
  ![241, 158, 273, 369, 164], ![65, 110, 272, 165, 370], ![243, 111, 164, 371, 113],
  ![102, 112, 165, 113, 166], ![372, 161, 113, 373, 167], ![147, 162, 166, 167, 168],
  ![104, 163, 374, 168, 375], ![105, 269, 376, 274, 275], ![246, 273, 274, 377, 169],
  ![66, 271, 275, 169, 276], ![248, 164, 169, 378, 114], ![67, 165, 276, 114, 277],
  ![250, 113, 114, 379, 115], ![68, 166, 277, 115, 278], ![252, 167, 115, 380, 279],
  ![106, 168, 278, 279, 381], ![255, 114, 382, 383, 280], ![257, 115, 280, 384, 385],
  ]

private def spectralIndices1 : List (Fin 5 → ℕ) := [
  ![386, 175, 20, 281, 21], ![387, 20, 69, 282, 36], ![388, 21, 36, 283, 117],
  ![389, 69, 118, 284, 72], ![390, 36, 72, 391, 74], ![392, 117, 74, 285, 122],
  ![20, 184, 22, 6, 4], ![281, 185, 6, 286, 7], ![21, 187, 4, 7, 35], ![69, 22, 23, 24, 5],
  ![282, 6, 24, 287, 25], ![36, 4, 5, 25, 16], ![283, 7, 25, 288, 37], ![118, 23, 393, 71, 77],
  ![284, 24, 71, 289, 73], ![72, 5, 77, 73, 290], ![74, 16, 290, 38, 123], ![285, 37, 38, 291, 76],
  ![122, 70, 123, 76, 183], ![22, 195, 26, 8, 9], ![6, 196, 8, 12, 0], ![4, 197, 9, 0, 10],
  ![286, 198, 12, 292, 13], ![7, 199, 0, 13, 11], ![35, 170, 10, 11, 39], ![23, 26, 394, 17, 293],
  ![24, 8, 17, 40, 2], ![5, 9, 293, 2, 130], ![287, 12, 40, 294, 18], ![25, 0, 2, 18, 1],
  ![16, 10, 130, 1, 80], ![288, 13, 18, 295, 27], ![37, 11, 1, 27, 41], ![70, 39, 80, 41, 131],
  ![71, 17, 395, 93, 396], ![289, 40, 93, 296, 42], ![397, 18, 42, 398, 28], ![38, 1, 133, 28, 134],
  ![291, 27, 28, 297, 81], ![26, 225, 399, 19, 298], ![8, 226, 19, 56, 3], ![9, 227, 298, 3, 299],
  ![12, 228, 56, 29, 14], ![0, 229, 3, 14, 15], ![10, 230, 299, 15, 300], ![292, 400, 29, 401, 30],
  ![13, 231, 14, 30, 31], ![11, 402, 15, 31, 32], ![39, 232, 300, 32, 403], ![17, 19, 404, 33, 301],
  ![2, 3, 301, 171, 302], ![294, 29, 34, 405, 172], ![18, 14, 171, 172, 116],
  ![1, 15, 302, 116, 303], ![295, 30, 172, 406, 173], ![27, 31, 116, 173, 174],
  ![41, 32, 303, 174, 407], ![93, 33, 408, 63, 304], ![296, 34, 63, 409, 305],
  ![42, 171, 304, 305, 306], ![28, 116, 306, 307, 308], ![297, 173, 307, 410, 309],
  ![81, 174, 308, 309, 411],
  ]

private def spectralCertOK (d : ℕ) (cc : Cert) (n : Fin 5 → ℕ) (i : Fin 5) : Bool :=
  (List.ofFn cc.1).sum == 10000 && (List.ofFn cc.2).sum == 10000 &&
    (List.finRange 5).all fun k =>
      decide (9 * (List.ofFn fun j => cc.1 j * UExp j k).sum +
        (2 * d - 1) * (List.ofFn fun j => cc.2 j * EExp j k).sum +
        (if k = 4 then 10000 else 0) ≤ 20000 * (n k + if k = i then 1 else 0) + 18000)

private def spectralTermOK (d : ℕ) (certs : List Cert) (p : Term × (Fin 5 → ℕ)) : Bool :=
  (List.finRange 5).all fun i => spectralCertOK d (certs.getD (p.2 i) (0, 0)) p.1.2.1 i

private noncomputable def spectralDen (d : ℕ) (U E b : ℝ) : ℝ :=
  U ^ 4 * E ^ (d - 1) * Real.sqrt (U * E * b)

private theorem mono_delta {z : Fin 5 → ℝ} (i : Fin 5) :
    mono z (fun k => if k = i then (1 : ℝ) else 0) = z i := by
  unfold mono
  rw [Finset.prod_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp

private theorem spectralCertBound {A M c a b : ℝ}
    (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (hz1 : ∀ k, gz A M c a b k ≤ 1) {d : ℕ} (hd : 1 ≤ d)
    {cc : Cert} {n : Fin 5 → ℕ} {i : Fin 5} (h : spectralCertOK d cc n i = true) :
    let z := gz A M c a b
    z i * (∏ k, z k ^ n k) / spectralDen d (gXU A M c a b) (gXEn A M c a b) b ≤
      mono z (fun _ => -(9 / 10 : ℝ)) := by
  intro z
  simp only [spectralCertOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    decide_eq_true_eq, true_implies, List.sum_ofFn] at h
  obtain ⟨⟨hθ, hφ⟩, hcheck⟩ := h
  let θ : Fin 8 → ℝ := fun j => (cc.1 j : ℝ) / 10000
  let φ : Fin 13 → ℝ := fun j => (cc.2 j : ℝ) / 10000
  let p := ∑ j, θ j • UExpR j
  let q := ∑ j, φ j • EExpR j
  let u : Fin 5 → ℝ := fun k => if k = 4 then 1 else 0
  let top : Fin 5 → ℝ := (fun k => (n k : ℝ)) + (fun k => if k = i then 1 else 0)
  let bot := (4 : ℝ) • p + ((d - 1 : ℕ) : ℝ) • q + (1 / 2 : ℝ) • (p + q + u)
  have hz : ∀ k, 0 < z k := gz_pos hA hM hc ha hb
  have hθ1 : ∑ j, θ j = 1 := by
    simp only [θ, ← Finset.sum_div, div_eq_iff (by norm_num : (10000 : ℝ) ≠ 0), one_mul]
    exact_mod_cast hθ
  have hφ1 : ∑ j, φ j = 1 := by
    simp only [φ, ← Finset.sum_div, div_eq_iff (by norm_num : (10000 : ℝ) ≠ 0), one_mul]
    exact_mod_cast hφ
  have hU := mono_le_gXU hA hM hc ha hb θ (fun _ => by dsimp [θ]; positivity) hθ1
  have hE := mono_le_gXEn hA hM hc ha hb φ (fun _ => by dsimp [φ]; positivity) hφ1
  have hp := mono_pos hz p
  have hq := mono_pos hz q
  have hb' : mono z u = b := mono_delta (z := z) 4
  have hden : mono z bot ≤ spectralDen d (gXU A M c a b) (gXEn A M c a b) b := by
    change mono z ((4 : ℝ) • p + ((d - 1 : ℕ) : ℝ) • q + (1 / 2 : ℝ) • (p + q + u)) ≤ _
    rw [mono_add hz, mono_add hz, mono_smul hz, mono_smul hz, mono_smul hz,
      mono_add hz, mono_add hz, Real.rpow_natCast, Real.rpow_ofNat, ← Real.sqrt_eq_rpow, hb']
    exact mul_le_mul
      (mul_le_mul (pow_le_pow_left₀ hp.le hU 4) (pow_le_pow_left₀ hq.le hE _)
        (pow_nonneg hq.le _) (pow_nonneg (hp.le.trans hU) _))
      (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_right (mul_le_mul hU hE hq.le (hp.le.trans hU)) hb.le))
      (Real.sqrt_nonneg _) (mul_nonneg (pow_nonneg (hp.le.trans hU) _)
        (pow_nonneg (hq.le.trans hE) _))
  have htop : z i * (∏ k, z k ^ n k) = mono z top := by
    change z i * _ = mono z ((fun k => (n k : ℝ)) + (fun k => if k = i then 1 else 0))
    rw [mono_add hz, mono_natCast, mono_delta, mul_comm]
  have hbot := mono_pos hz bot
  rw [htop]
  calc
    _ ≤ mono z top / mono z bot :=
      div_le_div_of_nonneg_left (mono_pos hz top).le hbot hden
    _ = mono z (top - bot) := by rw [div_eq_iff hbot.ne', ← mono_add hz, sub_add_cancel]
    _ ≤ mono z (fun _ => -(9 / 10 : ℝ)) := by
      apply mono_le_of_le_one hz hz1
      intro k
      have e1 : p k = (∑ j, (cc.1 j : ℝ) * UExp j k) / 10000 := by
        simp only [p, θ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, UExpR, Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
      have e2 : q k = (∑ j, (cc.2 j : ℝ) * EExp j k) / 10000 := by
        simp only [q, φ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, EExpR, Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
      have h₂ : 1 ≤ 2 * d := by omega
      have h' := hcheck k
      have h'' :
          9 * (∑ j, (cc.1 j : ℝ) * UExp j k) +
            (2 * (d : ℝ) - 1) * (∑ j, (cc.2 j : ℝ) * EExp j k) +
            (if k = 4 then 10000 else 0) ≤
            20000 * ((n k : ℝ) + if k = i then 1 else 0) + 18000 := by
        split_ifs at h' ⊢ <;> exact_mod_cast h'
      simp only [top, bot, u, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        e1, e2, Nat.cast_sub hd, Nat.cast_one]
      split_ifs at h'' ⊢ <;> nlinarith only [h'']

private theorem spectralListBound {A M c a b : ℝ}
    (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (hz1 : ∀ k, gz A M c a b k ≤ 1) (hsum : ∑ k, gz A M c a b k = 1)
    {d : ℕ} (hd : 1 ≤ d) {L : List Term} {I : List (Fin 5 → ℕ)}
    (hlen : L.length = I.length) (hL : (L.zip I).all (spectralTermOK d spectralCerts) = true) :
    let z := gz A M c a b
    evalAbs L z / spectralDen d (gXU A M c a b) (gXEn A M c a b) b ≤
      5 * absSum L * mono z (fun _ => -(9 / 10 : ℝ)) := by
  intro z
  let D := spectralDen d (gXU A M c a b) (gXEn A M c a b) b
  let G := mono z (fun _ => -(9 / 10 : ℝ))
  have hi (i : Fin 5) : z i * evalAbs L z / D ≤ absSum L * G := by
    induction L generalizing I with
    | nil => simp [evalAbs, absSum]
    | cons t L ih =>
      cases I with
      | nil => simp at hlen
      | cons v I =>
        simp only [List.length_cons, Nat.succ.injEq] at hlen
        simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hL
        have ht := hL.1
        simp only [spectralTermOK, List.all_eq_true, List.mem_finRange, true_implies] at ht
        have hb' := spectralCertBound hA hM hc ha hb hz1 hd (ht i)
        have h := mul_le_mul_of_nonneg_left hb' (abs_nonneg (t.1 : ℝ))
        change |(t.1 : ℝ)| * (z i * (∏ k, z k ^ t.2.1 k) / D) ≤ |(t.1 : ℝ)| * G at h
        have h' := ih hlen hL.2
        have key : z i * (|(t.1 : ℝ)| * ∏ k, z k ^ t.2.1 k) =
            |(t.1 : ℝ)| * (z i * ∏ k, z k ^ t.2.1 k) := by ring
        simpa only [evalAbs, absSum, List.map_cons, List.sum_cons, add_mul, mul_add,
          add_div, ← mul_div_assoc, key] using add_le_add h h'
  change evalAbs L z / D ≤ 5 * absSum L * G
  calc
    _ = ∑ i, z i * evalAbs L z / D := by rw [← Finset.sum_div, ← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ _i : Fin 5, absSum L * G := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp; ring

private theorem spectralDom₁ :
    (domTerms₁.zip spectralIndices2).all (spectralTermOK 2 spectralCerts) = true := by
  decide +kernel

private theorem spectralDom₂ :
    (domTerms₂.zip spectralIndices1).all (spectralTermOK 1 spectralCerts) = true := by
  decide +kernel

open QED.ChainProof.SetCRegDisp QED.ChainProof.SetCK

/-- A mass-independent spectral majorant for either spectator endpoint. -/
theorem abs_crossPFAt_mul_sqrt_le {lam Lam T μ : ℝ}
    (hl : 0 < lam) (hreg : lam < Lam) (hT : 0 < T) (hμ : 0 ≤ μ)
    (haT : lam ^ 2 ≠ T) (hbT : Lam ^ 2 ≠ T) {z : Fin 5 → ℝ}
    (hz : ∀ i, 0 < z i) (hsum : ∑ i, z i = 1) :
    Real.sqrt T * |crossPFAt μ (lam ^ 2) (Lam ^ 2) T z| ≤
      ((15 * absSum domTerms₁ + 5 * absSum domTerms₂) / 2) *
        mono z (fun _ => -(9 / 10 : ℝ)) := by
  obtain ⟨A, M, c, a, b, rfl⟩ : ∃ A M c a b, z = gz A M c a b :=
    ⟨z 0, z 1, z 2, z 3, z 4, (gz_eq z).symm⟩
  let z := gz A M c a b
  have hA : 0 < A := hz 0
  have hM : 0 < M := hz 1
  have hc : 0 < c := hz 2
  have ha : 0 < a := hz 3
  have hb : 0 < b := hz 4
  have hz1 (i : Fin 5) : z i ≤ 1 :=
    hsum ▸ Finset.single_le_sum (fun j _ => (hz j).le) (Finset.mem_univ i)
  let U := gXU A M c a b
  let E := gXE A M c a b
  let En := gXEn A M c a b
  let K := E + μ * a
  let F := M * gPsi1 A (M / 2) M c a b / (2 * U ^ 6)
  let G := M * gPsi2 A (M / 2) M c a b / (2 * U ^ 5)
  let s := K / b
  let R := vpPhotonT 1 lam Lam T
  have hU : 0 < U := gXU_pos hA hM hc ha hb
  have hE : 0 < E := gXE_pos hA hM hc ha hb
  have hK : E ≤ K := le_add_of_nonneg_right (mul_nonneg hμ ha.le)
  have hK0 := hE.trans_le hK
  have hs : 0 < s := div_pos hK0 hb
  have hgap := (pow_lt_pow_left₀ hreg hl.le (by decide : 2 ≠ 0)).ne
  rw [crossPFAt_eq_dressedPhoton hμ (sq_nonneg _) (sq_nonneg _) hT.le hgap haT hbT hz,
    crossedDressedPhoton_eq_vpPhotonT]
  change Real.sqrt T * |-(F / b ^ 2) * deriv R s - (G / b) * R s| ≤ _
  have hr := vpPhotonT_le_single one_pos hl hreg.le hT hs.le
  have hd := mul_abs_deriv_vpPhotonT_le one_pos hl hreg.le hT hs
  simp only [one_pow, mul_one] at hr hd
  have hd' : |deriv R s| ≤ 3 / (s * (s + T)) := by
    rwa [mul_comm s, ← le_div_iff₀ hs, div_div, mul_comm (s + T)] at hd
  have hr' : |R s| ≤ 1 / (s + T) := by
    rw [abs_of_nonneg (vpPhotonT_nonneg hl (hl.trans hreg) hT one_pos hs.le)]
    exact hr
  have hv : b * (s + T) = K + T * b := by dsimp only [s]; field_simp
  have hv' : b ^ 2 * (s * (s + T)) = K * (K + T * b) := by
    rw [← hv]
    dsimp only [s]
    field_simp
  have hw : Real.sqrt T / (K + T * b) ≤ 1 / Real.sqrt (E * b) := by
    rw [div_le_div_iff₀ (by positivity) (Real.sqrt_pos.2 (mul_pos hE hb)),
      one_mul, ← Real.sqrt_mul hT.le, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have he := pow_le_pow_left₀ (by positivity : 0 ≤ E + T * b)
      (add_le_add_left hK (T * b)) 2
    have h : T * (E * b) ≤ (E + T * b) ^ 2 := by
      nlinarith only [sq_nonneg E, sq_nonneg (T * b), mul_nonneg hE.le (mul_nonneg hT.le hb.le)]
    exact h.trans he
  have hF : |F| / b ^ 2 * (3 / (s * (s + T))) = 3 * |F| / (K * (K + T * b)) := by
    rw [div_mul_div_comm, hv', mul_comm |F|]
  have hG : |G| / b * (1 / (s + T)) = |G| / (K + T * b) := by
    rw [div_mul_div_comm, hv, mul_one]
  have hmono₂ := spectralListBound hA hM hc ha hb hz1 hsum (by decide)
    (by decide +kernel) spectralDom₁
  have hmono₁ := spectralListBound hA hM hc ha hb hz1 hsum (by decide)
    (by decide +kernel) spectralDom₂
  have hN : En = U * E := by change En = U * (En / U); field_simp
  have hEn : 0 < En := by rw [hN]; exact mul_pos hU hE
  have hS : Real.sqrt (U * En * b) = U * Real.sqrt (E * b) := by
    rw [hN, show U * (U * E) * b = U ^ 2 * (E * b) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hU.le]
  have hf : |F| / (E * Real.sqrt (E * b)) ≤
      5 * absSum domTerms₁ * mono z (fun _ => -(9 / 10 : ℝ)) / 2 := by
    dsimp only [F]
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * U ^ 6), mul_gPsi1_eq]
    have he : (2 * U ^ 6) * (E * Real.sqrt (E * b)) =
        spectralDen 2 U En b * 2 := by
      rw [spectralDen, hS, hN]
      norm_num only [Nat.reduceSub, pow_one]
      ring
    rw [div_div, he, ← div_div]
    exact div_le_div_of_nonneg_right
      ((div_le_div_of_nonneg_right (abs_evalTerms_le (fun j => (hz j).le) _)
        (by unfold spectralDen; positivity))
        |>.trans hmono₂) (by norm_num)
  have hg : |G| / Real.sqrt (E * b) ≤
      5 * absSum domTerms₂ * mono z (fun _ => -(9 / 10 : ℝ)) / 2 := by
    dsimp only [G]
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * U ^ 5), mul_gPsi2_eq]
    have he : (2 * U ^ 5) * Real.sqrt (E * b) = spectralDen 1 U En b * 2 := by
      simp only [spectralDen, Nat.sub_self, pow_zero, mul_one, hS]
      ring
    rw [div_div, he, ← div_div]
    exact div_le_div_of_nonneg_right
      ((div_le_div_of_nonneg_right (abs_evalTerms_le (fun j => (hz j).le) _)
        (by unfold spectralDen; positivity))
        |>.trans hmono₁) (by norm_num)
  calc
    _ ≤ Real.sqrt T * (|F| / b ^ 2 * (3 / (s * (s + T))) + |G| / b * (1 / (s + T))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_neg, abs_div, abs_of_pos (sq_pos_of_pos hb)]
        exact mul_le_mul_of_nonneg_left hd' (by positivity)
      · rw [abs_mul, abs_div, abs_of_pos hb]
        exact mul_le_mul_of_nonneg_left hr' (by positivity)
    _ = (3 * |F| / K + |G|) * (Real.sqrt T / (K + T * b)) := by
      rw [hF, hG]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ ≤ (3 * |F| / E + |G|) * (1 / Real.sqrt (E * b)) :=
      mul_le_mul (add_le_add_left (div_le_div_of_nonneg_left (by positivity) hE hK) _)
        hw (by positivity) (by positivity)
    _ = 3 * (|F| / (E * Real.sqrt (E * b))) + |G| / Real.sqrt (E * b) := by ring
    _ ≤ _ := by linarith only [hf, hg]

/-- The crossed kernel has a uniform inverse-square-root spectral bound. -/
theorem exists_abs_xExact_le :
    ∃ C : ℝ, ∀ {lam Lam T : ℝ}, 0 < lam → lam < Lam → 4 ≤ T →
      lam ^ 2 ≠ T → Lam ^ 2 ≠ T → |xExact T lam Lam| ≤ C / Real.sqrt T := by
  let W := fun y : Fin 4 → ℝ => ((15 * absSum domTerms₁ + 5 * absSum domTerms₂) / 2) *
    mono (simplexPoint y) (fun _ => -(9 / 10 : ℝ))
  have hW : IntegrableOn W (simplexSet 4) :=
    (integrableOn_prod_simplexPoint_rpow Finset.univ (by norm_num) (by norm_num)).const_mul _
  refine ⟨∫ y in simplexSet 4, 4 * W y, fun {lam Lam T} hl hreg hT haT hbT => ?_⟩
  have ht : 0 < T := by linarith
  let f := fun y => crossPFAt (lam ^ 2) (lam ^ 2) (Lam ^ 2) T (simplexPoint y) -
    crossPFAt (Lam ^ 2) (lam ^ 2) (Lam ^ 2) T (simplexPoint y)
  rw [xExact_eq_integral_crossPFAt (sq_pos_of_pos hl) (sq_pos_of_pos (hl.trans hreg)) hT]
  change |2 * ∫ y in simplexSet 4, f y| ≤ _
  apply (le_div_iff₀ (Real.sqrt_pos.2 ht)).2
  have h := norm_integral_le_of_norm_le (hW.const_mul 4)
    (f := fun y => Real.sqrt T * (2 * f y)) ?_
  · simpa only [integral_const_mul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg T), mul_comm, mul_left_comm, mul_assoc] using h
  filter_upwards [QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos
    (by decide : 0 < 4)] with y hy
  have hsum := QED.Integration.TwoLoop.sum_simplexPoint y
  have h1 := abs_crossPFAt_mul_sqrt_le hl hreg ht (sq_nonneg lam) haT hbT hy hsum
  have h2 := abs_crossPFAt_mul_sqrt_le hl hreg ht (sq_nonneg Lam) haT hbT hy hsum
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg T), abs_mul, abs_two]
  have hb := mul_le_mul_of_nonneg_left (abs_sub
    (crossPFAt (lam ^ 2) (lam ^ 2) (Lam ^ 2) T (simplexPoint y))
    (crossPFAt (Lam ^ 2) (lam ^ 2) (Lam ^ 2) T (simplexPoint y))) (Real.sqrt_nonneg T)
  change _ ≤ 4 * W y
  change Real.sqrt T * |f y| ≤ _ at hb
  rw [mul_add] at hb
  change _ ≤ W y at h1 h2
  linarith only [hb, h1, h2]

end QED.ChainProof.SetCUnitM

namespace QED.ChainProof.SetCRegDisp

open Complex Real Filter Set Topology QED.ChainProof.SetCK QED.ChainProof.SetCUnitM

/-- The two transverse crossed placements supply all three regulator-piece fields. -/
theorem isRegPieceAE_uBDT_crossed_pair (P : Params) (he : P.e ≠ 0) (hm : 0 < P.m) :
    IsRegPieceAE (fun mγ Λ T => 64 * π ^ 6 / P.e ^ 6 *
      ((1 / I) * (uBDT P 2 mγ Λ T + uBDT P 3 mγ Λ T)).re)
      (fun T => crossUnit 0 T + crossUnit T 0) where
  meas := by
    filter_upwards [eventually_regRange one_pos 1] with p hp
    let t : ℝ → ℝ := fun T => max T 4
    have ht : Continuous t := continuous_id.max continuous_const
    have ht₀ (T : ℝ) : 0 < t T := (by norm_num : 0 < (4 : ℝ)).trans_le (le_max_right _ _)
    have h (i : Fin 12) : Continuous fun T => uBDT P i p.1 p.2 (t T) :=
      continuous_iff_continuousAt.2 fun T =>
        (continuousAt_uBDT P i hm hp.1 (hp.1.trans (hp.2.1.trans hp.2.2)) (ht₀ T)).comp
          ht.continuousAt
    exact (Complex.continuous_re.measurable.comp
      (((h 2).add (h 3)).measurable.const_mul (1 / I))).const_mul _
  lim T hT := tendsto_uBDT_crossed_pair P he hm hT
  bound := by
    obtain ⟨C, hC⟩ := exists_abs_xExact_le
    refine ⟨C, 1, 1, one_pos, fun mγ Λ hγ hγ1 hΛ => ?_⟩
    have hγΛ := hγ1.trans hΛ
    filter_upwards [ae_restrict_mem measurableSet_Ici, ae_ne_heavy_spectral_mass P.m mγ,
      ae_ne_heavy_spectral_mass P.m Λ] with T hT ha hb
    have ht : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hT
    rw [uBDT_crossed_pair_eq_xExact P he hm hγ hγΛ ht ha.symm hb.symm]
    exact hC (div_pos hγ hm) (div_lt_div_of_pos_right hγΛ hm) hT ha.symm hb.symm

end QED.ChainProof.SetCRegDisp

end
