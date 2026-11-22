/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegXGeom
public import QED.Integration.SimplexMerge
public import QED.ChainProof.SetCRegXSplit
public import QED.TwoLoop.UnitXGraphReduceV

/-!
# A photon parameter split in the extended crossed unit

Split the parameter of the repeated photon, placing the complementary part
in the last extra coordinate. The grouped parameters are independent of the
split and the second Symanzik function changes by an affine mass term.
-/

public section

open MeasureTheory

namespace QED.ChainProof.SetCUnitM

open QED.Integration.Feynman (simplexPoint simplexSet)
open QED.ChainProof.SetCRegX QED.ChainProof.SetCUnit
open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.UnitXGraph QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.Integration.TwoLoop QED.Integration.SimplexMerge

variable {r : ℕ}

private theorem mEmb_castSucc (i : Fin 8) :
    (mEmb r i).castSucc = mEmb (r + 1) i := Fin.ext rfl

private theorem mExtra_castSucc (j : Fin r) :
    (mExtra r j).castSucc = mExtra (r + 1) j.castSucc := Fin.ext rfl

private theorem mExtra_last : mExtra (r + 1) (Fin.last r) = Fin.last (r + 8) := Fin.ext rfl

private theorem mExtra_ne_mEmb (j : Fin r) (s : Fin 8) : mExtra r j ≠ mEmb r s := by
  intro h
  have : (mExtra r j).val = (mEmb r s).val := congrArg Fin.val h
  have hs : (s : ℕ) < 8 := s.isLt
  change (j : ℕ) + 8 = (s : ℕ) at this
  omega

private theorem splitAt_extra (s : Fin 8) (z : Fin (r + 8) → ℝ) (t : ℝ) (j : Fin r) :
    splitAt (mEmb r s) z t (mExtra (r + 1) j.castSucc) = z (mExtra r j) := by
  rw [← mExtra_castSucc, splitAt_castSucc, Function.update_of_ne (mExtra_ne_mEmb j s)]

/-- The photon split leaves every grouped parameter unchanged. -/
theorem groupExtra_splitAt (s : Fin 8) (z : Fin (r + 8) → ℝ) (t : ℝ) :
    groupExtra s (splitAt (mEmb r s) z t) = groupExtra s z := by
  funext i
  unfold groupExtra
  rw [← mEmb_castSucc, splitAt_castSucc, Fin.sum_univ_castSucc, mExtra_last, splitAt_last]
  simp only [splitAt_extra]
  by_cases h : i = s
  · subst i
    rw [Function.update_self, ite_eq_left rfl, ite_eq_left rfl]
    ring
  · rw [Function.update_of_ne ((mEmb r).injective.ne h), ite_eq_right h, ite_eq_right h]

/-- The second Symanzik function acquires the complementary split weight times
the difference of squared masses. -/
theorem symanzikV_unitM_splitAt (c : Class5) (s : Fin 8) (p p' : Fin 4 → ℝ)
    (M : Fin 8 → ℝ) (cs : Fin (r + 1) → ℝ) (z : Fin (r + 8) → ℝ) (t : ℝ) :
    symanzikV (unitMMatrix c s (fun _ : Fin (r + 1) => 1))
      (unitMMomenta c s (fun _ : Fin (r + 1) => 1) p p') (mExt M cs)
      (splitAt (mEmb r s) z t) =
    symanzikV (unitMMatrix c s (fun _ : Fin r => 1))
      (unitMMomenta c s (fun _ : Fin r => 1) p p') (mExt M (Fin.init cs)) z +
      (z (mEmb r s) - t) * (cs (Fin.last r) ^ 2 - M s ^ 2) := by
  rw [symanzikV_unitM_group, symanzikV_unitM_group, groupExtra_splitAt,
    Fin.sum_univ_castSucc, mExtra_last, splitAt_last, add_assoc]
  simp only [splitAt_extra, Fin.init]

/-- On the crossed shell, the four photon squared masses enter `V` diagonally
with their own weights. The massless part depends only on the five group sums. -/
theorem symanzikV_X_unitMasses {P : Params} (hm : P.m = 1)
    (a A b B : ℝ) (z : Fin 8 → ℝ) :
    symanzikV crossedAlpha (pvMomentaE .X (restMomentum P.m) (restMomentum P.m))
      (unitMasses P.m a A b B) z =
    gXE (xA z) (xM z) (xc z) (xa z) (xb z) +
      z 4 * a ^ 2 + z 5 * b ^ 2 + z 6 * A ^ 2 + z 7 * B ^ 2 := by
  let P' := { P with mγ := 0, Λ := 0 }
  have h := symanzikV_crossed P' hm z
  have h' :
      symanzikV crossedAlpha (pvMomentaE .X (restMomentum P.m) (restMomentum P.m))
        (pvMasses P') z =
      gXE (xA z) (xM z) (xc z) (xa z) (xb z) := by
    simpa [crossedV, P'] using h
  rw [← h']
  unfold symanzikV
  simp [pvMasses, unitMasses, P', classPVMasses, Fin.sum_univ_succ]
  ring

/-- Lowering a factorial-weighted resolvent across one split gives the divided
difference with the same factorial convention in the lower dimension. -/
theorem integral_factorial_resolvent_split {K a b w : ℝ} (n : ℕ) (hab : a ≠ b)
    (ha : 0 < K + a * w) (hb : 0 < K + b * w) (F : ℝ) :
    ∫ t in (0 : ℝ)..w, (F * ((n + 1).factorial : ℝ)) /
        (K + a * t + b * (w - t)) ^ (n + 2) =
      (F * (n.factorial : ℝ) / (K + a * w) ^ (n + 1) -
        F * (n.factorial : ℝ) / (K + b * w) ^ (n + 1)) / (b - a) := by
  simp only [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_mass_split n hab ha hb, Nat.factorial_succ]
  push_cast
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hab' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  simp only [div_eq_mul_inv, mul_inv]
  field_simp [hn, hab']

/-- An equal-mass split produces the negative derivative of the lower
resolvent in its squared mass. -/
theorem hasDerivAt_factorial_resolvent_repeat {K a w : ℝ} (n : ℕ) (ha : 0 < K + a * w)
    (F : ℝ) :
    HasDerivAt (fun m => F * (n.factorial : ℝ) / (K + m * w) ^ (n + 1))
      (-(∫ t in (0 : ℝ)..w, F * ((n + 1).factorial : ℝ) /
        (K + a * t + a * (w - t)) ^ (n + 2))) a := by
  have h : HasDerivAt (fun m => K + m * w) w a := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id a).mul_const w).const_add K
  have H := (hasDerivAt_const a (F * (n.factorial : ℝ))).div (h.pow (n + 1))
    (pow_ne_zero _ ha.ne')
  convert H using 1
  simp only [div_eq_mul_inv] at *
  rw [intervalIntegral.integral_const_mul, integral_mass_split_repeat, Nat.factorial_succ]
  push_cast
  simp only [Pi.pow_apply, zero_mul, zero_sub]
  set D := K + a * w
  have hD : D ≠ 0 := ha.ne'
  rw [show n + 2 = n + 1 + 1 by rfl, pow_succ D (n + 1), pow_succ D n]
  have hq : D ^ n ≠ 0 := pow_ne_zero _ hD
  generalize D ^ n = q at hq ⊢
  field_simp [hD, hq]

/-- Integrate one photon split on the simplex when the integrand has the
factorial-weighted affine resolvent form along the split. -/
theorem integral_simplex_factorial_resolvent_split {m : ℕ} (hm : 0 < m) (i : Fin (m + 1))
    (n : ℕ) {a b : ℝ} (hab : a ≠ b) (F K : (Fin (m + 1) → ℝ) → ℝ)
    (f : (Fin (m + 2) → ℝ) → ℝ)
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet (m + 1)))
    (hF : ∀ w t, f (splitAt i w t) =
      F w * ((n + 1).factorial : ℝ) / (K w + a * t + b * (w i - t)) ^ (n + 2))
    (hV : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      0 < K (simplexPoint x) + a * simplexPoint x i ∧
      0 < K (simplexPoint x) + b * simplexPoint x i) :
    let g := fun w : Fin (m + 1) → ℝ =>
      (F w * (n.factorial : ℝ) / (K w + a * w i) ^ (n + 1) -
        F w * (n.factorial : ℝ) / (K w + b * w i) ^ (n + 1)) / (b - a)
    IntegrableOn (fun x => g (simplexPoint x)) (simplexSet m) ∧
      ∫ x in simplexSet (m + 1), f (simplexPoint x) =
        ∫ x in simplexSet m, g (simplexPoint x) := by
  intro g
  obtain ⟨hint, heq⟩ := integral_simplex_splitAt hm i hf
  have hpoint : (fun x : Fin m → ℝ => ∫ t in (0 : ℝ)..simplexPoint x i,
      f (splitAt i (simplexPoint x) t)) =ᵐ[volume.restrict (simplexSet m)]
        (fun x => g (simplexPoint x)) := by
    filter_upwards [hV] with x hx
    simp only [hF]
    exact integral_factorial_resolvent_split n hab hx.1 hx.2 _
  exact ⟨hint.congr hpoint, heq.trans (integral_congr_ae hpoint)⟩

/-- Integrate the simplex split at a repeated mass. The new integrand is the
negative of the lower resolvent's pointwise squared-mass derivative. -/
theorem integral_simplex_factorial_resolvent_repeat {m : ℕ} (hm : 0 < m) (i : Fin (m + 1))
    (n : ℕ) (a : ℝ) (F K : (Fin (m + 1) → ℝ) → ℝ)
    (f : (Fin (m + 2) → ℝ) → ℝ)
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet (m + 1)))
    (hF : ∀ w t, f (splitAt i w t) =
      F w * ((n + 1).factorial : ℝ) / (K w + a * t + a * (w i - t)) ^ (n + 2))
    (hV : ∀ᵐ x ∂(volume.restrict (simplexSet m)), 0 < K (simplexPoint x) + a * simplexPoint x i) :
    let g := fun w : Fin (m + 1) → ℝ =>
      -deriv (fun q => F w * (n.factorial : ℝ) / (K w + q * w i) ^ (n + 1)) a
    IntegrableOn (fun x => g (simplexPoint x)) (simplexSet m) ∧
      ∫ x in simplexSet (m + 1), f (simplexPoint x) =
        ∫ x in simplexSet m, g (simplexPoint x) := by
  intro g
  obtain ⟨hint, heq⟩ := integral_simplex_splitAt hm i hf
  have hpoint : (fun x : Fin m → ℝ => ∫ t in (0 : ℝ)..simplexPoint x i,
      f (splitAt i (simplexPoint x) t)) =ᵐ[volume.restrict (simplexSet m)]
        (fun x => g (simplexPoint x)) := by
    filter_upwards [hV] with x hx
    simp only [hF, g, (hasDerivAt_factorial_resolvent_repeat n hx _).deriv, neg_neg]
  exact ⟨hint.congr hpoint, heq.trans (integral_congr_ae hpoint)⟩

end QED.ChainProof.SetCUnitM

end
