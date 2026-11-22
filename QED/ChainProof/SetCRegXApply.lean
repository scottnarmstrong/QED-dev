/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegXIntegrand
public import QED.ChainProof.SetCRegXMerge
public import QED.ChainProof.SetCUnitMDisp
public import QED.ChainProof.SetCRegXIntegral
import QED.TwoLoop.UnitXGraphReduce
import QED.ChainProof.SetCMainBKKCurve

/-!
# Apply the photon split to the crossed Pauli integrand

The trace factors stay fixed along the split from
`QED/ChainProof/SetCRegXMerge.lean`. The two endpoints correspond to
the original element mass and its replacement by the last extra mass.
On the eight-line simplex the two photon differences and the electron
midpoint give the five-parameter crossed unit. The repeated endpoints
give mass derivatives and the partial fractions combine into the same
dressed photon used by the dispersive shell kernels.
-/

@[expose] public section

open MeasureTheory
open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.UnitXGraph QED.ChainProof.SetCUnit
open QED.Integration.Feynman (simplexPoint simplexSet)
open QED.Integration.TwoLoop QED.Integration.SimplexMerge

namespace QED.ChainProof.SetCUnitM

/-- Adjacent factorial-weighted resolvents with fixed real coefficients. -/
noncomputable def factorialResolventPair (n : ℕ) (F G V : ℝ) : ℝ :=
  F * ((n + 1).factorial : ℝ) / V ^ (n + 2) - G * (n.factorial : ℝ) / V ^ (n + 1)

/-- The two resolvents combine into a single divided difference. -/
theorem integral_factorialResolventPair_split {K a b W : ℝ}
    (n : ℕ) (F G : ℝ) (hab : a ≠ b)
    (ha : 0 < K + a * W) (hb : 0 < K + b * W) :
    ∫ t in (0 : ℝ)..W, factorialResolventPair (n + 1) F G (K + a * t + b * (W - t)) =
      (factorialResolventPair n F G (K + a * W) -
        factorialResolventPair n F G (K + b * W)) / (b - a) := by
  have e (t : ℝ) : K + a * t + b * (W - t) = K + b * W + (a - b) * t := by ring
  have hEnd : 0 < K + b * W + (a - b) * W := by rwa [← e, sub_self, mul_zero, add_zero]
  have hI (j : ℕ) (f : ℝ) :
      IntervalIntegrable (fun t => f * ((j + 1).factorial : ℝ) /
        (K + a * t + b * (W - t)) ^ (j + 2)) volume 0 W := by
    simpa only [e, div_eq_mul_inv] using
      (intervalIntegrable_inv_pow_affine (j + 2) hb hEnd).const_mul
        (f * ((j + 1).factorial : ℝ))
  unfold factorialResolventPair
  rw [intervalIntegral.integral_sub (hI (n + 1) F) (hI n G),
    integral_factorial_resolvent_split (n + 1) hab ha hb,
    integral_factorial_resolvent_split n hab ha hb]
  ring

private theorem crossedResolvent_eq_pair (r : ℕ) (w : Fin 8 → ℝ) (V : ℝ) :
    crossedResolvent r w V =
      factorialResolventPair (r + 2) (xPsi1 w / xU w ^ 6 / 2) (xPsi2 w / xU w ^ 5 / 2) V := by
  unfold crossedResolvent factorialResolventPair
  ring

/-- The two crossed terms combine into a single divided difference. -/
theorem integral_crossedResolvent_split {K a b W : ℝ}
    (r : ℕ) (w : Fin 8 → ℝ) (hab : a ≠ b)
    (ha : 0 < K + a * W) (hb : 0 < K + b * W) :
    ∫ t in (0 : ℝ)..W, crossedResolvent (r + 1) w (K + a * t + b * (W - t)) =
      (crossedResolvent r w (K + a * W) - crossedResolvent r w (K + b * W)) / (b - a) := by
  simp only [crossedResolvent_eq_pair]
  exact integral_factorialResolventPair_split (r + 2) _ _ hab ha hb

variable {r : ℕ}

/-- The normalized crossed integrand before deleting the last extra line. -/
noncomputable def crossedParam (P : Params) (s : Fin 8) (a A b B : ℝ) (cs : Fin r → ℝ)
    (z : Fin (r + 8) → ℝ) : ℝ :=
  crossedResolvent r (groupExtra s z)
    (symanzikV (unitMMatrix .X s (fun _ : Fin r => 1))
      (unitMMomenta .X s (fun _ : Fin r => 1) (restMomentum P.m) (restMomentum P.m))
      (unitMMasses P.m a A b B cs) z)

private theorem unitMV0_slot (P : Params) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    (a A b B t : ℝ) (cs : Fin r → ℝ) (x : Fin (r + 7) → ℝ) :
    unitMV0 .X P s (fun _ => 1)
        (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs) x =
      unitMV0 .X P s (fun _ => 1) (unitMMasses P.m a A b B cs) x +
        simplexPoint x (mEmb r s) * (t ^ 2 - unitMasses P.m a A b B s ^ 2) := by
  have hMass :
      unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) cs =
        Function.update (unitMMasses P.m a A b B cs) (mEmb r s) t := by
    funext i
    by_cases hi : i = mEmb r s
    · subst i
      rw [Function.update_self, unitMMasses_mEmb, unitMasses_slot hs, ite_eq_left rfl]
    · rw [Function.update_of_ne hi, unitMMasses_slot hs P.m a A b B t cs i hi]
  unfold unitMV0
  rw [hMass, QED.ChainProof.SetCMainB.symanzikV_update, unitMMasses_mEmb]

private theorem ae_unitMV0_pos_X (P : Params) (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {cs : Fin r → ℝ} (hcs : ∀ j, μ₀ ≤ cs j) :
    ∀ᵐ x ∂(volume.restrict (simplexSet (r + 7))),
      0 < unitMV0 .X P s (fun _ => 1) (unitMMasses P.m a A b B cs) x := by
  have hc : Class5.X ∈ openClasses := by decide
  have hX : ExtraGe μ₀ (fun _ : Fin r => 1) cs := fun j => ⟨one_pos, le_rfl, hcs j⟩
  let C := unitMCurve hc P hm hs hμ₀ hM hX
  filter_upwards [C.ae_le_vfun] with x hx
  apply C.hc.trans_le
  simpa only [C, unitMCurve, CurveData.vfun, unitMV0, curveMomentum_zero]
    using hx 0 (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)

/-- Integrate out the last extra line when its mass differs from the element mass. -/
theorem integral_crossedParam_split (P : Params) (hm : 0 < P.m) {s : Fin 8}
    (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {cs : Fin (r + 1) → ℝ} (hcs : ∀ j, μ₀ ≤ cs j)
    (hne : unitMasses P.m a A b B s ^ 2 ≠ cs (Fin.last r) ^ 2) :
    let t := cs (Fin.last r)
    (∫ x in simplexSet (r + 8), crossedParam P s a A b B cs (simplexPoint x)) =
      ((∫ x in simplexSet (r + 7), crossedParam P s a A b B (Fin.init cs) (simplexPoint x)) -
        (∫ x in simplexSet (r + 7),
          crossedParam P s (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B)
            (Fin.init cs) (simplexPoint x))) / (t ^ 2 - unitMasses P.m a A b B s ^ 2) := by
  intro t
  have ht : μ₀ ≤ t := hcs (Fin.last r)
  have hi : ∀ j, μ₀ ≤ Fin.init cs j := fun j => hcs j.castSucc
  have hMt := massesGe_slot (s := s) hM ht
  have hI := integrableOn_crossedResolvent P hm hs hμ₀ hM hcs
  have hIa : IntegrableOn (fun x => crossedParam P s a A b B (Fin.init cs) (simplexPoint x))
      (simplexSet (r + 7)) := integrableOn_crossedResolvent P hm hs hμ₀ hM hi
  have hIb : IntegrableOn (fun x =>
      crossedParam P s (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B)
        (Fin.init cs) (simplexPoint x)) (simplexSet (r + 7)) :=
    integrableOn_crossedResolvent P hm hs hμ₀ hMt hi
  have hF : IntegrableOn (fun x => crossedParam P s a A b B cs (simplexPoint x))
      (simplexSet (r + 8)) := hI
  obtain ⟨_, e⟩ := integral_simplex_splitAt (m := r + 7) (by omega) (mEmb r s) hF
  rw [e, ← integral_sub hIa hIb, ← integral_div]
  apply integral_congr_ae
  filter_upwards [ae_unitMV0_pos_X P hm hs hμ₀ hM hi, ae_unitMV0_pos_X P hm hs hμ₀ hMt hi]
    with x ha hb
  let W := simplexPoint x (mEmb r s)
  let α := unitMasses P.m a A b B s ^ 2
  let β := t ^ 2
  let K := unitMV0 .X P s (fun _ => 1) (unitMMasses P.m a A b B (Fin.init cs)) x - α * W
  have eα : K + α * W =
      unitMV0 .X P s (fun _ => 1) (unitMMasses P.m a A b B (Fin.init cs)) x := by
    simp [K]
  have eβ : K + β * W = unitMV0 .X P s (fun _ => 1)
      (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B)
        (Fin.init cs)) x := by
    rw [unitMV0_slot P hs]
    dsimp [K, α, β, W]
    ring
  have eInt := integral_crossedResolvent_split r (groupExtra s (simplexPoint x)) hne
    (eα.symm ▸ ha) (eβ.symm ▸ hb)
  rw [eα, eβ] at eInt
  convert eInt using 1 <;> try rfl
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only [crossedParam]
  rw [groupExtra_splitAt]
  congr 1
  have eV := symanzikV_unitM_splitAt .X s (restMomentum P.m) (restMomentum P.m)
    (unitMasses P.m a A b B) cs (simplexPoint x) u
  unfold unitMMasses
  rw [eV]
  change unitMV0 .X P s (fun _ => 1) (unitMMasses P.m a A b B (Fin.init cs)) x +
      (W - u) * (β - α) = K + α * u + β * (W - u)
  rw [← eα]
  ring

/-- An equal pair contributes the width of its shared parameter group. -/
theorem integral_crossedParam_repeat (P : Params) (hm : 0 < P.m) {s : Fin 8}
    (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {cs : Fin (r + 1) → ℝ} (hcs : ∀ j, μ₀ ≤ cs j)
    (heq : cs (Fin.last r) ^ 2 = unitMasses P.m a A b B s ^ 2) :
    let g := fun x : Fin (r + 7) → ℝ => simplexPoint x (mEmb r s) *
      crossedResolvent (r + 1) (groupExtra s (simplexPoint x))
        (unitMV0 .X P s (fun _ => 1) (unitMMasses P.m a A b B (Fin.init cs)) x)
    IntegrableOn g (simplexSet (r + 7)) ∧
      (∫ x in simplexSet (r + 8), crossedParam P s a A b B cs (simplexPoint x)) =
        ∫ x in simplexSet (r + 7), g x := by
  intro g
  have hF : IntegrableOn (fun x => crossedParam P s a A b B cs (simplexPoint x))
      (simplexSet (r + 8)) := integrableOn_crossedResolvent P hm hs hμ₀ hM hcs
  obtain ⟨hI, e⟩ := integral_simplex_splitAt (m := r + 7) (by omega) (mEmb r s) hF
  have h (x : Fin (r + 7) → ℝ) :
      (∫ u in (0 : ℝ)..simplexPoint x (mEmb r s),
        crossedParam P s a A b B cs (splitAt (mEmb r s) (simplexPoint x) u)) = g x := by
    have hValue (u : ℝ) :
        crossedParam P s a A b B cs (splitAt (mEmb r s) (simplexPoint x) u) =
          crossedResolvent (r + 1) (groupExtra s (simplexPoint x))
            (unitMV0 .X P s (fun _ => 1) (unitMMasses P.m a A b B (Fin.init cs)) x) := by
      unfold crossedParam unitMMasses unitMV0
      rw [groupExtra_splitAt, symanzikV_unitM_splitAt, heq, sub_self, mul_zero, add_zero]
    simp only [g, hValue, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  simp only [h] at hI e
  exact ⟨hI, e⟩

section Base

open Set QED.ChainProof.SetCK

private theorem integral_factorialResolventPair_double
    {K a A b B Wa Wb : ℝ} (hK : 0 ≤ K) (hWa : 0 < Wa) (hWb : 0 < Wb)
    (ha : 0 < a) (hA : 0 < A) (hb : 0 < b) (hB : 0 < B)
    (haA : a ≠ A) (hbB : b ≠ B) (F G : ℝ) :
    let V := fun x y => K + x * Wa + y * Wb
    let f := factorialResolventPair 0 F G
    (∫ t in (0 : ℝ)..Wa, ∫ u in (0 : ℝ)..Wb,
      factorialResolventPair 2 F G
        ((K + a * t + A * (Wa - t)) + b * u + B * (Wb - u))) =
      ((f (V a b) - f (V a B)) - (f (V A b) - f (V A B))) / ((A - a) * (B - b)) := by
  intro V f
  let Q := fun t : ℝ => K + a * t + A * (Wa - t)
  have hV {q : ℝ} (hq : 0 < q) (t : ℝ) (ht : t ∈ uIcc 0 Wa) :
      0 < Q t + q * Wb := by
    rw [uIcc_of_le hWa.le] at ht
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (add_nonneg hK (mul_nonneg ha.le ht.1))
        (mul_nonneg hA.le (sub_nonneg.mpr ht.2))) (mul_pos hq hWb)
  have hI {q : ℝ} (hq : 0 < q) :
      IntervalIntegrable (fun t => factorialResolventPair 1 F G (Q t + q * Wb)) volume 0 Wa := by
    have hC (j : ℕ) : ContinuousOn (fun t => ((Q t + q * Wb) ^ j)⁻¹) (uIcc 0 Wa) := by
      apply ContinuousOn.inv₀
      · dsimp only [Q]
        fun_prop
      · exact fun t ht => pow_ne_zero _ (hV hq t ht).ne'
    unfold factorialResolventPair
    simp only [div_eq_mul_inv]
    apply ContinuousOn.intervalIntegrable
    exact ((hC 3).const_mul (F * ((2 : ℕ).factorial : ℝ))).sub
      ((hC 2).const_mul (G * ((1 : ℕ).factorial : ℝ)))
  have hSplit {q : ℝ} (hq : 0 < q) :
      (∫ t in (0 : ℝ)..Wa, factorialResolventPair 1 F G (Q t + q * Wb)) =
        (f (V a q) - f (V A q)) / (A - a) := by
    have hs := integral_factorialResolventPair_split (K := K + q * Wb) 0 F G haA
      (by positivity : 0 < K + q * Wb + a * Wa) (by positivity)
    dsimp only [f, V]
    calc
      _ = ∫ t in (0 : ℝ)..Wa,
          factorialResolventPair 1 F G (K + q * Wb + a * t + A * (Wa - t)) := by
        apply intervalIntegral.integral_congr
        intro t _
        change factorialResolventPair 1 F G (Q t + q * Wb) =
          factorialResolventPair 1 F G (K + q * Wb + a * t + A * (Wa - t))
        apply congrArg (factorialResolventPair 1 F G)
        dsimp only [Q]
        ring
      _ = _ := by
        rw [hs, show K + q * Wb + a * Wa = K + a * Wa + q * Wb by ring,
          show K + q * Wb + A * Wa = K + A * Wa + q * Wb by ring]
  calc
    _ = ∫ t in (0 : ℝ)..Wa,
          (factorialResolventPair 1 F G (Q t + b * Wb) -
            factorialResolventPair 1 F G (Q t + B * Wb)) / (B - b) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact integral_factorialResolventPair_split 1 F G hbB (hV hb t ht) (hV hB t ht)
    _ = _ := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hI hb) (hI hB),
        hSplit hb, hSplit hB]
      simp only [div_eq_mul_inv, mul_inv]
      ring

private theorem groupExtra_zero (s : Fin 8) (z : Fin 8 → ℝ) :
    groupExtra (r := 0) s z = z := by
  funext i
  have hi : mEmb 0 i = i := Fin.ext rfl
  simp [groupExtra, hi]

private theorem crossedParam_zero_split {P : Params} (hm : P.m = 1) (s : Fin 8)
    (a A b B : ℝ) (w : Fin 5 → ℝ) (v t u : ℝ) :
    crossedParam P s a A b B (fun j : Fin 0 => Fin.elim0 j) (crossedSplit w v t u) =
      factorialResolventPair 2
        (gPsi1 (w 0) v (w 1) (w 2) (w 3) (w 4) / gXU (w 0) (w 1) (w 2) (w 3) (w 4) ^ 6 / 2)
        (gPsi2 (w 0) v (w 1) (w 2) (w 3) (w 4) / gXU (w 0) (w 1) (w 2) (w 3) (w 4) ^ 5 / 2)
        ((gXE (w 0) (w 1) (w 2) (w 3) (w 4) + a ^ 2 * t + A ^ 2 * (w 3 - t)) +
          b ^ 2 * u + B ^ 2 * (w 4 - u)) := by
  have e := groupExtra_zero s (crossedSplit w v t u)
  unfold crossedParam unitMMasses
  rw [crossedResolvent_eq_pair, symanzikV_unitM_group, e]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change factorialResolventPair 2 _ _
    (symanzikV crossedAlpha (pvMomentaE .X (restMomentum P.m) (restMomentum P.m))
      (unitMasses P.m a A b B) (crossedSplit w v t u)) = _
  rw [symanzikV_X_unitMasses hm]
  simp only [xPsi1, xPsi2, xan, xbn, xCn, xU, gPsi1, gPsi2, crossedSplit_xA, crossedSplit_xt,
    crossedSplit_xM, crossedSplit_xc, crossedSplit_xa, crossedSplit_xb]
  change factorialResolventPair 2 _ _ (_ + t * a ^ 2 + u * b ^ 2 +
    (w 3 - t) * A ^ 2 + (w 4 - u) * B ^ 2) = _
  congr 1
  ring

private theorem crossedMerged_crossedParam_zero {P : Params} (hm : P.m = 1)
    (s : Fin 8) {a A b B : ℝ} (ha : 0 < a) (hA : 0 < A) (hb : 0 < b) (hB : 0 < B)
    (haA : a ^ 2 ≠ A ^ 2) (hbB : b ^ 2 ≠ B ^ 2) (w : Fin 5 → ℝ) (hw : ∀ i, 0 < w i) :
    crossedMerged (crossedParam P s a A b B (fun j : Fin 0 => Fin.elim0 j)) w =
      ((crossedAt (a ^ 2) (b ^ 2) w - crossedAt (a ^ 2) (B ^ 2) w) -
        (crossedAt (A ^ 2) (b ^ 2) w - crossedAt (A ^ 2) (B ^ 2) w)) /
        ((A ^ 2 - a ^ 2) * (B ^ 2 - b ^ 2)) := by
  let U := gXU (w 0) (w 1) (w 2) (w 3) (w 4)
  let K := gXE (w 0) (w 1) (w 2) (w 3) (w 4)
  let F := fun v => gPsi1 (w 0) v (w 1) (w 2) (w 3) (w 4) / U ^ 6 / 2
  let G := fun v => gPsi2 (w 0) v (w 1) (w 2) (w 3) (w 4) / U ^ 5 / 2
  let V := fun x y => K + x * w 3 + y * w 4
  let f := fun v x y => factorialResolventPair 0 (F v) (G v) (V x y)
  let D := fun v => ((f v (a ^ 2) (b ^ 2) - f v (a ^ 2) (B ^ 2)) -
    (f v (A ^ 2) (b ^ 2) - f v (A ^ 2) (B ^ 2))) / ((A ^ 2 - a ^ 2) * (B ^ 2 - b ^ 2))
  have hD (v : ℝ) :
      (∫ t in (0 : ℝ)..w 3, ∫ u in (0 : ℝ)..w 4,
        crossedParam P s a A b B (fun j : Fin 0 => Fin.elim0 j) (crossedSplit w v t u)) =
        D v := by
    simp only [crossedParam_zero_split hm]
    exact integral_factorialResolventPair_double
      (gXE_nonneg (hw 0) (hw 1) (hw 2) (hw 3) (hw 4)) (hw 3) (hw 4)
      (pow_pos ha 2) (pow_pos hA 2) (pow_pos hb 2) (pow_pos hB 2) haA hbB (F v) (G v)
  have hAt (x y : ℝ) : crossedAt x y w = w 1 * f (w 1 / 2) x y := by
    simp only [crossedAt, crossedTerm, f, V, K, F, G, U, factorialResolventPair]
    norm_num [div_eq_mul_inv, mul_inv]
    left
    ring
  unfold crossedMerged
  simp only [hD, hAt]
  rw [integral_affine_eq_mid (D 0) (D 1 - D 0)]
  · dsimp only [D]
    ring
  · intro v
    dsimp only [D, f, factorialResolventPair, F, G]
    rw [gPsi1_affine (w 0) v, gPsi2_affine (w 0) v]
    ring

/-- The eight-line crossed integral is the two independent photon divided differences
of the five-parameter crossed unit. -/
theorem integral_crossedParam_zero (P : Params) (hm : P.m = 1)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ}
    (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    (haA : a ^ 2 ≠ A ^ 2) (hbB : b ^ 2 ≠ B ^ 2) :
    (∫ x in simplexSet 7,
      crossedParam P s a A b B (fun j : Fin 0 => Fin.elim0 j) (simplexPoint x)) =
      ((crossUnit (a ^ 2) (b ^ 2) - crossUnit (a ^ 2) (B ^ 2)) -
        (crossUnit (A ^ 2) (b ^ 2) - crossUnit (A ^ 2) (B ^ 2))) /
          ((A ^ 2 - a ^ 2) * (B ^ 2 - b ^ 2)) := by
  have hmPos : 0 < P.m := by rw [hm]; exact one_pos
  have hF : IntegrableOn (fun x =>
      crossedParam P s a A b B (fun j : Fin 0 => Fin.elim0 j) (simplexPoint x)) (simplexSet 7) :=
    integrableOn_crossedResolvent P hmPos hs hμ₀ hM (fun j => Fin.elim0 j)
  obtain ⟨_, e⟩ := integral_simplex_crossedSplit hF
  obtain ⟨ha, hA, hb, hB⟩ := hM
  have haPos := hμ₀.trans_le ha
  have hAPos := hμ₀.trans_le hA
  have hbPos := hμ₀.trans_le hb
  have hBPos := hμ₀.trans_le hB
  have hI (x y : ℝ) := integrableOn_crossedAt (sq_nonneg x) (sq_nonneg y)
  have hA₁ := hI a b
  have hA₂ := hI a B
  have hB₁ := hI A b
  have hB₂ := hI A B
  simp only [crossUnit]
  have iA : IntegrableOn (fun y => crossedAt (a ^ 2) (b ^ 2) (simplexPoint y) -
      crossedAt (a ^ 2) (B ^ 2) (simplexPoint y)) (simplexSet 4) := hA₁.sub hA₂
  have iB : IntegrableOn (fun y => crossedAt (A ^ 2) (b ^ 2) (simplexPoint y) -
      crossedAt (A ^ 2) (B ^ 2) (simplexPoint y)) (simplexSet 4) := hB₁.sub hB₂
  rw [e, ← integral_sub hA₁ hA₂, ← integral_sub hB₁ hB₂,
    ← integral_sub iA iB, ← integral_div]
  apply integral_congr_ae
  filter_upwards [QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos
    (by norm_num : 0 < 4)] with y hy
  exact crossedMerged_crossedParam_zero hm s haPos hAPos hbPos hBPos haA hbB _ hy

private theorem integrableOn_crossDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    IntegrableOn (fun y => crossDerivAt a b (simplexPoint y)) (simplexSet 4) := by
  obtain ⟨C, q, hq, hq₁, hC⟩ := QED.TwoLoop.UnitXClose.crossedDom
  have hint := (integrableOn_prod_simplexPoint_rpow (m := 4) Finset.univ hq hq₁).const_mul
    (7 / b * C)
  apply hint.mono' ((measurable_crossDerivAt a b).comp
    (continuous_simplexPoint' (m := 4)).measurable).aestronglyMeasurable
  filter_upwards [QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos
    (by norm_num : 0 < 4)] with y hy
  let z := simplexPoint y
  let E := gXE (z 0) (z 1) (z 2) (z 3) (z 4)
  let V := E + a * z 3 + b * z 4
  have hE : 0 ≤ E := gXE_nonneg (hy 0) (hy 1) (hy 2) (hy 3) (hy 4)
  have hz₃ : 0 < z 3 := hy 3
  have hz₄ : 0 < z 4 := hy 4
  have hV : 0 < V := add_pos_of_nonneg_of_pos (add_nonneg hE (mul_nonneg ha hz₃.le))
    (mul_pos hb hz₄)
  let b' := b + V / z 4
  have hV' : E + a * z 3 + b' * z 4 = 2 * V := by
    dsimp only [b']
    rw [add_mul, div_mul_cancel₀ _ (hy 4).ne']
    dsimp only [V]
    ring
  have e : crossDerivAt a b z = (z 4 / V) * (-3 * crossedAt a b z + 4 * crossedAt a b' z) := by
    simp only [crossDerivAt, crossedAt_eq_inv]
    change (z 4 / V) * _ = (z 4 / V) * (-3 * (z 1 * (_ * V⁻¹ ^ 2 - _ * V⁻¹)) +
      4 * (z 1 * (_ * (E + a * z 3 + b' * z 4)⁻¹ ^ 2 - _ * (E + a * z 3 + b' * z 4)⁻¹)))
    rw [hV']
    simp only [show gXE (z 0) (z 1) (z 2) (z 3) (z 4) + a * z 3 + b * z 4 = V from rfl,
      div_eq_mul_inv, mul_inv, ← inv_pow]
    ring
  have hb' : 0 ≤ b' := add_nonneg hb.le (div_nonneg hV.le hz₄.le)
  have hD : |crossedAt a b z| ≤ C * ∏ k, z k ^ (-q) :=
    hC a b ha hb.le z hy (sum_simplexPoint y)
  have hD' : |crossedAt a b' z| ≤ C * ∏ k, z k ^ (-q) :=
    hC a b' ha hb' z hy (sum_simplexPoint y)
  have hFrac : z 4 / V ≤ 1 / b := by
    apply (div_le_div_iff₀ hV hb).2
    change z 4 * b ≤ 1 * (E + a * z 3 + b * z 4)
    nlinarith [mul_nonneg ha (hy 3).le]
  have hInner : |-3 * crossedAt a b z + 4 * crossedAt a b' z| ≤
      7 * (C * ∏ k ∈ Finset.univ, z k ^ (-q)) := by
    calc
      _ ≤ |-3 * crossedAt a b z| + |4 * crossedAt a b' z| := abs_add_le _ _
      _ ≤ _ := by
        simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
        linarith
  change ‖crossDerivAt a b z‖ ≤ _
  rw [Real.norm_eq_abs, e, abs_mul, abs_of_nonneg (div_nonneg hz₄.le hV.le)]
  exact (mul_le_mul hFrac hInner (abs_nonneg _) (by positivity)).trans_eq (by ring)

private theorem crossedMerged_crossedParam_zero_right_repeat {P : Params} (hm : P.m = 1)
    (s : Fin 8) {a A b : ℝ} (hb : 0 < b) (haA : a ^ 2 ≠ A ^ 2)
    (w : Fin 5 → ℝ) (hw : ∀ i, 0 < w i) :
    crossedMerged (crossedParam P s a A b b (fun j : Fin 0 => Fin.elim0 j)) w =
      (crossDerivAt (A ^ 2) (b ^ 2) w - crossDerivAt (a ^ 2) (b ^ 2) w) / (A ^ 2 - a ^ 2) := by
  let U := gXU (w 0) (w 1) (w 2) (w 3) (w 4)
  let E := gXE (w 0) (w 1) (w 2) (w 3) (w 4)
  let F := fun v => gPsi1 (w 0) v (w 1) (w 2) (w 3) (w 4) / U ^ 6 / 2
  let G := fun v => gPsi2 (w 0) v (w 1) (w 2) (w 3) (w 4) / U ^ 5 / 2
  let K := E + b ^ 2 * w 4
  let f := fun v x => factorialResolventPair 1 (F v) (G v) (K + x * w 3)
  let D := fun v => w 4 * (f v (a ^ 2) - f v (A ^ 2)) / (A ^ 2 - a ^ 2)
  have hK : 0 < K := add_pos_of_nonneg_of_pos
    (gXE_nonneg (hw 0) (hw 1) (hw 2) (hw 3) (hw 4)) (mul_pos (pow_pos hb 2) (hw 4))
  have hD (v : ℝ) :
      (∫ t in (0 : ℝ)..w 3, ∫ u in (0 : ℝ)..w 4,
        crossedParam P s a A b b (fun j : Fin 0 => Fin.elim0 j) (crossedSplit w v t u)) = D v := by
    simp only [crossedParam_zero_split hm]
    have ep (t u : ℝ) : (E + a ^ 2 * t + A ^ 2 * (w 3 - t)) +
        b ^ 2 * u + b ^ 2 * (w 4 - u) = K + a ^ 2 * t + A ^ 2 * (w 3 - t) := by
      unfold K
      ring
    change (∫ t in (0 : ℝ)..w 3, ∫ u in (0 : ℝ)..w 4,
        factorialResolventPair 2 (F v) (G v)
          ((E + a ^ 2 * t + A ^ 2 * (w 3 - t)) + b ^ 2 * u + b ^ 2 * (w 4 - u))) = _
    simp only [ep, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul,
      integral_factorialResolventPair_split (K := K) 1 (F v) (G v) haA
        (add_pos_of_pos_of_nonneg hK (mul_nonneg (sq_nonneg _) (hw 3).le))
        (add_pos_of_pos_of_nonneg hK (mul_nonneg (sq_nonneg _) (hw 3).le))]
    simp only [D, f]
    ring
  have hAt (x : ℝ) : crossDerivAt x (b ^ 2) w =
      -(w 1 * w 4 * f (w 1 / 2) x) := by
    have e : E + x * w 3 + b ^ 2 * w 4 = K + x * w 3 := by unfold K; ring
    unfold crossDerivAt
    change (w 4 / (E + x * w 3 + b ^ 2 * w 4)) * _ = _
    rw [e]
    simp only [f, factorialResolventPair, F, G, U]
    norm_num [div_eq_mul_inv, mul_inv, ← inv_pow]
    ring
  unfold crossedMerged
  simp only [hD, hAt]
  rw [integral_affine_eq_mid (D 0) (D 1 - D 0)]
  · dsimp only [D]
    ring
  · intro v
    dsimp only [D, f, factorialResolventPair, F, G]
    rw [gPsi1_affine (w 0) v, gPsi2_affine (w 0) v]
    ring

/-- A repeated right photon mass gives the negative squared-mass derivative
of the crossed unit, with the distinct spectator difference outside it. -/
theorem integral_crossedParam_zero_right_repeat (P : Params) (hm : P.m = 1)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ a A b : ℝ}
    (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b b) (haA : a ^ 2 ≠ A ^ 2) :
    (∫ x in simplexSet 7,
      crossedParam P s a A b b (fun j : Fin 0 => Fin.elim0 j) (simplexPoint x)) =
      (deriv (crossUnit (A ^ 2)) (b ^ 2) - deriv (crossUnit (a ^ 2)) (b ^ 2)) /
        (A ^ 2 - a ^ 2) := by
  have hmPos : 0 < P.m := by rw [hm]; exact one_pos
  have hF : IntegrableOn (fun x =>
      crossedParam P s a A b b (fun j : Fin 0 => Fin.elim0 j) (simplexPoint x)) (simplexSet 7) :=
    integrableOn_crossedResolvent P hmPos hs hμ₀ hM (fun j => Fin.elim0 j)
  obtain ⟨_, e⟩ := integral_simplex_crossedSplit hF
  have hbPos := hμ₀.trans_le hM.2.2.1
  have hb₂ := pow_pos hbPos 2
  rw [e, (hasDerivAt_crossUnit_right (sq_nonneg A) hb₂).deriv,
    (hasDerivAt_crossUnit_right (sq_nonneg a) hb₂).deriv,
    ← integral_sub (integrableOn_crossDerivAt (sq_nonneg A) hb₂)
      (integrableOn_crossDerivAt (sq_nonneg a) hb₂), ← integral_div]
  apply integral_congr_ae
  filter_upwards [QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos
    (by norm_num : 0 < 4)] with y hy
  exact crossedMerged_crossedParam_zero_right_repeat hm s hbPos haA _ hy

private theorem crossedMerged_crossedParam_zero_left_repeat {P : Params} (hm : P.m = 1)
    (s : Fin 8) {a b B : ℝ} (ha : 0 < a) (hbB : b ^ 2 ≠ B ^ 2)
    (w : Fin 5 → ℝ) (hw : ∀ i, 0 < w i) :
    crossedMerged (crossedParam P s a a b B (fun j : Fin 0 => Fin.elim0 j)) w =
      (crossDerivAt (B ^ 2) (a ^ 2) (w ∘ crossMirrorPerm) -
        crossDerivAt (b ^ 2) (a ^ 2) (w ∘ crossMirrorPerm)) / (B ^ 2 - b ^ 2) := by
  let U := gXU (w 0) (w 1) (w 2) (w 3) (w 4)
  let E := gXE (w 0) (w 1) (w 2) (w 3) (w 4)
  let F := fun v => gPsi1 (w 0) v (w 1) (w 2) (w 3) (w 4) / U ^ 6 / 2
  let G := fun v => gPsi2 (w 0) v (w 1) (w 2) (w 3) (w 4) / U ^ 5 / 2
  let K := E + a ^ 2 * w 3
  let f := fun v x => factorialResolventPair 1 (F v) (G v) (K + x * w 4)
  let D := fun v => w 3 * (f v (b ^ 2) - f v (B ^ 2)) / (B ^ 2 - b ^ 2)
  have hK : 0 < K := add_pos_of_nonneg_of_pos
    (gXE_nonneg (hw 0) (hw 1) (hw 2) (hw 3) (hw 4)) (mul_pos (pow_pos ha 2) (hw 3))
  have hD (v : ℝ) :
      (∫ t in (0 : ℝ)..w 3, ∫ u in (0 : ℝ)..w 4,
        crossedParam P s a a b B (fun j : Fin 0 => Fin.elim0 j) (crossedSplit w v t u)) = D v := by
    simp only [crossedParam_zero_split hm]
    have ep (t : ℝ) : E + a ^ 2 * t + a ^ 2 * (w 3 - t) = K := by unfold K; ring
    change (∫ t in (0 : ℝ)..w 3, ∫ u in (0 : ℝ)..w 4,
        factorialResolventPair 2 (F v) (G v)
          ((E + a ^ 2 * t + a ^ 2 * (w 3 - t)) + b ^ 2 * u + B ^ 2 * (w 4 - u))) = _
    simp only [ep]
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      integral_factorialResolventPair_split (K := K) 1 (F v) (G v) hbB
        (add_pos_of_pos_of_nonneg hK (mul_nonneg (sq_nonneg _) (hw 4).le))
        (add_pos_of_pos_of_nonneg hK (mul_nonneg (sq_nonneg _) (hw 4).le))]
    simp only [D, f]
    ring
  have hAt (x : ℝ) : crossDerivAt x (a ^ 2) (w ∘ crossMirrorPerm) =
      -(w 1 * w 3 * f (w 1 / 2) x) := by
    have e0 : crossMirrorPerm 0 = 2 := by decide
    have e1 : crossMirrorPerm 1 = 1 := by decide
    have e2 : crossMirrorPerm 2 = 0 := by decide
    have e3 : crossMirrorPerm 3 = 4 := by decide
    have e4 : crossMirrorPerm 4 = 3 := by decide
    have e : E + x * w 4 + a ^ 2 * w 3 = K + x * w 4 := by unfold K; ring
    simp only [crossDerivAt, Function.comp_apply, e0, e1, e2, e3, e4, gXU_mirror, gXE_mirror,
      gPsi1_mirror, gPsi2_mirror]
    change (w 3 / (E + x * w 4 + a ^ 2 * w 3)) * _ = _
    rw [e]
    simp only [f, factorialResolventPair, F, G, U]
    norm_num [div_eq_mul_inv, mul_inv, ← inv_pow]
    ring
  unfold crossedMerged
  simp only [hD, hAt]
  rw [integral_affine_eq_mid (D 0) (D 1 - D 0)]
  · dsimp only [D]
    ring
  · intro v
    dsimp only [D, f, factorialResolventPair, F, G]
    rw [gPsi1_affine (w 0) v, gPsi2_affine (w 0) v]
    ring

/-- A repeated left photon mass gives the squared-mass derivative in the
first slot, expressed using the crossed mirror. -/
theorem integral_crossedParam_zero_left_repeat (P : Params) (hm : P.m = 1)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ a b B : ℝ}
    (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a a b B) (hbB : b ^ 2 ≠ B ^ 2) :
    (∫ x in simplexSet 7,
      crossedParam P s a a b B (fun j : Fin 0 => Fin.elim0 j) (simplexPoint x)) =
      (deriv (crossUnit (B ^ 2)) (a ^ 2) - deriv (crossUnit (b ^ 2)) (a ^ 2)) /
        (B ^ 2 - b ^ 2) := by
  have hmPos : 0 < P.m := by rw [hm]; exact one_pos
  have hF : IntegrableOn (fun x =>
      crossedParam P s a a b B (fun j : Fin 0 => Fin.elim0 j) (simplexPoint x)) (simplexSet 7) :=
    integrableOn_crossedResolvent P hmPos hs hμ₀ hM (fun j => Fin.elim0 j)
  obtain ⟨_, e⟩ := integral_simplex_crossedSplit hF
  have ha := hμ₀.trans_le hM.1
  have ha₂ := pow_pos ha 2
  rw [e, (hasDerivAt_crossUnit_right (sq_nonneg B) ha₂).deriv,
    (hasDerivAt_crossUnit_right (sq_nonneg b) ha₂).deriv,
    ← integral_sub (integrableOn_crossDerivAt (sq_nonneg B) ha₂)
      (integrableOn_crossDerivAt (sq_nonneg b) ha₂), ← integral_div]
  let g : (Fin 5 → ℝ) → ℝ := fun w =>
    (crossDerivAt (B ^ 2) (a ^ 2) w - crossDerivAt (b ^ 2) (a ^ 2) w) / (B ^ 2 - b ^ 2)
  change _ = ∫ y in simplexSet 4, g (simplexPoint y)
  rw [← integral_simplex_comp_perm crossMirrorPerm g]
  apply integral_congr_ae
  filter_upwards [QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos
    (by norm_num : 0 < 4)] with y hy
  exact crossedMerged_crossedParam_zero_left_repeat hm s ha hbB _ hy

end Base

section DressedPhoton

open Set Filter Topology QED.ChainProof.SetCK QED.ChainProof.SetCRegBubble

/-- The crossed partial fractions before integration over the five groups. -/
noncomputable def crossPFAt (μ a b c : ℝ) (z : Fin 5 → ℝ) : ℝ :=
  bubCoefC a b c * crossedAt μ c z + bubCoefA a b c * crossedAt μ a z +
    bubCoefB a b c * crossedAt μ b z -
    bubCoefA2 a c * crossDerivAt μ a z - bubCoefB2 b c * crossDerivAt μ b z

/-- The finite-regulator crossed kernel as one integral of its pointwise
partial-fraction action. -/
theorem xExact_eq_integral_crossPFAt {lam Lam T : ℝ}
    (ha : 0 < lam ^ 2) (hb : 0 < Lam ^ 2) (hT : 4 ≤ T) :
    xExact T lam Lam =
      2 * ∫ y in simplexSet 4,
        crossPFAt (lam ^ 2) (lam ^ 2) (Lam ^ 2) T (simplexPoint y) -
          crossPFAt (Lam ^ 2) (lam ^ 2) (Lam ^ 2) T (simplexPoint y) := by
  have h (μ : ℝ) (hμ : 0 ≤ μ) :
      IntegrableOn (fun y => crossPFAt μ (lam ^ 2) (Lam ^ 2) T (simplexPoint y))
        (simplexSet 4) ∧
      crossPF μ (lam ^ 2) (Lam ^ 2) T =
        ∫ y in simplexSet 4, crossPFAt μ (lam ^ 2) (Lam ^ 2) T (simplexPoint y) := by
    let fC := fun y => bubCoefC (lam ^ 2) (Lam ^ 2) T * crossedAt μ T (simplexPoint y)
    let fA := fun y => bubCoefA (lam ^ 2) (Lam ^ 2) T * crossedAt μ (lam ^ 2) (simplexPoint y)
    let fB := fun y => bubCoefB (lam ^ 2) (Lam ^ 2) T * crossedAt μ (Lam ^ 2) (simplexPoint y)
    let fD := fun y => bubCoefA2 (lam ^ 2) T * crossDerivAt μ (lam ^ 2) (simplexPoint y)
    let fE := fun y => bubCoefB2 (Lam ^ 2) T * crossDerivAt μ (Lam ^ 2) (simplexPoint y)
    have hC : IntegrableOn fC (simplexSet 4) :=
      (integrableOn_crossedAt hμ (show 0 ≤ T by linarith)).const_mul _
    have hA : IntegrableOn fA (simplexSet 4) := (integrableOn_crossedAt hμ ha.le).const_mul _
    have hB : IntegrableOn fB (simplexSet 4) := (integrableOn_crossedAt hμ hb.le).const_mul _
    have hD : IntegrableOn fD (simplexSet 4) := (integrableOn_crossDerivAt hμ ha).const_mul _
    have hE : IntegrableOn fE (simplexSet 4) := (integrableOn_crossDerivAt hμ hb).const_mul _
    refine ⟨(((hC.add hA).add hB).sub hD).sub hE, ?_⟩
    rw [crossPF, (hasDerivAt_crossUnit_right hμ ha).deriv, (hasDerivAt_crossUnit_right hμ hb).deriv]
    simp only [crossUnit, ← integral_const_mul]
    change (∫ y in simplexSet 4, fC y) + (∫ y in simplexSet 4, fA y) +
        (∫ y in simplexSet 4, fB y) - (∫ y in simplexSet 4, fD y) -
        (∫ y in simplexSet 4, fE y) =
      ∫ y in simplexSet 4, (((fC + fA) + fB) - fD) y - fE y
    rw [integral_sub (((hC.add hA).add hB).sub hD) hE]
    simp only [Pi.sub_apply]
    rw [integral_sub ((hC.add hA).add hB) hD]
    simp only [Pi.add_apply]
    have hCA : IntegrableOn (fun y => fC y + fA y) (simplexSet 4) := hC.add hA
    rw [integral_add hCA hB, integral_add hC hA]
  obtain ⟨hI₁, e₁⟩ := h (lam ^ 2) ha.le
  obtain ⟨hI₂, e₂⟩ := h (Lam ^ 2) hb.le
  rw [xExact, e₁, e₂, integral_sub hI₁ hI₂]

/-- The dressed photon as a rational function of a positive argument.
The parameters are squared masses. -/
noncomputable def crossedDressedPhoton (a b c s : ℝ) : ℝ :=
  s ^ 2 * (1 / (s + a) - 1 / (s + b)) ^ 2 / (s + c)

/-- In electron-mass units this rational function is the dressed photon
used in the dispersive shell kernels. -/
theorem crossedDressedPhoton_eq_vpPhotonT (lam Lam T : ℝ) :
    crossedDressedPhoton (lam ^ 2) (Lam ^ 2) T =
      QED.ChainProof.SetCRegDisp.vpPhotonT 1 lam Lam T := by
  funext s
  simp only [crossedDressedPhoton, QED.ChainProof.SetCRegDisp.vpPhotonT,
    QED.TwoLoop.UnitVPLink.photonD, one_pow, mul_one]
  ring

private theorem deriv_crossedDressedPhoton {a b c s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 < s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    deriv (crossedDressedPhoton a b c) s =
      -(bubCoefC a b c / (s + c) ^ 2) - bubCoefA a b c / (s + a) ^ 2 -
        bubCoefB a b c / (s + b) ^ 2 - 2 * bubCoefA2 a c / (s + a) ^ 3 -
        2 * bubCoefB2 b c / (s + b) ^ 3 := by
  have lin (d : ℝ) : HasDerivAt (fun q => q + d) 1 s := (hasDerivAt_id s).add_const d
  have pole (k : ℝ) {d : ℝ} (hd : 0 ≤ d) :
      HasDerivAt (fun q => k / (q + d)) (-(k / (s + d) ^ 2)) s := by
    have hp := (hasDerivAt_const s k).div (lin d) (add_pos_of_pos_of_nonneg hs hd).ne'
    convert hp using 1
    simp only [zero_mul, mul_one, zero_sub, neg_div]
  have double (k : ℝ) {d : ℝ} (hd : 0 ≤ d) :
      HasDerivAt (fun q => k / (q + d) ^ 2) (-(2 * k / (s + d) ^ 3)) s := by
    have hne := (add_pos_of_pos_of_nonneg hs hd).ne'
    have hp := (hasDerivAt_const s k).div ((lin d).pow 2) (pow_ne_zero 2 hne)
    convert hp using 1
    simp only [Pi.pow_apply, zero_mul, zero_sub, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    field_simp [hne]
  have h := ((((pole (bubCoefC a b c) hc).add (pole (bubCoefA a b c) ha)).add
    (pole (bubCoefB a b c) hb)).add (double (bubCoefA2 a c) ha)).add
      (double (bubCoefB2 b c) hb)
  have he : crossedDressedPhoton a b c =ᶠ[𝓝 s] (fun q =>
      bubCoefC a b c / (q + c) + bubCoefA a b c / (q + a) + bubCoefB a b c / (q + b) +
        bubCoefA2 a c / (q + a) ^ 2 + bubCoefB2 b c / (q + b) ^ 2) := by
    filter_upwards [Ioi_mem_nhds hs] with q hq
    exact bubble_partialFractions hab hac hbc (add_pos_of_pos_of_nonneg hq ha).ne'
      (add_pos_of_pos_of_nonneg hq hb).ne' (add_pos_of_pos_of_nonneg hq hc).ne'
  rw [(h.congr_of_eventuallyEq he).deriv]
  ring

/-- At an interior simplex point the partial fractions combine into the
dressed photon and its derivative at a positive argument. -/
theorem crossPFAt_eq_dressedPhoton {μ a b c : ℝ}
    (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {z : Fin 5 → ℝ} (hz : ∀ i, 0 < z i) :
    let U := gXU (z 0) (z 1) (z 2) (z 3) (z 4)
    let K := gXE (z 0) (z 1) (z 2) (z 3) (z 4) + μ * z 3
    let F := z 1 * gPsi1 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4) / (2 * U ^ 6)
    let G := z 1 * gPsi2 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4) / (2 * U ^ 5)
    crossPFAt μ a b c z =
      -(F / z 4 ^ 2) * deriv (crossedDressedPhoton a b c) (K / z 4) -
        (G / z 4) * crossedDressedPhoton a b c (K / z 4) := by
  intro U K F G
  let s := K / z 4
  have hK : 0 < K := add_pos_of_pos_of_nonneg
    (gXE_pos (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)) (mul_nonneg hμ (hz 3).le)
  have hs : 0 < s := div_pos hK (hz 4)
  have hv (t : ℝ) : K + t * z 4 = z 4 * (s + t) := by
    dsimp only [s]
    rw [mul_add, mul_comm (z 4) (K / z 4), div_mul_cancel₀ _ (hz 4).ne', mul_comm (z 4) t]
  have hA (t : ℝ) : crossedAt μ t z =
      F / (z 4 ^ 2 * (s + t) ^ 2) - G / (z 4 * (s + t)) := by
    unfold crossedAt crossedTerm
    change z 1 * (_ / (2 * U ^ 6 * (K + t * z 4) ^ 2) -
      _ / (2 * U ^ 5 * (K + t * z 4))) = _
    rw [hv t]
    simp only [F, G, mul_pow, div_eq_mul_inv, mul_inv, ← inv_pow]
    ring
  have hD (t : ℝ) : crossDerivAt μ t z =
      -(2 * F / (z 4 ^ 2 * (s + t) ^ 3)) + G / (z 4 * (s + t) ^ 2) := by
    unfold crossDerivAt
    change (z 4 / (K + t * z 4)) * (-2 * (F / (K + t * z 4) ^ 2) +
      G / (K + t * z 4)) = _
    rw [hv t]
    have he : z 4 / (z 4 * (s + t)) = (s + t)⁻¹ := by
      rw [div_eq_mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ (hz 4).ne', one_mul]
    rw [he]
    simp only [mul_pow, div_eq_mul_inv, mul_inv, ← inv_pow]
    ring
  change _ = -(F / z 4 ^ 2) * deriv (crossedDressedPhoton a b c) s -
    (G / z 4) * crossedDressedPhoton a b c s
  rw [deriv_crossedDressedPhoton ha hb hc hs hab hac hbc]
  have hR : crossedDressedPhoton a b c s = _ :=
    bubble_partialFractions hab hac hbc (add_pos_of_pos_of_nonneg hs ha).ne'
      (add_pos_of_pos_of_nonneg hs hb).ne' (add_pos_of_pos_of_nonneg hs hc).ne'
  rw [hR]
  simp only [crossPFAt, hA, hD, div_eq_mul_inv, mul_inv, ← inv_pow]
  ring

end DressedPhoton

end QED.ChainProof.SetCUnitM

end
