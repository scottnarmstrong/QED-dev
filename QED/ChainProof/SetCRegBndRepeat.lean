/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegBndSplit
public import QED.ChainProof.SetCRegXPartialFractions
public import QED.ChainProof.SetCRegBndParam
public import QED.ChainProof.SetCRegBndMain
import QED.ChainProof.SetCMainBKKCurve
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Divided differences with a repeated photon mass

After removing a repeated extra line by
`QED/ChainProof/SetCRegBndSplit.lean`, splitting the remaining distinct line
integrates the original slot width against the higher resolvents.
-/

@[expose] public section

open MeasureTheory Set
open QED.Integration.SimplexMerge

namespace QED.ChainProof.SetCUnitM

private theorem hasDerivAt_factorialResolventPair
    (n : ℕ) (F G : ℝ) {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (factorialResolventPair n F G) (-factorialResolventPair (n + 1) F G v) v := by
  unfold factorialResolventPair
  simp only [div_eq_mul_inv]
  have h₁ := ((((hasDerivAt_id v).pow (n + 2)).inv (pow_ne_zero _ hv)).const_mul
    (F * ((n + 1).factorial : ℝ)))
  have h₂ := ((((hasDerivAt_id v).pow (n + 1)).inv (pow_ne_zero _ hv)).const_mul
    (G * (n.factorial : ℝ)))
  refine (h₁.sub h₂).congr_deriv ?_
  simp only [Pi.pow_apply, id_eq, mul_one, Nat.add_sub_cancel, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    show n + 2 - 1 = n + 1 by omega]
  simp only [show n + 2 = n + 1 + 1 by omega, show n + 3 = n + 1 + 1 + 1 by omega, pow_succ]
  field_simp
  ring

/-- The split after a repeat in the original slot retains its endpoint width. -/
theorem integral_mul_factorialResolventPair_split {K a b W : ℝ}
    (n : ℕ) (F G : ℝ) (hab : a ≠ b)
    (ha : 0 < K + a * W) (hb : 0 < K + b * W) :
    (∫ t in (0 : ℝ)..W,
      t * factorialResolventPair (n + 2) F G (K + a * t + b * (W - t))) =
      (W * factorialResolventPair (n + 1) F G (K + a * W) -
        (factorialResolventPair n F G (K + a * W) -
          factorialResolventPair n F G (K + b * W)) / (b - a)) / (b - a) := by
  let V := fun t => K + a * t + b * (W - t)
  let q := fun t => factorialResolventPair (n + 1) F G (V t)
  let q' := fun t => factorialResolventPair (n + 2) F G (V t)
  have e (t : ℝ) : V t = K + b * W + (a - b) * t := by dsimp [V]; ring
  have eW : V W = K + a * W := by dsimp [V]; ring
  have hEnd : 0 < K + b * W + (a - b) * W := by rwa [← e, eW]
  have hpos (t : ℝ) (ht : t ∈ uIcc 0 W) : 0 < V t := by
    rw [e]
    exact pos_of_mem_uIcc_affine hb hEnd ht
  have hcont (j : ℕ) : ContinuousOn (fun t => factorialResolventPair j F G (V t))
      (uIcc 0 W) := by
    unfold factorialResolventPair
    have hV : Continuous V := by dsimp [V]; fun_prop
    exact (continuousOn_const.div (hV.pow _).continuousOn
      (fun t ht => pow_ne_zero _ (hpos t ht).ne')).sub
      (continuousOn_const.div (hV.pow _).continuousOn
        (fun t ht => pow_ne_zero _ (hpos t ht).ne'))
  have hd (t : ℝ) (ht : t ∈ Ioo (min 0 W) (max 0 W)) :
      HasDerivAt q ((b - a) * q' t) t := by
    have hV : HasDerivAt V (a - b) t := by
      have hEq : V = fun y => K + b * W + (a - b) * y := funext e
      rw [hEq]
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id t).const_mul (a - b)).const_add (K + b * W))
    have h := (hasDerivAt_factorialResolventPair (n + 1) F G
      (hpos t ⟨ht.1.le, ht.2.le⟩).ne').comp t hV
    refine h.congr_deriv ?_
    dsimp only [q']
    ring
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := id) (u' := fun _ => 1) continuous_id.continuousOn (hcont (n + 1))
    (fun t _ => hasDerivAt_id t) hd (continuous_const.intervalIntegrable 0 W)
    ((hcont (n + 2)).const_mul (b - a)).intervalIntegrable
  simp only [id_eq, zero_mul, sub_zero, one_mul] at hparts
  have hrewrite (t : ℝ) : t * ((b - a) * q' t) = (b - a) * (t * q' t) := by ring
  simp_rw [hrewrite, intervalIntegral.integral_const_mul] at hparts
  have hsplit := integral_factorialResolventPair_split (K := K) n F G hab ha hb
  change (∫ t in (0 : ℝ)..W, q t) = _ at hsplit
  rw [hsplit, eW] at hparts
  exact (eq_div_iff (sub_ne_zero.mpr hab.symm)).2 (by
    rw [mul_comm]
    exact hparts)


open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.ChainProof.SetCUnit
open QED.Integration.Feynman (simplexPoint simplexSet)
open QED.Integration.TwoLoop

/-- Grouped resolvents with one repeated original mass after its line has been removed. -/
noncomputable def groupedParamRepeat {r : ℕ} (c : Class5) (P : Params) (s : Fin 8)
    (F G : (Fin 8 → ℝ) → ℝ) (a A b B : ℝ) (cs : Fin r → ℝ) (z : Fin (r + 8) → ℝ) : ℝ :=
  z (mEmb r s) * factorialResolventPair (r + 3) (F (groupExtra s z)) (G (groupExtra s z))
    (symanzikV (unitMMatrix c s (fun _ : Fin r => 1))
      (unitMMomenta c s (fun _ : Fin r => 1) (restMomentum P.m) (restMomentum P.m))
      (unitMMasses P.m a A b B cs) z)

/-- The second removal after a repeat gives a weighted endpoint and an ordinary split.
The weighted endpoint is integrable as a consequence of the split. -/
theorem integral_groupedParamRepeat_split {r : ℕ} {c : Class5} (hc : c ∈ openClasses)
    (P : Params) (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    (F G : (Fin 8 → ℝ) → ℝ) {cs : Fin (r + 1) → ℝ} (hcs : ∀ j, μ₀ ≤ cs j)
    (hI : IntegrableOn (fun x => groupedParamRepeat c P s F G a A b B cs (simplexPoint x))
      (simplexSet (r + 8)))
    (hIa : IntegrableOn (fun x =>
      groupedParam c P s F G a A b B (Fin.init cs) (simplexPoint x)) (simplexSet (r + 7)))
    (hIb : IntegrableOn (fun x =>
      groupedParam c P s F G (slotMa s (cs (Fin.last r)) a) (slotMA s (cs (Fin.last r)) A)
        (slotMb s (cs (Fin.last r)) b) (slotMB s (cs (Fin.last r)) B)
        (Fin.init cs) (simplexPoint x)) (simplexSet (r + 7)))
    (hne : unitMasses P.m a A b B s ^ 2 ≠ cs (Fin.last r) ^ 2) :
    let d := cs (Fin.last r) ^ 2 - unitMasses P.m a A b B s ^ 2
    let f := fun x => groupedParamRepeat c P s F G a A b B (Fin.init cs) (simplexPoint x)
    let g := fun x => groupedParam c P s F G a A b B (Fin.init cs) (simplexPoint x)
    let h := fun x => groupedParam c P s F G
      (slotMa s (cs (Fin.last r)) a) (slotMA s (cs (Fin.last r)) A)
      (slotMb s (cs (Fin.last r)) b) (slotMB s (cs (Fin.last r)) B)
      (Fin.init cs) (simplexPoint x)
    IntegrableOn f (simplexSet (r + 7)) ∧
      (∫ x in simplexSet (r + 8), groupedParamRepeat c P s F G a A b B cs (simplexPoint x)) =
        ((∫ x in simplexSet (r + 7), f x) -
          ((∫ x in simplexSet (r + 7), g x) - (∫ x in simplexSet (r + 7), h x)) / d) / d := by
  intro d f g h
  let t := cs (Fin.last r)
  have ht : μ₀ ≤ t := hcs (Fin.last r)
  have hi : ∀ j, μ₀ ≤ Fin.init cs j := fun j => hcs j.castSucc
  have hMt := massesGe_slot (s := s) hM ht
  have aePos {a A b B : ℝ} (hM : MassesGe μ₀ a A b B) :
      ∀ᵐ x ∂(volume.restrict (simplexSet (r + 7))),
        0 < unitMV0 c P s (fun _ => 1) (unitMMasses P.m a A b B (Fin.init cs)) x := by
    have hX : ExtraGe μ₀ (fun _ : Fin r => 1) (Fin.init cs) :=
      fun j => ⟨one_pos, le_rfl, hi j⟩
    let C := unitMCurve hc P hm hs hμ₀ hM hX
    filter_upwards [C.ae_le_vfun] with x hx
    apply C.hc.trans_le
    simpa only [C, unitMCurve, CurveData.vfun, unitMV0, curveMomentum_zero]
      using hx 0 (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1)
  have eMass :
      unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B) (Fin.init cs) =
        Function.update (unitMMasses P.m a A b B (Fin.init cs)) (mEmb r s) t := by
    funext i
    by_cases hi' : i = mEmb r s
    · subst i
      rw [Function.update_self, unitMMasses_mEmb, unitMasses_slot hs, ite_eq_left rfl]
    · rw [Function.update_of_ne hi', unitMMasses_slot hs P.m a A b B t (Fin.init cs) i hi']
  let inner := fun x : Fin (r + 7) → ℝ => ∫ u in (0 : ℝ)..simplexPoint x (mEmb r s),
    groupedParamRepeat c P s F G a A b B cs (splitAt (mEmb r s) (simplexPoint x) u)
  obtain ⟨hinner, eqInt⟩ := integral_simplex_splitAt (m := r + 7) (by omega) (mEmb r s) hI
  change IntegrableOn inner _ at hinner
  change _ = ∫ x in simplexSet (r + 7), inner x at eqInt
  have eqInner : inner =ᵐ[volume.restrict (simplexSet (r + 7))] fun x =>
      (f x - (g x - h x) / d) / d := by
    filter_upwards [aePos hM, aePos hMt] with x ha hb
    let W := simplexPoint x (mEmb r s)
    let α := unitMasses P.m a A b B s ^ 2
    let β := t ^ 2
    let V := unitMV0 c P s (fun _ => 1) (unitMMasses P.m a A b B (Fin.init cs)) x
    let K := V - α * W
    have eα : K + α * W = V := by simp [K]
    have eβ : K + β * W = unitMV0 c P s (fun _ => 1)
        (unitMMasses P.m (slotMa s t a) (slotMA s t A) (slotMb s t b) (slotMB s t B)
          (Fin.init cs)) x := by
      unfold unitMV0
      rw [eMass, QED.ChainProof.SetCMainB.symanzikV_update, unitMMasses_mEmb]
      change K + β * W = V + W * (β - α)
      dsimp only [K]
      ring
    let w := groupExtra s (simplexPoint x)
    have eVal (u : ℝ) :
        groupedParamRepeat c P s F G a A b B cs (splitAt (mEmb r s) (simplexPoint x) u) =
          u * factorialResolventPair (r + 2 + 2) (F w) (G w)
            (K + α * u + β * (W - u)) := by
      have es : (mEmb r s).castSucc = mEmb (r + 1) s := Fin.ext rfl
      unfold groupedParamRepeat unitMMasses
      rw [groupExtra_splitAt, ← es, splitAt_castSucc, Function.update_self,
        symanzikV_unitM_splitAt]
      congr 2
      change V + (W - u) * (β - α) = K + α * u + β * (W - u)
      dsimp only [K]
      ring
    dsimp only [inner]
    simp_rw [eVal]
    rw [integral_mul_factorialResolventPair_split (r + 2) (F w) (G w) hne
      (eα.symm ▸ ha) (eβ.symm ▸ hb), eα, eβ]
    rfl
  have hdiff : IntegrableOn (fun x => (g x - h x) / d) (simplexSet (r + 7)) :=
    (hIa.sub hIb).div_const d
  have hd : d ≠ 0 := sub_ne_zero.mpr hne.symm
  have eqF : f =ᵐ[volume.restrict (simplexSet (r + 7))]
      fun x => d * inner x + (g x - h x) / d := by
    filter_upwards [eqInner] with x hx
    rw [hx]
    field_simp
    ring
  have hf : IntegrableOn f (simplexSet (r + 7)) :=
    ((hinner.const_mul d).add hdiff).congr eqF.symm
  refine ⟨hf, ?_⟩
  rw [eqInt, integral_congr_ae eqInner, integral_div, integral_sub hf hdiff,
    integral_div, integral_sub hIa hIb]


/-- The four reduced numerator-cancellation terms on the eight-line simplex. -/
noncomputable def groupedParamFourTerms (c : Class5) (P : Params) (s : Fin 8)
    (F G : (Fin 8 → ℝ) → ℝ) (a A b B p q M : ℝ) : ℝ :=
    let mass := fun t => (slotMa s t a, slotMA s t A, slotMb s t b, slotMB s t B)
    let I := fun {r : ℕ} (t : ℝ) (cs : Fin r → ℝ) =>
      ∫ x in simplexSet (r + 7), groupedParam c P s F G
        (mass t).1 (mass t).2.1 (mass t).2.2.1 (mass t).2.2.2 cs (simplexPoint x)
    let R := ∫ x in simplexSet 7, groupedParamRepeat c P s F G
      (mass p).1 (mass p).2.1 (mass p).2.2.1 (mass p).2.2.2 Fin.elim0 (simplexPoint x)
    let D := QED.ChainProof.SetCRegX.massDividedDifference
    let f := D (p ^ 2) (M ^ 2) (I p Fin.elim0) (I M Fin.elim0)
    let g := D (q ^ 2) (M ^ 2) (I q Fin.elim0) (I M Fin.elim0)
    let ff := D (p ^ 2) (M ^ 2) R f
    let fg := D (p ^ 2) (q ^ 2) f g
    f - p ^ 2 * ff - q ^ 2 * (fg - p ^ 2 * D (p ^ 2) (q ^ 2) ff fg)

/-- Expand the four numerator-cancellation terms to the eight-line simplex,
retaining the repeated light endpoint. The heavy member of the original
photon pair is still present on this simplex. -/
theorem integral_groupedParam_four_terms {c : Class5} (hc : c ∈ openClasses)
    (P : Params) (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ a A b B p q M : ℝ} (hμ : 0 < μ) (hMass : MassesGe μ a A b B)
    (hp : μ ≤ p) (hq : μ ≤ q) (hM : μ ≤ M)
    (hpq : p ^ 2 ≠ q ^ 2) (hpM : p ^ 2 ≠ M ^ 2) (hqM : q ^ 2 ≠ M ^ 2)
    (F G : (Fin 8 → ℝ) → ℝ)
    (hI : ∀ {r : ℕ} {a A b B : ℝ} (cs : Fin r → ℝ),
      MassesGe μ a A b B → (∀ j, μ ≤ cs j) →
      IntegrableOn (fun x => groupedParam c P s F G a A b B cs (simplexPoint x))
        (simplexSet (r + 7))) :
    let mass := fun t => (slotMa s t a, slotMA s t A, slotMb s t b, slotMB s t B)
    let I := fun {r : ℕ} (t : ℝ) (cs : Fin r → ℝ) =>
      ∫ x in simplexSet (r + 7), groupedParam c P s F G
        (mass t).1 (mass t).2.1 (mass t).2.2.1 (mass t).2.2.2 cs (simplexPoint x)
    I p ![M] - p ^ 2 * I p ![M, p] -
        q ^ 2 * (I p ![M, q] - p ^ 2 * I p ![M, q, p]) =
      groupedParamFourTerms c P s F G a A b B p q M := by
  intro mass I
  unfold groupedParamFourTerms
  let R := ∫ x in simplexSet 7, groupedParamRepeat c P s F G
    (mass p).1 (mass p).2.1 (mass p).2.2.1 (mass p).2.2.2 Fin.elim0 (simplexPoint x)
  let D := QED.ChainProof.SetCRegX.massDividedDifference
  let f := D (p ^ 2) (M ^ 2) (I p Fin.elim0) (I M Fin.elim0)
  let g := D (q ^ 2) (M ^ 2) (I q Fin.elim0) (I M Fin.elim0)
  let ff := D (p ^ 2) (M ^ 2) R f
  let fg := D (p ^ 2) (q ^ 2) f g
  change I p ![M] - p ^ 2 * I p ![M, p] - q ^ 2 * (I p ![M, q] -
      p ^ 2 * I p ![M, q, p]) =
    f - p ^ 2 * ff - q ^ 2 * (fg - p ^ 2 * D (p ^ 2) (q ^ 2) ff fg)
  let J := fun {r : ℕ} (t : ℝ) (cs : Fin r → ℝ) =>
    ∫ x in simplexSet (r + 7), groupedParamRepeat c P s F G
      (mass t).1 (mass t).2.1 (mass t).2.2.1 (mass t).2.2.2 cs (simplexPoint x)
  have hmass {t : ℝ} (ht : μ ≤ t) :
      MassesGe μ (mass t).1 (mass t).2.1 (mass t).2.2.1 (mass t).2.2.2 :=
    massesGe_slot hMass ht
  have hslot (t : ℝ) :
      unitMasses P.m (mass t).1 (mass t).2.1 (mass t).2.2.1 (mass t).2.2.2 s = t := by
    exact (unitMasses_slot hs P.m a A b B t s).trans (ite_eq_left rfl)
  have ema (v t : ℝ) : slotMa s v (mass t).1 = (mass v).1 := by
    dsimp [mass, slotMa]
    split_ifs <;> rfl
  have emA (v t : ℝ) : slotMA s v (mass t).2.1 = (mass v).2.1 := by
    dsimp [mass, slotMA]
    split_ifs <;> rfl
  have emb (v t : ℝ) : slotMb s v (mass t).2.2.1 = (mass v).2.2.1 := by
    dsimp [mass, slotMb]
    split_ifs <;> rfl
  have emB (v t : ℝ) : slotMB s v (mass t).2.2.2 = (mass v).2.2.2 := by
    dsimp [mass, slotMB]
    split_ifs <;> rfl
  have hsnoc {r : ℕ} {cs : Fin r → ℝ} {v : ℝ} (hcs : ∀ j, μ ≤ cs j) (hv : μ ≤ v) :
      ∀ j, μ ≤ Fin.snoc (α := fun _ => ℝ) cs v j := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.snoc_last] using hv
    · simpa only [Fin.snoc_castSucc] using hcs i
  have hsplit {r : ℕ} (cs : Fin r → ℝ) (hcs : ∀ j, μ ≤ cs j)
      {t v : ℝ} (ht : μ ≤ t) (hv : μ ≤ v) (hne : t ^ 2 ≠ v ^ 2) :
      I t (Fin.snoc cs v) = D (t ^ 2) (v ^ 2) (I t cs) (I v cs) := by
    have hEnd := hI cs (hmass hv) hcs
    have h := integral_groupedParam_split hc P hm hs hμ (hmass ht) F G (hsnoc hcs hv)
      (hI _ (hmass ht) (hsnoc hcs hv))
      (by simpa only [Fin.init_snoc] using hI cs (hmass ht) hcs)
      (by simpa only [Fin.init_snoc, Fin.snoc_last, ema, emA, emb, emB] using hEnd)
      (by simpa only [Fin.snoc_last, hslot] using hne)
    simpa only [I, D, QED.ChainProof.SetCRegX.massDividedDifference, Fin.init_snoc,
      Fin.snoc_last, hslot, ema, emA, emb, emB] using h
  have hrepeat {r : ℕ} (cs : Fin r → ℝ) (hcs : ∀ j, μ ≤ cs j) {t : ℝ} (ht : μ ≤ t) :
      IntegrableOn (fun x => groupedParamRepeat c P s F G
        (mass t).1 (mass t).2.1 (mass t).2.2.1 (mass t).2.2.2 cs (simplexPoint x))
        (simplexSet (r + 7)) ∧ I t (Fin.snoc cs t) = J t cs := by
    have h := integral_groupedParam_repeat c P s F G
      (hI _ (hmass ht) (hsnoc hcs ht)) (by simp only [Fin.snoc_last, hslot])
    simpa only [I, J, groupedParamRepeat, unitMV0, Fin.init_snoc] using h
  have hrsplit {r : ℕ} (cs : Fin r → ℝ) (hcs : ∀ j, μ ≤ cs j)
      {t v : ℝ} (ht : μ ≤ t) (hv : μ ≤ v) (hne : t ^ 2 ≠ v ^ 2) :
      J t (Fin.snoc cs v) =
        D (t ^ 2) (v ^ 2) (J t cs) (D (t ^ 2) (v ^ 2) (I t cs) (I v cs)) := by
    have hEnd := hI cs (hmass hv) hcs
    have h := integral_groupedParamRepeat_split hc P hm hs hμ (hmass ht) F G (hsnoc hcs hv)
      (hrepeat _ (hsnoc hcs hv) ht).1
      (by simpa only [Fin.init_snoc] using hI cs (hmass ht) hcs)
      (by simpa only [Fin.init_snoc, Fin.snoc_last, ema, emA, emb, emB] using hEnd)
      (by simpa only [Fin.snoc_last, hslot] using hne)
    simpa only [I, J, D, QED.ChainProof.SetCRegX.massDividedDifference, Fin.init_snoc,
      Fin.snoc_last, hslot, ema, emA, emb, emB] using h.2
  let nil : Fin 0 → ℝ := Fin.elim0
  have hn : ∀ j, μ ≤ nil j := fun j => Fin.elim0 j
  have e1 : Fin.snoc nil M = ![M] := by
    funext j
    fin_cases j
    rfl
  have e2 (t : ℝ) : Fin.snoc ![M] t = ![M, t] := by
    funext j
    fin_cases j <;> rfl
  have e3 : Fin.snoc ![M, q] p = ![M, q, p] := by
    funext j
    fin_cases j <;> rfl
  have hm1 : ∀ j, μ ≤ (![M] : Fin 1 → ℝ) j := e1 ▸ hsnoc hn hM
  have hm2 : ∀ j, μ ≤ (![M, q] : Fin 2 → ℝ) j := e2 q ▸ hsnoc hm1 hq
  have eL : I p ![M] = f := by simpa only [e1] using hsplit nil hn hp hM hpM
  have eH : I q ![M] = g := by simpa only [e1] using hsplit nil hn hq hM hqM
  have eR : J p ![M] = ff := by simpa only [e1] using hrsplit nil hn hp hM hpM
  have ePQ : I p ![M, q] = fg := by
    simpa only [e2, eL, eH] using hsplit ![M] hm1 hp hq hpq
  have ePP : I p ![M, p] = ff := by
    simpa only [e2, eR] using (hrepeat ![M] hm1 hp).2
  have ePQP : I p ![M, q, p] = D (p ^ 2) (q ^ 2) ff fg := by
    rw [← e3, (hrepeat ![M, q] hm2 hp).2, ← e2 q, hrsplit ![M] hm1 hp hq hpq, eR, eL, eH]
  rw [eL, ePP, ePQ, ePQP]


open QED.ChainProof.SetCRegDisp QED.ChainProof.SetCMain
open QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.UnitSCGraph QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.LimitCovariance

private theorem kerT_im_eq_four_terms_aux {c : Class5} (hc : c ∈ openClasses)
    (P : Params) (hm : P.m = 1) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    (hs' : s = 4 ∨ s = 5) {p q T : ℝ} (hp : 0 < p) (hpq : p < q) (hT : 0 < T)
    (hpT : p ^ 2 ≠ T) (hqT : q ^ 2 ≠ T) (F G : (Fin 8 → ℝ) → ℝ)
    (hTrace : ∀ {r : ℕ} {μ a A b B : ℝ} (hμ : 0 < μ) (hM : MassesGe μ a A b B)
      (cs : Fin r → ℝ), (∀ j, μ ≤ cs j) →
      let f := fun x => groupedParam c P s F G a A b B cs (simplexPoint x)
      IntegrableOn f (simplexSet (r + 7)) ∧
        (unitMPauliZero c P s (fun _ => 1) (unitMMasses P.m a A b B cs)).im =
          ∫ x in simplexSet (r + 7), f x) :
    (kerT c P s p q T).im = groupedParamFourTerms c P s F G p q p q p q (√T) := by
  let M := √T
  let μ := min p M
  have hμ : 0 < μ := lt_min hp (Real.sqrt_pos.2 hT)
  have hμp : μ ≤ p := min_le_left _ _
  have hμq : μ ≤ q := hμp.trans hpq.le
  have hμM : μ ≤ M := min_le_right _ _
  have hMass : MassesGe μ p q p q := ⟨hμp, hμq, hμp, hμq⟩
  have hsquare : p ^ 2 ≠ q ^ 2 :=
    (pow_lt_pow_left₀ hpq hp.le (by decide : 2 ≠ 0)).ne
  have hMsq : M ^ 2 = T := Real.sq_sqrt hT.le
  have hI {r : ℕ} {a A b B : ℝ} (cs : Fin r → ℝ) (hmass : MassesGe μ a A b B)
      (hcs : ∀ j, μ ≤ cs j) :=
    (hTrace hμ hmass cs hcs).1
  have h := integral_groupedParam_four_terms hc P (hm ▸ one_pos) hs hμ hMass
    hμp hμq hμM hsquare (hMsq ▸ hpT) (hMsq ▸ hqT) F G @hI
  have e (r : ℕ) (cs : Fin r → ℝ) :
      groupedParam c P s F G (slotMa s p p) (slotMA s p q) (slotMb s p p)
        (slotMB s p q) cs = groupedParam c P s F G p q p q cs := by
    rcases hs' with rfl | rfl <;> rfl
  dsimp only at h
  simp only [e] at h
  have eMs : √(P.m ^ 2 * T) = M := by rw [hm, one_pow, one_mul]
  rw [kerT_eq_zero_units hc P (hm ▸ one_pos) hs hp (hp.trans hpq) hT, eMs]
  simp only [← Complex.ofReal_pow, Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
    Complex.ofReal_re, zero_mul, add_zero]
  have h1 : ∀ j, μ ≤ (![M] : Fin 1 → ℝ) j := by
    intro j
    fin_cases j
    exact hμM
  have h2 (t : ℝ) (ht : μ ≤ t) : ∀ j, μ ≤ (![M, t] : Fin 2 → ℝ) j := by
    intro j
    fin_cases j
    · exact hμM
    · exact ht
  have h3 : ∀ j, μ ≤ (![M, q, p] : Fin 3 → ℝ) j := by
    intro j
    fin_cases j
    · exact hμM
    · exact hμq
    · exact hμp
  rw [(hTrace hμ hMass ![M] h1).2, (hTrace hμ hMass ![M, p] (h2 p hμp)).2,
    (hTrace hμ hMass ![M, q] (h2 q hμq)).2, (hTrace hμ hMass ![M, q, p] h3).2]
  exact h

/-- The L transverse Pauli value on the eight-line simplex at unit mass and charge. -/
theorem kerT_L_im_eq_four_terms {P : Params} (hm : P.m = 1) (he : P.e = 1)
    {s : Fin 8} (hs : s = 4 ∨ s = 5) {p q T : ℝ}
    (hp : 0 < p) (hpq : p < q) (hT : 0 < T) (hpT : p ^ 2 ≠ T) (hqT : q ^ 2 ≠ T) :
    (kerT .L P s p q T).im =
      groupedParamFourTerms .L P s (fun w => (secondCoeff (ladderT1 P w)).im / 6)
        (fun w => -(secondCoeff (ladderT2 P w)).im / 2) p q p q p q (√T) := by
  have hs₄ : 4 ≤ (s : ℕ) := by rcases hs with rfl | rfl <;> decide
  refine kerT_im_eq_four_terms_aux (c := .L) (by decide) P hm hs₄ hs hp hpq hT hpT hqT
    (fun w => (secondCoeff (ladderT1 P w)).im / 6)
    (fun w => -(secondCoeff (ladderT2 P w)).im / 2) ?_
  intro r μ a A b B hμ hM cs hcs
  exact unitMPauliZero_L_im_eq_pair (r := r) (cs := cs) hm he hs₄ hμ hM hcs

/-- The Sp transverse Pauli value on the eight-line simplex at unit mass and charge. -/
theorem kerT_Sp_im_eq_four_terms {P : Params} (hm : P.m = 1) (he : P.e = 1)
    {s : Fin 8} (hs : s = 4 ∨ s = 5) {p q T : ℝ}
    (hp : 0 < p) (hpq : p < q) (hT : 0 < T) (hpT : p ^ 2 ≠ T) (hqT : q ^ 2 ≠ T) :
    (kerT .Sp P s p q T).im =
      groupedParamFourTerms .Sp P s (fun w => (secondCoeff (classT1 .Sp permSp P w)).im / 6)
        (fun w => -(secondCoeff (classT2 .Sp permSp P w)).im / 2) p q p q p q (√T) := by
  have hs₄ : 4 ≤ (s : ℕ) := by rcases hs with rfl | rfl <;> decide
  refine kerT_im_eq_four_terms_aux (c := .Sp) (by decide) P hm hs₄ hs hp hpq hT hpT hqT
    (fun w => (secondCoeff (classT1 .Sp permSp P w)).im / 6)
    (fun w => -(secondCoeff (classT2 .Sp permSp P w)).im / 2) ?_
  intro r μ a A b B hμ hM cs hcs
  exact unitMPauliZero_Sp_im_eq_pair (r := r) (cs := cs) hm he hs₄ hμ hM hcs

/-- The Sm transverse Pauli value on the eight-line simplex at unit mass and charge. -/
theorem kerT_Sm_im_eq_four_terms {P : Params} (hm : P.m = 1) (he : P.e = 1)
    {s : Fin 8} (hs : s = 4 ∨ s = 5) {p q T : ℝ}
    (hp : 0 < p) (hpq : p < q) (hT : 0 < T) (hpT : p ^ 2 ≠ T) (hqT : q ^ 2 ≠ T) :
    (kerT .Sm P s p q T).im =
      groupedParamFourTerms .Sm P s (fun w => (secondCoeff (classT1 .Sm permSm P w)).im / 6)
        (fun w => -(secondCoeff (classT2 .Sm permSm P w)).im / 2) p q p q p q (√T) := by
  have hs₄ : 4 ≤ (s : ℕ) := by rcases hs with rfl | rfl <;> decide
  refine kerT_im_eq_four_terms_aux (c := .Sm) (by decide) P hm hs₄ hs hp hpq hT hpT hqT
    (fun w => (secondCoeff (classT1 .Sm permSm P w)).im / 6)
    (fun w => -(secondCoeff (classT2 .Sm permSm P w)).im / 2) ?_
  intro r μ a A b B hμ hM cs hcs
  exact unitMPauliZero_Sm_im_eq_pair (r := r) (cs := cs) hm he hs₄ hμ hM hcs

/-- The Cp transverse Pauli value on the eight-line simplex at unit mass and charge. -/
theorem kerT_Cp_im_eq_four_terms {P : Params} (hm : P.m = 1) (he : P.e = 1)
    {s : Fin 8} (hs : s = 4 ∨ s = 5) {p q T : ℝ}
    (hp : 0 < p) (hpq : p < q) (hT : 0 < T) (hpT : p ^ 2 ≠ T) (hqT : q ^ 2 ≠ T) :
    (kerT .Cp P s p q T).im =
      groupedParamFourTerms .Cp P s (fun w => (secondCoeff (classT1 .Cp permCp P w)).im / 6)
        (fun w => -(secondCoeff (classT2 .Cp permCp P w)).im / 2) p q p q p q (√T) := by
  have hs₄ : 4 ≤ (s : ℕ) := by rcases hs with rfl | rfl <;> decide
  refine kerT_im_eq_four_terms_aux (c := .Cp) (by decide) P hm hs₄ hs hp hpq hT hpT hqT
    (fun w => (secondCoeff (classT1 .Cp permCp P w)).im / 6)
    (fun w => -(secondCoeff (classT2 .Cp permCp P w)).im / 2) ?_
  intro r μ a A b B hμ hM cs hcs
  exact unitMPauliZero_Cp_im_eq_pair (r := r) (cs := cs) hm he hs₄ hμ hM hcs

/-- The Cm transverse Pauli value on the eight-line simplex at unit mass and charge. -/
theorem kerT_Cm_im_eq_four_terms {P : Params} (hm : P.m = 1) (he : P.e = 1)
    {s : Fin 8} (hs : s = 4 ∨ s = 5) {p q T : ℝ}
    (hp : 0 < p) (hpq : p < q) (hT : 0 < T) (hpT : p ^ 2 ≠ T) (hqT : q ^ 2 ≠ T) :
    (kerT .Cm P s p q T).im =
      groupedParamFourTerms .Cm P s (fun w => (secondCoeff (classT1 .Cm permCm P w)).im / 6)
        (fun w => -(secondCoeff (classT2 .Cm permCm P w)).im / 2) p q p q p q (√T) := by
  have hs₄ : 4 ≤ (s : ℕ) := by rcases hs with rfl | rfl <;> decide
  refine kerT_im_eq_four_terms_aux (c := .Cm) (by decide) P hm hs₄ hs hp hpq hT hpT hqT
    (fun w => (secondCoeff (classT1 .Cm permCm P w)).im / 6)
    (fun w => -(secondCoeff (classT2 .Cm permCm P w)).im / 2) ?_
  intro r μ a A b B hμ hM cs hcs
  exact unitMPauliZero_Cm_im_eq_pair (r := r) (cs := cs) hm he hs₄ hμ hM hcs

end QED.ChainProof.SetCUnitM

end
