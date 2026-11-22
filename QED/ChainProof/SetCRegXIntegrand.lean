/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegXGeom
public import QED.ChainProof.SetCUnitMPauli
public import QED.TwoLoop.UnitXGraphTraceMain
import QED.TwoLoop.UnitXGraphReduceChengWu
import QED.TwoLoop.UnitXGraphReduceBound

/-!
# The grouped numerator of the extended crossed unit

The crossed electron chain in `QED/TwoLoop/UnitXGraphTraceMain.lean` gives the three
Wick contractions of the extended unit. Only the factorials and the second Symanzik
function depend on the extra lines.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.ChainProof.SetCUnit
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitLGraph
open QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.ClassIntegrable
open QED.Integration.Feynman (simplexPoint simplexSet)
open QED.Integration.TwoLoop

variable {r : ℕ}

private theorem unitMMomenta_emb (s : Fin 8) (p p' : Fin 4 → ℝ) (i : Fin 8) :
    unitMMomenta .X s (fun _ : Fin r => 1) p p' (mEmb r i) = pvMomentaE .X p p' i := by
  simp [unitMMomenta, mScale, mLine, mExt_mEmb]

private theorem unitM_lineMomentum_emb (s : Fin 8) (p p' : Fin 4 → ℝ) (i : Fin 8)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    Integration.TwoLoop.lineMomentum (unitMMatrix .X s (fun _ : Fin r => 1))
      (unitMMomenta .X s (fun _ : Fin r => 1) p p') (mEmb r i) ℓ =
      Integration.TwoLoop.lineMomentum crossedAlpha (pvMomentaE .X p p') i ℓ := by
  funext ν
  unfold Integration.TwoLoop.lineMomentum
  simp only [unitMMatrix_mEmb, unitMMomenta_emb]

private theorem crossedChain_unitM (P : Params) (s : Fin 8) (u : ℝ) (μ : Fin 4)
    (l : Fin 5 → Fin 4) :
    crossedChain P u μ l =
      elecChain (unitMMatrix .X s (fun _ : Fin r => 1))
        (unitMMomenta .X s (fun _ : Fin r => 1) (restMomentum P.m) (curveMomentum P.m u))
        (crossedB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
        (fun _ => P.m) (mEmb r ∘ crossedLines) := by
  funext ℓ
  simp only [crossedChain, elecChain, Function.comp_apply, unitM_lineMomentum_emb]

private theorem unitMPauliNum_X_chain (P : Params) (s : Fin 8) (M : Fin (r + 8) → ℝ)
    (x : Fin (r + 7) → ℝ) (u : ℝ) :
    unitMPauliNum .X P s (fun _ => 1) M x u =
      -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4,
        crossedWeight P μ l * paramNumOf (crossedChain P u μ l)
          (unitMMatrix .X s (fun _ => 1))
          (unitMMomenta .X s (fun _ => 1) (restMomentum P.m) (curveMomentum P.m u)) M x := by
  set α := unitMMatrix .X s (fun _ : Fin r => 1)
  set pm := unitMMomenta .X s (fun _ : Fin r => 1) (restMomentum P.m) (curveMomentum P.m u)
  have hq : ∀ μ l, ∃ Q : LoopQuartic, Q.eval = crossedChain P u μ l := fun μ l =>
    exists_quartic_elecChain _ _ _ _ _
  have hqμ : ∀ μ, ∃ Q : LoopQuartic,
      Q.eval = fun ℓ => ∑ l : Fin 5 → Fin 4, crossedWeight P μ l * crossedChain P u μ l ℓ :=
    fun μ => exists_quartic_sum _ _ (hq μ)
  have h1 : unitMPauliNum .X P s (fun _ => 1) M x u = -((π : ℂ) ^ 4) *
      paramNumOf (fun ℓ => ∑ j : Idx,
        pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
          openF .X P (curveMomentum P.m u) j ℓ) α pm M x := by
    rw [paramNumOf_sum _ _ _ _ _ _ fun j => exists_quartic_openF_X P _ j, unitMPauliNum,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (fun ℓ => ∑ j : Idx,
      pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
        openF .X P (curveMomentum P.m u) j ℓ) =
      fun ℓ => ladderConst P * ∑ μ, (1 : ℂ) *
        ∑ l : Fin 5 → Fin 4, crossedWeight P μ l * crossedChain P u μ l ℓ := by
    funext ℓ
    rw [sum_pauliWt_openF_X]
    simp only [one_mul]
    rfl
  rw [h1, h2, paramNumOf_const_mul _ _ _ _ _ (exists_quartic_sum _ _ hqμ),
    paramNumOf_sum _ _ _ _ _ _ hqμ]
  simp only [one_mul]
  rw [mul_assoc]
  congr 2
  exact Finset.sum_congr rfl fun μ _ => paramNumOf_sum _ _ _ _ _ _ (hq μ)

/-- The three crossed trace terms retain their shape under grouping, with the
factorials of the enlarged simplex. -/
theorem unitMPauliNum_X_eq_T (P : Params) (s : Fin 8) (M : Fin (r + 8) → ℝ)
    (x : Fin (r + 7) → ℝ) (u : ℝ) :
    let w := groupExtra s (simplexPoint x)
    let V : ℂ := ↑(symanzikV (unitMMatrix .X s (fun _ : Fin r => 1))
      (unitMMomenta .X s (fun _ : Fin r => 1) (restMomentum P.m) (curveMomentum P.m u))
      M (simplexPoint x))
    unitMPauliNum .X P s (fun _ => 1) M x u =
      ((r + 3).factorial : ℂ) / 6 * crossedT1 P w u +
      ((r + 2).factorial : ℂ) / 2 * crossedT2 P w u * V +
      ((r + 1).factorial : ℂ) * crossedT3 P w u * V ^ 2 := by
  dsimp only
  rw [unitMPauliNum_X_chain]
  have eAt (B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :=
    @paramNumOf_elecChain (r + 7) (unitMMatrix .X s (fun _ : Fin r => 1))
      (unitMMomenta .X s (fun _ : Fin r => 1) (restMomentum P.m) (curveMomentum P.m u))
      M x B (fun _ => P.m) (mEmb r ∘ crossedLines)
  simp only [crossedChain_unitM (r := r) P s, eAt, symanzikMatrix_unitM_group,
    symanzikU_unitM_group, loopShift_unitM_group]
  have he :
      elecAt (unitMMatrix .X s (fun _ : Fin r => 1))
        (unitMMomenta .X s (fun _ : Fin r => 1) (restMomentum P.m) (curveMomentum P.m u))
        (fun _ => P.m) (mEmb r ∘ crossedLines)
        (-loopShift crossedAlpha (crossedMom P u) (groupExtra s (simplexPoint x))) =
      crossedE P (groupExtra s (simplexPoint x)) u := by
    funext k
    simp only [crossedE, elecAt, Function.comp_apply, unitM_lineMomentum_emb]
  have e2 (B E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
      chainTwo (unitMMatrix .X s (fun _ : Fin r => 1)) B E (mEmb r ∘ crossedLines) A =
        chainTwo crossedAlpha B E crossedLines A := by
    simp only [chainTwo, contrC, Function.comp_apply, unitMMatrix_mEmb]
  have e3 (B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
      chainFour (unitMMatrix .X s (fun _ : Fin r => 1)) B (mEmb r ∘ crossedLines) A =
        chainFour crossedAlpha B crossedLines A := by
    simp only [chainFour, contrC, Function.comp_apply, unitMMatrix_mEmb]
  have h4 : r + 7 - 4 = r + 3 := by omega
  have h5 : r + 7 - 5 = r + 2 := by omega
  have h6 : r + 7 - 6 = r + 1 := by omega
  simp only [he, e2, e3, h4, h5, h6, crossedT1, crossedT2, crossedT3]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring

/-- The extended crossed jet uses the same two trace polynomials as the
eight-line unit. The jet of the double contraction vanishes. -/
theorem secondCoeff_unitMPauliNum_X {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (s : Fin 8) (M : Fin 8 → ℝ) (cs : Fin r → ℝ) (x : Fin (r + 7) → ℝ)
    (hU : xU (groupExtra s (simplexPoint x)) ≠ 0) :
    let w := groupExtra s (simplexPoint x)
    let V : ℂ := ↑(unitMV0 .X P s (fun _ => 1) (mExt M cs) x)
    secondCoeff (unitMPauliNum .X P s (fun _ => 1) (mExt M cs) x) =
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst) *
        (((r + 3).factorial : ℂ) / 2 * ↑(xPsi1 w / xU w ^ 6) -
          ((r + 2).factorial : ℂ) / 2 * ↑(xPsi2 w / xU w ^ 5) * V) := by
  dsimp only
  let w := groupExtra s (simplexPoint x)
  let V (u : ℝ) : ℂ := ↑(symanzikV (unitMMatrix .X s (fun _ : Fin r => 1))
      (unitMMomenta .X s (fun _ : Fin r => 1) (restMomentum P.m) (curveMomentum P.m u))
      (mExt M cs) (simplexPoint x))
  have hVeq (u : ℝ) : V u = ↑(symanzikV crossedAlpha (crossedMom P u) M w +
      ∑ j, simplexPoint x (mExtra r j) * (cs j ^ 2 - M s ^ 2)) := by
    unfold V
    rw [symanzikV_unitM_group]
  have hv : V 0 = ↑(unitMV0 .X P s (fun _ => 1) (mExt M cs) x) := by
    simp only [V, unitMV0, curveMomentum_zero]
  have hV : Tendsto V (𝓝 0) (𝓝 (V 0)) := by
    rw [hVeq 0]
    simp only [crossedMom, curveMomentum_zero]
    have hc := (continuous_crossedV (restMomentum P.m) M w).tendsto (restMomentum P.m)
    have ht := (hc.comp (tendsto_curveMomentum P.m)).add_const
      (∑ j, simplexPoint x (mExtra r j) * (cs j ^ 2 - M s ^ 2))
    exact ((Complex.continuous_ofReal.tendsto _).comp ht).congr (fun u => (hVeq u).symm)
  have t1 := hasJet2_crossedT1 hm he hU
  have t2 := hasJet2_mul_tendsto (hasJet2_crossedT2 hm he hU) hV
  have t3 := hasJet2_mul_tendsto (hasJet2_crossedT3 hm w) (hV.pow 2)
  have h := (((t1.const_mul (((r + 3).factorial : ℂ) / 6)).add
    (t2.const_mul (((r + 2).factorial : ℂ) / 2))).add
      (t3.const_mul ((r + 1).factorial : ℂ)))
  have hj := h.congr (show ∀ u, unitMPauliNum .X P s (fun _ => 1) (mExt M cs) x u = _ by
    intro u
    rw [unitMPauliNum_X_eq_T]
    change _ + _ * _ * V u + _ * _ * V u ^ 2 = _
    simp only [mul_assoc, w])
  rw [hj.secondCoeff_eq, hv]
  ring

private theorem groupExtra_pos (s : Fin 8) {z : Fin (r + 8) → ℝ} (hz : ∀ i, 0 < z i)
    (i : Fin 8) : 0 < groupExtra s z i := by
  unfold groupExtra
  apply add_pos_of_pos_of_nonneg (hz _)
  split
  · exact Finset.sum_nonneg fun j _ => (hz (mExtra r j)).le
  · exact le_rfl

/-- The first Symanzik polynomial of the grouped crossed unit is positive
almost everywhere on the extended simplex. -/
theorem ae_xU_groupExtra_ne_zero (s : Fin 8) :
    ∀ᵐ x ∂(volume.restrict (simplexSet (r + 7))),
      xU (groupExtra s (simplexPoint x)) ≠ 0 := by
  filter_upwards [QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos
    (m := r + 7) (by omega)] with x hx
  exact (xU_pos (groupExtra_pos s hx)).ne'

/-- The two crossed Pauli resolvents after the second-order projection. -/
noncomputable def crossedResolvent (r : ℕ) (w : Fin 8 → ℝ) (V : ℝ) : ℝ :=
  (r + 3).factorial / 2 * (xPsi1 w / xU w ^ 6) / V ^ (r + 4) -
    (r + 2).factorial / 2 * (xPsi2 w / xU w ^ 5) / V ^ (r + 3)

/-- The extended Pauli value is the integral of the two resolvents, with the
same trace polynomials as in the unextended unit. -/
theorem unitMPauliZero_X_eq_integral {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (s : Fin 8) (M : Fin 8 → ℝ) (cs : Fin r → ℝ) :
    unitMPauliZero .X P s (fun _ => 1) (mExt M cs) =
      (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 / kConst) *
        ↑(∫ x in simplexSet (r + 7), crossedResolvent r (groupExtra s (simplexPoint x))
          (unitMV0 .X P s (fun _ => 1) (mExt M cs) x)) := by
  rw [unitMPauliZero, ← integral_complex_ofReal, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_xU_groupExtra_ne_zero (r := r) s] with x hx
  rw [secondCoeff_unitMPauliNum_X hm he s M cs x hx]
  unfold crossedResolvent
  set v := unitMV0 .X P s (fun _ => 1) (mExt M cs) x
  push_cast
  rw [show r + 4 = (r + 3) + 1 by rfl, pow_succ]
  by_cases hv : v = 0
  · simp [hv]
  · have hn : (v : ℂ) ≠ 0 := ofReal_ne_zero.mpr hv
    field_simp [hn]
    ring

private theorem sum_groupExtra_eq (s : Fin 8) (z : Fin (r + 8) → ℝ) :
    ∑ i, groupExtra s z i = ∑ i, z i := by
  have hsum : (∑ i, z i) = (∑ i, z (mEmb r i)) + ∑ j, z (mExtra r j) := by
    let e := (finSumFinEquiv (m := 8) (n := r)).trans (finCongr (Nat.add_comm 8 r))
    rw [← e.sum_comp z, Fintype.sum_sum_type]
    congr 1
    exact Finset.sum_congr rfl fun j _ => congrArg z (Fin.ext (Nat.add_comm 8 j.val))
  rw [hsum]
  simp only [groupExtra, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem measurable_crossedResolvent (r : ℕ) :
    Measurable fun p : (Fin 8 → ℝ) × ℝ => crossedResolvent r p.1 p.2 := by
  have ha (k : Fin 4) : Measurable fun z : Fin 8 → ℝ => xan z k := by
    fin_cases k <;>
      simp only [xan, gXan, xA, xM, xc, xa, xb] <;> fun_prop
  have hb (k : Fin 4) : Measurable fun z : Fin 8 → ℝ => xbn z k := by
    fin_cases k <;>
      simp only [xbn, gXbn, xA, xt, xM, xc, xa, xb] <;> fun_prop
  have hc (k : Fin 6) : Measurable fun z : Fin 8 → ℝ => xCn z k := by
    fin_cases k <;>
      simp only [xCn, xA, xM, xc, xa, xb] <;> fun_prop
  have hU : Measurable fun z : Fin 8 → ℝ => xU z := by
    unfold xU gXU xA xM xc xa xb
    fun_prop
  have h1 : Measurable fun z : Fin 8 → ℝ => xPsi1 z := by
    unfold xPsi1 psiT1h
    fun_prop
  have h2 : Measurable fun z : Fin 8 → ℝ => xPsi2 z := by
    unfold xPsi2 psiT2h
    fun_prop
  unfold crossedResolvent
  fun_prop

private theorem abs_crossedResolvent_le {C₁ C₂ v₀ V : ℝ} {w : Fin 8 → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hv₀ : 0 < v₀) (hV : v₀ ≤ V)
    (h₁ : |xPsi1 w| ≤ C₁ * xU w ^ 4) (h₂ : |xPsi2 w| ≤ C₂ * xU w ^ 2) :
    |crossedResolvent r w V| ≤
      ((r + 3).factorial / 2 * C₁ / v₀ ^ (r + 4) +
        (r + 2).factorial / 2 * C₂ / v₀ ^ (r + 3)) / xU w ^ 3 := by
  set U := xU w with hUw
  have hU : 0 < U := xU_pos hw
  have hU₁ : U ≤ 1 := xU_le_one hw hw1
  have hVp := hv₀.trans_le hV
  have hC₁ := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans h₁) (pow_pos hU 4)
  have hC₂ := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans h₂) (pow_pos hU 2)
  have b₁ : |xPsi1 w| / U ^ 6 / V ^ (r + 4) ≤ C₁ / v₀ ^ (r + 4) / U ^ 3 := by
    calc
      _ ≤ (C₁ * U ^ 4) / U ^ 6 / v₀ ^ (r + 4) := by
        exact div_le_div₀ (by positivity) (div_le_div_of_nonneg_right h₁ (by positivity))
          (by positivity) (pow_le_pow_left₀ hv₀.le hV _)
      _ = C₁ / v₀ ^ (r + 4) / U ^ 2 := by
        field_simp [hU.ne', hv₀.ne']
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hU.le 2) hU₁
  have b₂ : |xPsi2 w| / U ^ 5 / V ^ (r + 3) ≤ C₂ / v₀ ^ (r + 3) / U ^ 3 := by
    calc
      _ ≤ (C₂ * U ^ 2) / U ^ 5 / v₀ ^ (r + 3) := by
        exact div_le_div₀ (by positivity) (div_le_div_of_nonneg_right h₂ (by positivity))
          (by positivity) (pow_le_pow_left₀ hv₀.le hV _)
      _ = _ := by field_simp [hU.ne', hv₀.ne']
  have hU' : 0 < xU w := hU
  unfold crossedResolvent
  refine (abs_sub _ _).trans ?_
  simp only [abs_div, abs_mul, abs_of_pos (pow_pos hU' 6), abs_of_pos (pow_pos hU' 5),
    abs_of_pos (pow_pos hVp _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r + 3).factorial / 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r + 2).factorial / 2), mul_div_assoc, add_div]
  exact add_le_add (mul_le_mul_of_nonneg_left b₁ (by positivity))
    (mul_le_mul_of_nonneg_left b₂ (by positivity))

/-- With all photon masses bounded below by a positive number, the grouped
crossed resolvent is integrable on the extended simplex. -/
theorem integrableOn_crossedResolvent (P : Params) (hm : 0 < P.m) {s : Fin 8}
    (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {cs : Fin r → ℝ} (hcs : ∀ j, μ₀ ≤ cs j) :
    IntegrableOn (fun x => crossedResolvent r (groupExtra s (simplexPoint x))
      (unitMV0 .X P s (fun _ => 1) (unitMMasses P.m a A b B cs) x)) (simplexSet (r + 7)) := by
  have hc : Class5.X ∈ openClasses := by decide
  have hX : ExtraGe μ₀ (fun _ : Fin r => 1) cs := fun j => ⟨one_pos, le_rfl, hcs j⟩
  let C := unitMCurve hc P hm hs hμ₀ hM hX
  have hV : ∀ᵐ x ∂(volume.restrict (simplexSet (r + 7))), C.c ≤
      unitMV0 .X P s (fun _ => 1) (unitMMasses P.m a A b B cs) x := by
    filter_upwards [C.ae_le_vfun] with x hx
    simpa only [C, unitMCurve, CurveData.vfun, unitMV0, curveMomentum_zero]
      using hx 0 (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)
  obtain ⟨C₁, hC₁⟩ := exists_bound_psiT1h
  obtain ⟨C₂, hC₂⟩ := exists_bound_psiT2h
  let K : ℝ := (r + 3).factorial / 2 * C₁ / C.c ^ (r + 4) +
    (r + 2).factorial / 2 * C₂ / C.c ^ (r + 3)
  have hsp := continuous_simplexPoint' (m := r + 7)
  have hgrp : Measurable (groupExtra (r := r) s) := by
    apply Measurable.of_eval
    intro i
    unfold groupExtra
    split
    · fun_prop
    · fun_prop
  have hmV : Measurable (unitMV0 .X P s (fun _ => 1) (unitMMasses P.m a A b B cs)) :=
    (measurable_symanzikV _ _ _).comp hsp.measurable
  apply ((integrableOn_prod_simplexPoint_rpow (m := r + 7)
    (Finset.univ.map (mEmb r)) (s := 3 / 4) (by norm_num) (by norm_num)).const_mul K).mono'
    ((measurable_crossedResolvent r).comp
      ((hgrp.comp hsp.measurable).prodMk hmV)).aestronglyMeasurable
  filter_upwards [QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos
    (m := r + 7) (by omega), hV] with x hx hxV
  let w := groupExtra s (simplexPoint x)
  have hw := groupExtra_pos s hx
  have hw1 : ∑ i, w i = 1 := (sum_groupExtra_eq s _).trans (sum_simplexPoint x)
  have hU := xU_pos hw
  have hbound := abs_crossedResolvent_le (r := r) hw hw1 C.hc hxV
    (abs_xPsi1_le hC₁ hw) (abs_xPsi2_le hC₂ hw hw1)
  have hK : 0 ≤ K := by
    have h := (abs_nonneg _).trans hbound
    rw [div_eq_mul_inv] at h
    exact nonneg_of_mul_nonneg_left h (by positivity)
  rw [Real.norm_eq_abs]
  refine hbound.trans ?_
  rw [div_eq_mul_inv, Finset.prod_map]
  apply mul_le_mul_of_nonneg_left _ hK
  refine (inv_xU_pow_three_le_prod_rpow hw).trans (Finset.prod_le_prod₀ ?_ ?_)
  · exact fun i _ => Real.rpow_nonneg (hw i).le _
  · intro i _
    apply Real.rpow_le_rpow_of_nonpos (hx (mEmb r i)) _ (by norm_num)
    apply le_add_of_nonneg_right
    split
    · exact Finset.sum_nonneg fun j _ => (hx (mExtra r j)).le
    · exact le_rfl

end QED.ChainProof.SetCUnitM

end
