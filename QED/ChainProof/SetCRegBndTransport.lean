/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegXHomogeneity
public import QED.ChainProof.SetCRegBndParam
public import QED.ChainProof.SetCRegBndMain

/-!
# Unit mass and charge for the ladder, self-energy and corner Pauli values

The chain factors from `QED/TwoLoop/UnitSCGraph.lean` and
`QED/TwoLoop/LimitCovarianceOpen.lean` isolate the five vertex charges.
The mass dilation acts on every line, including the extra spectral lines.
-/

public section

open Complex MeasureTheory

namespace QED.ChainProof.SetCUnitM

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.UnitSCGraph QED.TwoLoop.MassScaling QED.TwoLoop.ParamNumEval
open QED.ChainProof.SetCUnit QED.Integration.TwoLoop

private theorem classNumeratorE_chargeOne_of_chain {c : Class5} {pa : Equiv.Perm (Fin 5)}
    {line : Fin 4 → FermionLine c.rep} (hch : IsChainForm c pa line)
    (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (α β μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    classNumeratorE c P pOut pIn kIn α β μ ℓ =
      (P.e : ℂ) ^ 5 * classNumeratorE c { P with e := 1 } pOut pIn kIn α β μ ℓ := by
  have hchain (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 4) :
      chainNum { P with e := 1 } pa E v = chainNum P pa E v := by
    simp only [chainNum, pvEta]
  rw [hch P, hch { P with e := 1 }, hchain]
  change (I * (P.e : ℂ)) ^ 5 * _ * _ = (P.e : ℂ) ^ 5 * ((I * (1 : ℂ)) ^ 5 * _ * _)
  rw [mul_pow, mul_one]
  ring

private theorem openF_chargeOne {c : Class5} (hc : c ∈ openClasses) (hX : c ≠ .X)
    (P : Params) (p' : Fin 4 → ℝ) (j : Idx) :
    openF c P p' j = fun ℓ => (P.e : ℂ) ^ 5 * openF c { P with e := 1 } p' j ℓ := by
  have hN : ∀ a b k μ i j ℓ,
      classNumeratorE c P a b k μ i j ℓ =
        (P.e : ℂ) ^ 5 * classNumeratorE c { P with e := 1 } a b k μ i j ℓ := by
    intro a b k μ i j ℓ
    cases c with
    | L => exact classNumeratorE_chargeOne_of_chain chain_L P a b k μ i j ℓ
    | X => exact (hX rfl).elim
    | Sp => exact classNumeratorE_chargeOne_of_chain isChainForm_Sp P a b k μ i j ℓ
    | Sm => exact classNumeratorE_chargeOne_of_chain isChainForm_Sm P a b k μ i j ℓ
    | Cp => exact classNumeratorE_chargeOne_of_chain isChainForm_Cp P a b k μ i j ℓ
    | Cm => exact classNumeratorE_chargeOne_of_chain isChainForm_Cm P a b k μ i j ℓ
    | VP => exact ((by decide : Class5.VP ∉ openClasses) hc).elim
    | Fp => exact ((by decide : Class5.Fp ∉ openClasses) hc).elim
    | Fm => exact ((by decide : Class5.Fm ∉ openClasses) hc).elim
  funext ℓ
  simp only [openF, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul, hN]
  ring

variable {r : ℕ}

private theorem unitMPauliNum_chargeOne {c : Class5} (hc : c ∈ openClasses) (hX : c ≠ .X)
    (P : Params) (s : Fin 8) (κ : Fin r → ℝ) (M : Fin (r + 8) → ℝ)
    (x : Fin (r + 7) → ℝ) :
    unitMPauliNum c P s κ M x =
      fun u => (P.e : ℂ) ^ 5 * unitMPauliNum c { P with e := 1 } s κ M x u := by
  let N := { P with e := 1 }
  funext u
  change unitMPauliNum c P s κ M x u = (P.e : ℂ) ^ 5 * unitMPauliNum c N s κ M x u
  unfold unitMPauliNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [openF_chargeOne hc hX P, paramNumOf_const_mul _ _ _ _ _
    (QED.TwoLoop.MassScaling.exists_quartic_openF hc N _ j)]
  ring

/-- A ladder, self-energy or corner Pauli value carries the fifth power of the charge. -/
theorem unitMPauliZero_chargeOne_of_ne_X {c : Class5} (hc : c ∈ openClasses) (hX : c ≠ .X)
    (P : Params) (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ a A b B : ℝ} (hμ : 0 < μ) (hM : MassesGe μ a A b B)
    {κ cs : Fin r → ℝ} (hκ : ExtraGe μ κ cs) :
    unitMPauliZero c P s κ (unitMMasses P.m a A b B cs) =
      (P.e : ℂ) ^ 5 * unitMPauliZero c { P with e := 1 } s κ
        (unitMMasses P.m a A b B cs) := by
  let N := { P with e := 1 }
  let M := unitMMasses P.m a A b B cs
  let C := unitMCurve hc N hm hs hμ hM hκ
  let F := fun u (j : Idx) => openF c N (curveMomentum N.m u) j
  let ω := fun u (j : Idx) =>
    pauliWt N.m (curveMomentum N.m u) (restMomentum N.m) j.1 j.2.1 j.2.2
  unfold unitMPauliZero
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [unitMPauliNum_chargeOne hc hX P]
  change secondCoeff (fun u => (P.e : ℂ) ^ 5 * projNum C F ω x u) /
      (unitMV0 c N s κ M x : ℂ) ^ (r + 4) = _
  have hcoeff := secondCoeff_const_mul_projNum C (D := 8) (n := 4) (r := 4) (Dω := 8)
    F ?_ (fun u _ j => QED.TwoLoop.MassScaling.exists_quartic_openF hc N _ j)
    ω (fun j => isUPoly_pauliWt N.m j) (sum_pauliWt_zero N.m) x ((P.e : ℂ) ^ 5)
  · rw [hcoeff, mul_div_assoc]
    rfl
  · intro j
    have h := isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
      (G := fun ℓ y => twoLoopNorm * classNumeratorE c N (fun _ => y 0)
        (fun _ => restMomentum N.m) (fun _ => y 0 - restMomentum N.m) (fun _ => j.2.1)
        (fun _ => j.2.2) (fun _ => j.1) ℓ)
      (fun ℓ => (isLoopPoly_classNumeratorE_out hc N _ _ _ _ ℓ).const_mul _)
      (ℓ := fun _ u => fun _ => curveMomentum N.m u) fun _ ν => isUPoly_curveMomentum N.m ν
    refine h.congr fun ℓ u _ => ?_
    simp only [F, openF, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul]

private theorem unitMMasses_inv_mass_smul {m : ℝ}
    (a A b B : ℝ) (cs : Fin r → ℝ) :
    (1 / m) • unitMMasses m a A b B cs =
      unitMMasses (1 / m * m) (a / m) (A / m) (b / m) (B / m) (fun j => cs j / m) := by
  funext i
  obtain ⟨j, rfl⟩ | ⟨j, rfl⟩ := mem_mEmb_or_mExtra i
  · simp only [Pi.smul_apply, smul_eq_mul, unitMMasses, mExt_mEmb]
    fin_cases j <;> simp [unitMasses, classPVMasses, Fin.isValue, div_eq_mul_inv, mul_comm]
  · simp only [Pi.smul_apply, smul_eq_mul, unitMMasses, mExt_mExtra]
    ring

/-- Transport the Pauli value to unit electron mass and unit charge. -/
theorem unitMPauliZero_normalize_of_ne_X {c : Class5} (hc : c ∈ openClasses) (hX : c ≠ .X)
    (P : Params) (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ a A b B : ℝ} (hμ : 0 < μ) (hM : MassesGe μ a A b B)
    {κ cs : Fin r → ℝ} (hκ : ExtraGe μ κ cs) :
    let N := massScale (1 / P.m) { P with e := 1 }
    unitMPauliZero c P s κ (unitMMasses P.m a A b B cs) =
      ((P.e : ℂ) ^ 5 * (P.m : ℂ) ^ 13 / ((P.m : ℂ) ^ 2) ^ (r + 4)) *
        unitMPauliZero c N s κ (unitMMasses N.m (a / P.m) (A / P.m) (b / P.m) (B / P.m)
          (fun j => cs j / P.m)) := by
  intro N
  rw [unitMPauliZero_chargeOne_of_ne_X hc hX P hm hs hμ hM hκ]
  have hS := unitMPauliZero_massScale hc { P with e := 1 } hm hs hμ hM hκ
    (one_div_ne_zero hm.ne')
  rw [unitMMasses_inv_mass_smul] at hS
  change unitMPauliZero c N s κ (unitMMasses N.m _ _ _ _ _) = _ at hS
  rw [hS]
  have hm' : (P.m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  simp only [Complex.ofReal_div, Complex.ofReal_one, div_pow]
  field_simp
  ring


open QED.ChainProof.SetCRegDisp QED.ChainProof.SetCMain

/-- The four zero-numerator terms scale with a common mass and charge factor. -/
theorem kerT_normalize_of_ne_X {c : Class5} (hc : c ∈ openClasses) (hX : c ≠ .X)
    (P : Params) (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {p q T : ℝ} (hp : 0 < p) (hq : 0 < q) (hT : 0 < T) :
    let N := massScale (1 / P.m) { P with e := 1 }
    kerT c P s p q T =
      ((P.e : ℂ) ^ 5 * (P.m : ℂ) ^ 3) * kerT c N s (p / P.m) (q / P.m) T := by
  intro N
  let M := Real.sqrt (P.m ^ 2 * T)
  let μ := min M (min p q)
  have hMp : 0 < M := Real.sqrt_pos.2 (mul_pos (pow_pos hm 2) hT)
  have hμ : 0 < μ := lt_min hMp (lt_min hp hq)
  have hμM : μ ≤ M := min_le_left _ _
  have hμp : μ ≤ p := (min_le_right _ _).trans (min_le_left _ _)
  have hμq : μ ≤ q := (min_le_right _ _).trans (min_le_right _ _)
  have hmass : MassesGe μ p q p q := ⟨hμp, hμq, hμp, hμq⟩
  have hN : N.m = 1 := by change (1 / P.m) * P.m = 1; field_simp
  have eM : M / P.m = Real.sqrt (N.m ^ 2 * T) := by
    rw [hN, one_pow, one_mul]
    dsimp [M]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm.le]
    field_simp
  let A {r : ℕ} (cs : Fin r → ℝ) :=
    unitMPauliZero c P s (fun _ => 1) (unitMMasses P.m p q p q cs)
  let B {r : ℕ} (cs : Fin r → ℝ) :=
    unitMPauliZero c N s (fun _ => 1)
      (unitMMasses N.m (p / P.m) (q / P.m) (p / P.m) (q / P.m) cs)
  have e {r : ℕ} (cs : Fin r → ℝ) (hcs : ∀ j, μ ≤ cs j) :
      A cs = ((P.e : ℂ) ^ 5 * (P.m : ℂ) ^ 13 / ((P.m : ℂ) ^ 2) ^ (r + 4)) *
        B (fun j => cs j / P.m) :=
    unitMPauliZero_normalize_of_ne_X hc hX P hm hs hμ hmass
      (fun j => ⟨one_pos, le_rfl, hcs j⟩)
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
  have e1 : (fun j => (![M] : Fin 1 → ℝ) j / P.m) = ![M / P.m] := by
    funext j
    fin_cases j
    rfl
  have e2 (t : ℝ) :
      (fun j => (![M, t] : Fin 2 → ℝ) j / P.m) = ![M / P.m, t / P.m] := by
    funext j
    fin_cases j <;> rfl
  have e3 : (fun j => (![M, q, p] : Fin 3 → ℝ) j / P.m) =
      ![M / P.m, q / P.m, p / P.m] := by
    funext j
    fin_cases j <;> rfl
  rw [kerT_eq_zero_units hc P hm hs hp hq hT,
    kerT_eq_zero_units hc N (hN ▸ one_pos) hs (div_pos hp hm) (div_pos hq hm) hT, ← eM]
  change A ![M] - (p ^ 2 : ℂ) * A ![M, p] -
      (q ^ 2 : ℂ) * (A ![M, q] - (p ^ 2 : ℂ) * A ![M, q, p]) =
    ((P.e : ℂ) ^ 5 * (P.m : ℂ) ^ 3) *
      (B ![M / P.m] - ((p / P.m : ℝ) : ℂ) ^ 2 * B ![M / P.m, p / P.m] -
        ((q / P.m : ℝ) : ℂ) ^ 2 *
          (B ![M / P.m, q / P.m] - ((p / P.m : ℝ) : ℂ) ^ 2 * B ![M / P.m, q / P.m, p / P.m]))
  rw [e _ h1, e _ (h2 p hμp), e _ (h2 q hμq), e _ h3, e1, e2, e2, e3]
  have hm' : (P.m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  push_cast
  field_simp

/-- The normalized real placement is invariant under the change to unit mass and charge. -/
theorem uBDT_normalized_real_of_ne_X (P : Params) (hm : 0 < P.m) (he : P.e ≠ 0)
    (i : Fin 12) (hX : repBClass i ≠ .X) {p q T : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hT : 0 < T) :
    let N := massScale (1 / P.m) { P with e := 1 }
    64 * Real.pi ^ 6 / P.e ^ 6 * ((1 / I) * uBDT P i p q T).re =
      64 * Real.pi ^ 6 * ((1 / I) * uBDT N i (p / P.m) (q / P.m) T).re := by
  intro N
  let R := { P with mγ := p, Λ := q }
  have hN : N.m = 1 := by change (1 / P.m) * P.m = 1; field_simp
  have hNe : N.e = 1 := rfl
  have ep : 1 / P.m * p = p / P.m := by ring
  have eq : 1 / P.m * q = q / P.m := by ring
  have eR : massScale (1 / R.m) { R with e := 1 } =
      { N with mγ := p / P.m, Λ := q / P.m } := by
    unfold R N massScale
    rw [ep, eq]
  have hk := kerT_normalize_of_ne_X (repBClass_mem i) hX R hm (four_le_repBSlot i) hp hq hT
  dsimp only at hk
  rw [eR] at hk
  rw [uBDT_normalized_real P he hm.ne']
  have h := uBDT_normalized_real N (by rw [hNe]; exact one_ne_zero)
    (by rw [hN]; exact one_ne_zero) i (p / P.m) (q / P.m) T
  have eDen : 4 * N.e ^ 5 * N.m ^ 5 = 4 := by rw [hN, hNe, one_pow, mul_one, mul_one]
  have ePow : N.e ^ 6 = 1 := by rw [hNe, one_pow]
  rw [ePow, div_one, eDen] at h
  rw [h, hk]
  simp only [R, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.mul_im,
    Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero]
  field_simp

end QED.ChainProof.SetCUnitM

end
