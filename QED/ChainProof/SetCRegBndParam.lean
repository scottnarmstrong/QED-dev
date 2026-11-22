/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMPauli
public import QED.ChainProof.SetCRegBndChain
public import QED.ChainProof.SetCRegXApply

/-!
# Integrability of the Pauli coefficient integrand at positive masses

The refined numerator bounds in `QED/TwoLoop/PauliZeroExplicitPiece.lean` give
integrable interpolation coefficients. The positive lower bound on the second
Symanzik function then gives absolute integrability of the Pauli integrand.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory Polynomial
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.ChainProof.SetCUnit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop

variable {r : ℕ}

/-- At positive Symanzik floor the explicit second-order integrand is integrable. -/
theorem integrableOn_secondCoeff_projNum (C : CurveData) {J : Type*} [Fintype J] {D n r Dω : ℕ}
    (F : ℝ → J → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hFpoly : ∀ j, IsUPoly D fun ℓ u => wt u ^ n * F u j ℓ)
    (hFq : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, ∃ Q : LoopQuartic, Q.eval = F u j)
    (hFB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ j, RefinedBound C.α C.E 4 (F u j))
    (ω : ℝ → J → ℂ) (hω : ∀ j, IsUPoly (ι := Fin C.m → ℝ) Dω fun _ u => wt u ^ r * ω u j)
    (hω0 : ∀ Y : J → ℂ, ∑ j, ω 0 j * Y j = 0) :
    IntegrableOn (fun x => secondCoeff (projNum C F ω x) /
      (C.vfun x 0 : ℂ) ^ (C.m - 3)) (simplexSet C.m) := by
  classical
  have hnode : ∀ k : Fin (D + 1), node D k ∈ Ioo (-1 : ℝ) 1 := node_mem D
  choose Qk hQk using fun j k => hFq (node D k) (hnode k) j
  have hBk : ∀ j k, RefinedBound C.α C.E 4 (Qk j k).eval := fun j k => by
    rw [hQk]
    exact hFB _ (hnode k) j
  set A : (Fin C.m → ℝ) → ℝ → ℂ := fun x u => ∑ j, (wt u ^ r * ω u j) * (-((π : ℂ) ^ 4) *
    ∑ k, (wt (node D k) ^ n * (lbasis D k).eval (u : ℂ)) *
      (wt u ^ 4 * paramNum (Qk j k) C.α (C.mom u) C.M x)) with hA_def
  have hA : IsUPoly (Dω + (D + 8)) A :=
    IsUPoly.sum _ fun j _ => (hω j).mul (IsUPoly.const_mul _ (IsUPoly.sum _ fun k _ =>
      ((isUPoly_lbasis D k).const_mul _).mul (isUPoly_paramNum (Qk j k) C.α C.M C.mom C.hmom)))
  have hAi : ∀ t, Integrable (fun x => A x (node (Dω + (D + 8)) t))
      (volume.restrict (simplexSet C.m)) := fun t => by
    refine integrable_finsetSum _ fun j _ => Integrable.const_mul ?_ _
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun k _ => Integrable.const_mul ?_ _
    exact (integrableOn_paramNum (Qk j k) C.α _ C.M C.hm C.hcrit (hBk j k)).const_mul _
  have hA0 : ∀ x, A x 0 = 0 := fun x => by
    simp only [hA_def, wt_zero, one_pow, one_mul]
    exact hω0 _
  -- the numerator `A` is `(1 - u²)^{r+n+4}` times the canonical projected numerator
  have hAN : ∀ x, ∀ u ∈ Ioo (-1 : ℝ) 1, A x u = wt u ^ (r + n + 4) * projNum C F ω x u := by
    intro x u hu
    have hw : wt u ^ n ≠ 0 := pow_ne_zero n (wt_ne_zero hu)
    simp only [hA_def, projNum]
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [paramNumOf_eq (eval_jointQuartic (hFpoly j) (hQk j) hu), jointQuartic, paramNum_qsum]
    have e1 : ∑ k, wt (node D k) ^ n * (lbasis D k).eval (u : ℂ) *
        (wt u ^ 4 * paramNum (Qk j k) C.α (C.mom u) C.M x) =
        wt u ^ 4 * ∑ k, wt (node D k) ^ n * (lbasis D k).eval (u : ℂ) *
          paramNum (Qk j k) C.α (C.mom u) C.M x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k, lam D n u k * paramNum (Qk j k) C.α (C.mom u) C.M x =
        (wt u ^ n)⁻¹ * ∑ k, wt (node D k) ^ n * (lbasis D k).eval (u : ℂ) *
          paramNum (Qk j k) C.α (C.mom u) C.M x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp only [lam]; ring
    rw [e1, e2]
    field_simp
    ring
  have hcoeff (x : Fin C.m → ℝ) :
      secondCoeff (projNum C F ω x) = (interp (Dω + (D + 8)) A x).coeff 2 := by
    have h0 : (interp (Dω + (D + 8)) A x).coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero, ← ofReal_zero, ← hA.eq_interp x 0 ⟨by norm_num, by norm_num⟩,
        hA0, ofReal_zero]
    have hg : ∀ u ∈ Ioo (-1 : ℝ) 1, wt u ^ (r + n + 4) * projNum C F ω x u =
        (interp (Dω + (D + 8)) A x).eval (u : ℂ) := fun u hu => by
      rw [← hAN x u hu, hA.eq_interp x u hu]
    exact secondCoeff_eq_coeff hg h0
  simp_rw [hcoeff]
  have hI := integrable_interp_coeff hAi 2
  refine Integrable.mono' (hI.norm.div_const (C.c ^ (C.m - 3))) ?_ ?_
  · exact hI.aestronglyMeasurable.div₀
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable
        (C.measurable_vfun 0).aestronglyMeasurable).pow _)
  · filter_upwards [C.ae_le_vfun] with x hx
    have hcx := hx 0 (by norm_num)
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (C.hc.trans_le hcx)]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos C.hc _)
      (pow_le_pow_left₀ C.hc.le hcx _)

section Pauli

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
include hc hm hs hμ₀ hM

/-- The multi-denominator Pauli integrand is integrable at strictly positive masses. -/
theorem integrableOn_unitMPauliZeroIntegrand {κ cs : Fin r → ℝ} (hX : ExtraGe μ₀ κ cs) :
    let M := unitMMasses P.m a A b B cs
    IntegrableOn (fun x => secondCoeff (unitMPauliNum c P s κ M x) /
      (unitMV0 c P s κ M x : ℂ) ^ (r + 4)) (simplexSet (r + 7)) := by
  dsimp only
  have hF : ∀ (p' : Fin 4 → ℝ) (j : Idx),
      (fun ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) p' j.1 ℓ) j.2.1 j.2.2) =
        fun ℓ => twoLoopNorm * classNumeratorE c P (fun _ => p') (fun _ => restMomentum P.m)
          (fun _ => p' - restMomentum P.m) (fun _ => j.2.1) (fun _ => j.2.2) (fun _ => j.1) ℓ :=
    fun p' j => funext fun ℓ => by simp only [Matrix.smul_apply, classNumM, Matrix.of_apply,
      smul_eq_mul]
  have hB : ∀ (p' : Fin 4 → ℝ) (j : Idx), RefinedBound (unitMMatrix c s κ) (unitME r) 4
      (fun ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) p' j.1 ℓ) j.2.1 j.2.2) :=
    fun p' j => by
      rw [hF]
      exact refinedBound_unitM hc P s κ _ _ _ _ _
  have hI := integrableOn_secondCoeff_projNum (unitMCurve hc P hm hs hμ₀ hM hX) (J := Idx) (D := 8)
    (n := 4) (r := 4) (Dω := 8)
    (fun u j ℓ => (twoLoopNorm • classNumM c P (restMomentum P.m) (curveMomentum P.m u) j.1 ℓ)
      j.2.1 j.2.2)
    (fun j => by
      have h := isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 4)
        (G := fun ℓ y => twoLoopNorm * classNumeratorE c P (fun _ => y 0)
          (fun _ => restMomentum P.m) (fun _ => y 0 - restMomentum P.m) (fun _ => j.2.1)
          (fun _ => j.2.2) (fun _ => j.1) ℓ)
        (fun ℓ => (isLoopPoly_classNumeratorE_out hc P _ _ _ _ ℓ).const_mul _)
        (ℓ := fun _ u => fun _ => curveMomentum P.m u) fun _ ν => isUPoly_curveMomentum P.m ν
      refine h.congr fun ℓ u _ => ?_
      simp only [Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul])
    (fun u _ j => by
      rw [hF]
      exact ((isLoopPoly_classNumeratorE hc P _ _ _ _ _ _).const_mul _).exists_loopQuartic)
    (fun u _ j => hB _ j)
    (fun u j => pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2)
    (fun j => isUPoly_pauliWt P.m j) (sum_pauliWt_zero P.m)
  simp only [CurveData.vfun, unitMCurve, curveMomentum_zero] at hI
  exact hI

end Pauli

open QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.UnitSCGraph

private theorem im_factorial_resolvents (r : ℕ) (A B : ℂ) {V : ℝ} (hV : V ≠ 0) :
    ((((r + 3).factorial : ℂ) / 6 * A + ((r + 2).factorial : ℂ) / 2 * B * (V : ℂ)) /
      (V : ℂ) ^ (r + 4)).im = factorialResolventPair (r + 2) (A.im / 6) (-B.im / 2) V := by
  have hVc : (V : ℂ) ≠ 0 := ofReal_ne_zero.mpr hV
  have h :
      (((r + 3).factorial : ℂ) / 6 * A +
        ((r + 2).factorial : ℂ) / 2 * B * (V : ℂ)) / (V : ℂ) ^ (r + 4) =
      A * ((((r + 3).factorial : ℝ) / 6 / V ^ (r + 4) : ℝ) : ℂ) +
        B * ((((r + 2).factorial : ℝ) / 2 / V ^ (r + 3) : ℝ) : ℂ) := by
    push_cast
    rw [show r + 4 = (r + 3) + 1 by omega, pow_succ]
    field_simp
  rw [h]
  simp only [add_im, mul_im, ofReal_im, mul_zero, ofReal_re, zero_add, factorialResolventPair,
    show r + 2 + 1 = r + 3 by omega, show r + 2 + 2 = r + 4 by omega]
  ring

private theorem unitMPauliZero_im_eq_pair {c : Class5} (hc : c ∈ openClasses)
    (P : Params) (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {cs : Fin r → ℝ} (hcs : ∀ j, μ₀ ≤ cs j) (F G : (Fin 8 → ℝ) → ℂ)
    (hcoef : ∀ x : Fin (r + 7) → ℝ,
      symanzikU (castLoopMatrix (class5LoopMatrixPV c)) (groupExtra s (simplexPoint x)) ≠ 0 →
      let M := unitMMasses P.m a A b B cs
      let w := groupExtra s (simplexPoint x)
      secondCoeff (unitMPauliNum c P s (fun _ => 1) M x) =
        ((r + 3).factorial : ℂ) / 6 * F w +
          ((r + 2).factorial : ℂ) / 2 * G w * (unitMV0 c P s (fun _ => 1) M x : ℂ)) :
    let M := unitMMasses P.m a A b B cs
    let f := fun x : Fin (r + 7) → ℝ =>
      factorialResolventPair (r + 2) ((F (groupExtra s (simplexPoint x))).im / 6)
        (-(G (groupExtra s (simplexPoint x))).im / 2) (unitMV0 c P s (fun _ => 1) M x)
    IntegrableOn f (simplexSet (r + 7)) ∧
      (unitMPauliZero c P s (fun _ => 1) M).im = ∫ x in simplexSet (r + 7), f x := by
  intro M f
  have hX : ExtraGe μ₀ (fun _ : Fin r => 1) cs := fun j => ⟨one_pos, le_rfl, hcs j⟩
  let C := unitMCurve hc P hm hs hμ₀ hM hX
  let g := fun x : Fin (r + 7) → ℝ => secondCoeff (unitMPauliNum c P s (fun _ => 1) M x) /
    (unitMV0 c P s (fun _ => 1) M x : ℂ) ^ (r + 4)
  have hI : IntegrableOn g (simplexSet (r + 7)) :=
    integrableOn_unitMPauliZeroIntegrand hc P hm hs hμ₀ hM hX
  have hUad := ae_posDef C.α (by have := C.hm; omega) C.hspan
  have he : (fun x => (g x).im) =ᵐ[volume.restrict (simplexSet (r + 7))] f := by
    filter_upwards [hUad, C.ae_le_vfun] with x hx hV
    have hU : symanzikU (unitMMatrix c s (fun _ : Fin r => 1)) (simplexPoint x) ≠ 0 :=
      hx.2.det_pos.ne'
    rw [symanzikU_unitM_group] at hU
    have hv := C.hc.trans_le (hV 0 (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1))
    have hv' : 0 < unitMV0 c P s (fun _ => 1) M x := by
      simpa only [C, M, unitMCurve, CurveData.vfun, unitMV0, curveMomentum_zero] using hv
    dsimp only [g, f]
    rw [hcoef x hU]
    exact im_factorial_resolvents r _ _ hv'.ne'
  refine ⟨(Complex.imCLM.integrable_comp hI).congr he, ?_⟩
  change (∫ x in simplexSet (r + 7), g x).im = _
  exact (integral_im hI).symm.trans (integral_congr_ae he)

/-- The imaginary Pauli value of the `L` unit as an integrable pair of resolvents. -/
theorem unitMPauliZero_L_im_eq_pair {P : Params} (hm : P.m = 1) (he : P.e = 1)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {cs : Fin r → ℝ} (hcs : ∀ j, μ₀ ≤ cs j) :
    let M := unitMMasses P.m a A b B cs
    let f := fun x : Fin (r + 7) → ℝ =>
      let w := groupExtra s (simplexPoint x)
      factorialResolventPair (r + 2) ((secondCoeff (ladderT1 P w)).im / 6)
        (-(secondCoeff (ladderT2 P w)).im / 2)
        (unitMV0 .L P s (fun _ => 1) M x)
    IntegrableOn f (simplexSet (r + 7)) ∧
      (unitMPauliZero .L P s (fun _ => 1) M).im = ∫ x in simplexSet (r + 7), f x := by
  apply unitMPauliZero_im_eq_pair (c := .L) (by decide) P (hm ▸ one_pos)
    hs hμ₀ hM hcs (fun w => secondCoeff (ladderT1 P w))
      (fun w => secondCoeff (ladderT2 P w))
  intro x hU
  apply secondCoeff_unitMPauliNum_L hm he s _ x
  rwa [← symanzikU_ladder]

/-- The imaginary Pauli value of the `Sp` unit as an integrable pair of resolvents. -/
theorem unitMPauliZero_Sp_im_eq_pair {P : Params} (hm : P.m = 1) (he : P.e = 1)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {cs : Fin r → ℝ} (hcs : ∀ j, μ₀ ≤ cs j) :
    let M := unitMMasses P.m a A b B cs
    let f := fun x : Fin (r + 7) → ℝ =>
      let w := groupExtra s (simplexPoint x)
      factorialResolventPair (r + 2) ((secondCoeff (classT1 .Sp permSp P w)).im / 6)
        (-(secondCoeff (classT2 .Sp permSp P w)).im / 2)
        (unitMV0 .Sp P s (fun _ => 1) M x)
    IntegrableOn f (simplexSet (r + 7)) ∧
      (unitMPauliZero .Sp P s (fun _ => 1) M).im = ∫ x in simplexSet (r + 7), f x := by
  apply unitMPauliZero_im_eq_pair (c := .Sp) (by decide) P (hm ▸ one_pos)
    hs hμ₀ hM hcs (fun w => secondCoeff (classT1 .Sp permSp P w))
      (fun w => secondCoeff (classT2 .Sp permSp P w))
  intro x hU
  apply secondCoeff_unitMPauliNum_Sp hm he s _ x
  rwa [← symanzikU_Sp]

/-- The imaginary Pauli value of the `Sm` unit as an integrable pair of resolvents. -/
theorem unitMPauliZero_Sm_im_eq_pair {P : Params} (hm : P.m = 1) (he : P.e = 1)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {cs : Fin r → ℝ} (hcs : ∀ j, μ₀ ≤ cs j) :
    let M := unitMMasses P.m a A b B cs
    let f := fun x : Fin (r + 7) → ℝ =>
      let w := groupExtra s (simplexPoint x)
      factorialResolventPair (r + 2) ((secondCoeff (classT1 .Sm permSm P w)).im / 6)
        (-(secondCoeff (classT2 .Sm permSm P w)).im / 2)
        (unitMV0 .Sm P s (fun _ => 1) M x)
    IntegrableOn f (simplexSet (r + 7)) ∧
      (unitMPauliZero .Sm P s (fun _ => 1) M).im = ∫ x in simplexSet (r + 7), f x := by
  apply unitMPauliZero_im_eq_pair (c := .Sm) (by decide) P (hm ▸ one_pos)
    hs hμ₀ hM hcs (fun w => secondCoeff (classT1 .Sm permSm P w))
      (fun w => secondCoeff (classT2 .Sm permSm P w))
  intro x hU
  apply secondCoeff_unitMPauliNum_Sm hm he s _ x
  rwa [← symanzikU_Sm]

/-- The imaginary Pauli value of the `Cp` unit as an integrable pair of resolvents. -/
theorem unitMPauliZero_Cp_im_eq_pair {P : Params} (hm : P.m = 1) (he : P.e = 1)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {cs : Fin r → ℝ} (hcs : ∀ j, μ₀ ≤ cs j) :
    let M := unitMMasses P.m a A b B cs
    let f := fun x : Fin (r + 7) → ℝ =>
      let w := groupExtra s (simplexPoint x)
      factorialResolventPair (r + 2) ((secondCoeff (classT1 .Cp permCp P w)).im / 6)
        (-(secondCoeff (classT2 .Cp permCp P w)).im / 2)
        (unitMV0 .Cp P s (fun _ => 1) M x)
    IntegrableOn f (simplexSet (r + 7)) ∧
      (unitMPauliZero .Cp P s (fun _ => 1) M).im = ∫ x in simplexSet (r + 7), f x := by
  apply unitMPauliZero_im_eq_pair (c := .Cp) (by decide) P (hm ▸ one_pos)
    hs hμ₀ hM hcs (fun w => secondCoeff (classT1 .Cp permCp P w))
      (fun w => secondCoeff (classT2 .Cp permCp P w))
  intro x hU
  apply secondCoeff_unitMPauliNum_Cp hm he s _ x
  rwa [← symanzikU_Cp]

/-- The imaginary Pauli value of the `Cm` unit as an integrable pair of resolvents. -/
theorem unitMPauliZero_Cm_im_eq_pair {P : Params} (hm : P.m = 1) (he : P.e = 1)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ))
    {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {cs : Fin r → ℝ} (hcs : ∀ j, μ₀ ≤ cs j) :
    let M := unitMMasses P.m a A b B cs
    let f := fun x : Fin (r + 7) → ℝ =>
      let w := groupExtra s (simplexPoint x)
      factorialResolventPair (r + 2) ((secondCoeff (classT1 .Cm permCm P w)).im / 6)
        (-(secondCoeff (classT2 .Cm permCm P w)).im / 2)
        (unitMV0 .Cm P s (fun _ => 1) M x)
    IntegrableOn f (simplexSet (r + 7)) ∧
      (unitMPauliZero .Cm P s (fun _ => 1) M).im = ∫ x in simplexSet (r + 7), f x := by
  apply unitMPauliZero_im_eq_pair (c := .Cm) (by decide) P (hm ▸ one_pos)
    hs hμ₀ hM hcs (fun w => secondCoeff (classT1 .Cm permCm P w))
      (fun w => secondCoeff (classT2 .Cm permCm P w))
  intro x hU
  apply secondCoeff_unitMPauliNum_Cm hm he s _ x
  rwa [← symanzikU_Cm]

end QED.ChainProof.SetCUnitM

end
