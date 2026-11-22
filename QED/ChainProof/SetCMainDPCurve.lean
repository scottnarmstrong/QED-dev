/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainDKLink
public import QED.ChainProof.SetCPauliAtCB

/-!
# Set (c), the `δ₃` classes: the terms of the longitudinal part along the curve

Helper level for the Pauli limits of the 24 classes `repD i t`
(`QED.ChainProof.SetCPauli.SetCClassPauli mainFam P₀ (.inr (i, t))`). The limit of the
longitudinal part is a combination, with coefficients independent of `p`, `p'`, of parametric
values of terms `kNum` on the ten-line unit with some electron lines deleted
(`QED.ChainProof.SetCMain.hasLimJ_dKUnit_int`, `hasLimJ_dKUnit_ext`). Along the curve
`p'(u)`, `p = (m, 0, 0, 0)`, the terms are polynomials in `p'` of degree at most six, and the
Phase 4 explicit second-order limit (`QED.TwoLoop.PauliZeroExplicit.tendsto_piece_explicit`)
applies term by term.

* `isLoopPolyMat_openChain_out`, `isLoopPolyMat_kOpen_out`: the degree of a chain in any
  variables;
* `isLoopAffine_unitM_out`: the line momenta of the unit are affine in `p'`;
  **`isLoopPoly_kNum_out`**: a term is a polynomial of degree at most six in `p'`;
* **`dkCurve`**: the parametric data `dkData` along the curve, with
  `(dkCurve …).toParamData hu = dkData …` definitionally;
* `dkF`, `pauliSum`: a term along the curve and the Pauli-weighted sum of entries;
* **`tendsto_evenQuot_dkTerm`**: the even quotient of the Pauli-weighted parametric values of a
  term along the curve tends to `pauliCurveZero (dkCurve …) m (dkF …)`.
-/

@[expose] public section

open Complex Matrix Filter Topology Set
open QED.Dirac (gamma slash reflectMatrix)

namespace QED.ChainProof.SetCMain

open QED.TwoLoop.Enumeration QED.ChainProof.SetCUnitM QED.TwoLoop.LimitCovariance
open QED.ChainProof.SetCUnit (unitConst unitConst_pos)
open QED.WickModel (Params)
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.ChainProof.SetCPauli (pauliCurveZero)
open QED.TwoLoop.Bridge (electronNumerator extMomenta IsLoopPoly IsLoopPolyMat IsLoopAffine
  pvMomentaE)
open QED.TwoLoop.CountertermLimit (isLoopPolyMat_mono isLoopPolyMat_neg)
open QED.Integration.TwoLoop (lineMomentum castLoopMatrix pvLines RefinedBound
  NoSubdivergenceRefined)

/-! ### Degrees in any variables -/

section Degree

variable {L : ℕ} (π : Equiv.Perm (Fin 5)) (μ : Fin 4)

/-- The degree of an open chain, in any variables. -/
theorem isLoopPolyMat_openChain_out
    {G : Fin 5 → (Fin L → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    {E : Fin 4 → (Fin L → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} {g : Fin 5 → ℕ} {e : Fin 4 → ℕ}
    (hG : ∀ t, IsLoopPolyMat L (g t) (G t)) (hE : ∀ j, IsLoopPolyMat L (e j) (E j)) {k : ℕ}
    (hk : ∑ t, g t + ∑ j, e j ≤ k) :
    IsLoopPolyMat L k fun y => openChain (fun t => G t y) (fun j => E j y) := by
  refine isLoopPolyMat_mono ((((((((((hG 4).mul (hE 3)).mul (hG 3)).mul (hE 2)).mul (hG 2)).mul
    (hE 1)).mul (hG 1)).mul (hE 0)).mul (hG 0))) ?_
  simp only [Fin.sum_univ_five, Fin.sum_univ_four] at hk
  omega

/-- The degree of `kOpen`, in any variables. -/
theorem isLoopPolyMat_kOpen_out {X Y : (Fin L → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    {E : Fin 4 → (Fin L → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} {dX dY k : ℕ} {dE : Fin 4 → ℕ}
    (hX : IsLoopPolyMat L dX X) (hY : IsLoopPolyMat L dY Y)
    (hE : ∀ j, IsLoopPolyMat L (dE j) (E j)) (hk : dX + dY + ∑ j, dE j ≤ k) :
    IsLoopPolyMat L k fun y => kOpen π μ (X y) (Y y) (fun j => E j y) := by
  unfold kOpen
  intro a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine IsLoopPoly.sum _ fun z _ => IsLoopPoly.const_mul _ ?_
  have hW : ∀ t, IsLoopPolyMat L ((![0, dX, dY, 0, 0] : Fin 5 → ℕ) t)
      (fun y => (![gamma μ, X y, Y y, gamma z, gamma z] : Fin 5 → _) t) := fun t => by
    fin_cases t
    · exact IsLoopPolyMat.const _
    · exact hX
    · exact hY
    · exact IsLoopPolyMat.const _
    · exact IsLoopPolyMat.const _
  exact isLoopPolyMat_openChain_out (k := k)
    (G := fun t y => (![gamma μ, X y, Y y, gamma z, gamma z] : Fin 5 → _) (π.symm t))
    (g := fun t => (![0, dX, dY, 0, 0] : Fin 5 → ℕ) (π.symm t)) (fun t => hW _) hE (by
      rw [Equiv.sum_comp π.symm (![0, dX, dY, 0, 0] : Fin 5 → ℕ)]
      simp only [Fin.sum_univ_five, Matrix.cons_val]
      omega) a b

end Degree

/-! ### The terms as polynomials in `p'` -/

section Out

variable (c : Class5) (σ : Fin 8) (m : ℝ) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)

/-- A line momentum of the unit is affine in `p'`. -/
theorem isLoopAffine_unitM_out (i : Fin 10) :
    IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ =>
      lineMomentum (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)) (unitMMomenta c σ ![1, 1] p (y 0)) i
        ℓ := by
  rcases QED.TwoLoop.PauliZeroLimit.extMomenta_cases c p (pvLines (mLine σ i)) with h | h | h
  · refine ⟨![0], fun ν => ∑ s, unitMMatrix c σ ![1, 1] i s * ℓ s ν + mScale ![1, 1] i * p ν,
      fun y => ?_⟩
    funext ν
    simp [lineMomentum, unitMMomenta, pvMomentaE, h]
  · refine ⟨![mScale ![1, 1] i], fun ν => ∑ s, unitMMatrix c σ ![1, 1] i s * ℓ s ν,
      fun y => ?_⟩
    funext ν
    simp [lineMomentum, unitMMomenta, pvMomentaE, h]
    ring
  · refine ⟨![0], fun ν => ∑ s, unitMMatrix c σ ![1, 1] i s * ℓ s ν, fun y => ?_⟩
    funext ν
    simp [lineMomentum, unitMMomenta, pvMomentaE, h]

theorem isLoopPolyMat_kSlotM_out (X : KSlot) :
    IsLoopPolyMat 1 1 fun y : Fin 1 → Fin 4 → ℝ => kSlotM c σ m p (y 0) X ℓ := by
  cases X
  · exact isLoopPolyMat_mono (IsLoopPolyMat.const _) (by norm_num)
  · have e : (fun y : Fin 1 → Fin 4 → ℝ => kSlotM c σ m p (y 0) .q ℓ) =
        fun y => -electronNumerator 0 (kQ c σ p (y 0) ℓ) := funext fun y => slash_eq_neg _
    rw [e]
    exact isLoopPolyMat_neg ((isLoopAffine_unitM_out c σ p ℓ 8).isLoopPolyMat_electronNumerator 0)
  · have h := QED.TwoLoop.CountertermLimit.isLoopPolyMat_add
      (isLoopPolyMat_mono (IsLoopPolyMat.const (L := 1) ((2 * (m : ℂ)) • 1)) (Nat.zero_le 1))
      (isLoopPolyMat_neg (IsLoopAffine.isLoopPolyMat_electronNumerator
        (F := fun y : Fin 1 → Fin 4 → ℝ => y 0) ⟨![1], 0, fun y => by simp⟩ m))
    refine (congrArg (IsLoopPolyMat 1 1) (funext fun y => ?_)).mp h
    simp [kSlotM, sub_eq_add_neg]
  · exact isLoopPolyMat_mono (IsLoopPolyMat.const _) (by norm_num)

theorem isLoopPolyMat_kEK_out (K : Finset (Fin 4)) (j : Fin 4) :
    IsLoopPolyMat 1 1 fun y : Fin 1 → Fin 4 → ℝ => kEK c σ m p (y 0) K j ℓ := by
  by_cases h : j ∈ K
  · have e : (fun y : Fin 1 → Fin 4 → ℝ => kEK c σ m p (y 0) K j ℓ) =
        fun y => electronNumerator m (kK c σ p (y 0) j ℓ) := funext fun y => by simp [kEK, h]
    rw [e]
    exact (isLoopAffine_unitM_out c σ p ℓ (eIdx j)).isLoopPolyMat_electronNumerator m
  · have e : (fun y : Fin 1 → Fin 4 → ℝ => kEK c σ m p (y 0) K j ℓ) = fun _ => 1 :=
      funext fun y => by simp [kEK, h]
    rw [e]
    exact isLoopPolyMat_mono (IsLoopPolyMat.const _) (by norm_num)

/-- **A term is a polynomial of degree six in `p'`.** -/
theorem isLoopPoly_kNum_out (π : Equiv.Perm (Fin 5)) (X Y : KSlot) (K : Finset (Fin 4))
    (μ a b : Fin 4) :
    IsLoopPoly 1 6 fun y : Fin 1 → Fin 4 → ℝ => kNum π c σ m p (y 0) X Y K μ ℓ a b :=
  isLoopPolyMat_kOpen_out π μ (isLoopPolyMat_kSlotM_out c σ m p ℓ X)
    (isLoopPolyMat_kSlotM_out c σ m p ℓ Y) (isLoopPolyMat_kEK_out c σ m p ℓ K)
    (by simp) a b

end Out

/-! ### The data along the curve -/

section Curve

variable (c : Class5) (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses) (σ : Fin 8)
  (hs : 4 ≤ (σ : ℕ)) (R : Params) (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)

/-- **The parametric data `dkData` along the curve** `p'(u)`, `p = (m, 0, 0, 0)`. -/
noncomputable def dkCurve {k : ℕ} (ι : Fin (k + 1) → Fin 10) (hk : 7 ≤ k)
    (E : Finset (Fin (k + 1)))
    (hcrit : NoSubdivergenceRefined 2 E (castLoopMatrix fun i => unitZ c σ (ι i))) :
    CurveData where
  m := k
  α := fun i => unitMMatrix c σ ![1, 1] (ι i)
  mom u := fun i => unitMMomenta c σ ![1, 1] (restMomentum R.m) (curveMomentum R.m u) (ι i)
  M := fun i => dkMasses R (ι i)
  E := E
  hm := hk
  hcrit := by rw [unitMMatrix_comp_eq]; exact hcrit
  c := unitConst R.m R.mγ
  hc := unitConst_pos hm hγ
  hV := fun u hu => (dkData c hc σ hs R hm hγ hγΛ (restMomentum R.m) (curveMomentum R.m u)
    (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
    ((dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu) ι hk E hcrit).hV
  hmom := fun i μ => by
    have h := isUPoly_ext_curve (ι := Fin k → ℝ) R.m
      (fun p' => extMomenta c (restMomentum R.m) p' (pvLines (mLine σ (ι i)))) (by
        rcases extMomenta_cases c (restMomentum R.m) (pvLines (mLine σ (ι i))) with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)) μ
    refine (h.const_mul fun _ => ((mScale (![1, 1] : Fin 2 → ℝ) (ι i) : ℝ) : ℂ)).congr
      fun _ u _ => ?_
    simp only [unitMMomenta, pvMomentaE, Pi.smul_apply, smul_eq_mul, ofReal_mul]
    ring
  hVeven := fun u z => by
    have h := QED.TwoLoop.ReflCovariance.isSpinLift_reflect (K := axisOne)
      (by rw [dot_axisOne]; exact one_ne_zero)
    have e := QED.TwoLoop.ReflCovariance.symanzikV_map h (fun i => unitMMatrix c σ ![1, 1] (ι i))
      (fun i => unitMMomenta c σ ![1, 1] (restMomentum R.m) (curveMomentum R.m u) (ι i))
      (fun i => dkMasses R (ι i)) z
    have e2 : (fun i => reflectMatrix axisOne *ᵥ
        unitMMomenta c σ ![1, 1] (restMomentum R.m) (curveMomentum R.m u) (ι i)) =
        fun i => unitMMomenta c σ ![1, 1] (restMomentum R.m) (curveMomentum R.m (-u)) (ι i) := by
      rw [← reflectMatrix_curveMomentum, ← reflectMatrix_restMomentum (m := R.m),
        unitMMomenta_map]
      simp only [reflectMatrix_restMomentum]
    rw [e2] at e
    exact e

variable {c hc σ hs R hm hγ hγΛ}

theorem dkCurve_toParamData {k : ℕ} (ι : Fin (k + 1) → Fin 10) (hk : 7 ≤ k)
    (E : Finset (Fin (k + 1)))
    (hcrit : NoSubdivergenceRefined 2 E (castLoopMatrix fun i => unitZ c σ (ι i))) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    (dkCurve c hc σ hs R hm hγ hγΛ ι hk E hcrit).toParamData hu =
      dkData c hc σ hs R hm hγ hγΛ (restMomentum R.m) (curveMomentum R.m u)
        (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
        ((dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu) ι hk E hcrit :=
  rfl

end Curve

/-! ### The even quotient of a term -/

section Term

variable (π : Equiv.Perm (Fin 5)) (c : Class5) (σ : Fin 8) (R : Params) (X Y : KSlot)
  (K : Finset (Fin 4))

/-- A term along the curve, at the entry `(μ, α, β)`. -/
noncomputable def dkF (u : ℝ) (x : Idx) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  kNum π c σ R.m (restMomentum R.m) (curveMomentum R.m u) X Y K x.1 ℓ x.2.1 x.2.2

/-- The Pauli-weighted sum of entries along the curve. -/
noncomputable def pauliSum (m : ℝ) (v : ℝ → Idx → ℂ) (u : ℝ) : ℂ :=
  ∑ x : Idx, pauliWt m (curveMomentum m u) (restMomentum m) x.1 x.2.1 x.2.2 * v u x

variable {c} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses) (hs : 4 ≤ (σ : ℕ))
  {R} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) {X Y K}
  (hXY : Disjoint (kSlotS X) (kSlotS Y)) (hd : kSlotD X + kSlotD Y + K.card ≤ 4)
include hXY hd

/-- **The even quotient of the parametric values of a term along the curve** tends to the
Phase 4 value `pauliCurveZero` of the term on the data `dkCurve`. -/
theorem tendsto_evenQuot_dkTerm {k : ℕ} (ι : Fin (k + 1) → Fin 10) (hk : 7 ≤ k)
    (hι : Function.Injective ι) (hS : ∀ x ∈ kSet X Y K, ∃ a, ι a = x)
    (hcrit : NoSubdivergenceRefined 2 (Finset.univ.filter fun a => ι a ∈ kSet X Y K)
      (castLoopMatrix fun a => unitZ c σ (ι a)))
    (v : ℝ → Idx → ℂ)
    (hv : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) (x : Idx),
      IsParamValue (dkData c hc σ hs R hm hγ hγΛ (restMomentum R.m) (curveMomentum R.m u)
        (dot_restMomentum (m := R.m)) (dot_curveMomentum R.m hu)
        ((dot_curveMomentum_sub R.m hu).symm ▸ curveQ_nonneg R.m hu) ι hk _ hcrit)
        (dkF π c σ R X Y K u x) (v u x)) :
    Tendsto (evenQuot (pauliSum R.m v)) (𝓝[≠] 0)
      (𝓝 (pauliCurveZero (dkCurve c hc σ hs R hm hγ hγΛ ι hk _ hcrit) R.m
        (dkF π c σ R X Y K))) := by
  have hP : ∀ x : Idx, IsUPoly 12 fun ℓ u => wt u ^ 6 * dkF π c σ R X Y K u x ℓ := fun x =>
    isUPoly_eval_of_isLoopPoly' (ι := Fin 2 → Fin 4 → ℝ) (n := 6)
      (G := fun ℓ y => kNum π c σ R.m (restMomentum R.m) (y 0) X Y K x.1 ℓ x.2.1 x.2.2)
      (fun ℓ => isLoopPoly_kNum_out c σ R.m _ ℓ π X Y K x.1 x.2.1 x.2.2)
      (ℓ := fun _ u => fun _ => curveMomentum R.m u) fun _ ν => isUPoly_curveMomentum R.m ν
  have hQ : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ x : Idx,
      ∃ Q : QED.Integration.TwoLoop.LoopQuartic, Q.eval = dkF π c σ R X Y K u x :=
    fun u _ x => (isLoopPolyMat_kNum π c σ R.m _ _ X Y K x.1 hd x.2.1 x.2.2).exists_loopQuartic
  have hB : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ x : Idx,
      RefinedBound (fun a => unitMMatrix c σ (![1, 1] : Fin 2 → ℝ) (ι a))
        (Finset.univ.filter fun a => ι a ∈ kSet X Y K) 4 (dkF π c σ R X Y K u x) :=
    fun u _ x => RefinedBound.comp_filter (F := dkF π c σ R X Y K u x) ι hι hS
      (refinedBoundMat_kNum π c σ R.m (restMomentum R.m) (curveMomentum R.m u) X Y K x.1 hXY hd
        x.2.1 x.2.2)
  have hv' : ∀ u (hu : u ∈ Ioo (-1 : ℝ) 1) (x : Idx),
      IsParamValue ((dkCurve c hc σ hs R hm hγ hγΛ ι hk _ hcrit).toParamData hu)
        (dkF π c σ R X Y K u x) (v u x) := hv
  exact tendsto_piece_explicit (dkCurve c hc σ hs R hm hγ hγΛ ι hk _ hcrit) (J := Idx) (D := 12)
    (n := 6) (r := 4) (Dω := 8)
    (dkF π c σ R X Y K) hP hQ hB v hv'
    (fun u (x : Idx) => pauliWt R.m (curveMomentum R.m u) (restMomentum R.m) x.1 x.2.1 x.2.2)
    (fun x => isUPoly_pauliWt R.m x) (sum_pauliWt_zero R.m)

end Term

end QED.ChainProof.SetCMain

end
