/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainDKTerm

/-!
# Set (c), the `δ₃` classes: the limits of the terms of the longitudinal part

Helper level for the open links `QED.ChainProof.SetCMain.DKLimLink`, `DKCovLink`. A term
`kNum` (`QED/ChainProof/SetCMainDKTerm.lean`) over the ten denominators of the unit, times the
scalars `k_d² + m²` of at most two of its deleted electron lines `d`, has a limit as `ε → 0⁺`:
the parametric value of the term on the unit with the lines `d` deleted.

* `dkD`: the parametric data `dkData` with the numerator lines of a term;
* `exists_paramValue_kNum`; **`hasLimJ_kNum0`**, **`hasLimJ_kNum1`**, **`hasLimJ_kNum2`**: no,
  one (any `d ∉ K`), two (`3`, `0`) scalars;
* **`dKUnit_int`**, **`dKUnit_ext`**: the integrand `dKUnitIntegrandD` as such terms, by the Ward
  identities at the vertex `kWardD i` (an internal vertex: two terms) or at both ends (for
  `i = 0, 6, 10`: four terms);
* `crit_int`, `crit_ext`: the numerator-aware criteria of the data used, by kernel evaluation;
* **`hasLimJ_dKUnit_int`**, **`hasLimJ_dKUnit_ext`**: the limits, as combinations of
  parametric values with coefficients independent of the external momenta.
-/

@[expose] public section
open Complex Matrix
open QED.Dirac (gamma slash vecAct)

namespace QED.ChainProof.SetCMain

open QED.TwoLoop.Enumeration QED.ChainProof.SetCUnitM QED.TwoLoop.LimitCovariance
open QED.ChainProof.SetCPauli.CB01 (HasLimJ hasLimJ_of_paramValue exists_paramValue)
open QED.WickModel (Params)
open QED.TwoLoop.Bridge (electronNumerator extMomenta)
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix pvLines
  NoSubdivergenceRefined IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff)

/-! ### The limits of the terms -/

section Terms

variable (c : Class5) (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses) (σ : Fin 8)
  (hs : 4 ≤ (σ : ℕ)) (R : Params) (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
  (p p' : Fin 4 → ℝ) (hp : Minkowski.dot p p = -R.m ^ 2) (hp' : Minkowski.dot p' p' = -R.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))

/-- The parametric data of the unit along `ι` with the numerator lines of `S`. -/
noncomputable abbrev dkD {k : ℕ} (ι : Fin (k + 1) → Fin 10) (hk : 7 ≤ k) (S : Finset (Fin 10))
    (hcrit : NoSubdivergenceRefined 2 (Finset.univ.filter fun a => ι a ∈ S)
      (castLoopMatrix fun a => unitZ c σ (ι a))) : ParamData :=
  dkData c hc σ hs R hm hγ hγΛ p p' hp hp' hq ι hk _ hcrit

/-- The ten inverse denominators of the unit. -/
noncomputable abbrev dkQ (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∏ k, (lineDenom (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)) (unitMMomenta c σ ![1, 1] p p')
    (dkMasses R) ε k ℓ)⁻¹

/-- The scalar `k_d² + m²` of the electron line `d`. -/
noncomputable abbrev dkA (d : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot (kK c σ p p' d ℓ) (kK c σ p p' d ℓ) + R.m ^ 2 : ℝ) : ℂ)

variable (π : Equiv.Perm (Fin 5)) (X Y : KSlot) (K : Finset (Fin 4)) (μ a b : Fin 4)
  (hXY : Disjoint (kSlotS X) (kSlotS Y)) (hd : kSlotD X + kSlotD Y + K.card ≤ 4)
include hXY hd

theorem exists_paramValue_kNum {k : ℕ} (ι : Fin (k + 1) → Fin 10) (hk : 7 ≤ k)
    (hι : Function.Injective ι) (hS : ∀ x ∈ kSet X Y K, ∃ a, ι a = x)
    (hcrit : NoSubdivergenceRefined 2 (Finset.univ.filter fun a => ι a ∈ kSet X Y K)
      (castLoopMatrix fun a => unitZ c σ (ι a))) :
    ∃ w, IsParamValue (dkD c hc σ hs R hm hγ hγΛ p p' hp hp' hq ι hk (kSet X Y K) hcrit)
      (fun ℓ => kNum π c σ R.m p p' X Y K μ ℓ a b) w :=
  by
  have hP := isLoopPolyMat_kNum π c σ R.m p p' X Y K μ hd a b
  have hB0 := refinedBoundMat_kNum π c σ R.m p p' X Y K μ hXY hd a b
  have hB := RefinedBound.comp_filter ι hι hS hB0
  exact exists_paramValue (dkD c hc σ hs R hm hγ hγΛ p p' hp hp' hq ι hk (kSet X Y K) hcrit) hP hB

/-- **A term over the ten denominators.** -/
theorem hasLimJ_kNum0
    (hcrit : NoSubdivergenceRefined 2 (Finset.univ.filter fun a => id a ∈ kSet X Y K)
      (castLoopMatrix fun a => unitZ c σ (id a))) :
    ∃ w, IsParamValue (dkD c hc σ hs R hm hγ hγΛ p p' hp hp' hq id (by norm_num) (kSet X Y K)
        hcrit) (fun ℓ => kNum π c σ R.m p p' X Y K μ ℓ a b) w ∧
      HasLimJ (fun ε ℓ => kNum π c σ R.m p p' X Y K μ ℓ a b * dkQ c σ R p p' ε ℓ) w := by
  obtain ⟨w, hw⟩ := exists_paramValue_kNum c hc σ hs R hm hγ hγΛ p p' hp hp' hq π X Y K μ a b
    hXY hd id (by norm_num) Function.injective_id (fun x _ => ⟨x, rfl⟩) hcrit
  exact ⟨w, hw, hasLimJ_of_paramValue hw⟩

omit hXY hd in
theorem exists_succAbove_eIdx {d : Fin 4} (hdK : d ∉ K) :
    ∀ x ∈ kSet X Y K, ∃ a, (eIdx d).succAbove a = x := fun x hx => by
  refine Fin.exists_succAbove_eq fun h => ?_
  subst h
  simp only [kSet, Finset.mem_union, Finset.mem_image] at hx
  rcases hx with (⟨j, hj, hjd⟩ | hx) | hx
  · exact hdK (eIdx_injective hjd ▸ hj)
  · exact eIdx_ne_eight d (by simpa using kSlotS_subset X hx)
  · exact eIdx_ne_eight d (by simpa using kSlotS_subset Y hx)

/-- **A term with one scalar `k_d² + m²`** of a deleted line `d ∉ K`: its limit is the value on
the unit with line `d` deleted. -/
theorem hasLimJ_kNum1 (d : Fin 4) (hdK : d ∉ K)
    (hcrit0 : NoSubdivergenceRefined 2 (Finset.univ.filter fun a => id a ∈ kSet X Y K)
      (castLoopMatrix fun a => unitZ c σ (id a)))
    (hcrit1 : NoSubdivergenceRefined 2
      (Finset.univ.filter fun a => (eIdx d).succAbove a ∈ kSet X Y K)
      (castLoopMatrix fun a => unitZ c σ ((eIdx d).succAbove a))) :
    ∃ w, IsParamValue (dkD c hc σ hs R hm hγ hγΛ p p' hp hp' hq (eIdx d).succAbove
        (by norm_num) (kSet X Y K) hcrit1) (fun ℓ => kNum π c σ R.m p p' X Y K μ ℓ a b) w ∧
      HasLimJ (fun ε ℓ => kNum π c σ R.m p p' X Y K μ ℓ a b * dkA c σ R p p' d ℓ *
        dkQ c σ R p p' ε ℓ) w := by
  obtain ⟨w, hw⟩ := exists_paramValue_kNum c hc σ hs R hm hγ hγΛ p p' hp hp' hq π X Y K μ a b
    hXY hd (eIdx d).succAbove (by norm_num) Fin.succAbove_right_injective
    (exists_succAbove_eIdx X Y K hdK) hcrit1
  obtain ⟨w0, -, h0⟩ := hasLimJ_kNum0 c hc σ hs R hm hγ hγΛ p p' hp hp' hq π X Y K μ a b hXY hd
    hcrit0
  refine ⟨w, hw, HasLimJ.of_denom (fun ε ℓ => ?_) (fun ε hε ℓ => prod_inv_succAbove _ _ _
    hε.ne' (eIdx d) ℓ) (hasLimJ_of_paramValue hw) h0⟩
  have h := sq_add_eq_lineDenom (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ))
    (unitMMomenta c σ ![1, 1] p p') (dkMasses R) ε (eIdx d) ℓ
  rw [dkMasses_eIdx] at h
  exact h

omit hXY hd in
theorem lineMomentum_comp {n k : ℕ} (α : Fin (n + 1) → Fin 2 → ℝ) (q : Fin (n + 1) → Fin 4 → ℝ)
    (f : Fin (k + 1) → Fin (n + 1)) (j : Fin (k + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (fun i => α (f i)) (fun i => q (f i)) j ℓ = lineMomentum α q (f j) ℓ :=
  rfl

/-- The line map deleting the electron lines `0` and `3`. -/
def dk03 (a : Fin 8) : Fin 10 := (eIdx 0).succAbove ((2 : Fin 9).succAbove a)

omit hXY hd in
theorem exists_dk03 (h0 : (0 : Fin 4) ∉ K) (h3 : (3 : Fin 4) ∉ K) :
    ∀ x ∈ kSet X Y K, ∃ a, dk03 a = x := fun x hx => by
  obtain ⟨y, rfl⟩ := exists_succAbove_eIdx X Y K h0 x hx
  have hy : y ≠ 2 := fun h => by
    subst h
    obtain ⟨a, ha⟩ := exists_succAbove_eIdx X Y K h3 _ hx
    exact Fin.succAbove_ne (eIdx 3) a (ha.trans (by decide))
  obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hy
  exact ⟨a, rfl⟩

omit hXY hd in
theorem dk03_injective : Function.Injective dk03 :=
  Fin.succAbove_right_injective.comp Fin.succAbove_right_injective

/-- **A term with the two scalars of the lines `3`, `0`**, both deleted: its limit is the value
on the unit with both lines deleted. -/
theorem hasLimJ_kNum2 (h0 : (0 : Fin 4) ∉ K) (h3 : (3 : Fin 4) ∉ K)
    (hcrit0 : NoSubdivergenceRefined 2 (Finset.univ.filter fun a => id a ∈ kSet X Y K)
      (castLoopMatrix fun a => unitZ c σ (id a)))
    (hcrit3 : NoSubdivergenceRefined 2
      (Finset.univ.filter fun a => (eIdx 3).succAbove a ∈ kSet X Y K)
      (castLoopMatrix fun a => unitZ c σ ((eIdx 3).succAbove a)))
    (hcrit0' : NoSubdivergenceRefined 2
      (Finset.univ.filter fun a => (eIdx 0).succAbove a ∈ kSet X Y K)
      (castLoopMatrix fun a => unitZ c σ ((eIdx 0).succAbove a)))
    (hcrit03 : NoSubdivergenceRefined 2 (Finset.univ.filter fun a => dk03 a ∈ kSet X Y K)
      (castLoopMatrix fun a => unitZ c σ (dk03 a))) :
    ∃ w, IsParamValue (dkD c hc σ hs R hm hγ hγΛ p p' hp hp' hq dk03 le_rfl (kSet X Y K)
        hcrit03) (fun ℓ => kNum π c σ R.m p p' X Y K μ ℓ a b) w ∧
      HasLimJ (fun ε ℓ => kNum π c σ R.m p p' X Y K μ ℓ a b * dkA c σ R p p' 3 ℓ *
        dkA c σ R p p' 0 ℓ * dkQ c σ R p p' ε ℓ) w := by
  obtain ⟨w, hw⟩ := exists_paramValue_kNum c hc σ hs R hm hγ hγΛ p p' hp hp' hq π X Y K μ a b
    hXY hd dk03 le_rfl dk03_injective (exists_dk03 X Y K h0 h3) hcrit03
  obtain ⟨w0, hw0⟩ := exists_paramValue_kNum c hc σ hs R hm hγ hγΛ p p' hp hp' hq π X Y K μ a b
    hXY hd (eIdx 0).succAbove (by norm_num) Fin.succAbove_right_injective
    (exists_succAbove_eIdx X Y K h0) hcrit0'
  obtain ⟨w3, -, h3'⟩ := hasLimJ_kNum1 c hc σ hs R hm hγ hγΛ p p' hp hp' hq π X Y K μ a b hXY hd
    3 h3 hcrit0 hcrit3
  have hin : HasLimJ (fun ε ℓ => kNum π c σ R.m p p' X Y K μ ℓ a b * dkA c σ R p p' 3 ℓ *
      ∏ i : Fin 9, (lineDenom (fun i => unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)
        ((eIdx 0).succAbove i)) (fun i => unitMMomenta c σ ![1, 1] p p' ((eIdx 0).succAbove i))
        (fun i => dkMasses R ((eIdx 0).succAbove i)) ε i ℓ)⁻¹) w := by
    refine HasLimJ.of_denom (fun ε ℓ => ?_) (fun ε hε ℓ => prod_inv_succAbove _ _ _ hε.ne' 2 ℓ)
      (hasLimJ_of_paramValue hw) (hasLimJ_of_paramValue hw0)
    have h := sq_add_eq_lineDenom (fun i => unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)
      ((eIdx 0).succAbove i)) (fun i => unitMMomenta c σ ![1, 1] p p' ((eIdx 0).succAbove i))
      (fun i => dkMasses R ((eIdx 0).succAbove i)) ε 2 ℓ
    rw [lineMomentum_comp] at h
    have e : (eIdx 0).succAbove 2 = eIdx 3 := by decide
    simp only [e, dkMasses_eIdx] at h
    exact h
  refine ⟨w, hw, HasLimJ.of_denom (F := fun ℓ => kNum π c σ R.m p p' X Y K μ ℓ a b *
    dkA c σ R p p' 3 ℓ) (fun ε ℓ => ?_) (fun ε hε ℓ => prod_inv_succAbove _ _ _ hε.ne' (eIdx 0) ℓ)
    hin h3'⟩
  have h := sq_add_eq_lineDenom (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ))
    (unitMMomenta c σ ![1, 1] p p') (dkMasses R) ε (eIdx 0) ℓ
  rw [dkMasses_eIdx] at h
  exact h

end Terms

/-! ### The integrand as terms -/

section Decomp

variable (i : Fin 12) (s : Fin 2) (R : Params) (p p' : Fin 4 → ℝ) (μ a b : Fin 4)

/-- The constant of the chain form of the integrand. -/
noncomputable def kCst (R : Params) : ℂ :=
  QED.TwoLoop.ClassLimit.twoLoopNorm * ((I * R.e) ^ 5 * (1 / I) ^ 4) *
    ((1 / I) * ((R.Λ ^ 2 - R.mγ ^ 2 : ℝ) : ℂ))

theorem dKUnit_eq_kOpen (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    dKUnitIntegrandD i s R (dkMasses R) ε p p' μ a b ℓ =
      kCst R * kOpen (kPermD i) μ (slash (kQ (repBClass i) (repBSlot i) p p' ℓ))
        (slash (kQ (repBClass i) (repBSlot i) p p' ℓ))
        (fun j => kEK (repBClass i) (repBSlot i) R.m p p' Finset.univ j ℓ) a b *
        dkQ (repBClass i) (repBSlot i) R p p' ε ℓ := by
  unfold dKUnitIntegrandD
  rw [kChainD_repD_eq, kChainD_eq_kOpen, elemMom_eq_kQ]
  simp only [lineMomentum_class_eq_kK (repBClass i) (repBSlot i)]
  have hE : (fun j => electronNumerator R.m (kK (repBClass i) (repBSlot i) p p' j ℓ)) =
      fun j => kEK (repBClass i) (repBSlot i) R.m p p' Finset.univ j ℓ :=
    funext fun j => by simp [kEK]
  rw [hE, Matrix.smul_apply, smul_eq_mul, kCst]
  ring

theorem kQ_int (j : Fin 3) (hj : kWardD i = j.succ.castSucc) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kQ (repBClass i) (repBSlot i) p p' ℓ = ((kSgnW i : ℤ) : ℝ) •
      (kK (repBClass i) (repBSlot i) p p' j.succ ℓ -
        kK (repBClass i) (repBSlot i) p p' j.castSucc ℓ) := by
  rw [← elemMom_eq_kQ, (elemMom_eq_kMom i p p' ℓ).1, hj,
    show (j.succ.castSucc : Fin 5).succ = j.succ.succ.castSucc from rfl, kMom_electron,
    show (j.succ.castSucc : Fin 5).castSucc = j.castSucc.succ.castSucc from rfl, kMom_electron,
    lineMomentum_class_eq_kK (repBClass i) (repBSlot i),
    lineMomentum_class_eq_kK (repBClass i) (repBSlot i)]

/-- **The integrand at an internal Ward vertex** `kWardD i = j + 1`: two terms, with the
scalars of the electron lines `j + 1` and `j`. -/
theorem dKUnit_int (j : Fin 3) (hj : kWardD i = j.succ.castSucc) (ε : ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    dKUnitIntegrandD i s R (dkMasses R) ε p p' μ a b ℓ =
      kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ) *
        (kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .one .q (Finset.univ.erase j.succ)
            μ ℓ a b * dkA (repBClass i) (repBSlot i) R p p' j.succ ℓ -
          kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .one .q
            (Finset.univ.erase j.castSucc) μ ℓ a b *
            dkA (repBClass i) (repBSlot i) R p p' j.castSucc ℓ) *
        dkQ (repBClass i) (repBSlot i) R p p' ε ℓ := by
  rw [dKUnit_eq_kOpen, kOpen_ward_int (kPermD i) μ R.m _ j (by rw [(kPermD_apply i).2.1, hj])
    _ _ _ _ _ (kQ_int i p p' j hj ℓ) (by simp [kEK]) (by simp [kEK]), kEK_update, kEK_update]
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, kNum, kSlotM]
  ring

theorem kQ_out (hW : kWardD i = 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kQ (repBClass i) (repBSlot i) p p' ℓ = ((kSgnW i : ℤ) : ℝ) •
      (p' - kK (repBClass i) (repBSlot i) p p' 3 ℓ) := by
  rw [← elemMom_eq_kQ, (elemMom_eq_kMom i p p' ℓ).1, hW,
    show (4 : Fin 5).succ = 5 from rfl, kMom_five,
    show (4 : Fin 5).castSucc = (3 : Fin 4).succ.castSucc from rfl, kMom_electron,
    lineMomentum_class_eq_kK (repBClass i) (repBSlot i)]

theorem kQ_in (hO : kOthD i = 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kQ (repBClass i) (repBSlot i) p p' ℓ = ((kSgnO i : ℤ) : ℝ) •
      (kK (repBClass i) (repBSlot i) p p' 0 ℓ - p) := by
  rw [← elemMom_eq_kQ, (elemMom_eq_kMom i p p' ℓ).2, hO,
    show (0 : Fin 5).succ = (0 : Fin 4).succ.castSucc from rfl, kMom_electron,
    show (0 : Fin 5).castSucc = 0 from rfl, kMom_zero,
    lineMomentum_class_eq_kK (repBClass i) (repBSlot i)]

theorem kOthD_of_kWardD : ∀ i : Fin 12, kWardD i = 4 → kOthD i = 0 := by decide

/-- **The integrand with the Ward identities at both ends** (`kWardD i = 4`): four terms. -/
theorem dKUnit_ext (hW : kWardD i = 4) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    dKUnitIntegrandD i s R (dkMasses R) ε p p' μ a b ℓ =
      kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ)) *
        (kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .out .inn Finset.univ μ ℓ a b +
          kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .out .one (Finset.univ.erase 0)
            μ ℓ a b * dkA (repBClass i) (repBSlot i) R p p' 0 ℓ -
          kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .one .inn (Finset.univ.erase 3)
            μ ℓ a b * dkA (repBClass i) (repBSlot i) R p p' 3 ℓ -
          kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .one .one
            ((Finset.univ.erase 3).erase 0) μ ℓ a b * dkA (repBClass i) (repBSlot i) R p p' 3 ℓ *
            dkA (repBClass i) (repBSlot i) R p p' 0 ℓ) *
        dkQ (repBClass i) (repBSlot i) R p p' ε ℓ := by
  have hO := kOthD_of_kWardD i hW
  rw [dKUnit_eq_kOpen, kOpen_ward_out (kPermD i) μ R.m _ (by rw [(kPermD_apply i).2.1, hW])
    _ _ p' _ _ (kQ_out i p p' hW ℓ) (by simp [kEK]), kEK_update,
    kOpen_ward_in (kPermD i) μ R.m _ (by rw [(kPermD_apply i).2.2.1, hO]) _ _ p _ _
      (kQ_in i p p' hO ℓ) (by simp [kEK]),
    kOpen_ward_in (kPermD i) μ R.m _ (by rw [(kPermD_apply i).2.2.1, hO]) _ _ p _ _
      (kQ_in i p p' hO ℓ) (by simp [kEK]), kEK_update, kEK_update]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul, kNum, kSlotM]
  ring

end Decomp

/-! ### The criteria -/

/-- The criterion of the term with lines `S` on the unit of class `repB i` along `ι`. -/
abbrev KCrit (i : Fin 12) {k : ℕ} (ι : Fin (k + 1) → Fin 10) (S : Finset (Fin 10)) : Prop :=
  NoSubdivergenceRefined 2 (Finset.univ.filter fun a => ι a ∈ S)
    (castLoopMatrix fun a => unitZ (repBClass i) (repBSlot i) (ι a))

theorem crit_int : ∀ (i : Fin 12) (j : Fin 3), kWardD i = j.succ.castSucc →
    ∀ d ∈ ({j.succ, j.castSucc} : Finset (Fin 4)),
      IntNoSubdivergenceRefined 2 (Finset.univ.filter fun a : Fin 10 =>
          id a ∈ kSet .one .q (Finset.univ.erase d))
        (fun a => unitZ (repBClass i) (repBSlot i) (id a)) ∧
      IntNoSubdivergenceRefined 2 (Finset.univ.filter fun a : Fin 9 =>
          (eIdx d).succAbove a ∈ kSet .one .q (Finset.univ.erase d))
        (fun a => unitZ (repBClass i) (repBSlot i) ((eIdx d).succAbove a)) := by
  decide +kernel

theorem kCrit_int_id {i : Fin 12} {j : Fin 3} (hj : kWardD i = j.succ.castSucc) {d : Fin 4}
    (hd : d ∈ ({j.succ, j.castSucc} : Finset (Fin 4))) :
    KCrit i id (kSet .one .q (Finset.univ.erase d)) :=
  (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (crit_int i j hj d hd).1

theorem kCrit_int_del {i : Fin 12} {j : Fin 3} (hj : kWardD i = j.succ.castSucc) {d : Fin 4}
    (hd : d ∈ ({j.succ, j.castSucc} : Finset (Fin 4))) :
    KCrit i (eIdx d).succAbove (kSet .one .q (Finset.univ.erase d)) :=
  (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (crit_int i j hj d hd).2

/-- The lines of the four terms at the two ends. -/
def kSetE : Fin 4 → Finset (Fin 10)
  | 0 => kSet .out .inn Finset.univ
  | 1 => kSet .out .one (Finset.univ.erase 0)
  | 2 => kSet .one .inn (Finset.univ.erase 3)
  | 3 => kSet .one .one ((Finset.univ.erase 3).erase 0)

theorem crit_ext : ∀ i : Fin 12, kWardD i = 4 →
    (∀ r, IntNoSubdivergenceRefined 2 (Finset.univ.filter fun a : Fin 10 => id a ∈ kSetE r)
      (fun a => unitZ (repBClass i) (repBSlot i) (id a))) ∧
    IntNoSubdivergenceRefined 2 (Finset.univ.filter fun a : Fin 9 => (eIdx 0).succAbove a ∈ kSetE 1)
      (fun a => unitZ (repBClass i) (repBSlot i) ((eIdx 0).succAbove a)) ∧
    IntNoSubdivergenceRefined 2 (Finset.univ.filter fun a : Fin 9 => (eIdx 3).succAbove a ∈ kSetE 2)
      (fun a => unitZ (repBClass i) (repBSlot i) ((eIdx 3).succAbove a)) ∧
    IntNoSubdivergenceRefined 2 (Finset.univ.filter fun a : Fin 9 => (eIdx 3).succAbove a ∈ kSetE 3)
      (fun a => unitZ (repBClass i) (repBSlot i) ((eIdx 3).succAbove a)) ∧
    IntNoSubdivergenceRefined 2 (Finset.univ.filter fun a : Fin 9 => (eIdx 0).succAbove a ∈ kSetE 3)
      (fun a => unitZ (repBClass i) (repBSlot i) ((eIdx 0).succAbove a)) ∧
    IntNoSubdivergenceRefined 2 (Finset.univ.filter fun a : Fin 8 => dk03 a ∈ kSetE 3)
      (fun a => unitZ (repBClass i) (repBSlot i) (dk03 a)) := by
  decide +kernel

section CritExt

variable {i : Fin 12} (hW : kWardD i = 4)
include hW

theorem kCrit_ext_id (r : Fin 4) : KCrit i id (kSetE r) :=
  (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr ((crit_ext i hW).1 r)

theorem kCrit_ext_1 : KCrit i (eIdx 0).succAbove (kSetE 1) :=
  (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (crit_ext i hW).2.1

theorem kCrit_ext_2 : KCrit i (eIdx 3).succAbove (kSetE 2) :=
  (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (crit_ext i hW).2.2.1

theorem kCrit_ext_3a : KCrit i (eIdx 3).succAbove (kSetE 3) :=
  (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (crit_ext i hW).2.2.2.1

theorem kCrit_ext_3b : KCrit i (eIdx 0).succAbove (kSetE 3) :=
  (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (crit_ext i hW).2.2.2.2.1

theorem kCrit_ext_3 : KCrit i dk03 (kSetE 3) :=
  (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr (crit_ext i hW).2.2.2.2.2

end CritExt

/-! ### The limits of the integrand -/

/-- The term `kNum` of the class `repB i`. -/
noncomputable abbrev kNi (i : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (X Y : KSlot)
    (K : Finset (Fin 4)) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' X Y K μ ℓ

section Lim

variable (i : Fin 12) (s : Fin 2) (R : Params) (hm : 0 < R.m) (hγ : 0 < R.mγ)
  (hγΛ : R.mγ ≤ R.Λ) (p p' : Fin 4 → ℝ) (hp : Minkowski.dot p p = -R.m ^ 2)
  (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))

/-- The data `dkD` of the class `repB i`. -/
noncomputable abbrev dkDi {k : ℕ} (ι : Fin (k + 1) → Fin 10) (hk : 7 ≤ k) (S : Finset (Fin 10))
    (hcrit : KCrit i ι S) : ParamData :=
  dkD (repBClass i) (repBClass_mem i) (repBSlot i) (four_le_repBSlot i) R hm hγ hγΛ p p' hp hp'
    hq ι hk S hcrit

theorem mem_pair_left (j : Fin 3) : j.succ ∈ ({j.succ, j.castSucc} : Finset (Fin 4)) :=
  Finset.mem_insert_self _ _

theorem mem_pair_right (j : Fin 3) : j.castSucc ∈ ({j.succ, j.castSucc} : Finset (Fin 4)) :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem kSlot_one_q : Disjoint (kSlotS .one) (kSlotS .q) := by simp [kSlotS]

theorem kDeg_int (d : Fin 4) :
    kSlotD .one + kSlotD .q + (Finset.univ.erase d).card ≤ 4 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [kSlotD]

/-- **The limit at an internal Ward vertex**: `kCst · σ · (w₁ - w₂)`, `w₁`, `w₂` the parametric
values of the two terms on the unit with the electron line `j + 1`, resp. `j`, deleted. -/
theorem hasLimJ_dKUnit_int (j : Fin 3) (hj : kWardD i = j.succ.castSucc) (μ a b : Fin 4) :
    ∃ w₁ w₂ : ℂ,
      IsParamValue (dkDi i R hm hγ hγΛ p p' hp hp' hq (eIdx j.succ).succAbove (by norm_num)
          (kSet .one .q (Finset.univ.erase j.succ)) (kCrit_int_del hj (mem_pair_left j)))
        (fun ℓ => kNi i R p p' .one .q (Finset.univ.erase j.succ) μ ℓ a b) w₁ ∧
      IsParamValue (dkDi i R hm hγ hγΛ p p' hp hp' hq (eIdx j.castSucc).succAbove (by norm_num)
          (kSet .one .q (Finset.univ.erase j.castSucc)) (kCrit_int_del hj (mem_pair_right j)))
        (fun ℓ => kNi i R p p' .one .q (Finset.univ.erase j.castSucc) μ ℓ a b) w₂ ∧
      HasLimJ (fun ε => dKUnitIntegrandD i s R (dkMasses R) ε p p' μ a b)
        (kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ) * (w₁ - w₂)) := by
  obtain ⟨w₁, hw₁, h₁⟩ := hasLimJ_kNum1 (repBClass i) (repBClass_mem i) (repBSlot i)
    (four_le_repBSlot i) R hm hγ hγΛ p p' hp hp' hq (kPermD i) .one .q _ μ a b kSlot_one_q
    (kDeg_int _) j.succ (by simp) (kCrit_int_id hj (mem_pair_left j))
    (kCrit_int_del hj (mem_pair_left j))
  obtain ⟨w₂, hw₂, h₂⟩ := hasLimJ_kNum1 (repBClass i) (repBClass_mem i) (repBSlot i)
    (four_le_repBSlot i) R hm hγ hγΛ p p' hp hp' hq (kPermD i) .one .q _ μ a b kSlot_one_q
    (kDeg_int _) j.castSucc (by simp) (kCrit_int_id hj (mem_pair_right j))
    (kCrit_int_del hj (mem_pair_right j))
  refine ⟨w₁, w₂, hw₁, hw₂, ?_⟩
  have h := (h₁.add (h₂.const_mul (-1))).const_mul (kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ))
  rw [show w₁ + -1 * w₂ = w₁ - w₂ by ring] at h
  refine h.congr fun ε _ => funext fun ℓ => ?_
  rw [dKUnit_int i s R p p' μ a b j hj ε ℓ]
  ring

/-- **The limit with the Ward identities at both ends**: `kCst · σ σ' · (w₀ + w₁ - w₂ - w₃)`,
`wᵣ` the parametric values of the four terms on the unit with no line, the line `0`, the line
`3`, both lines deleted. -/
theorem hasLimJ_dKUnit_ext (hW : kWardD i = 4) (μ a b : Fin 4) :
    ∃ w₀ w₁ w₂ w₃ : ℂ,
      IsParamValue (dkDi i R hm hγ hγΛ p p' hp hp' hq id (by norm_num) (kSetE 0)
          (kCrit_ext_id hW 0))
        (fun ℓ => kNi i R p p' .out .inn Finset.univ μ ℓ a b) w₀ ∧
      IsParamValue (dkDi i R hm hγ hγΛ p p' hp hp' hq (eIdx 0).succAbove (by norm_num) (kSetE 1)
          (kCrit_ext_1 hW))
        (fun ℓ => kNi i R p p' .out .one (Finset.univ.erase 0) μ ℓ a b) w₁ ∧
      IsParamValue (dkDi i R hm hγ hγΛ p p' hp hp' hq (eIdx 3).succAbove (by norm_num) (kSetE 2)
          (kCrit_ext_2 hW))
        (fun ℓ => kNi i R p p' .one .inn (Finset.univ.erase 3) μ ℓ a b) w₂ ∧
      IsParamValue (dkDi i R hm hγ hγΛ p p' hp hp' hq dk03 le_rfl (kSetE 3) (kCrit_ext_3 hW))
        (fun ℓ => kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b) w₃ ∧
      HasLimJ (fun ε => dKUnitIntegrandD i s R (dkMasses R) ε p p' μ a b)
        (kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ)) *
          (w₀ + w₁ - w₂ - w₃)) := by
  obtain ⟨w₀, hw₀, h₀⟩ := hasLimJ_kNum0 (repBClass i) (repBClass_mem i) (repBSlot i)
    (four_le_repBSlot i) R hm hγ hγΛ p p' hp hp' hq (kPermD i) .out .inn _ μ a b
    (by simp [kSlotS]) (by decide) (kCrit_ext_id hW 0)
  obtain ⟨w₁, hw₁, h₁⟩ := hasLimJ_kNum1 (repBClass i) (repBClass_mem i) (repBSlot i)
    (four_le_repBSlot i) R hm hγ hγΛ p p' hp hp' hq (kPermD i) .out .one _ μ a b
    (by simp [kSlotS]) (by decide) 0 (by simp) (kCrit_ext_id hW 1) (kCrit_ext_1 hW)
  obtain ⟨w₂, hw₂, h₂⟩ := hasLimJ_kNum1 (repBClass i) (repBClass_mem i) (repBSlot i)
    (four_le_repBSlot i) R hm hγ hγΛ p p' hp hp' hq (kPermD i) .one .inn _ μ a b
    (by simp [kSlotS]) (by decide) 3 (by simp) (kCrit_ext_id hW 2) (kCrit_ext_2 hW)
  obtain ⟨w₃, hw₃, h₃⟩ := hasLimJ_kNum2 (repBClass i) (repBClass_mem i) (repBSlot i)
    (four_le_repBSlot i) R hm hγ hγΛ p p' hp hp' hq (kPermD i) .one .one _ μ a b
    (by simp [kSlotS]) (by decide) (by simp) (by simp) (kCrit_ext_id hW 3) (kCrit_ext_3a hW)
    (kCrit_ext_3b hW) (kCrit_ext_3 hW)
  refine ⟨w₀, w₁, w₂, w₃, hw₀, hw₁, hw₂, hw₃, ?_⟩
  have h := (((h₀.add h₁).add (h₂.const_mul (-1))).add (h₃.const_mul (-1))).const_mul
    (kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ)))
  rw [show w₀ + w₁ + -1 * w₂ + -1 * w₃ = w₀ + w₁ - w₂ - w₃ by ring] at h
  refine h.congr fun ε _ => funext fun ℓ => ?_
  rw [dKUnit_ext i s R p p' μ a b hW ε ℓ]
  ring

end Lim

end QED.ChainProof.SetCMain

end
