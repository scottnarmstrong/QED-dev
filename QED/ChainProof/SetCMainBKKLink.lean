/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBKKTerm
public import QED.ChainProof.SetCMainBRestLink
public import QED.ChainProof.SetCMainBPauliPiece

/-!
# Set (c), the bubble classes: the longitudinal dispersive link

Proves the link `QED.ChainProof.SetCMainB.MainBKKLink` for all twelve bubble classes `repB i`.
By `QED.ChainProof.SetCMainB.kkB_eq_unit` the longitudinal dispersive part is
`-2c · wKD 1 · ∑_f ∫₀¹ w_f(x) K k² (M_f² + x(1-x)k² - iε)⁻¹ dx`, `K` the longitudinal integrand of
`repD i 0`. After the Ward identities (`QED.ChainProof.SetCMain.dKUnit_int`, `dKUnit_ext`) `K` is
a combination of numerators `kNum` times scalars `k_d² + m²` of electron lines over the ten
denominators of the unit; each scalar is removed by deleting its line (`kkVal_scalar`), and the
factor `k²` cancels against the extra line `9` (`kkVal_sq`), except on the term with both lines
`0`, `3` deleted, where `k²` stays in the numerator.

* `kkVal_kNum_sq`, `kkVal_kNum_sq_scalar`: a term with `k²` and no, resp. one scalar;
* `kkVal_ext_three`: the term with `k²` and the two scalars of the lines `3`, `0`;
* **`kkVal_dKUnit_int`**, **`kkVal_dKUnit_ext`**, **`kkVal_dKUnit`**: the integrand `K k²`
  times the spectral factor has a dispersive limit with its value, for every weight integrable
  on `(0, 1)`;
* `kkH`, `kkLimB`, **`tendsto_kkB`**: the limit of the longitudinal dispersive part, explicitly
  `-2c · wKD 1 · ∑_f ∫₀¹ w_f(x) lim_ε J(K k² (M_f² + x(1-x)k² - iε)⁻¹) dx`;
* **`mainBKKLink`**: `MainBKKLink P₀ i` for all twelve orbits.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open QED.WickModel (Params)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCLink QED.ChainProof.SetALink QED.ChainProof.SetCMain
open QED.ChainProof.SetCUnitM QED.GradedProof.X0 QED.TwoLoop.Enumeration
open QED.TwoLoop.Bridge (IsLoopPoly IsLoopPolyMat)
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat)
open QED.Integration.TwoLoop (RefinedBound)
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### The degree two term -/

section Two

variable (π : Equiv.Perm (Fin 5)) (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ)
  (μ : Fin 4)

/-- The term with no fixed vertex and the electron lines `1`, `2` has degree two. -/
theorem isLoopPolyMat_kNum_two :
    IsLoopPolyMat 2 2 (kNum π c σ m p p' .one .one ((Finset.univ.erase 3).erase 0) μ) :=
  isLoopPolyMat_kOpen π μ (isLoopPolyMat_kSlotM c σ m p p' .one)
    (isLoopPolyMat_kSlotM c σ m p p' .one) (isLoopPolyMat_kEK c σ m p p' _)
    (by rw [sum_ite_mem_one]; decide)

/-- The pointwise bound of the term with no fixed vertex and the electron lines `1`, `2`, of
degree two. -/
theorem refinedBoundMat_kNum_two :
    RefinedBoundMat (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ))
      (kSet .one .one ((Finset.univ.erase 3).erase 0)) 2
      (kNum π c σ m p p' .one .one ((Finset.univ.erase 3).erase 0) μ) := by
  have hE8 : ∀ (Z : KSlot) (j : Fin 4), Disjoint (kSlotS Z)
      (if j ∈ (Finset.univ.erase 3).erase 0 then {eIdx j} else ∅) := fun Z j => by
    refine Finset.disjoint_of_subset_left (kSlotS_subset Z) ?_
    split_ifs
    · simpa using (eIdx_ne_eight j).symm
    · simp
  refine refinedBoundMat_kOpen π μ (refinedBoundMat_kSlotM c σ m p p' .one)
    (refinedBoundMat_kSlotM c σ m p p' .one) (refinedBoundMat_kEK c σ m p p' _)
    (by simp [kSlotS]) (hE8 _) (hE8 _) (fun j j' h => ?_) ?_ ?_ (fun j => ?_) ?_
  · split_ifs <;> simp [eIdx_injective.ne h]
  · unfold kSet; exact Finset.subset_union_right.trans Finset.subset_union_left
  · unfold kSet; exact Finset.subset_union_right
  · split_ifs with h
    · unfold kSet
      exact Finset.singleton_subset_iff.2
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)))
    · simp
  · rw [sum_ite_mem_one]; decide

end Two

/-! ### The terms with `k²` -/

section Terms

variable {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t : ℝ} (hm : 0 < R.m)
  (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
  (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
  (ht : R.m ≤ t) {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1))
  {F : (Fin 2 → Fin 4 → ℝ) → ℂ} {S : Finset (Fin 10)} (hP : IsLoopPoly 2 4 F)
  (hB : RefinedBound (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ)) S 4 F)
include hm hγ hγΛ hp hp' hq ht hw hP hB

/-- **A term with `k²` and no scalar**: `k²` cancels against the line `9`. -/
theorem kkVal_kNum_sq (h₀ : KKOk i (fun a : Fin 10 => a) S)
    (h₉ : KKOk i (fun a : Fin 9 => (9 : Fin 10).succAbove a) S) :
    KKVal w (kkT i R p p' t (fun a : Fin 10 => a)
      fun ℓ => F ℓ * elemSq (repBClass i) (repBSlot i) p p' ℓ) :=
  kkVal_sq (fun a : Fin 10 => a) 9 rfl
    (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) h₉ hP hB)
    (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) h₀ hP hB)

/-- **A term with `k²` and the scalar of the electron line `d`**: the line `d` is deleted, and
`k²` cancels against the line `9`. -/
theorem kkVal_kNum_sq_scalar (d : Fin 4) (h₀ : KKOk i (fun a : Fin 10 => a) S)
    (h₉ : KKOk i (fun a : Fin 9 => (9 : Fin 10).succAbove a) S)
    (hd : KKOk i (fun a : Fin 9 => (eIdx d).succAbove a) S)
    (hd₉ : KKOk i (fun a : Fin 8 => (eIdx d).succAbove ((8 : Fin 9).succAbove a)) S) :
    KKVal w (kkT i R p p' t (fun a : Fin 10 => a)
      fun ℓ => F ℓ * elemSq (repBClass i) (repBSlot i) p p' ℓ * kkA i R p p' (eIdx d) ℓ) :=
  kkVal_scalar (fun a : Fin 10 => a) (eIdx d)
    (kkVal_sq (fun a : Fin 9 => (eIdx d).succAbove a) 8 (eIdx_succAbove_eight d)
      (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) hd₉ hP hB)
      (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) hd hP hB))
    (kkVal_kNum_sq hm hγ hγΛ hp hp' hq ht hw hP hB h₀ h₉)

end Terms

/-- **The term with `k²` and the two scalars of the lines `3`, `0`**: with both lines deleted
the factor `k²` stays in the numerator (lines `8`, `9`, degree `2 + 2`); otherwise it cancels
against the line `9`. -/
theorem kkVal_ext_three {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t : ℝ} (hm : 0 < R.m)
    (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
    (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (ht : R.m ≤ t) {w : ℝ → ℂ} (hw : IntegrableOn w (Ioo 0 1)) (hW : kWardD i = 4)
    (μ a b : Fin 4) :
    KKVal w (kkT i R p p' t (fun a : Fin 10 => a) fun ℓ =>
      kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b *
        elemSq (repBClass i) (repBSlot i) p p' ℓ * kkA i R p p' (eIdx 3) ℓ *
        kkA i R p p' (eIdx 0) ℓ) := by
  obtain ⟨hall, -, -, -, -, hd0, hd09, hd3, hd39, h03⟩ := kkOk_ext i hW
  have hP : IsLoopPoly 2 4 fun ℓ =>
      kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b :=
    (isLoopPolyMat_kNum _ _ _ _ _ _ _ _ _ μ (by decide) a b)
  have hB : RefinedBound (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
      (kSetE 3) 4 fun ℓ => kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b :=
    refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ μ (by simp [kSlotS]) (by decide) a b
  have hP2 : IsLoopPoly 2 4 fun ℓ =>
      kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b *
        elemSq (repBClass i) (repBSlot i) p p' ℓ :=
    (isLoopPolyMat_kNum_two _ _ _ _ _ _ μ a b).mul (isLoopPoly_elemSq _ _ p p')
  have hB2 : RefinedBound (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
      (kSetE 3 ∪ {8, 9}) 4 fun ℓ =>
        kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b *
          elemSq (repBClass i) (repBSlot i) p p' ℓ :=
    (refinedBoundMat_kNum_two _ _ _ _ _ _ μ a b).mul (refinedBound_elemSq _ _ p p')
      (by decide)
  -- the line `0` deleted: the scalar of the line `3` is that of the line `2` of the rest
  have hdel : KKVal w (kkT i R p p' t (fun a : Fin 9 => (eIdx 0).succAbove a) fun ℓ =>
      kNi i R p p' .one .one ((Finset.univ.erase 3).erase 0) μ ℓ a b *
        elemSq (repBClass i) (repBSlot i) p p' ℓ * kkA i R p p' (eIdx 3) ℓ) := by
    have h := kkVal_scalar (fun a : Fin 9 => (eIdx 0).succAbove a) 2
      (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw le_rfl h03 hP2 hB2)
      (kkVal_sq (fun a : Fin 9 => (eIdx 0).succAbove a) 8 (eIdx_succAbove_eight 0)
        (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) hd09 hP hB)
        (kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) hd0 hP hB))
    rwa [eIdx_zero_succAbove_two] at h
  exact kkVal_scalar (fun a : Fin 10 => a) (eIdx 0) hdel
    (kkVal_kNum_sq_scalar hm hγ hγΛ hp hp' hq ht hw hP hB 3 (hall 3).1 (hall 3).2 hd3 hd39)

/-! ### The integrand -/

theorem kWardD_cases : ∀ i : Fin 12, kWardD i = 4 ∨ ∃ j : Fin 3, kWardD i = j.succ.castSucc := by
  decide

section Integrand

variable {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t : ℝ} {w : ℝ → ℂ}

theorem kkDen_id (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkDen i R p p' (fun a : Fin 10 => a) ε ℓ = dkQ (repBClass i) (repBSlot i) R p p' ε ℓ := rfl

/-- **The integrand at an internal Ward vertex** `kWardD i = j + 1` has a dispersive limit. -/
theorem kkVal_dKUnit_int (j : Fin 3) (hj : kWardD i = j.succ.castSucc) (μ a b : Fin 4)
    (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
    (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (ht : R.m ≤ t) (hw : IntegrableOn w (Ioo 0 1)) :
    KKVal w (fun ε x ℓ => dKUnitIntegrandD i 0 R (dkMasses R) ε p p' μ a b ℓ *
      elemSq (repBClass i) (repBSlot i) p p' ℓ * kkSpec i p p' t ε x ℓ) := by
  have hT : ∀ d ∈ ({j.succ, j.castSucc} : Finset (Fin 4)), KKVal w
      (kkT i R p p' t (fun a : Fin 10 => a) fun ℓ =>
        kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b *
          elemSq (repBClass i) (repBSlot i) p p' ℓ * kkA i R p p' (eIdx d) ℓ) := fun d hd => by
    obtain ⟨h0, hdl, h9, hd9⟩ := kkOk_int i j hj d hd
    exact kkVal_kNum_sq_scalar hm hγ hγΛ hp hp' hq ht hw
      (isLoopPolyMat_kNum _ _ _ _ _ _ _ _ _ μ (kDeg_int d) a b)
      (refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ μ kSlot_one_q (kDeg_int d) a b) d h0 h9 hdl hd9
  refine (((hT _ (mem_pair_left j)).add ((hT _ (mem_pair_right j)).const_mul (-1))).const_mul
    (kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ))).congr fun ε _ x _ ℓ => ?_
  rw [dKUnit_int i 0 R p p' μ a b j hj ε ℓ]
  simp only [kkT, kkA_eIdx, kkDen_id]
  ring

/-- **The integrand with the Ward identities at both ends** has a dispersive limit. -/
theorem kkVal_dKUnit_ext (hW : kWardD i = 4) (μ a b : Fin 4)
    (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
    (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (ht : R.m ≤ t) (hw : IntegrableOn w (Ioo 0 1)) :
    KKVal w (fun ε x ℓ => dKUnitIntegrandD i 0 R (dkMasses R) ε p p' μ a b ℓ *
      elemSq (repBClass i) (repBSlot i) p p' ℓ * kkSpec i p p' t ε x ℓ) := by
  obtain ⟨hall, h1d, h1d9, h2d, h2d9, -⟩ := kkOk_ext i hW
  have h₀ := kkVal_kNum_sq hm hγ hγΛ hp hp' hq ht hw
    (isLoopPolyMat_kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .out .inn Finset.univ μ
      (by decide) a b)
    (refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ μ (by simp [kSlotS]) (by decide) a b)
    (hall 0).1 (hall 0).2
  have h₁ := kkVal_kNum_sq_scalar hm hγ hγΛ hp hp' hq ht hw
    (isLoopPolyMat_kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .out .one
      (Finset.univ.erase 0) μ (by decide) a b)
    (refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ μ (by simp [kSlotS]) (by decide) a b)
    0 (hall 1).1 (hall 1).2 h1d h1d9
  have h₂ := kkVal_kNum_sq_scalar hm hγ hγΛ hp hp' hq ht hw
    (isLoopPolyMat_kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .one .inn
      (Finset.univ.erase 3) μ (by decide) a b)
    (refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ μ (by simp [kSlotS]) (by decide) a b)
    3 (hall 2).1 (hall 2).2 h2d h2d9
  have h₃ := kkVal_ext_three hm hγ hγΛ hp hp' hq ht hw hW μ a b
  refine ((((h₀.add h₁).add (h₂.const_mul (-1))).add (h₃.const_mul (-1))).const_mul
    (kCst R * ((((kSgnW i : ℤ) : ℝ) : ℂ) * (((kSgnO i : ℤ) : ℝ) : ℂ)))).congr
    fun ε _ x _ ℓ => ?_
  rw [dKUnit_ext i 0 R p p' μ a b hW ε ℓ]
  simp only [kkT, kkA_eIdx, kkDen_id]
  ring

/-- **The longitudinal integrand times `k²` and the spectral factor has a dispersive limit**,
for every weight integrable on `(0, 1)` and every spectral mass `t ≥ m`. -/
theorem kkVal_dKUnit (μ a b : Fin 4)
    (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
    (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (ht : R.m ≤ t) (hw : IntegrableOn w (Ioo 0 1)) :
    KKVal w (fun ε x ℓ => dKUnitIntegrandD i 0 R (dkMasses R) ε p p' μ a b ℓ *
      elemSq (repBClass i) (repBSlot i) p p' ℓ * kkSpec i p p' t ε x ℓ) := by
  rcases kWardD_cases i with hW | ⟨j, hj⟩
  · exact kkVal_dKUnit_ext hW μ a b hm hγ hγΛ hp hp' hq ht hw
  · exact kkVal_dKUnit_int j hj μ a b hm hγ hγΛ hp hp' hq ht hw

end Integrand

/-! ### The link -/

/-- The longitudinal integrand times `k²` and the spectral factor of mass `t`. -/
noncomputable def kkH (i : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (μ α β : Fin 4) :
    ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ := fun ε x ℓ =>
  dKUnitIntegrandD i 0 R (dkMasses R) ε p p' μ α β ℓ * elemSq (repBClass i) (repBSlot i) p p' ℓ *
    kkSpec i p p' t ε x ℓ

/-- **The limit of the longitudinal dispersive part**, a vertex function of `(p', p)`:
`-2c · wKD 1 · ∑_f ∫₀¹ w_f(x) lim_ε J(K k² (M_f² + x(1-x)k² - iε)⁻¹) dx`. -/
noncomputable def kkLimB (R : Params) (i : Fin 12) : Piece := fun p' p μ =>
  Matrix.of fun α β => -2 * vpCst R * wKD R 1 * ∑ f, ∫ x in Ioo (0 : ℝ) 1,
    dispWt R f x * kkLimX (kkH i R p p' (R.mass f) μ α β) x

/-- **The limit of the longitudinal dispersive part** at any parameters with positive masses,
on-shell external momenta and loop masses `≥ m`, with its value `kkLimB`: by `kkB_eq_unit` the
value is `-2c · wKD 1 · ∑_f` of the joint integrals of the `x`-integrals of `kkVal_dKUnit`. -/
theorem tendsto_kkB (R : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (hΦ : Φ.mass Φ.openLine = R.m) (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
    (hMf : ∀ f, R.m ≤ R.mass f) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -R.m ^ 2)
    (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (i : Fin 12) (μ α β : Fin 4) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
      (kkB { R with ε := ε } Φ i p p' μ α β)) (𝓝[>] 0) (𝓝 (kkLimB R i p' p μ α β)) := by
  have hK : ∀ f : Fin 3, KKVal (dispWt R f) (kkH i R p p' (R.mass f) μ α β) := fun f =>
    kkVal_dKUnit μ α β hm hγ hγΛ hp hp' hq (hMf f) (integrableOn_dispWt R f)
  refine ((tendsto_finsetSum _ fun f _ => (hK f).tendsto).const_mul
    (-2 * vpCst R * wKD R 1)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hpt : ∀ ℓ, kkB { R with ε := ε } Φ i p p' μ α β ℓ =
      (fun ℓ' => -2 * vpCst R * wKD R 1 * ∑ f, ∫ x in Ioo (0 : ℝ) 1, dispWt R f x *
        kkH i R p p' (R.mass f) μ α β ε x ℓ') (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) := fun ℓ =>
    kkB_eq_unit { R with ε := ε } R Φ hΦ rfl rfl rfl i p p' μ α β hε.ne' ℓ
  rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_eq_of_comp (chgMD i) (isUnit_det_chgMD i)
    (G := fun ℓ' => -2 * vpCst R * wKD R 1 * ∑ f, ∫ x in Ioo (0 : ℝ) 1, dispWt R f x *
      kkH i R p p' (R.mass f) μ α β ε x ℓ') _ hpt,
    QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul,
    (jointEnergyFirstIntegrable_finSum _ _ fun f _ => (hK f).2.2.1 ε hε).2]

/-- **The longitudinal dispersive link of `repB i`**, all twelve orbits. -/
theorem mainBKKLink (P₀ : Params) (i : Fin 12) : MainBKKLink P₀ i := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  exact ⟨kkLimB (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) i p' p, tendsto_kkB
    (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) rfl hm hγ hγΛ
    (setCAdm_mass hA) hp hp' hq.le i⟩

end QED.ChainProof.SetCMainB

end
