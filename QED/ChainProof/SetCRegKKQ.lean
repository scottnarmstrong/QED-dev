/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKWard2

/-!
# Set (c): the doubly pinched values of the longitudinal integrand

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSum` (`QED/ChainProof/SetCRegKKNorm.lean`).
The second Ward step (`QED/ChainProof/SetCRegKKWard2.lean`) writes the numerator of a pinched
value `QED.ChainProof.SetCRegDisp.kkPin` `P(i, d)` through the scalars `k_{d'}² + m²` of the
electron lines `d'` next to the other end of the element line. Each scalar removes its line;
since the reduction engine needs at least eight lines, the factor `k²/(k² + Λ²)` of the pinched
value is folded back into `k²` over the lines `8`, `9`. The result is the doubly pinched value

`Q(i, d, d') = lim_ε J(N k² D⁻¹)`, `N` the chain with `1` at both ends of the element line and the
electron lines `d`, `d'` deleted, `D` the eight remaining lines;

at the outgoing (incoming) end the Ward identity leaves in addition the end term with
`2m - A(p')` (`A(p) - 2m`), whose Pauli weight vanishes on shell
(`QED/ChainProof/SetCRegKKShell.lean`).

* `kkT_scalar`, `kkT_sq`: the scalar and `k²` reductions pointwise in `ε`;
* `isLoopPolyMat_kNum_one_one`, `refinedBoundMat_kNum_one_one`: the chains with `1` at both ends
  and at most two electron lines have degree two;
* `qPos`, `qι`, **`kkQ`**: the doubly pinched value; `QOk`, `EOk`: its kernel-decidable
  hypotheses;
* **`kkLimX_part`**: one scalar of the second step gives `Q(i, d, d')`;
* `kkEnd`: the end terms; **`kkPin_eq_int`**, **`kkPin_eq_out`**, **`kkPin_eq_in`**: the pinched
  values in doubly pinched values and end terms.
-/

@[expose] public section

open Complex MeasureTheory Set
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.TwoLoop.Enumeration QED.TwoLoop.LimitCovariance
open QED.TwoLoop.Bridge (IsLoopPoly IsLoopPolyMat)
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat)
open QED.Integration.TwoLoop (RefinedBound)

/-! ### The reductions pointwise in `ε` -/

section Pointwise

variable {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t : ℝ}

/-- **The scalar of a line, pointwise**: `k² + M² = D + iε`. -/
theorem kkT_scalar {k : ℕ} (ι : Fin (k + 2) → Fin 10) (j : Fin (k + 2))
    (G : (Fin 2 → Fin 4 → ℝ) → ℂ) {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkT i R p p' t ι (fun ℓ => G ℓ * kkA i R p p' (ι j) ℓ) ε x ℓ =
      kkT i R p p' t (fun a => ι (j.succAbove a)) G ε x ℓ +
        (ε : ℂ) * I * kkT i R p p' t ι G ε x ℓ := by
  have hD := prod_inv_succAbove
    (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a))
    (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p' (ι a))
    (fun a => dkMasses R (ι a)) hε j ℓ
  have hA := sq_add_eq_lineDenom
    (fun a => unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ) (ι a))
    (fun a => unitMMomenta (repBClass i) (repBSlot i) ![1, 1] p p' (ι a))
    (fun a => dkMasses R (ι a)) ε j ℓ
  beta_reduce at hD hA
  simp only [kkT, kkDen]
  rw [hD, show kkA i R p p' (ι j) ℓ = _ from hA]
  ring

/-- **The factor `k²`, pointwise**: `k² = (k² + Λ²) - Λ²` at the line `ι j = 9`. -/
theorem kkT_sq {k : ℕ} (ι : Fin (k + 1) → Fin 10) (j : Fin (k + 1)) (hj : ι j = 9)
    (G : (Fin 2 → Fin 4 → ℝ) → ℂ) (ε x : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkT i R p p' t ι (fun ℓ => G ℓ * elemSq (repBClass i) (repBSlot i) p p' ℓ) ε x ℓ =
      kkT i R p p' t ι (fun ℓ => G ℓ * kkA i R p p' (ι j) ℓ) ε x ℓ -
        ((R.Λ ^ 2 : ℝ) : ℂ) * kkT i R p p' t ι G ε x ℓ := by
  simp only [kkT]
  rw [hj, kkA_nine]
  ring

theorem kSc_eq_kkA (j : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kSc (repBClass i) (repBSlot i) R.m p p' ℓ j = kkA i R p p' (eIdx j) ℓ := by
  rw [kkA, dkMasses_eIdx]
  rfl

end Pointwise

/-! ### The chains with `1` at both ends -/

section Two

variable (π : Equiv.Perm (Fin 5)) (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ)
  (μ : Fin 4) {K : Finset (Fin 4)}

/-- The chain with `1` at both ends and at most two electron lines has degree two. -/
theorem isLoopPolyMat_kNum_one_one (hK : K.card ≤ 2) :
    IsLoopPolyMat 2 2 (kNum π c σ m p p' .one .one K μ) :=
  isLoopPolyMat_kOpen π μ (isLoopPolyMat_kSlotM c σ m p p' .one)
    (isLoopPolyMat_kSlotM c σ m p p' .one) (isLoopPolyMat_kEK c σ m p p' _)
    (by rw [sum_ite_mem_one]; simpa [kSlotD] using hK)

/-- The pointwise bound of the chain with `1` at both ends and at most two electron lines, of
degree two. -/
theorem refinedBoundMat_kNum_one_one (hK : K.card ≤ 2) :
    RefinedBoundMat (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)) (kSet .one .one K) 2
      (kNum π c σ m p p' .one .one K μ) := by
  have hE8 : ∀ (Z : KSlot) (j : Fin 4), Disjoint (kSlotS Z)
      (if j ∈ K then {eIdx j} else ∅) := fun Z j => by
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
  · rw [sum_ite_mem_one]; simpa [kSlotD] using hK

end Two

/-! ### The doubly pinched value -/

/-- The position of the electron line `d'` among the lines kept when `d` is deleted. -/
def qPos (d d' : Fin 4) : Fin 9 :=
  if (d' : ℕ) < d then ⟨d', by omega⟩ else ⟨d' - 1, by omega⟩

/-- The position of the electron line `d'` among the lines kept when `d` and `9` are deleted. -/
def qPos₈ (d d' : Fin 4) : Fin 8 :=
  if (d' : ℕ) < d then ⟨d', by omega⟩ else ⟨d' - 1, by omega⟩

/-- The line map deleting the electron lines `d` and `d'`. -/
def qι (d d' : Fin 4) : Fin 8 → Fin 10 := fun a => (eIdx d).succAbove ((qPos d d').succAbove a)

theorem q_shape : ∀ d d' : Fin 4, d ≠ d' → pinι₈ d (qPos₈ d d') = eIdx d' ∧
    pinι₉ d (qPos d d') = eIdx d' ∧ qι d d' 7 = 9 ∧
    (fun a => pinι₈ d ((qPos₈ d d').succAbove a)) = fun a => qι d d' ((7 : Fin 8).succAbove a) := by
  decide

theorem card_erase_erase_le : ∀ d d' : Fin 4, d ≠ d' →
    ((Finset.univ.erase d).erase d').card ≤ 2 := by
  decide

/-- **The doubly pinched value** `Q(i, d, d')`: the chain with `1` at both ends of the element
line and the electron lines `d`, `d'` deleted, times `k²`, over the eight remaining lines. -/
noncomputable def kkQ (i : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (d d' : Fin 4)
    (μ a b : Fin 4) (x : ℝ) : ℂ :=
  kkLimX (kkT i R p p' t (qι d d') fun ℓ =>
    kNi i R p p' .one .one ((Finset.univ.erase d).erase d') μ ℓ a b *
      elemSq (repBClass i) (repBSlot i) p p' ℓ) x

/-- The kernel-decidable hypotheses of the terms of one scalar of the second step. -/
def QOk (i : Fin 12) (d d' : Fin 4) : Prop :=
  KKOk i (qι d d') (kSet .one .one ((Finset.univ.erase d).erase d') ∪ {8, 9}) ∧
    KKOk i (pinι₈ d) (kSet .one .one ((Finset.univ.erase d).erase d')) ∧
    KKOk i (qι d d') (kSet .one .one ((Finset.univ.erase d).erase d')) ∧
    KKOk i (pinι₉ d) (kSet .one .one ((Finset.univ.erase d).erase d'))

instance (i : Fin 12) (d d' : Fin 4) : Decidable (QOk i d d') := by unfold QOk; infer_instance

/-- The kernel-decidable hypotheses of an end term. -/
def EOk (i : Fin 12) (d : Fin 4) (Y : KSlot) : Prop :=
  KKOk i (pinι₈ d) (kSet .one Y (Finset.univ.erase d)) ∧
    KKOk i (pinι₉ d) (kSet .one Y (Finset.univ.erase d))

instance (i : Fin 12) (d : Fin 4) (Y : KSlot) : Decidable (EOk i d Y) := by
  unfold EOk; infer_instance

/-- **The end term** with `Y` at the other end of the element line and the line `d` deleted. -/
noncomputable def kkEnd (i : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (d : Fin 4)
    (Y : KSlot) (μ a b : Fin 4) (x : ℝ) : ℂ :=
  kkLimX (kkT i R p p' t (pinι₈ d)
      fun ℓ => kNi i R p p' .one Y (Finset.univ.erase d) μ ℓ a b) x -
    ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t (pinι₉ d)
      fun ℓ => kNi i R p p' .one Y (Finset.univ.erase d) μ ℓ a b) x

/-- The family of one scalar of the second step: the term `(k_{d'}² + m²) N` over the lines of
the pinched value, `N` the chain with `1` at both ends and the lines `d`, `d'` deleted. -/
noncomputable def kkPart (i : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (d d' : Fin 4)
    (μ a b : Fin 4) : ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ := fun ε x ℓ =>
  kkT i R p p' t (pinι₈ d) (fun ℓ => kSc (repBClass i) (repBSlot i) R.m p p' ℓ d' *
      kNi i R p p' .one .one ((Finset.univ.erase d).erase d') μ ℓ a b) ε x ℓ -
    ((R.Λ ^ 2 : ℝ) : ℂ) * kkT i R p p' t (pinι₉ d) (fun ℓ =>
      kSc (repBClass i) (repBSlot i) R.m p p' ℓ d' *
        kNi i R p p' .one .one ((Finset.univ.erase d).erase d') μ ℓ a b) ε x ℓ

/-- The family of a pinched value with the slots `1`, `Y` and the line `d` deleted. -/
noncomputable def kkPinF (i : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (d : Fin 4)
    (Y : KSlot) (μ a b : Fin 4) : ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ := fun ε x ℓ =>
  kkT i R p p' t (pinι₈ d) (fun ℓ => kNi i R p p' .one Y (Finset.univ.erase d) μ ℓ a b) ε x ℓ +
    -((R.Λ ^ 2 : ℝ) : ℂ) * kkT i R p p' t (pinι₉ d)
      (fun ℓ => kNi i R p p' .one Y (Finset.univ.erase d) μ ℓ a b) ε x ℓ

/-! ### One scalar of the second step -/

section Part

variable {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t : ℝ} {w : ℝ → ℂ} {x : ℝ}
  (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
  (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
  (ht : R.m ≤ t) (hw : IntegrableOn w (Ioo 0 1)) (hx : x ∈ Ioo (0 : ℝ) 1)
include hm hγ hγΛ hp hp' hq ht hw hx

/-- **One scalar of the second step**: the pinched value of the term `(k_{d'}² + m²) N`, `N` the
chain with `1` at both ends and the lines `d`, `d'` deleted, is the doubly pinched value
`Q(i, d, d')`; the family has a dispersive limit. -/
theorem kkLimX_part {d d' : Fin 4} (hd : d ≠ d') (hok : QOk i d d') (μ a b : Fin 4) :
    KKVal w (kkPart i R p p' t d d' μ a b) ∧ kkLimX (kkPart i R p p' t d d' μ a b) x =
      kkQ i R p p' t d d' μ a b x := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hok
  obtain ⟨s₈, s₉, s₇, sf⟩ := q_shape d d' hd
  set K := (Finset.univ.erase d).erase d'
  set G : (Fin 2 → Fin 4 → ℝ) → ℂ := fun ℓ => kNi i R p p' .one .one K μ ℓ a b
  have hK := card_erase_erase_le d d' hd
  have hP : IsLoopPoly 2 4 G :=
    isLoopPolyMat_kNum _ _ _ _ _ _ _ _ _ μ (by simpa [kSlotD] using hK.trans (by norm_num)) a b
  have hB : RefinedBound (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
      (kSet .one .one K) 4 G :=
    refinedBoundMat_kNum _ _ _ _ _ _ _ _ _ μ (by simp [kSlotS])
      (by simpa [kSlotD] using hK.trans (by norm_num)) a b
  have hP2 : IsLoopPoly 2 4 fun ℓ => G ℓ * elemSq (repBClass i) (repBSlot i) p p' ℓ :=
    (isLoopPolyMat_kNum_one_one _ _ _ _ _ _ μ hK a b).mul (isLoopPoly_elemSq _ _ p p')
  have hB2 : RefinedBound (unitMMatrix (repBClass i) (repBSlot i) (![1, 1] : Fin 2 → ℝ))
      (kSet .one .one K ∪ {8, 9}) 4 fun ℓ => G ℓ * elemSq (repBClass i) (repBSlot i) p p' ℓ :=
    (refinedBoundMat_kNum_one_one _ _ _ _ _ _ μ hK a b).mul (refinedBound_elemSq _ _ p p')
      (by
        refine Finset.disjoint_left.2 fun q hq hq' => ?_
        simp only [kSet, kSlotS, Finset.union_empty, Finset.mem_image] at hq
        obtain ⟨j, -, rfl⟩ := hq
        revert hq'
        revert j
        decide)
  have vQ := kkVal_kkT hm hγ hγΛ hp hp' hq ht hw le_rfl h₁ hP2 hB2
  have v₈ := kkVal_kkT hm hγ hγΛ hp hp' hq ht hw le_rfl h₂ hP hB
  have v₈' := kkVal_kkT hm hγ hγΛ hp hp' hq ht hw le_rfl h₃ hP hB
  have v₉ := kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) h₄ hP hB
  have hS := (v₈.add (v₈'.const_mul (-1))).add (v₉.const_mul (-((R.Λ ^ 2 : ℝ) : ℂ)))
  have hR := hS.coef (fun ε => (ε : ℂ) * I) tendsto_ofReal_mul_I (A := 1)
    fun ε hε hε1 => by simpa [abs_of_pos hε] using hε1
  have key : ∀ ε : ℝ, 0 < ε → ∀ x ∈ Ioo (0 : ℝ) 1, ∀ ℓ,
      kkT i R p p' t (qι d d') (fun ℓ => G ℓ * elemSq (repBClass i) (repBSlot i) p p' ℓ) ε x ℓ +
        (ε : ℂ) * I * (kkT i R p p' t (pinι₈ d) G ε x ℓ + -1 * kkT i R p p' t (qι d d') G ε x ℓ +
          -((R.Λ ^ 2 : ℝ) : ℂ) * kkT i R p p' t (pinι₉ d) G ε x ℓ) =
      kkT i R p p' t (pinι₈ d) (fun ℓ => kSc (repBClass i) (repBSlot i) R.m p p' ℓ d' * G ℓ)
          ε x ℓ -
        ((R.Λ ^ 2 : ℝ) : ℂ) * kkT i R p p' t (pinι₉ d)
          (fun ℓ => kSc (repBClass i) (repBSlot i) R.m p p' ℓ d' * G ℓ) ε x ℓ :=
    fun ε hε x _ ℓ => by
      have e₁ := kkT_scalar (i := i) (R := R) (p := p) (p' := p') (t := t) (pinι₈ d)
        (qPos₈ d d') G hε.ne' x ℓ
      have e₂ := kkT_scalar (i := i) (R := R) (p := p) (p' := p') (t := t) (pinι₉ d)
        (qPos d d') G hε.ne' x ℓ
      have e₃ := kkT_scalar (i := i) (R := R) (p := p) (p' := p') (t := t) (qι d d') 7 G
        hε.ne' x ℓ
      have e₄ := kkT_sq (i := i) (R := R) (p := p) (p' := p') (t := t) (qι d d') 7 s₇ G ε x ℓ
      rw [s₈] at e₁
      rw [s₉] at e₂
      change _ = kkT i R p p' t (qι d d') G ε x ℓ + _ at e₂
      rw [sf] at e₁
      have e₅ : (fun ℓ => kSc (repBClass i) (repBSlot i) R.m p p' ℓ d' * G ℓ) =
          fun ℓ => G ℓ * kkA i R p p' (eIdx d') ℓ := funext fun ℓ => by rw [kSc_eq_kkA, mul_comm]
      rw [e₅, e₁, e₂, e₄, e₃]
      ring
  refine ⟨(vQ.add hR).congr key, ?_⟩
  unfold kkPart
  rw [← KKVal.limX_congr key hx, KKVal.limX_add vQ hR hx,
    KKVal.limX_coef _ tendsto_ofReal_mul_I hS hx, zero_mul, add_zero]
  rfl

end Part

/-! ### The pinched values in doubly pinched values -/

/-- The kernel-decidable hypotheses of a pinched value. -/
def POk (i : Fin 12) (d : Fin 4) : Prop :=
  KKOk i (pinι₈ d) (kSet .one .q (Finset.univ.erase d)) ∧
    KKOk i (pinι₉ d) (kSet .one .q (Finset.univ.erase d))

instance (i : Fin 12) (d : Fin 4) : Decidable (POk i d) := by unfold POk; infer_instance

section Pin

variable {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t : ℝ} {w : ℝ → ℂ} {x : ℝ}
  (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
  (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
  (ht : R.m ≤ t) (hw : IntegrableOn w (Ioo 0 1)) (hx : x ∈ Ioo (0 : ℝ) 1)
include hm hγ hγΛ hp hp' hq ht hw hx

/-- **The value of the family `kkPinF`** with dispersive limits of its two terms. -/
theorem kkVal_pinF {d : Fin 4} {Y : KSlot} (hY : kSlotD Y ≤ 1)
    (h₈ : KKOk i (pinι₈ d) (kSet .one Y (Finset.univ.erase d)))
    (h₉ : KKOk i (pinι₉ d) (kSet .one Y (Finset.univ.erase d))) (μ a b : Fin 4) :
    KKVal w (kkPinF i R p p' t d Y μ a b) ∧ kkLimX (kkPinF i R p p' t d Y μ a b) x =
      kkLimX (kkT i R p p' t (pinι₈ d)
          fun ℓ => kNi i R p p' .one Y (Finset.univ.erase d) μ ℓ a b) x -
        ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t (pinι₉ d)
          fun ℓ => kNi i R p p' .one Y (Finset.univ.erase d) μ ℓ a b) x := by
  have hd : kSlotD .one + kSlotD Y + (Finset.univ.erase d).card ≤ 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    show 0 + kSlotD Y + (4 - 1) ≤ 4
    omega
  have hS : Disjoint (kSlotS .one) (kSlotS Y) := by simp [kSlotS]
  have hP := isLoopPolyMat_kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .one Y
    (Finset.univ.erase d) μ hd a b
  have hB := refinedBoundMat_kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .one Y
    (Finset.univ.erase d) μ hS hd a b
  have v₈ := kkVal_kkT hm hγ hγΛ hp hp' hq ht hw le_rfl h₈ hP hB
  have v₉ := kkVal_kkT hm hγ hγΛ hp hp' hq ht hw (by norm_num) h₉ hP hB
  refine ⟨v₈.add (v₉.const_mul _), ?_⟩
  unfold kkPinF
  rw [KKVal.limX_add v₈ (v₉.const_mul _) hx, KKVal.limX_const_mul _ v₉ hx]
  ring

/-- **A pinched value at an internal other end** `kOthD i = j + 1`:
`P(i, d) = σ (Q(i, d, j + 1) - Q(i, d, j))`. -/
theorem kkPin_eq_int {d : Fin 4} (j : Fin 3) (hj : kOthD i = j.succ.castSucc)
    (h₁ : j.succ ≠ d) (h₂ : j.castSucc ≠ d) (hok : POk i d) (hq₁ : QOk i d j.succ)
    (hq₂ : QOk i d j.castSucc) (μ a b : Fin 4) :
    kkPin i R p p' t d μ a b x = ((kSgnO i : ℤ) : ℂ) *
      (kkQ i R p p' t d j.succ μ a b x - kkQ i R p p' t d j.castSucc μ a b x) := by
  obtain ⟨-, e⟩ := kkVal_pinF hm hγ hγΛ hp hp' hq ht hw hx (by simp [kSlotD]) hok.1 hok.2 μ a b
  obtain ⟨u₁, l₁⟩ := kkLimX_part hm hγ hγΛ hp hp' hq ht hw hx h₁.symm hq₁ μ a b
  obtain ⟨u₂, l₂⟩ := kkLimX_part hm hγ hγΛ hp hp' hq ht hw hx h₂.symm hq₂ μ a b
  rw [kkPin, ← e, KKVal.limX_congr (H₁ := fun ε x ℓ => ((kSgnO i : ℤ) : ℂ) *
      (kkPart i R p p' t d j.succ μ a b ε x ℓ + -1 * kkPart i R p p' t d j.castSucc μ a b ε x ℓ))
      (fun ε _ x _ ℓ => ?_) hx,
    KKVal.limX_const_mul _ (u₁.add (u₂.const_mul (-1))) hx,
    KKVal.limX_add u₁ (u₂.const_mul _) hx, KKVal.limX_const_mul _ u₂ hx, l₁, l₂]
  · ring
  have hN := congrFun (congrFun (kNi_pin_ward_int i p p' ℓ R d μ j hj h₁ h₂) a) b
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at hN
  simp only [kkPinF, kkPart, kkT, hN]
  ring

/-- **A pinched value at the outgoing other end** `kOthD i = 4`:
`P(i, d) = σ (E(i, d) - Q(i, d, 3))`, `E` the end term with `2m - A(p')`. -/
theorem kkPin_eq_out {d : Fin 4} (hO : kOthD i = 4) (h₃ : (3 : Fin 4) ≠ d) (hok : POk i d)
    (he : EOk i d .out) (hq₃ : QOk i d 3) (μ a b : Fin 4) :
    kkPin i R p p' t d μ a b x = ((kSgnO i : ℤ) : ℂ) *
      (kkEnd i R p p' t d .out μ a b x - kkQ i R p p' t d 3 μ a b x) := by
  obtain ⟨-, e⟩ := kkVal_pinF hm hγ hγΛ hp hp' hq ht hw hx (by simp [kSlotD]) hok.1 hok.2 μ a b
  obtain ⟨o, eo⟩ := kkVal_pinF hm hγ hγΛ hp hp' hq ht hw hx (by simp [kSlotD]) he.1 he.2 μ a b
  obtain ⟨u₃, l₃⟩ := kkLimX_part hm hγ hγΛ hp hp' hq ht hw hx h₃.symm hq₃ μ a b
  rw [kkPin, ← e, kkEnd, ← eo, KKVal.limX_congr (H₁ := fun ε x ℓ => ((kSgnO i : ℤ) : ℂ) *
      (kkPinF i R p p' t d .out μ a b ε x ℓ + -1 * kkPart i R p p' t d 3 μ a b ε x ℓ))
      (fun ε _ x _ ℓ => ?_) hx,
    KKVal.limX_const_mul _ (o.add (u₃.const_mul (-1))) hx,
    KKVal.limX_add o (u₃.const_mul _) hx, KKVal.limX_const_mul _ u₃ hx, l₃]
  · ring
  have hN := congrFun (congrFun (kNi_pin_ward_out i p p' ℓ R d μ hO h₃) a) b
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at hN
  simp only [kkPinF, kkPart, kkT, hN]
  ring

/-- **A pinched value at the incoming other end** `kOthD i = 0`:
`P(i, d) = σ (E(i, d) + Q(i, d, 0))`, `E` the end term with `A(p) - 2m`. -/
theorem kkPin_eq_in {d : Fin 4} (hO : kOthD i = 0) (h₀ : (0 : Fin 4) ≠ d) (hok : POk i d)
    (he : EOk i d .inn) (hq₀ : QOk i d 0) (μ a b : Fin 4) :
    kkPin i R p p' t d μ a b x = ((kSgnO i : ℤ) : ℂ) *
      (kkEnd i R p p' t d .inn μ a b x + kkQ i R p p' t d 0 μ a b x) := by
  obtain ⟨-, e⟩ := kkVal_pinF hm hγ hγΛ hp hp' hq ht hw hx (by simp [kSlotD]) hok.1 hok.2 μ a b
  obtain ⟨o, eo⟩ := kkVal_pinF hm hγ hγΛ hp hp' hq ht hw hx (by simp [kSlotD]) he.1 he.2 μ a b
  obtain ⟨u₀, l₀⟩ := kkLimX_part hm hγ hγΛ hp hp' hq ht hw hx h₀.symm hq₀ μ a b
  rw [kkPin, ← e, kkEnd, ← eo, KKVal.limX_congr (H₁ := fun ε x ℓ => ((kSgnO i : ℤ) : ℂ) *
      (kkPinF i R p p' t d .inn μ a b ε x ℓ + kkPart i R p p' t d 0 μ a b ε x ℓ))
      (fun ε _ x _ ℓ => ?_) hx,
    KKVal.limX_const_mul _ (o.add u₀) hx, KKVal.limX_add o u₀ hx, l₀]
  have hN := congrFun (congrFun (kNi_pin_ward_in i p p' ℓ R d μ hO h₀) a) b
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] at hN
  simp only [kkPinF, kkPart, kkT, hN]
  ring

end Pin

end QED.ChainProof.SetCRegDisp

end
