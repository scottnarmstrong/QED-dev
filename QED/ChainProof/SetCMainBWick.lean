/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBClosed
public import QED.ChainProof.SetCMainDChain
public import QED.ChainProof.SetCLinkIntB

/-!
# Set (c), the bubble classes: the combinatorics of the Wick step

Helper level for set (c), the bubble classes `QED.ChainProof.SetCLink.repB i` (seven `gauge`
vertices, the bubble on the vertices `5`, `6`). The contraction `repB i` is
`QED.ChainProof.SetCLink.repD i 0` with the `photonCt` vertex replaced by the bubble: the same
open line, the photon fields `skP i ↔ 5`, `6 ↔ skQ i` in place of `skP i ↔ (5, 0)`,
`(5, 1) ↔ skQ i`, and the same third photon line. This file records that dictionary and the
routing, all checked by kernel evaluation on the twelve orbits:

* `mv3`, `mvReal3`, **`lineMomentum₂_eq_mv3`**: a line momentum at three loops as an integer
  vector (the three loop coefficients and those of `p_in`, `k_in`);
* `vB`, `slotKB`: the fermion fields of `kB` as those of `kD` plus the two bubble fields, and the
  photon fields of `kB` as those of `kD` (`pgB 5 ↦ (5, 0)`, `pgB 6 ↦ (5, 1)`);
* `lineBO`, `lineBb`, `photB`: the lines of `repB i` (the four open lines in the labels of
  `QED.ChainProof.SetCMain.lineRD`, the two bubble lines, the three photon lines);
* **`mv3_lineBO`**, **`mv3_lineBb`**, **`mv3_photB`**: in the frozen routing the bubble momentum is
  the third loop momentum, the open lines and photon lines carry the momenta of the
  corresponding lines of `repD i 0` at the first two, and the second bubble line carries the
  bubble momentum plus the photon momentum of `repD i 0` at its field `(5, 0)`.
-/

@[expose] public section

open Complex
open QED.WickModel (Params Contraction FermionLine PhotonLine Line lineMomentum₂
  photonMomentum₂)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCLink QED.ChainProof.SetALink QED.ChainProof.SetALinkV
open QED.GradedProof.X0
open QED.ChainProof.SetCMain (fvD lineRD lineRD_bijective lineRD_tail photD photD_bijective
  lowEnd)
open QED.ChainProof.Enum (pc)
open QED.TwoLoop.Enumeration (lineData)

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Integer momentum vectors at three loops -/

/-- The integer momentum vector of a line at three loops: the loop row and, with
`p_out = p_in + k_in`, the coefficients of `p_in` and `k_in`. -/
def mv3 (C : Contraction 1 1 κ) (l : Line C) : Fin 5 → ℤ :=
  ![row3 C l 0, row3 C l 1, row3 C l 2,
    if edgeChord (lineData C) (edgeOf l) then 0 else
      cIn C (edgeSide (lineData C) (edgeOf l)) - cOut C (edgeSide (lineData C) (edgeOf l)),
    if edgeChord (lineData C) (edgeOf l) then 0 else
      cK C (edgeSide (lineData C) (edgeOf l)) - cOut C (edgeSide (lineData C) (edgeOf l))]

/-- The momentum of an integer vector at three loops. -/
noncomputable def mvReal3 (ℓ : Fin 3 → Fin 4 → ℝ) (p q : Fin 4 → ℝ) (v : Fin 5 → ℤ) :
    Fin 4 → ℝ :=
  ((v 0 : ℤ) : ℝ) • ℓ 0 + ((v 1 : ℤ) : ℝ) • ℓ 1 + ((v 2 : ℤ) : ℝ) • ℓ 2 +
    ((v 3 : ℤ) : ℝ) • p + ((v 4 : ℤ) : ℝ) • q

/-- **A line momentum at three loops as its integer vector**, under momentum conservation. -/
theorem lineMomentum₂_eq_mv3 (C : Contraction 1 1 κ) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 3 → Fin 4 → ℝ) (l : Line C) :
    lineMomentum₂ C pOut pIn kIn ℓ l = mvReal3 ℓ (pIn 0) (kIn 0) (mv3 C l) := by
  rw [lineMomentum₂_eq_rowMom3, extPart]
  split_ifs with h
  · simp [mvReal3, rowMom3, row3, mv3, h, Fin.sum_univ_three]
  · rw [sum_externalMomentum_D C pOut pIn kIn hmom]
    simp [mvReal3, rowMom3, row3, mv3, h, Fin.sum_univ_three]
    abel

/-- A two-loop integer vector at three loops, with no third loop momentum. -/
def ext3 (v : Fin 4 → ℤ) : Fin 5 → ℤ := ![v 0, v 1, 0, v 2, v 3]

/-- The bubble momentum. -/
def bub3 : Fin 5 → ℤ := ![0, 0, 1, 0, 0]

/-- The loop momenta of the frozen routing of `repB i` from the nested ones: the bubble momentum
`ℓ 0` is the third. -/
def rot (ℓ : Fin 3 → Fin 4 → ℝ) : Fin 3 → Fin 4 → ℝ := ![ℓ 1, ℓ 2, ℓ 0]

/-- The matrix of `rot`. -/
def rotM : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem isUnit_det_rotM : IsUnit rotM.det := by
  rw [Int.isUnit_iff]
  left
  simp [rotM, Matrix.det_fin_three]

theorem rot_eq (ℓ : Fin 3 → Fin 4 → ℝ) : rot ℓ = (fun s => ∑ r, rotM s r • ℓ r) + 0 := by
  funext s
  fin_cases s <;> simp [rot, rotM, Fin.sum_univ_three]

theorem mvReal3_rot_ext3 (ℓ : Fin 3 → Fin 4 → ℝ) (p q : Fin 4 → ℝ) (v : Fin 4 → ℤ) :
    mvReal3 (rot ℓ) p q (ext3 v) = mvReal (Fin.tail ℓ) p q v := by
  simp [mvReal3, mvReal, rot, ext3, Fin.tail]

theorem mvReal3_rot_bub (ℓ : Fin 3 → Fin 4 → ℝ) (p q : Fin 4 → ℝ) (v : Fin 4 → ℤ) :
    mvReal3 (rot ℓ) p q (ext3 v + bub3) = mvReal (Fin.tail ℓ) p q v + ℓ 0 := by
  simp [mvReal3, mvReal, rot, ext3, bub3, Fin.tail]
  abel

theorem mvReal3_rot_bub3 (ℓ : Fin 3 → Fin 4 → ℝ) (p q : Fin 4 → ℝ) :
    mvReal3 (rot ℓ) p q bub3 = ℓ 0 := by
  simp [mvReal3, rot, bub3]

/-! ### The fields of `kB` as those of `kD` -/

/-- The fermion fields of `kB`: the open-line vertices `t < 5` are those of `kD`, the bubble
vertices `5`, `6` are `0`, `1`. -/
def vB (t : Wick.FermionVertex kB) : Wick.FermionVertex kD ⊕ Fin 2 :=
  if h : t.1.val < 5 then .inl (fvD ⟨t.1.val, h⟩) else .inr ⟨t.1.val - 5, by omega⟩

/-- The photon fields of `kD` indexed by the vertices of `kB`. -/
def slotTab : Fin 7 → Wick.PhotonSlot kD :=
  ![plD 0, plD 1, plD 2, plD 3, plD 4, pc kD 5 0, pc kD 5 1]

/-- The photon field of `kD` of a photon field of `kB`. -/
def slotKB (y : Wick.PhotonSlot kB) : Wick.PhotonSlot kD := slotTab y.1

theorem vB_bijective : Function.Bijective vB := by decide

theorem slotB_bijective : Function.Bijective slotKB := by decide

/-- A spinor assignment of `kB` from one of `kD` and one of the two bubble vertices. -/
def glue (α : Wick.FermionVertex kD → Fin 4) (a : Fin 2 → Fin 4) (t : Wick.FermionVertex kB) :
    Fin 4 :=
  Sum.elim α a (vB t)

theorem sum_glue (G : (Wick.FermionVertex kB → Fin 4) → ℂ) :
    ∑ α, G α = ∑ α : Wick.FermionVertex kD → Fin 4, ∑ a : Fin 2 → Fin 4, G (glue α a) := by
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv ((Equiv.arrowCongr (Equiv.ofBijective vB vB_bijective)
    (Equiv.refl (Fin 4))).trans (Equiv.sumArrowEquivProdArrow _ _ _)) _ _ fun α => ?_)
  refine congrArg G (funext fun t => ?_)
  set E := Equiv.ofBijective vB vB_bijective
  have hE : ∀ x, E.symm (vB x) = x := fun x => E.symm_apply_apply x
  unfold glue
  rcases h : vB t with v | j
  · simp only [Sum.elim_inl, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr,
      Equiv.coe_fn_mk, Function.comp_apply, Equiv.refl_apply]
    rw [← h, hE]
  · simp only [Sum.elim_inr, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr,
      Equiv.coe_fn_mk, Function.comp_apply, Equiv.refl_apply]
    rw [← h, hE]

theorem sum_slotB (G : (Wick.PhotonSlot kB → Fin 4) → ℂ) :
    ∑ lor, G lor = ∑ lor : Wick.PhotonSlot kD → Fin 4, G (lor ∘ slotKB) := by
  refine (Fintype.sum_equiv (Equiv.arrowCongr (Equiv.ofBijective slotKB slotB_bijective)
    (Equiv.refl (Fin 4))) _ _ fun lor => ?_)
  refine congrArg G (funext fun y => ?_)
  simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply]
  exact congrArg lor ((Equiv.ofBijective slotKB slotB_bijective).symm_apply_apply y).symm

/-! ### The lines of `repB i` -/

theorem lineBO_spec : ∀ (i : Fin 12) (j : Fin 4),
    ((repB i).1.1 (.inr (fvB (Fin.castLE (by norm_num) (Fin.rev j.succ))))).isRight := by
  decide +kernel

/-- The open fermion line of `repB i` that is the line `lineRD i 0 j` of `repD i 0`. -/
def lineBO (i : Fin 12) (j : Fin 4) : FermionLine (repB i) :=
  ⟨fvB (Fin.castLE (by norm_num) (Fin.rev j.succ)), lineBO_spec i j⟩

theorem lineBb_spec : ∀ (i : Fin 12) (s : Fin 2),
    ((repB i).1.1 (.inr (fvB (![5, 6] s)))).isRight := by
  decide +kernel

/-- The bubble line of `repB i` starting at the bubble vertex `5 + s`. -/
def lineBb (i : Fin 12) (s : Fin 2) : FermionLine (repB i) := ⟨fvB (![5, 6] s), lineBb_spec i s⟩

/-- All fermion lines of `repB i`. -/
def lineBAll (i : Fin 12) : Fin 4 ⊕ Fin 2 → FermionLine (repB i) := Sum.elim (lineBO i) (lineBb i)

theorem lineBAll_bijective : ∀ i, Function.Bijective (lineBAll i) := by decide +kernel

theorem prod_lineB {M : Type*} [CommMonoid M] (i : Fin 12) (g : FermionLine (repB i) → M) :
    ∏ f, g f = (∏ j, g (lineBO i j)) * (g (lineBb i 0) * g (lineBb i 1)) := by
  rw [← (Equiv.ofBijective _ (lineBAll_bijective i)).prod_comp, Fintype.prod_sum_type,
    Fin.prod_univ_two]
  rfl

theorem prod_lineRD0 {M : Type*} [CommMonoid M] (i : Fin 12) (g : FermionLine (repD i 0) → M) :
    ∏ f, g f = ∏ j, g (lineRD i 0 j) :=
  ((Equiv.ofBijective _ (lineRD_bijective i 0)).prod_comp g).symm

/-- The fermion fields of the open lines are those of `repD i 0`. -/
theorem vB_lineBO : ∀ (i : Fin 12) (j : Fin 4), vB (lineBO i j).1 = .inl (lineRD i 0 j).1 ∧
    vB (lineBO i j).tail = .inl (lineRD i 0 j).tail := by
  decide +kernel

theorem vB_lineBb : ∀ i : Fin 12, vB (lineBb i 0).1 = .inr 0 ∧ vB (lineBb i 0).tail = .inr 1 ∧
    vB (lineBb i 1).1 = .inr 1 ∧ vB (lineBb i 1).tail = .inr 0 := by
  decide +kernel

theorem zOf_lineBO : ∀ (i : Fin 12) (j : Fin 4), ¬ zOf (repB i) (lineBO i j).1 := by
  decide +kernel

theorem zOf_lineBb : ∀ (i : Fin 12) (s : Fin 2), zOf (repB i) (lineBb i s).1 := by
  decide +kernel

/-- One end of each of the three photon lines of `repB i`: the bubble fields and the other
photon line. -/
def photEndB (i : Fin 12) : Fin 3 → Wick.PhotonSlot kB := ![pgB 5, pgB 6, plB (skR i)]

theorem photB_spec : ∀ (i : Fin 12) (r : Fin 3), ∃ b,
    (repB i).1.2 (.inr (lowEnd (repB i) (photEndB i r))) = .inr b ∧
      Wick.photonKey (lowEnd (repB i) (photEndB i r)) < Wick.photonKey b := by
  decide +kernel

/-- The three photon lines of `repB i`. -/
def photB (i : Fin 12) (r : Fin 3) : PhotonLine (repB i) :=
  ⟨lowEnd (repB i) (photEndB i r), photB_spec i r⟩

theorem photB_bijective : ∀ i, Function.Bijective (photB i) := by decide +kernel

theorem prod_photB {M : Type*} [CommMonoid M] (i : Fin 12) (g : PhotonLine (repB i) → M) :
    ∏ x, g x = ∏ r, g (photB i r) :=
  ((Equiv.ofBijective _ (photB_bijective i)).prod_comp g).symm

theorem prod_photD0 {M : Type*} [CommMonoid M] (i : Fin 12) (g : PhotonLine (repD i 0) → M) :
    ∏ x, g x = ∏ r, g (photD i 0 r) :=
  ((Equiv.ofBijective _ (photD_bijective i 0)).prod_comp g).symm

/-- The photon fields of the photon lines are those of `repD i 0`. -/
theorem slotB_photB : ∀ (i : Fin 12) (r : Fin 3), slotKB (photB i r).1 = (photD i 0 r).1 ∧
    slotKB (photB i r).head = (photD i 0 r).head := by
  decide +kernel

/-- The external fields of `repB i`. -/
theorem ext_repB : ∀ i : Fin 12, (repB i).1.1 (.inl 0) = .inr (fvB 0) ∧
    (repB i).1.1 (.inr (fvB 4)) = .inl 0 ∧ (repB i).1.2 (.inl 0) = .inr (plB (skE i)) := by
  decide +kernel

/-- The external fields of `repD i 0`. -/
theorem ext_repD0 : ∀ i : Fin 12, (repD i 0).1.1 (.inl 0) = .inr (fvD 0) ∧
    (repD i 0).1.1 (.inr (fvD 4)) = .inl 0 ∧ (repD i 0).1.2 (.inl 0) = .inr (plD (skE i)) := by
  decide +kernel

/-! ### The routing -/

theorem mv3_lineBO : ∀ (i : Fin 12) (j : Fin 4),
    mv3 (repB i) (.inl (lineBO i j)) = ext3 (mv (repD i 0) (.inl (lineRD i 0 j))) := by
  decide +kernel

theorem mv3_lineBb : ∀ i : Fin 12, mv3 (repB i) (.inl (lineBb i 0)) = bub3 ∧
    mv3 (repB i) (.inl (lineBb i 1)) = ext3 (pmv (repD i 0) (pc kD 5 0)) + bub3 := by
  decide +kernel

theorem mv3_photB : ∀ (i : Fin 12) (r : Fin 3),
    mv3 (repB i) (.inr (photB i r)) = ext3 (mv (repD i 0) (.inr (photD i 0 r))) := by
  decide +kernel

end QED.ChainProof.SetCMainB

end
