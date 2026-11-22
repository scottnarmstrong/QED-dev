/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopFaceChk1
public import QED.DimReg.ThreeLoopFaceChk2
public import QED.DimReg.ThreeLoopFaceChk3
public import QED.DimReg.ThreeLoopFaceChk4
public import QED.DimReg.ThreeLoopFaceChk5
public import QED.DimReg.ThreeLoopPolyEval

/-!
# Certified sector data and the line family of the face polynomial `G₇`

The kernel checks of `QED.DimReg.ThreeLoopFaceChk1`–`5` and the skeleton check
`QED.DimReg.ThreeLoop.faceSkel` give, on every box `T`, the sector check of the box polynomial
of `G₇ = G|_{x₇ = x₈ = 0}` and the line condition along `(n + λw₇, d₀ + 2h₇λ)` on all leaves
(`box_check`). They assemble into

* `S7 : LPSectorData 7`, the certified sector data of `G₇`;
* `F7 : LineFamily 7`, the Lee–Pomeransky family of `G₇` along the lines of direction
  `w₇ = (1, 1, 1, 1, 2, 2, 2)`, `h₇ = 3`, with `Lp = 4`.
-/

@[expose] public section

namespace QED.DimReg.ThreeLoop

open QED.DimReg.Sector QED.DimReg.LineCont

/-! ### Assembling the pieces -/

theorem faceJobs_ok : ∀ x ∈ faceJobs, chkJob x.1 x.2 = true := by
  have h : faceJobs.all (fun x => chkJob x.1 x.2) = true := by
    simp only [faceJobs, List.all_append, faceChk1, faceChk2, faceChk3, faceChk4, faceChk5,
      faceChk6, faceChk7, faceChk8, faceChk9, faceChk10, faceChk11, faceChk12, faceChk13,
      faceChk14, faceChk15, Bool.and_self]
  simpa only [List.all_eq_true] using h

/-- **The pruned check passes on the box with index `b`**, for every `b < 128`. -/
theorem pchk3_treeB {b : ℕ} (hb : b < 128) : pchk3 h7 (treeB b) (rootQ b) (rootV b) = true := by
  have hs := faceSkel
  simp only [List.all_eq_true, List.mem_range] at hs
  refine pchk3_of_cut h7 (cutsOf b) _ [] _ _ (hs b hb) fun c hc => ?_
  simp only [List.nil_append, cutsOf, List.mem_map, List.mem_filter, beq_iff_eq] at hc
  obtain ⟨⟨b', c'⟩, ⟨hx, hb'⟩, rfl⟩ := hc
  simp only at hb'
  subst hb'
  exact faceJobs_ok _ hx

theorem bitsOf_flagIdx : ∀ fl : List Bool, bitsOf fl.length (flagIdx fl) = fl
  | [] => rfl
  | b :: bs => by
    have h1 : (((if b then 1 else 0) + 2 * flagIdx bs) % 2 == 1) = b := by
      cases b <;> simp [Nat.add_mul_mod_self_left]
    have h2 : ((if b then 1 else 0) + 2 * flagIdx bs) / 2 = flagIdx bs := by
      split <;> omega
    simp only [List.length_cons, bitsOf, flagIdx, h1, h2, bitsOf_flagIdx bs]

theorem flagIdx_lt : ∀ fl : List Bool, flagIdx fl < 2 ^ fl.length
  | [] => by simp [flagIdx]
  | b :: bs => by
    have := flagIdx_lt bs
    simp only [flagIdx, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem coef_g7_ne : ∀ s ∈ g7, s.2 ≠ 0 := by decide +kernel

theorem coef_boxPoly7_ne (fl : List Bool) : ∀ s ∈ boxPoly7 fl, s.2 ≠ 0 := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
  exact coef_g7_ne t ht

theorem w7_le : ∀ i : Fin 7, w7 i ≤ h7 * d7.getD i 0 := by decide

/-- **The sector check and the line check on every box.** -/
theorem box_check (T : Finset (Fin 7)) :
    (⟨treeOf (flagsOf T), [boxPolyF T d7 g7]⟩ : SDCert 7).check = true ∧
      ∀ ps ∈ (treeOf (flagsOf T)).paths, ∀ k, formOk w7 h7
        (leafForm d7 (flagsOf T) ps (NPoly.minE ((boxPolyF T d7 g7).pull ps)) k) = true := by
  have hl : (flagsOf T).length = 7 := by simp [flagsOf]
  have hb : flagIdx (flagsOf T) < 128 := by
    have := flagIdx_lt (flagsOf T)
    rw [hl] at this
    simpa using this
  have hbits : bitsOf 7 (flagIdx (flagsOf T)) = flagsOf T := by
    have := bitsOf_flagIdx (flagsOf T)
    rwa [hl] at this
  have h := pchk3_treeB hb
  unfold rootQ rootV at h
  rw [hbits] at h
  have := check_of_pchk3 (fun i _ => w7_le i) (coef_boxPoly7_ne _) h
  rwa [boxPoly7_eq, flagSet_flagsOf] at this

/-! ### The instances -/

/-- **The certified sector data of `G₇`.** -/
def S7 : LPSectorData 7 where
  G := g7
  D := d7
  tree T := treeOf (flagsOf T)
  deg := deg_g7
  check T := (box_check T).1

theorem S7_G : S7.G = g7 := by simp only [S7]

theorem S7_D : S7.D = d7 := by simp only [S7]

theorem S7_tree (T : Finset (Fin 7)) : S7.tree T = treeOf (flagsOf T) := by simp only [S7]

theorem S7_leafMin (T : Finset (Fin 7)) (ps : List (Fin 7 × Fin 7)) :
    S7.leafMin T ps = NPoly.minE ((boxPolyF T d7 g7).pull ps) := by
  simp only [LPSectorData.leafMin, S7]

/-- **The line condition on all leaves of `S7`.** -/
theorem line7 (T : Finset (Fin 7)) : ∀ ps ∈ (S7.tree T).paths, ∀ k,
    formOk w7 h7 (leafForm S7.D (flagsOf T) ps (S7.leafMin T ps) k) = true := by
  rw [S7_tree, S7_D]
  simp only [S7_leafMin]
  exact (box_check T).2

/-- The terms with nonzero coefficient. -/
def nzTerms (P : ZPoly) : ZPoly := P.filter fun t => t.2 != 0

theorem eval_nzTerms (P : ZPoly) (y : Fin 7 → ℝ) : ZPoly.eval (nzTerms P) y = ZPoly.eval P y := by
  induction P with
  | nil => rfl
  | cons t P ih =>
    by_cases ht : t.2 = 0
    · simp [nzTerms, ht] at ih ⊢; exact ih
    · simp [nzTerms, ht] at ih ⊢; exact ih

/-- The monomials of `xᵢ ∂ᵢ G₇`. -/
def raise7 (i : Fin 7) : ZPoly :=
  nzTerms (ZPoly.mul [(unitExp i, 1)] (ZPoly.diff i (ZPoly.ofN g7)))

/-- The exponent check of `raise7`. -/
def raiseOk7 : Bool :=
  (List.finRange 7).all fun i => (raise7 i).all fun t =>
    Nat.ble 1 (t.1.getD i 0) && Nat.ble ((List.finRange 7).map fun j => t.1.getD j 0).sum 4

theorem raiseOk7_eq : raiseOk7 = true := by decide +kernel

theorem raise7_spec (i : Fin 7) : ∀ t ∈ ZPoly.toML (N := 7) (raise7 i),
    1 ≤ t.2 i ∧ ∑ j, t.2 j ≤ 4 := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
  have h := raiseOk7_eq
  simp only [raiseOk7, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Nat.ble_eq] at h
  obtain ⟨h1, h2⟩ := h i s hs
  exact ⟨h1, by rw [← sum_map_finRange]; exact h2⟩

theorem g7_pos_term : 0 < (g7[0]'(by rw [length_g7]; omega)).2 := by decide +kernel

/-- **The Lee–Pomeransky family of `G₇`** along the lines of direction `(w₇, h₇)`. -/
noncomputable def F7 : LineFamily 7 where
  S := S7
  w := w7
  one_le_w := by decide
  h := h7
  one_le_h := by decide
  Lp := 4
  G' b x := ZPoly.eval (ZPoly.diff b (ZPoly.ofN g7)) x
  pos _ hx := NPoly.eval_pos_of_mem (List.getElem_mem _) g7_pos_term hx
  deriv b x _ := by
    rw [S7_G]
    simpa only [ZPoly.eval_ofN] using ZPoly.hasDerivAt_eval_update (ZPoly.ofN g7) x b
  R i := ZPoly.toML (raise7 i)
  raise i x := by
    rw [ZPoly.polyEval_toML, raise7, eval_nzTerms, ZPoly.eval_mul]
    simp [mono_unitExp]
  raise_spec := raise7_spec
  line := line7

end QED.DimReg.ThreeLoop
