/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.Routing
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Changing the chords: routings related by an integer unimodular affine map

Obligation O2-5 (ii) (`docs/TWO-LOOP-DERIVATION.md`). Two contractions `C`, `C'` whose internal
lines correspond, with the ends moved by a bijection of the vertices up to orientation
(`LineCorr`), have routings (T₄) related by a change of loop momenta `ℓ ↦ M ℓ + a` with `M` an
integer matrix of determinant `±1`. This is the situation of a relabelling of the vertices: the
labels (X₂₀) change, so the chords (T₁) change.

* `QED.TwoLoop.Relabel.IsIntAffine.lineMomentum₂`: every line momentum of the routing is
  `∑ r, m r • ℓ r + b` with integer `m`.
* `QED.TwoLoop.Relabel.LineCorr.isConserved_pull`: a conserved assignment of `C'`, pulled back
  along the correspondence (with a sign on the reversed lines), is a conserved assignment of `C`.
* `QED.TwoLoop.Relabel.LineCorr.exists_routing_change` (**O2-5 (ii)**): for connected `C`, `C'`
  with the same number of loops, external momenta summing to zero and matching vertex by vertex,
  `pull (lineMomentum₂ C' ℓ) = lineMomentum₂ C (M ℓ + a)` for an integer `M` with
  `IsUnit M.det`. The pulled-back routing is conserved, so by uniqueness
  (`eq_lineMomentum₂_of_isConserved`) it is the routing of `C` at its chord momenta, which are
  integer affine in `ℓ`; the same argument in the other direction gives an integer inverse.
-/

@[expose] public section

namespace QED.TwoLoop.Relabel

open QED.WickModel QED.TwoLoop.Routing

variable {nf nA : ℕ}

/-! ### Integer affine functions of the loop momenta -/

/-- A function of the loop momenta of the form `ℓ ↦ ∑ r, m r • ℓ r + b` with integer `m`. -/
def IsIntAffine {L : ℕ} (F : (Fin L → Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∃ (m : Fin L → ℤ) (b : Fin 4 → ℝ), ∀ ℓ, F ℓ = ∑ r, m r • ℓ r + b

namespace IsIntAffine

variable {L : ℕ} {F G : (Fin L → Fin 4 → ℝ) → Fin 4 → ℝ}

theorem const (b : Fin 4 → ℝ) : IsIntAffine (L := L) fun _ => b :=
  ⟨0, b, fun ℓ => by simp⟩

theorem apply (r₀ : Fin L) : IsIntAffine fun ℓ : Fin L → Fin 4 → ℝ => ℓ r₀ :=
  ⟨Pi.single r₀ 1, 0, fun ℓ => by simp [Pi.single_apply, ite_smul]⟩

theorem add (hF : IsIntAffine F) (hG : IsIntAffine G) : IsIntAffine fun ℓ => F ℓ + G ℓ := by
  obtain ⟨m, b, h⟩ := hF
  obtain ⟨m', b', h'⟩ := hG
  refine ⟨m + m', b + b', fun ℓ => ?_⟩
  simp only [h, h', Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem neg (hF : IsIntAffine F) : IsIntAffine fun ℓ => -F ℓ := by
  obtain ⟨m, b, h⟩ := hF
  refine ⟨-m, -b, fun ℓ => ?_⟩
  simp only [h, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, neg_add]

theorem sub (hF : IsIntAffine F) (hG : IsIntAffine G) : IsIntAffine fun ℓ => F ℓ - G ℓ := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem ite (p : Prop) [Decidable p] (hF : IsIntAffine F) (hG : IsIntAffine G) :
    IsIntAffine fun ℓ => if p then F ℓ else G ℓ := by
  by_cases hp : p <;> simpa [hp]

theorem sum {ι : Type*} (s : Finset ι) {F : ι → (Fin L → Fin 4 → ℝ) → Fin 4 → ℝ}
    (hF : ∀ i, IsIntAffine (F i)) : IsIntAffine fun ℓ => ∑ i ∈ s, F i ℓ := by
  choose m b h using hF
  refine ⟨∑ i ∈ s, m i, ∑ i ∈ s, b i, fun ℓ => ?_⟩
  simp only [h, Finset.sum_add_distrib, Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem chordMomentum {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}
    (g : Line C) : IsIntAffine fun ℓ : Fin L → Fin 4 → ℝ => chordMomentum ℓ g := by
  classical
  unfold QED.WickModel.chordMomentum
  split_ifs with h
  · exact apply _
  · exact const 0

/-- Every line momentum of the routing (T₄) is integer affine in the loop momenta. -/
theorem lineMomentum₂ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (f : Line C) :
    IsIntAffine fun ℓ : Fin L → Fin 4 → ℝ => lineMomentum₂ C pOut pIn kIn ℓ f := by
  classical
  unfold QED.WickModel.lineMomentum₂
  split_ifs with hf
  · exact chordMomentum f
  · refine sum _ fun v => (const _).add (sum _ fun g => ?_)
    exact (ite _ (chordMomentum g) (const 0)).sub (ite _ (chordMomentum g) (const 0))

end IsIntAffine

/-! ### Integer matrices acting on the loop momenta -/

/-- The integer matrix `M` acting on the loop momenta: `(M ℓ) s = ∑ r, M s r • ℓ r`. -/
def matAct {L : ℕ} (M : Matrix (Fin L) (Fin L) ℤ) (ℓ : Fin L → Fin 4 → ℝ) : Fin L → Fin 4 → ℝ :=
  fun s => ∑ r, M s r • ℓ r

theorem matAct_add {L : ℕ} (M : Matrix (Fin L) (Fin L) ℤ) (x y : Fin L → Fin 4 → ℝ) :
    matAct M (x + y) = matAct M x + matAct M y := by
  funext s
  simp [matAct, smul_add, Finset.sum_add_distrib]

theorem matAct_matAct {L : ℕ} (M M' : Matrix (Fin L) (Fin L) ℤ) (ℓ : Fin L → Fin 4 → ℝ) :
    matAct M' (matAct M ℓ) = matAct (M' * M) ℓ := by
  funext s
  simp only [matAct, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

theorem eq_one_of_matAct {L : ℕ} {M : Matrix (Fin L) (Fin L) ℤ}
    (h : ∀ ℓ, matAct M ℓ = ℓ) : M = 1 := by
  ext s t
  have := congrFun (congrFun (h fun r => if r = t then Pi.single 0 1 else 0) s) 0
  simp only [matAct, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
  simp only [Pi.smul_apply, Pi.single_eq_same, zsmul_eq_mul, mul_one] at this
  rw [Matrix.one_apply]
  split_ifs with hst
  · subst hst
    simpa using this
  · simpa [hst] using this

/-! ### Enumerating the chords -/

section Chords

variable {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}

open scoped Classical in
/-- The number of chords below a line. -/
noncomputable def chordRank (f : Line C) : ℕ :=
  (Finset.univ.filter fun g : Line C => IsChord g ∧ g.label < f.label).card

open scoped Classical in
theorem chordRank_lt_of_label_lt {f g : Line C} (hf : IsChord f) (h : f.label < g.label) :
    chordRank f < chordRank g := by
  unfold chordRank
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (fun x hx => ?_) |>.mpr ⟨f, by simp [hf, h], by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩

theorem chordRank_injective :
    Function.Injective fun g : {g : Line C // IsChord g} => chordRank g.1 := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  simp only at h
  rcases lt_trichotomy f.label g.label with hlt | heq | hgt
  · exact absurd h (chordRank_lt_of_label_lt hf hlt).ne
  · exact Subtype.ext (Chord.label_injective heq)
  · exact absurd h (chordRank_lt_of_label_lt hg hgt).ne'

open scoped Classical in
/-- The chords, numbered by increasing label. -/
noncomputable def chordEquiv : {g : Line C // IsChord g} ≃ Fin (loopCount C) :=
  Equiv.ofBijective (fun g => ⟨chordRank g.1, card_chordsBelow_lt g.2⟩) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun x y h => chordRank_injective (congrArg Fin.val h), ?_⟩
    rw [Fintype.card_fin, Fintype.card_subtype]
    rfl

/-- Loop momenta realizing given momenta on the chords. -/
noncomputable def chordValues {L : ℕ} (hL : loopCount C = L) (k : Line C → Fin 4 → ℝ) :
    Fin L → Fin 4 → ℝ :=
  fun r => k ((chordEquiv (C := C)).symm (Fin.cast hL.symm r)).1

theorem chordMomentum_chordValues {L : ℕ} (hL : loopCount C = L) (k : Line C → Fin 4 → ℝ)
    {g : Line C} (hg : IsChord g) : chordMomentum (chordValues hL k) g = k g := by
  subst hL
  classical
  have h := card_chordsBelow_lt hg
  unfold chordMomentum
  simp only [h, ↓reduceDIte]
  have : (chordEquiv (C := C)).symm ⟨_, h⟩ = ⟨g, hg⟩ :=
    (Equiv.symm_apply_eq _).mpr (Fin.ext (by simp [chordEquiv, chordRank]))
  simp only [chordValues, Fin.cast_eq_self]
  convert congrArg (fun x : {g : Line C // IsChord g} => k x.1) this

theorem chordValues_chordMomentum {L : ℕ} (hL : loopCount C = L) (ℓ : Fin L → Fin 4 → ℝ) :
    chordValues hL (fun g => chordMomentum ℓ g) = ℓ := by
  subst hL
  funext r
  set g := (chordEquiv (C := C)).symm r with hg
  have hr : chordEquiv g = r := by rw [hg, Equiv.apply_symm_apply]
  classical
  have h := card_chordsBelow_lt g.2
  simp only [chordValues, Fin.cast_eq_self, ← hg]
  unfold chordMomentum
  simp only [h, ↓reduceDIte]
  congr 1

theorem chordValues_congr {L : ℕ} (hL : loopCount C = L) {k k' : Line C → Fin 4 → ℝ}
    (h : ∀ g, IsChord g → k g = k' g) : chordValues hL k = chordValues hL k' :=
  funext fun _ => h _ ((chordEquiv (C := C)).symm _).2

/-- The routing gives the chords their loop momenta. -/
theorem chordValues_lineMomentum₂ {L : ℕ} (hL : loopCount C = L) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin L → Fin 4 → ℝ) :
    chordValues hL (lineMomentum₂ C pOut pIn kIn ℓ) = ℓ := by
  rw [chordValues_congr hL (k' := fun g => chordMomentum ℓ g) fun g hg => by
    unfold lineMomentum₂
    simp only [hg, ↓reduceIte], chordValues_chordMomentum]

end Chords

/-! ### Corresponding contractions -/

/-- A correspondence of the internal lines of `C` and `C'`: the ends of each line are moved by a
bijection of the vertices, reversed on the lines with `rev f`. -/
structure LineCorr {N N' : ℕ} {κ : Fin N → Wick.VertexKind} {κ' : Fin N' → Wick.VertexKind}
    (C : Contraction nf nA κ) (C' : Contraction nf nA κ') where
  /-- The bijection of the vertices. -/
  vtx : Fin N ≃ Fin N'
  /-- The bijection of the internal lines. -/
  line : Line C ≃ Line C'
  /-- The lines whose orientation is reversed. -/
  rev : Line C → Bool
  ends_line : ∀ f, (line f).ends =
    if rev f then (vtx f.ends.2, vtx f.ends.1) else (vtx f.ends.1, vtx f.ends.2)

namespace LineCorr

variable {N N' : ℕ} {κ : Fin N → Wick.VertexKind} {κ' : Fin N' → Wick.VertexKind}
  {C : Contraction nf nA κ} {C' : Contraction nf nA κ'}

/-- A momentum assignment of `C'` pulled back to `C`, with a sign on the reversed lines. -/
def pull (c : LineCorr C C') (P' : Line C' → Fin 4 → ℝ) (f : Line C) : Fin 4 → ℝ :=
  if c.rev f then -P' (c.line f) else P' (c.line f)

/-- The inverse correspondence. -/
def symm (c : LineCorr C C') : LineCorr C' C where
  vtx := c.vtx.symm
  line := c.line.symm
  rev f' := c.rev (c.line.symm f')
  ends_line f' := by
    have h := c.ends_line (c.line.symm f')
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    cases c.rev (c.line.symm f') <;> simp

theorem pull_symm_pull (c : LineCorr C C') (P' : Line C' → Fin 4 → ℝ) :
    c.symm.pull (c.pull P') = P' := by
  funext f'
  simp only [pull, symm, Equiv.apply_symm_apply]
  cases c.rev (c.line.symm f') <;> simp

theorem inflow_pull (c : LineCorr C C') (P' : Line C' → Fin 4 → ℝ) (v : Fin N) :
    inflow (c.pull P') v = inflow P' (c.vtx v) := by
  unfold inflow
  rw [← c.line.sum_comp]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [c.ends_line f, pull]
  cases c.rev f
  · simp only [Bool.false_eq_true, ↓reduceIte, c.vtx.injective.eq_iff]
  · simp only [↓reduceIte, c.vtx.injective.eq_iff]
    split_ifs <;> abel

/-- A conserved assignment of `C'` pulls back to a conserved assignment of `C`, when the external
momenta match vertex by vertex. -/
theorem isConserved_pull (c : LineCorr C C') {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ}
    (hext : ∀ v, externalMomentum C' pOut pIn kIn (c.vtx v) = externalMomentum C pOut pIn kIn v)
    {P' : Line C' → Fin 4 → ℝ} (hP' : IsConserved C' pOut pIn kIn P') :
    IsConserved C pOut pIn kIn (c.pull P') := fun v => by
  rw [inflow_pull, ← hext]
  exact hP' _

theorem symm_hext (c : LineCorr C C') {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ}
    (hext : ∀ v, externalMomentum C' pOut pIn kIn (c.vtx v) = externalMomentum C pOut pIn kIn v)
    (v : Fin N') :
    externalMomentum C pOut pIn kIn (c.symm.vtx v) = externalMomentum C' pOut pIn kIn v := by
  have := hext (c.vtx.symm v)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

/-- The routing of `C'` pulled back to `C` is the routing of `C` at integer affine chord
momenta. -/
theorem exists_pull_lineMomentum₂ (c : LineCorr C C') {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} (hV' : VerticesConnected C')
    (hext : ∀ v, externalMomentum C' pOut pIn kIn (c.vtx v) = externalMomentum C pOut pIn kIn v)
    (hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0) {L : ℕ} (hL : loopCount C = L) :
    ∃ (M : Matrix (Fin L) (Fin L) ℤ) (a : Fin L → Fin 4 → ℝ), ∀ ℓ : Fin L → Fin 4 → ℝ,
      c.pull (lineMomentum₂ C' pOut pIn kIn ℓ) = lineMomentum₂ C pOut pIn kIn (matAct M ℓ + a) := by
  have hsum' : ∑ v, externalMomentum C' pOut pIn kIn v = 0 := by
    rw [← c.vtx.sum_comp]
    simp only [hext, hsum]
  have haff : ∀ r, IsIntAffine fun ℓ : Fin L → Fin 4 → ℝ =>
      chordValues hL (c.pull (lineMomentum₂ C' pOut pIn kIn ℓ)) r := fun r => by
    simp only [chordValues, pull]
    exact IsIntAffine.ite _ (IsIntAffine.lineMomentum₂ _ _ _ _ _).neg
      (IsIntAffine.lineMomentum₂ _ _ _ _ _)
  choose M a hMa using haff
  refine ⟨Matrix.of M, fun r => a r, fun ℓ => ?_⟩
  have hcons := c.isConserved_pull hext (isConserved_lineMomentum₂ hV' hsum' ℓ)
  have hval : matAct (Matrix.of M) ℓ + (fun r => a r) =
      chordValues hL (c.pull (lineMomentum₂ C' pOut pIn kIn ℓ)) := by
    funext r
    exact (hMa r ℓ).symm
  rw [hval]
  funext f
  exact eq_lineMomentum₂_of_isConserved hcons
    (fun g hg => (chordMomentum_chordValues hL _ hg).symm) f

/-- **Changing the chords** (O2-5 (ii)): for corresponding contractions `C`, `C'` with connected
vertices and the same number `L` of loops, whose external momenta match vertex by vertex and sum to
zero, the routing of `C'` pulled back to `C` is the routing of `C` at `M ℓ + a`, for an integer
matrix `M` with `det M = ±1` and real shifts `a`. -/
theorem exists_routing_change (c : LineCorr C C') {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} (hV : VerticesConnected C) (hV' : VerticesConnected C')
    (hext : ∀ v, externalMomentum C' pOut pIn kIn (c.vtx v) = externalMomentum C pOut pIn kIn v)
    (hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0) {L : ℕ} (hL : loopCount C = L)
    (hL' : loopCount C' = L) :
    ∃ (M : Matrix (Fin L) (Fin L) ℤ), IsUnit M.det ∧ ∃ a : Fin L → Fin 4 → ℝ,
      ∀ ℓ : Fin L → Fin 4 → ℝ, c.pull (lineMomentum₂ C' pOut pIn kIn ℓ) =
        lineMomentum₂ C pOut pIn kIn (matAct M ℓ + a) := by
  obtain ⟨M, a, h⟩ := c.exists_pull_lineMomentum₂ hV' hext hsum hL
  have hsum' : ∑ v, externalMomentum C' pOut pIn kIn v = 0 := by
    rw [← c.vtx.sum_comp]
    simp only [hext, hsum]
  obtain ⟨M', a', h'⟩ := c.symm.exists_pull_lineMomentum₂ hV (c.symm_hext hext) hsum' hL'
  refine ⟨M, ?_, a, h⟩
  -- the composite change of loop momenta is the identity
  have hid : ∀ ℓ : Fin L → Fin 4 → ℝ, matAct M' (matAct M ℓ + a) + a' = ℓ := fun ℓ => by
    have h1 := h' (matAct M ℓ + a)
    rw [← h ℓ, pull_symm_pull] at h1
    have h2 := congrArg (chordValues hL') h1
    rw [chordValues_lineMomentum₂, chordValues_lineMomentum₂] at h2
    exact h2.symm
  have h0 := hid 0
  have hMM : ∀ ℓ, matAct (M' * M) ℓ = ℓ := fun ℓ => by
    have := hid ℓ
    rw [matAct_add, matAct_matAct, add_assoc] at this
    have h0' := h0
    rw [show matAct M (0 : Fin L → Fin 4 → ℝ) = 0 by funext s; simp [matAct], zero_add] at h0'
    rwa [h0', add_zero] at this
  have hone := eq_one_of_matAct hMM
  have hdet : M'.det * M.det = 1 := by rw [← Matrix.det_mul, hone, Matrix.det_one]
  exact IsUnit.of_mul_eq_one_right _ hdet

end LineCorr

end QED.TwoLoop.Relabel

end
