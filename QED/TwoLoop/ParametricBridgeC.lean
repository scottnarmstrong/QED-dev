/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ParametricBridgeLX
public import QED.TwoLoop.LoopPolySubst

/-!
# The corner classes in parametric form

Part of obligations O2-7 and O2-10 (`docs/TWO-LOOP-DERIVATION.md`, sections 4.1–4.4) for the
corner classes `C₊`, `C₋` of five gauge vertices (`QED.TwoLoop.Enumeration.Class5.Cp`, `.Cm`),
continuing `QED/TwoLoop/ParametricBridgeLX.lean`. Their representatives have the open line
`0 → 1 → 2 → 3 → 4` and

| class | external photon at | internal photons | chords (T₁) |
| --- | --- | --- | --- |
| `C₊` | `1` | `(0 3) (2 4)` | `v₀v₁` (`ℓ 0`), `v₂v₃` (`ℓ 1`) |
| `C₋` | `3` | `(0 2) (1 4)` | `v₀v₁` (`ℓ 0`), `v₁v₂` (`ℓ 1`) |

**Common data** (used also for `S±` in `QED/TwoLoop/ParametricBridgeS.lean`): `extMomenta c` are
the external momenta of the class lines of `QED/Integration/SymanzikPositivityClasses.lean`
(`classCpSpMomenta` for `C₊`, `S₊`; `classCmSmMomenta` for `C₋`, `S₋`; `classLXMomenta` for `L`,
`X`), `classMomE c` the routing by `class5LoopMatrix c` and these momenta, `classNumeratorE` the
numerator of the amplitude in that routing and `pvDenomE c` the eight Pauli–Villars line
denominators (loop matrix `class5LoopMatrixPV c`, masses `classPVMasses m m_γ m_γ Λ Λ`). For `L`
and `X` they are the data of `ParametricBridgeLX` (`classMomE_eq_classMom`, …, by `rfl`).

**The frozen routing** is the class routing at the loop momenta `M ℓ + a` with `M` integer
unimodular (`lineMomentum₂_cCp`, `lineMomentum₂_cCm`; `M = matCp`, `matCm`), and its loop matrix
is `frozenLoopMatrix c = class5LoopMatrix c * M` (`frozenLoopMatrixCp_eq`, `frozenLoopMatrixCm_eq`,
kernel-checked), which satisfies the no-subdivergence criterion with one denominator per line and
with the photon lines doubled (`intNoSubdivergence_frozenLoopMatrixCp`, …).

**The value in parametric form** (`contractionValue₂_Cp_eq`, `contractionValue₂_Cm_eq`): for
`ε ≠ 0` and under momentum conservation, the value (T₁₀) is the joint energy-first integral of
`(2π)⁻⁸ N(ℓ) ∏ᵢ₌₀⁷ Dᵢ(ℓ)⁻¹` with `Dᵢ = pvDenomE c …` and `N = classNumeratorE c …` a polynomial of
total degree at most `4` in the class loop momenta (`isLoopPoly_classNumeratorE_Cp`, …) and in the
frozen ones (`…_frozen`, by `QED.TwoLoop.Bridge.IsLoopPoly.comp_intAffine`; also for `L`, `X`:
`isLoopPoly_classNumerator_L_frozen`, `…_X_frozen`). The data are those of
the proved criterion (`noSubdivergence_loopMatrixPV`) and positivity bounds
(`symanzikV_classCpPV_ge`, `symanzikV_classCmPV_ge`).
-/

@[expose] public section

namespace QED.TwoLoop.Bridge

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Relabel
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix
  class5LoopMatrixPV classLXMomenta classCpSpMomenta classCmSmMomenta classVPMomenta
  classPVMasses pvLines IntNoSubdivergence NoSubdivergence)

/-- The fermion fields of the five gauge vertices. -/
local notation "FV" => Wick.FermionVertex (gauges 5)

/-- The photon fields of the five gauge vertices. -/
local notation "PS" => Wick.PhotonSlot (gauges 5)

/-! ### Common data -/

/-- The external momenta of the class lines (line order of `class5LoopMatrix`), from
`QED/Integration/SymanzikPositivity*.lean`. -/
def extMomenta : Class5 → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 6 → Fin 4 → ℝ
  | .Cp, p, p' => classCpSpMomenta p p'
  | .Sp, p, p' => classCpSpMomenta p p'
  | .Cm, p, p' => classCmSmMomenta p p'
  | .Sm, p, p' => classCmSmMomenta p p'
  | .VP, p, p' => classVPMomenta p p'
  | _, p, p' => classLXMomenta p p'

/-- The routing of an open-line class representative by the class loop matrix
`class5LoopMatrix c` and the external momenta `extMomenta c p p'`, at loop momenta `ℓ`. -/
def classMomE (c : Class5) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line c.rep) :
    Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix (class5LoopMatrix c)) (extMomenta c p p') (lineIdx f) ℓ

/-- The numerator of the class amplitude in the routing `classMomE`. -/
noncomputable def classNumeratorE (c : Class5) (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  amplitudeNumerator P c.rep zeroFlavoring pIn kIn (classMomE c (pIn 0) (pOut 0) ℓ) αOut βIn μ

/-- The external momenta of the eight lines of the Pauli–Villars form. -/
def pvMomentaE (c : Class5) (p p' : Fin 4 → ℝ) : Fin 8 → Fin 4 → ℝ :=
  fun i => extMomenta c p p' (pvLines i)

/-- The denominator `Dᵢ(ℓ)` of line `i` of the Pauli–Villars form of class `c`. -/
noncomputable def pvDenomE (c : Class5) (P : Params) (p p' : Fin 4 → ℝ) (i : Fin 8)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  lineDenom (castLoopMatrix (class5LoopMatrixPV c)) (pvMomentaE c p p') (pvMasses P) P.ε i ℓ

theorem classMomE_eq_classMom {c : Class5} (hc : c = .L ∨ c = .X) :
    classMomE c = classMom c := by
  rcases hc with rfl | rfl <;> rfl

theorem classNumeratorE_eq_classNumerator {c : Class5} (hc : c = .L ∨ c = .X) :
    classNumeratorE c = classNumerator c := by
  rcases hc with rfl | rfl <;> rfl

theorem pvDenomE_eq_pvDenom {c : Class5} (hc : c = .L ∨ c = .X) : pvDenomE c = pvDenom c := by
  rcases hc with rfl | rfl <;> rfl

/-- The numerator of `L` in the frozen loop momenta has total degree at most `4`. -/
theorem isLoopPoly_classNumerator_L_frozen (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 fun ℓ => classNumerator .L P pOut pIn kIn αOut βIn μ (chgL (pIn 0) ℓ) :=
  (isLoopPoly_classNumerator_L P pOut pIn kIn αOut βIn μ).comp_intAffine matL _

/-- The numerator of `X` in the frozen loop momenta has total degree at most `4`. -/
theorem isLoopPoly_classNumerator_X_frozen (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 fun ℓ => classNumerator .X P pOut pIn kIn αOut βIn μ (chgX (pIn 0) ℓ) :=
  (isLoopPoly_classNumerator_X P pOut pIn kIn αOut βIn μ).comp_intAffine matX _

/-! ### `C₊`: lines -/

/-- The representative of the class `C₊`. -/
abbrev cCp : Contraction 1 1 (gauges 5) := Class5.Cp.rep

/-- The fermion lines of `C₊`, by head `1, 2, 3, 4` (tails `0, 1, 2, 3`). -/
def lineCp : Fin 4 → FermionLine cCp :=
  ![⟨fv5 1, by decide +kernel⟩, ⟨fv5 2, by decide +kernel⟩, ⟨fv5 3, by decide +kernel⟩,
    ⟨fv5 4, by decide +kernel⟩]

/-- The photon lines `0 → 3` and `2 → 4` of `C₊`, indexed by the fields of `0` and `2`. -/
def photCp : Fin 2 → PhotonLine cCp :=
  ![⟨ps5 0, by decide +kernel⟩, ⟨ps5 2, by decide +kernel⟩]

theorem lineCp_bijective : Function.Bijective lineCp := by decide +kernel

theorem photCp_bijective : Function.Bijective photCp := by decide +kernel

theorem ends_lineCp : (Line.ends (.inl (lineCp 0) : Line cCp)) = (0, 1) ∧
    (Line.ends (.inl (lineCp 1) : Line cCp)) = (1, 2) ∧
    (Line.ends (.inl (lineCp 2) : Line cCp)) = (2, 3) ∧
    (Line.ends (.inl (lineCp 3) : Line cCp)) = (3, 4) := by decide +kernel

theorem ends_photCp : (Line.ends (.inr (photCp 0) : Line cCp)) = (0, 3) ∧
    (Line.ends (.inr (photCp 1) : Line cCp)) = (2, 4) := by decide +kernel

theorem prod_fermionLine_Cp {M : Type*} [CommMonoid M] [Fintype (FermionLine cCp)]
    (g : FermionLine cCp → M) :
    ∏ f, g f = g (lineCp 0) * g (lineCp 1) * g (lineCp 2) * g (lineCp 3) := by
  rw [← (Equiv.ofBijective _ lineCp_bijective).prod_comp, Fin.prod_univ_four]
  rfl

theorem prod_photonLine_Cp {M : Type*} [CommMonoid M] [Fintype (PhotonLine cCp)]
    (g : PhotonLine cCp → M) : ∏ f, g f = g (photCp 0) * g (photCp 1) := by
  rw [← (Equiv.ofBijective _ photCp_bijective).prod_comp, Fin.prod_univ_two]
  rfl

theorem sum_line_Cp {M : Type*} [AddCommMonoid M] [Fintype (FermionLine cCp)]
    [Fintype (PhotonLine cCp)] (g : Line cCp → M) :
    ∑ f, g f = g (.inl (lineCp 0)) + g (.inl (lineCp 1)) + g (.inl (lineCp 2)) +
      g (.inl (lineCp 3)) + (g (.inr (photCp 0)) + g (.inr (photCp 1))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ lineCp_bijective).sum_comp,
    ← (Equiv.ofBijective _ photCp_bijective).sum_comp, Fin.sum_univ_four, Fin.sum_univ_two]
  rfl

theorem card_fermionLine_Cp [Fintype (FermionLine cCp)] : Fintype.card (FermionLine cCp) = 4 := by
  rw [← Fintype.card_of_bijective lineCp_bijective, Fintype.card_fin]

theorem lineIdx_Cp : lineIdx (.inl (lineCp 0) : Line cCp) = 0 ∧
    lineIdx (.inl (lineCp 1) : Line cCp) = 1 ∧
    lineIdx (.inl (lineCp 2) : Line cCp) = 2 ∧ lineIdx (.inl (lineCp 3) : Line cCp) = 3 ∧
    lineIdx (.inr (photCp 0) : Line cCp) = 4 ∧ lineIdx (.inr (photCp 1) : Line cCp) = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### `C₊`: external momenta and the class routing -/

theorem extPsi_iff_Cp (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cCp.1.1 (.inr t) = .inl 0) ↔ v = 0 := by
  revert v
  decide +kernel

theorem extA_iff_Cp (v : Fin 5) :
    (∃ a : PS, a.1 = v ∧ cCp.1.2 (.inl 0) = .inr a) ↔ v = 1 := by
  revert v
  decide +kernel

theorem extPsiBar_iff_Cp (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cCp.1.1 (.inl 0) = .inr t) ↔ v = 4 := by
  revert v
  decide +kernel

/-- The external momenta (X₁₉) of `C₊`: `pIn` flows in at `0`, `kIn` at `1`, `pOut` out at `4`. -/
theorem externalMomentum_cCp (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cCp pOut pIn kIn v =
      (if v = 0 then pIn 0 else 0) + (if v = 1 then kIn 0 else 0) -
        (if v = 4 then pOut 0 else 0) := by
  unfold externalMomentum
  simp only [Fin.sum_univ_one, extPsi_iff_Cp, extA_iff_Cp, extPsiBar_iff_Cp]

/-- The class routing of `C₊` is conserved at every vertex, for all loop momenta, under momentum
conservation. -/
theorem isConserved_classMomE_Cp {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved cCp pOut pIn kIn (classMomE .Cp (pIn 0) (pOut 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3⟩ := ends_lineCp
  obtain ⟨g0, g1⟩ := ends_photCp
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := lineIdx_Cp
  intro v
  rw [inflow, sum_line_Cp, externalMomentum_cCp, hmom]
  simp only [classMomE, e0, e1, e2, e3, g0, g1, i0, i1, i2, i3, i4, i5]
  funext μ
  fin_cases v <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCpSpMomenta,
      Fin.sum_univ_two] <;>
    ring

/-! ### `C₊`: chords and the frozen routing -/

theorem isChord_cCp_iff :
    ∀ f : Line cCp, IsChord f ↔ f = .inl (lineCp 0) ∨ f = .inl (lineCp 2) := by
  decide +kernel

open scoped Classical in
theorem card_chordsBelow_Cp : (Finset.univ.filter fun g : Line cCp =>
      IsChord g ∧ g.label < (Line.label (.inl (lineCp 0) : Line cCp))).card = 0 ∧
    (Finset.univ.filter fun g : Line cCp =>
      IsChord g ∧ g.label < (Line.label (.inl (lineCp 2) : Line cCp))).card = 1 := by
  have l0 : (Line.label (.inl (lineCp 0) : Line cCp)) = 1 := rfl
  have l1 : (Line.label (.inl (lineCp 2) : Line cCp)) = 3 := rfl
  constructor
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (isChord_cCp_iff g).mp hg with rfl | rfl
    · simp [l0] at hl
    · simp [l0, l1] at hl
  · rw [Finset.card_eq_one]
    refine ⟨.inl (lineCp 0), Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (isChord_cCp_iff g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(isChord_cCp_iff _).mpr (Or.inl rfl), by simp [l0, l1]⟩

theorem chordMomentum_lineCp (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (lineCp 0) : Line cCp) = ℓ 0 ∧
      chordMomentum ℓ (.inl (lineCp 2) : Line cCp) = ℓ 1 := by
  classical
  obtain ⟨h0, h1⟩ := card_chordsBelow_Cp
  constructor
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by rw [Fin.val_zero]; convert h0)
    · exact absurd (by convert (show 0 < 2 by norm_num) using 2; convert h0) h
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by rw [Fin.val_one]; convert h1)
    · exact absurd (by convert (show 1 < 2 by norm_num) using 2; convert h1) h

/-- The unimodular change of loop momenta from the frozen routing of `C₊` to its class routing. -/
def matCp : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, -1]

theorem isUnit_det_matCp : IsUnit matCp.det := by
  rw [Matrix.det_fin_two]
  simp [matCp]

/-- The class loop momenta of `C₊` in terms of the frozen ones: `(ℓ₁ - p', ℓ₀ - ℓ₁ + p' - p)`. -/
def chgCp (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  (fun s => ∑ r, matCp s r • ℓ r) + ![-p', p' - p]

/-- **The frozen routing of `C₊` is the class routing** at the loop momenta `chgCp p p' ℓ`, under
momentum conservation. -/
theorem lineMomentum₂_cCp {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ cCp pOut pIn kIn ℓ =
      classMomE .Cp (pIn 0) (pOut 0) (chgCp (pIn 0) (pOut 0) ℓ) := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (isConserved_classMomE_Cp hmom _) (fun g hg => ?_)
    f).symm
  obtain ⟨c0, c1⟩ := chordMomentum_lineCp ℓ
  obtain ⟨i0, i1, i2, -⟩ := lineIdx_Cp
  rcases (isChord_cCp_iff g).mp hg with rfl | rfl
  · rw [c0, classMomE, i0]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCpSpMomenta, chgCp,
      matCp, Fin.sum_univ_two]
    ring
  · rw [c1, classMomE, i2]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCpSpMomenta, chgCp,
      matCp, Fin.sum_univ_two]

/-- The loop matrix of the frozen routing of `C₊` (rows `v₀v₁, v₁v₂, v₂v₃, v₃v₄`, photons
`0 → 3`, `2 → 4`; columns the chord momenta `ℓ₀`, `ℓ₁`). -/
def frozenLoopMatrixCp : Fin 6 → Fin 2 → ℤ :=
  ![![1, 0], ![1, 0], ![0, 1], ![-1, 1], ![-1, 0], ![1, -1]]

/-- The external momenta of the frozen routing of `C₊`. -/
def frozenMomentaCp (p k : Fin 4 → ℝ) : Fin 6 → Fin 4 → ℝ := ![0, k, 0, p, p, k]

theorem frozenLoopMatrixCp_eq :
    frozenLoopMatrixCp = fun i s => ∑ r, class5LoopMatrix .Cp i r * matCp r s := by
  decide

/-- **The frozen routing of `C₊` with its loop matrix**: `k_f(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ` with
`α = frozenLoopMatrixCp`, `i = lineIdx f`. -/
theorem lineMomentum₂_cCp_eq_frozen {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line cCp) :
    lineMomentum₂ cCp pOut pIn kIn ℓ f =
      lineMomentum (castLoopMatrix frozenLoopMatrixCp) (frozenMomentaCp (pIn 0) (kIn 0))
        (lineIdx f) ℓ := by
  rw [lineMomentum₂_cCp hmom, classMomE, hmom]
  generalize lineIdx f = i
  funext μ
  fin_cases i <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCpSpMomenta, chgCp,
      matCp, frozenLoopMatrixCp, frozenMomentaCp, Fin.sum_univ_two] <;>
    ring

theorem intNoSubdivergence_frozenLoopMatrixCp : IntNoSubdivergence frozenLoopMatrixCp := by
  decide

theorem intNoSubdivergence_frozenLoopMatrixCp_PV :
    IntNoSubdivergence fun i => frozenLoopMatrixCp (pvLines i) := by
  decide

/-! ### `C₊`: flavorings and the amplitude -/

theorem cCp_orbit : ∀ x : Fin 1 ⊕ FV, ∃ i : Fin 6, (cCp.1.1 ^ (i : ℕ)) x = .inl 0 := by
  decide +kernel

theorem sameCycle_cCp (x : Fin 1 ⊕ FV) : Equiv.Perm.SameCycle cCp.1.1 x (.inl 0) := by
  obtain ⟨i, hi⟩ := cCp_orbit x
  exact ⟨(i : ℕ), by rw [zpow_natCast]; exact hi⟩

/-- `C₊` has no closed fermion loop. -/
theorem isEmpty_closedLoop_Cp : IsEmpty (ClosedLoop cCp) := by
  refine ⟨fun ⟨q, hq⟩ => ?_⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact hq 0 (Quotient.sound (sameCycle_cCp x).symm)

theorem preserves_iff_Cp (φ : Flavoring (gauges 5)) : Preserves cCp φ ↔ φ = zeroFlavoring := by
  refine ⟨fun hφ => Subtype.ext (funext fun t => ?_), fun h => h ▸ preserves_zeroFlavoring⟩
  exact fermionFlavor_eq_of_sameCycle hφ (sameCycle_cCp (.inr t))

open scoped Classical in
/-- The regulated amplitude (T₈) of `C₊` is its amplitude (T₇) at flavour `0`. -/
theorem regulatedAmplitude₂_cCp (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line cCp → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P cCp pIn kIn k αOut βIn μ =
      contractionAmplitude₂ P cCp zeroFlavoring pIn kIn k αOut βIn μ := by
  have hfil : (Finset.univ : Finset (Flavoring (gauges 5))).filter (Preserves cCp) =
      {zeroFlavoring} := Finset.ext fun φ => by simp [preserves_iff_Cp]
  have hw : loopWeight P cCp zeroFlavoring = 1 := by
    have := isEmpty_closedLoop_Cp
    simp [loopWeight]
  rw [regulatedAmplitude₂, hfil, Finset.sum_singleton, hw, Complex.ofReal_one, one_mul]

/-- The denominators of `C₊` in the class routing are the eight Pauli–Villars line denominators. -/
theorem amplitudeDenominator_cCp (P : Params) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    amplitudeDenominator P cCp zeroFlavoring (classMomE .Cp p p' ℓ) =
      ∏ i : Fin 8, (pvDenomE .Cp P p p' i ℓ)⁻¹ := by
  have h : amplitudeDenominator P cCp zeroFlavoring (classMomE .Cp p p' ℓ) =
      (pvDenomE .Cp P p p' 0 ℓ)⁻¹ * (pvDenomE .Cp P p p' 1 ℓ)⁻¹ * (pvDenomE .Cp P p p' 2 ℓ)⁻¹ *
        (pvDenomE .Cp P p p' 3 ℓ)⁻¹ *
          (((pvDenomE .Cp P p p' 4 ℓ)⁻¹ * (pvDenomE .Cp P p p' 6 ℓ)⁻¹) *
            ((pvDenomE .Cp P p p' 5 ℓ)⁻¹ * (pvDenomE .Cp P p p' 7 ℓ)⁻¹)) := by
    rw [amplitudeDenominator, prod_fermionLine_Cp, prod_photonLine_Cp]
    rfl
  rw [h, Fin.prod_univ_eight]
  ring

/-- **The integrand of `C₊` in parametric form**: for `ε ≠ 0`, the regulated amplitude (T₈) in
the class routing is the numerator times the eight Pauli–Villars line denominators. -/
theorem regulatedAmplitude₂_classMomE_Cp (P : Params) (hε : P.ε ≠ 0)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cCp pIn kIn (classMomE .Cp (pIn 0) (pOut 0) ℓ) αOut βIn μ =
      classNumeratorE .Cp P pOut pIn kIn αOut βIn μ ℓ *
        ∏ i : Fin 8, (pvDenomE .Cp P (pIn 0) (pOut 0) i ℓ)⁻¹ := by
  rw [regulatedAmplitude₂_cCp, contractionAmplitude₂_eq P hε, amplitudeDenominator_cCp]
  rfl

/-- **The value of `C₊` in parametric form.** For `ε ≠ 0` and under momentum conservation, the
value (T₁₀) of the class is the joint energy-first integral of `(2π)⁻⁸` times the class numerator
times the product of the eight Pauli–Villars line denominators for the loop matrix
`class5LoopMatrixPV .Cp`. No integrability is needed. -/
theorem contractionValue₂_Cp_eq (P : Params) (hε : P.ε ≠ 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.Cp.rep pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          (classNumeratorE .Cp P pOut pIn kIn αOut βIn μ ℓ *
            ∏ i : Fin 8, (pvDenomE .Cp P (pIn 0) (pOut 0) i ℓ)⁻¹) := by
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .Cp)]
  simp only [lineMomentum₂_cCp hmom]
  have h := JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
    (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cCp pIn kIn (classMomE .Cp (pIn 0) (pOut 0) ℓ) αOut βIn μ)
    matCp isUnit_det_matCp ![-(pOut 0), pOut 0 - pIn 0]
  refine h.trans ?_
  refine congrArg (QED.TwoLoop.jointEnergyFirstIntegral 2) (funext fun ℓ => ?_)
  rw [regulatedAmplitude₂_classMomE_Cp P hε]

/-- The numerator of `C₊` is a polynomial of total degree at most `4` in the loop momenta. -/
theorem isLoopPoly_classNumeratorE_Cp (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 (classNumeratorE .Cp P pOut pIn kIn αOut βIn μ) := by
  have h := isLoopPoly_amplitudeNumerator P cCp zeroFlavoring pIn kIn
    (classMomE .Cp (pIn 0) (pOut 0)) (fun f => isLoopAffine_lineMomentum _ _ _) αOut βIn μ
  rwa [card_fermionLine_Cp] at h

/-- The integrand of `C₊` at the frozen routing, in the frozen loop momenta. -/
theorem regulatedAmplitude₂_lineMomentum₂_Cp (P : Params) (hε : P.ε ≠ 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cCp pIn kIn (lineMomentum₂ cCp pOut pIn kIn ℓ) αOut βIn μ =
      classNumeratorE .Cp P pOut pIn kIn αOut βIn μ (chgCp (pIn 0) (pOut 0) ℓ) *
        ∏ i : Fin 8, (pvDenomE .Cp P (pIn 0) (pOut 0) i (chgCp (pIn 0) (pOut 0) ℓ))⁻¹ := by
  rw [lineMomentum₂_cCp hmom, regulatedAmplitude₂_classMomE_Cp P hε]

/-- The numerator of `C₊` in the frozen loop momenta also has total degree at most `4`. -/
theorem isLoopPoly_classNumeratorE_Cp_frozen (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 fun ℓ =>
      classNumeratorE .Cp P pOut pIn kIn αOut βIn μ (chgCp (pIn 0) (pOut 0) ℓ) :=
  (isLoopPoly_classNumeratorE_Cp P pOut pIn kIn αOut βIn μ).comp_intAffine matCp _

/-! ### `C₋`: lines -/

/-- The representative of the class `C₋`. -/
abbrev cCm : Contraction 1 1 (gauges 5) := Class5.Cm.rep

/-- The fermion lines of `C₋`, by head `1, 2, 3, 4` (tails `0, 1, 2, 3`). -/
def lineCm : Fin 4 → FermionLine cCm :=
  ![⟨fv5 1, by decide +kernel⟩, ⟨fv5 2, by decide +kernel⟩, ⟨fv5 3, by decide +kernel⟩,
    ⟨fv5 4, by decide +kernel⟩]

/-- The photon lines `0 → 2` and `1 → 4` of `C₋`, indexed by the fields of `0` and `1`. -/
def photCm : Fin 2 → PhotonLine cCm :=
  ![⟨ps5 0, by decide +kernel⟩, ⟨ps5 1, by decide +kernel⟩]

theorem lineCm_bijective : Function.Bijective lineCm := by decide +kernel

theorem photCm_bijective : Function.Bijective photCm := by decide +kernel

theorem ends_lineCm : (Line.ends (.inl (lineCm 0) : Line cCm)) = (0, 1) ∧
    (Line.ends (.inl (lineCm 1) : Line cCm)) = (1, 2) ∧
    (Line.ends (.inl (lineCm 2) : Line cCm)) = (2, 3) ∧
    (Line.ends (.inl (lineCm 3) : Line cCm)) = (3, 4) := by decide +kernel

theorem ends_photCm : (Line.ends (.inr (photCm 0) : Line cCm)) = (0, 2) ∧
    (Line.ends (.inr (photCm 1) : Line cCm)) = (1, 4) := by decide +kernel

theorem prod_fermionLine_Cm {M : Type*} [CommMonoid M] [Fintype (FermionLine cCm)]
    (g : FermionLine cCm → M) :
    ∏ f, g f = g (lineCm 0) * g (lineCm 1) * g (lineCm 2) * g (lineCm 3) := by
  rw [← (Equiv.ofBijective _ lineCm_bijective).prod_comp, Fin.prod_univ_four]
  rfl

theorem prod_photonLine_Cm {M : Type*} [CommMonoid M] [Fintype (PhotonLine cCm)]
    (g : PhotonLine cCm → M) : ∏ f, g f = g (photCm 0) * g (photCm 1) := by
  rw [← (Equiv.ofBijective _ photCm_bijective).prod_comp, Fin.prod_univ_two]
  rfl

theorem sum_line_Cm {M : Type*} [AddCommMonoid M] [Fintype (FermionLine cCm)]
    [Fintype (PhotonLine cCm)] (g : Line cCm → M) :
    ∑ f, g f = g (.inl (lineCm 0)) + g (.inl (lineCm 1)) + g (.inl (lineCm 2)) +
      g (.inl (lineCm 3)) + (g (.inr (photCm 0)) + g (.inr (photCm 1))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ lineCm_bijective).sum_comp,
    ← (Equiv.ofBijective _ photCm_bijective).sum_comp, Fin.sum_univ_four, Fin.sum_univ_two]
  rfl

theorem card_fermionLine_Cm [Fintype (FermionLine cCm)] : Fintype.card (FermionLine cCm) = 4 := by
  rw [← Fintype.card_of_bijective lineCm_bijective, Fintype.card_fin]

theorem lineIdx_Cm : lineIdx (.inl (lineCm 0) : Line cCm) = 0 ∧
    lineIdx (.inl (lineCm 1) : Line cCm) = 1 ∧
    lineIdx (.inl (lineCm 2) : Line cCm) = 2 ∧ lineIdx (.inl (lineCm 3) : Line cCm) = 3 ∧
    lineIdx (.inr (photCm 0) : Line cCm) = 4 ∧ lineIdx (.inr (photCm 1) : Line cCm) = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### `C₋`: external momenta and the class routing -/

theorem extPsi_iff_Cm (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cCm.1.1 (.inr t) = .inl 0) ↔ v = 0 := by
  revert v
  decide +kernel

theorem extA_iff_Cm (v : Fin 5) :
    (∃ a : PS, a.1 = v ∧ cCm.1.2 (.inl 0) = .inr a) ↔ v = 3 := by
  revert v
  decide +kernel

theorem extPsiBar_iff_Cm (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cCm.1.1 (.inl 0) = .inr t) ↔ v = 4 := by
  revert v
  decide +kernel

/-- The external momenta (X₁₉) of `C₋`: `pIn` flows in at `0`, `kIn` at `3`, `pOut` out at `4`. -/
theorem externalMomentum_cCm (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cCm pOut pIn kIn v =
      (if v = 0 then pIn 0 else 0) + (if v = 3 then kIn 0 else 0) -
        (if v = 4 then pOut 0 else 0) := by
  unfold externalMomentum
  simp only [Fin.sum_univ_one, extPsi_iff_Cm, extA_iff_Cm, extPsiBar_iff_Cm]

/-- The class routing of `C₋` is conserved at every vertex, for all loop momenta, under momentum
conservation. -/
theorem isConserved_classMomE_Cm {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved cCm pOut pIn kIn (classMomE .Cm (pIn 0) (pOut 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3⟩ := ends_lineCm
  obtain ⟨g0, g1⟩ := ends_photCm
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := lineIdx_Cm
  intro v
  rw [inflow, sum_line_Cm, externalMomentum_cCm, hmom]
  simp only [classMomE, e0, e1, e2, e3, g0, g1, i0, i1, i2, i3, i4, i5]
  funext μ
  fin_cases v <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCmSmMomenta,
      Fin.sum_univ_two] <;>
    ring

/-! ### `C₋`: chords and the frozen routing -/

theorem isChord_cCm_iff :
    ∀ f : Line cCm, IsChord f ↔ f = .inl (lineCm 0) ∨ f = .inl (lineCm 1) := by
  decide +kernel

open scoped Classical in
theorem card_chordsBelow_Cm : (Finset.univ.filter fun g : Line cCm =>
      IsChord g ∧ g.label < (Line.label (.inl (lineCm 0) : Line cCm))).card = 0 ∧
    (Finset.univ.filter fun g : Line cCm =>
      IsChord g ∧ g.label < (Line.label (.inl (lineCm 1) : Line cCm))).card = 1 := by
  have l0 : (Line.label (.inl (lineCm 0) : Line cCm)) = 1 := rfl
  have l1 : (Line.label (.inl (lineCm 1) : Line cCm)) = 2 := rfl
  constructor
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (isChord_cCm_iff g).mp hg with rfl | rfl
    · simp [l0] at hl
    · simp [l0, l1] at hl
  · rw [Finset.card_eq_one]
    refine ⟨.inl (lineCm 0), Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (isChord_cCm_iff g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(isChord_cCm_iff _).mpr (Or.inl rfl), by simp [l0, l1]⟩

theorem chordMomentum_lineCm (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (lineCm 0) : Line cCm) = ℓ 0 ∧
      chordMomentum ℓ (.inl (lineCm 1) : Line cCm) = ℓ 1 := by
  classical
  obtain ⟨h0, h1⟩ := card_chordsBelow_Cm
  constructor
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by rw [Fin.val_zero]; convert h0)
    · exact absurd (by convert (show 0 < 2 by norm_num) using 2; convert h0) h
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by rw [Fin.val_one]; convert h1)
    · exact absurd (by convert (show 1 < 2 by norm_num) using 2; convert h1) h

/-- The unimodular change of loop momenta from the frozen routing of `C₋` to its class routing. -/
def matCm : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 1]

theorem isUnit_det_matCm : IsUnit matCm.det := by
  rw [Matrix.det_fin_two]
  simp [matCm]

/-- The class loop momenta of `C₋` in terms of the frozen ones: `(ℓ₁ - p, ℓ₁ - ℓ₀)`. -/
def chgCm (p _p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  (fun s => ∑ r, matCm s r • ℓ r) + ![-p, 0]

/-- **The frozen routing of `C₋` is the class routing** at the loop momenta `chgCm p p' ℓ`, under
momentum conservation. -/
theorem lineMomentum₂_cCm {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ cCm pOut pIn kIn ℓ =
      classMomE .Cm (pIn 0) (pOut 0) (chgCm (pIn 0) (pOut 0) ℓ) := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (isConserved_classMomE_Cm hmom _) (fun g hg => ?_)
    f).symm
  obtain ⟨c0, c1⟩ := chordMomentum_lineCm ℓ
  obtain ⟨i0, i1, i2, -⟩ := lineIdx_Cm
  rcases (isChord_cCm_iff g).mp hg with rfl | rfl
  · rw [c0, classMomE, i0]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCmSmMomenta, chgCm,
      matCm, Fin.sum_univ_two]
    ring
  · rw [c1, classMomE, i1]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCmSmMomenta, chgCm,
      matCm, Fin.sum_univ_two]

/-- The loop matrix of the frozen routing of `C₋` (rows `v₀v₁, v₁v₂, v₂v₃, v₃v₄`, photons
`0 → 2`, `1 → 4`; columns the chord momenta `ℓ₀`, `ℓ₁`). -/
def frozenLoopMatrixCm : Fin 6 → Fin 2 → ℤ :=
  ![![1, 0], ![0, 1], ![-1, 1], ![-1, 1], ![-1, 0], ![1, -1]]

/-- The external momenta of the frozen routing of `C₋`. -/
def frozenMomentaCm (p k : Fin 4 → ℝ) : Fin 6 → Fin 4 → ℝ := ![0, 0, p, p + k, p, 0]

theorem frozenLoopMatrixCm_eq :
    frozenLoopMatrixCm = fun i s => ∑ r, class5LoopMatrix .Cm i r * matCm r s := by
  decide

/-- **The frozen routing of `C₋` with its loop matrix**: `k_f(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ` with
`α = frozenLoopMatrixCm`, `i = lineIdx f`. -/
theorem lineMomentum₂_cCm_eq_frozen {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line cCm) :
    lineMomentum₂ cCm pOut pIn kIn ℓ f =
      lineMomentum (castLoopMatrix frozenLoopMatrixCm) (frozenMomentaCm (pIn 0) (kIn 0))
        (lineIdx f) ℓ := by
  rw [lineMomentum₂_cCm hmom, classMomE, hmom]
  generalize lineIdx f = i
  funext μ
  fin_cases i <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCmSmMomenta, chgCm,
      matCm, frozenLoopMatrixCm, frozenMomentaCm, Fin.sum_univ_two] <;>
    ring

theorem intNoSubdivergence_frozenLoopMatrixCm : IntNoSubdivergence frozenLoopMatrixCm := by
  decide

theorem intNoSubdivergence_frozenLoopMatrixCm_PV :
    IntNoSubdivergence fun i => frozenLoopMatrixCm (pvLines i) := by
  decide

/-! ### `C₋`: flavorings and the amplitude -/

theorem cCm_orbit : ∀ x : Fin 1 ⊕ FV, ∃ i : Fin 6, (cCm.1.1 ^ (i : ℕ)) x = .inl 0 := by
  decide +kernel

theorem sameCycle_cCm (x : Fin 1 ⊕ FV) : Equiv.Perm.SameCycle cCm.1.1 x (.inl 0) := by
  obtain ⟨i, hi⟩ := cCm_orbit x
  exact ⟨(i : ℕ), by rw [zpow_natCast]; exact hi⟩

/-- `C₋` has no closed fermion loop. -/
theorem isEmpty_closedLoop_Cm : IsEmpty (ClosedLoop cCm) := by
  refine ⟨fun ⟨q, hq⟩ => ?_⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact hq 0 (Quotient.sound (sameCycle_cCm x).symm)

theorem preserves_iff_Cm (φ : Flavoring (gauges 5)) : Preserves cCm φ ↔ φ = zeroFlavoring := by
  refine ⟨fun hφ => Subtype.ext (funext fun t => ?_), fun h => h ▸ preserves_zeroFlavoring⟩
  exact fermionFlavor_eq_of_sameCycle hφ (sameCycle_cCm (.inr t))

open scoped Classical in
/-- The regulated amplitude (T₈) of `C₋` is its amplitude (T₇) at flavour `0`. -/
theorem regulatedAmplitude₂_cCm (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line cCm → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P cCm pIn kIn k αOut βIn μ =
      contractionAmplitude₂ P cCm zeroFlavoring pIn kIn k αOut βIn μ := by
  have hfil : (Finset.univ : Finset (Flavoring (gauges 5))).filter (Preserves cCm) =
      {zeroFlavoring} := Finset.ext fun φ => by simp [preserves_iff_Cm]
  have hw : loopWeight P cCm zeroFlavoring = 1 := by
    have := isEmpty_closedLoop_Cm
    simp [loopWeight]
  rw [regulatedAmplitude₂, hfil, Finset.sum_singleton, hw, Complex.ofReal_one, one_mul]

/-- The denominators of `C₋` in the class routing are the eight Pauli–Villars line denominators. -/
theorem amplitudeDenominator_cCm (P : Params) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    amplitudeDenominator P cCm zeroFlavoring (classMomE .Cm p p' ℓ) =
      ∏ i : Fin 8, (pvDenomE .Cm P p p' i ℓ)⁻¹ := by
  have h : amplitudeDenominator P cCm zeroFlavoring (classMomE .Cm p p' ℓ) =
      (pvDenomE .Cm P p p' 0 ℓ)⁻¹ * (pvDenomE .Cm P p p' 1 ℓ)⁻¹ * (pvDenomE .Cm P p p' 2 ℓ)⁻¹ *
        (pvDenomE .Cm P p p' 3 ℓ)⁻¹ *
          (((pvDenomE .Cm P p p' 4 ℓ)⁻¹ * (pvDenomE .Cm P p p' 6 ℓ)⁻¹) *
            ((pvDenomE .Cm P p p' 5 ℓ)⁻¹ * (pvDenomE .Cm P p p' 7 ℓ)⁻¹)) := by
    rw [amplitudeDenominator, prod_fermionLine_Cm, prod_photonLine_Cm]
    rfl
  rw [h, Fin.prod_univ_eight]
  ring

/-- **The integrand of `C₋` in parametric form**: for `ε ≠ 0`, the regulated amplitude (T₈) in
the class routing is the numerator times the eight Pauli–Villars line denominators. -/
theorem regulatedAmplitude₂_classMomE_Cm (P : Params) (hε : P.ε ≠ 0)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cCm pIn kIn (classMomE .Cm (pIn 0) (pOut 0) ℓ) αOut βIn μ =
      classNumeratorE .Cm P pOut pIn kIn αOut βIn μ ℓ *
        ∏ i : Fin 8, (pvDenomE .Cm P (pIn 0) (pOut 0) i ℓ)⁻¹ := by
  rw [regulatedAmplitude₂_cCm, contractionAmplitude₂_eq P hε, amplitudeDenominator_cCm]
  rfl

/-- **The value of `C₋` in parametric form.** For `ε ≠ 0` and under momentum conservation, the
value (T₁₀) of the class is the joint energy-first integral of `(2π)⁻⁸` times the class numerator
times the product of the eight Pauli–Villars line denominators for the loop matrix
`class5LoopMatrixPV .Cm`. No integrability is needed. -/
theorem contractionValue₂_Cm_eq (P : Params) (hε : P.ε ≠ 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.Cm.rep pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          (classNumeratorE .Cm P pOut pIn kIn αOut βIn μ ℓ *
            ∏ i : Fin 8, (pvDenomE .Cm P (pIn 0) (pOut 0) i ℓ)⁻¹) := by
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .Cm)]
  simp only [lineMomentum₂_cCm hmom]
  have h := JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
    (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cCm pIn kIn (classMomE .Cm (pIn 0) (pOut 0) ℓ) αOut βIn μ)
    matCm isUnit_det_matCm ![-(pIn 0), 0]
  refine h.trans ?_
  refine congrArg (QED.TwoLoop.jointEnergyFirstIntegral 2) (funext fun ℓ => ?_)
  rw [regulatedAmplitude₂_classMomE_Cm P hε]

/-- The numerator of `C₋` is a polynomial of total degree at most `4` in the loop momenta. -/
theorem isLoopPoly_classNumeratorE_Cm (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 (classNumeratorE .Cm P pOut pIn kIn αOut βIn μ) := by
  have h := isLoopPoly_amplitudeNumerator P cCm zeroFlavoring pIn kIn
    (classMomE .Cm (pIn 0) (pOut 0)) (fun f => isLoopAffine_lineMomentum _ _ _) αOut βIn μ
  rwa [card_fermionLine_Cm] at h

/-- The integrand of `C₋` at the frozen routing, in the frozen loop momenta. -/
theorem regulatedAmplitude₂_lineMomentum₂_Cm (P : Params) (hε : P.ε ≠ 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cCm pIn kIn (lineMomentum₂ cCm pOut pIn kIn ℓ) αOut βIn μ =
      classNumeratorE .Cm P pOut pIn kIn αOut βIn μ (chgCm (pIn 0) (pOut 0) ℓ) *
        ∏ i : Fin 8, (pvDenomE .Cm P (pIn 0) (pOut 0) i (chgCm (pIn 0) (pOut 0) ℓ))⁻¹ := by
  rw [lineMomentum₂_cCm hmom, regulatedAmplitude₂_classMomE_Cm P hε]

/-- The numerator of `C₋` in the frozen loop momenta also has total degree at most `4`. -/
theorem isLoopPoly_classNumeratorE_Cm_frozen (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 fun ℓ =>
      classNumeratorE .Cm P pOut pIn kIn αOut βIn μ (chgCm (pIn 0) (pOut 0) ℓ) :=
  (isLoopPoly_classNumeratorE_Cm P pOut pIn kIn αOut βIn μ).comp_intAffine matCm _


/-! ### Summary for `C₊` and `C₋` -/

theorem noSubdivergence_frozenLoopMatrixCp :
    NoSubdivergence (castLoopMatrix frozenLoopMatrixCp) :=
  (QED.Integration.TwoLoop.noSubdivergence_castLoopMatrix_iff _).mpr
    intNoSubdivergence_frozenLoopMatrixCp

theorem noSubdivergence_frozenLoopMatrixCm :
    NoSubdivergence (castLoopMatrix frozenLoopMatrixCm) :=
  (QED.Integration.TwoLoop.noSubdivergence_castLoopMatrix_iff _).mpr
    intNoSubdivergence_frozenLoopMatrixCm

/-- **Parametric form of `C₊` and `C₋`.** For `ε ≠ 0` and under momentum conservation, the value
(T₁₀) is the joint energy-first integral of `(2π)⁻⁸ N(ℓ) ∏ᵢ₌₀⁷ Dᵢ(ℓ)⁻¹` with `N` a polynomial of
total degree at most `4` in the loop momenta and `Dᵢ` the line denominators of the Pauli–Villars
form of the class, whose loop matrix `class5LoopMatrixPV c` satisfies the no-subdivergence
criterion. -/
theorem parametricForm_C {c : Class5} (hc : c = .Cp ∨ c = .Cm) (P : Params) (hε : P.ε ≠ 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ =
        QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
          (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
            (classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ *
              ∏ i : Fin 8, (pvDenomE c P (pIn 0) (pOut 0) i ℓ)⁻¹)) ∧
      IsLoopPoly 2 4 (classNumeratorE c P pOut pIn kIn αOut βIn μ) ∧
      NoSubdivergence (castLoopMatrix (class5LoopMatrixPV c)) := by
  rcases hc with rfl | rfl
  · exact ⟨contractionValue₂_Cp_eq P hε hmom αOut βIn μ,
      isLoopPoly_classNumeratorE_Cp P pOut pIn kIn αOut βIn μ,
      QED.Integration.TwoLoop.noSubdivergence_loopMatrixPV (by decide)⟩
  · exact ⟨contractionValue₂_Cm_eq P hε hmom αOut βIn μ,
      isLoopPoly_classNumeratorE_Cm P pOut pIn kIn αOut βIn μ,
      QED.Integration.TwoLoop.noSubdivergence_loopMatrixPV (by decide)⟩

end QED.TwoLoop.Bridge

end
