/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ParametricBridge
public import QED.TwoLoop.EnumerationGauge5
public import QED.TwoLoop.RelabelInvariance
public import QED.Integration.SymanzikPositivityClasses

/-!
# The ladder and crossed-ladder classes in parametric form

Part of obligations O2-7 and O2-10 (`docs/TWO-LOOP-DERIVATION.md`, sections 4.1–4.4) for the
classes `L` and `X` of five gauge vertices (`QED.TwoLoop.Enumeration.Class5.L`, `.X`). Their
representatives have the open line `0 → 1 → 2 → 3 → 4` (external photon at `2`) and the internal
photons `(0 4) (1 3)` (`L`) and `(0 3) (1 4)` (`X`).

**The frozen routing.** The chords (T₁) are the fermion lines `0 → 1` (`ℓ 0`) and `1 → 2`
(`ℓ 1`). Ordering the six lines as `v₀v₁, v₁v₂, v₂v₃, v₃v₄`, then the photons
(`lineIdx`, by label), the frozen routing (T₄) is, under momentum conservation `p' = p + k`
(`p = pIn 0`, `k = kIn 0`, `p' = pOut 0`):

| line | `v₀v₁` | `v₁v₂` | `v₂v₃` | `v₃v₄` | photon 1 | photon 2 |
| --- | --- | --- | --- | --- | --- | --- |
| `L` | `ℓ₀` | `ℓ₁` | `ℓ₁ + k` | `ℓ₀ + k` | `p - ℓ₀` (`0 → 4`) | `ℓ₀ - ℓ₁` (`1 → 3`) |
| `X` | `ℓ₀` | `ℓ₁` | `ℓ₁ + k` | `ℓ₁ - ℓ₀ + p + k` | `p - ℓ₀` (`0 → 3`) | `ℓ₀ - ℓ₁` (`1 → 4`) |

so the loop matrices of the frozen routing are `frozenLoopMatrixL`, `frozenLoopMatrixX`
(`lineMomentum₂_cL_eq_frozen`, `lineMomentum₂_cX_eq_frozen`).

**The link to the class loop matrices** (removing the "matched numerically only" caveat of
`QED/Integration/SymanzikIntegrabilityClasses.lean` for these two classes). The frozen routing is
the routing by `class5LoopMatrix c` with the external momenta `classLXMomenta p p'` of
`QED/Integration/SymanzikPositivity.lean`, at the loop momenta `M ℓ + a` with `M` integer
unimodular (`lineMomentum₂_cL`, `lineMomentum₂_cX`; `M = matL`, `matX`):
`frozenLoopMatrix c = class5LoopMatrix c * M` (`frozenLoopMatrixL_eq`, `frozenLoopMatrixX_eq`).
Both frozen matrices satisfy the no-subdivergence criterion, with one denominator per line and
with the photon lines doubled (`intNoSubdivergence_frozenLoopMatrixL`, …, `…PV`).

**The value in parametric form** (`contractionValue₂_L_eq`, `contractionValue₂_X_eq`): for
`ε ≠ 0` and under momentum conservation, the value (T₁₀) is the joint energy-first integral of
`(2π)⁻⁸ N(ℓ) ∏ᵢ₌₀⁷ Dᵢ(ℓ)⁻¹`, where `Dᵢ = lineDenom` for the loop matrix `class5LoopMatrixPV c`
(each photon line doubled), the external momenta `classLXMomenta p p' ∘ pvLines`, and the masses
`classPVMasses m m_γ m_γ Λ Λ` (the Pauli–Villars pair of each photon combined), exactly the data
of the proved criterion (`noSubdivergence_loopMatrixPV`) and the positivity bounds
(`symanzikV_classLPV_ge`, `symanzikV_classXPV_ge`); and `N = classNumerator c …` is a polynomial
of total degree at most `4` in the loop momenta (`isLoopPoly_classNumerator_L`, `…_X`).
-/

@[expose] public section

namespace QED.TwoLoop.Bridge

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Relabel
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix
  class5LoopMatrixPV classLXMomenta classPVMasses pvLines IntNoSubdivergence NoSubdivergence)

/-- The fermion fields of the five gauge vertices. -/
local notation "FV" => Wick.FermionVertex (gauges 5)

/-- The photon fields of the five gauge vertices. -/
local notation "PS" => Wick.PhotonSlot (gauges 5)

/-! ### Common data -/

/-- The index of a line of a contraction of five gauge vertices with the lines of `L` and `X`,
read off its label (X₂₀): the fermion lines with heads `1, 2, 3, 4` (labels `1, 2, 3, 4`) are
`0, 1, 2, 3`, the photon lines from the fields of vertices `0` and `1` (labels `5`, `7`) are `4`
and `5`. -/
def lineIdx {C : Contraction 1 1 (gauges 5)} (f : Line C) : Fin 6 :=
  match f.label with
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | _ => 5

/-- The routing of the class representative by the class loop matrix `class5LoopMatrix c` and
the external momenta `classLXMomenta p p'`, at loop momenta `ℓ`. -/
def classMom (c : Class5) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line c.rep) :
    Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix (class5LoopMatrix c)) (classLXMomenta p p') (lineIdx f) ℓ

/-- The flavoring with every vertex of flavour `0`. -/
def zeroFlavoring : Flavoring (gauges 5) := ⟨fun _ => 0, fun _ _ => rfl⟩

/-- The numerator of the class amplitude in the class routing. -/
noncomputable def classNumerator (c : Class5) (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  amplitudeNumerator P c.rep zeroFlavoring pIn kIn (classMom c (pIn 0) (pOut 0) ℓ) αOut βIn μ

/-- The Pauli–Villars data of `L` and `X` in the line order of `class5LoopMatrixPV`: external
momenta. -/
def pvMomenta (p p' : Fin 4 → ℝ) : Fin 8 → Fin 4 → ℝ := fun i => classLXMomenta p p' (pvLines i)

/-- The Pauli–Villars masses: electrons `m`, photons `m_γ` (lines `4, 5`) and `Λ` (lines `6, 7`). -/
def pvMasses (P : Params) : Fin 8 → ℝ := classPVMasses P.m P.mγ P.mγ P.Λ P.Λ

/-- The denominator `Dᵢ(ℓ)` of line `i` of the Pauli–Villars form of class `c`. -/
noncomputable def pvDenom (c : Class5) (P : Params) (p p' : Fin 4 → ℝ) (i : Fin 8)
    (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  lineDenom (castLoopMatrix (class5LoopMatrixPV c)) (pvMomenta p p') (pvMasses P) P.ε i ℓ

theorem preserves_zeroFlavoring {C : Contraction 1 1 (gauges 5)} : Preserves C zeroFlavoring := by
  intro a
  rcases C.1.1 a with _ | _ <;> rcases a with _ | _ <;> rfl

/-! ### The ladder `L`: lines -/

/-- The representative of the ladder class. -/
abbrev cL : Contraction 1 1 (gauges 5) := Class5.L.rep

/-- The fermion lines of `L`, by head `1, 2, 3, 4` (tails `0, 1, 2, 3`). -/
def lineL : Fin 4 → FermionLine cL :=
  ![⟨fv5 1, by decide +kernel⟩, ⟨fv5 2, by decide +kernel⟩, ⟨fv5 3, by decide +kernel⟩,
    ⟨fv5 4, by decide +kernel⟩]

/-- The photon lines `0 → 4` and `1 → 3` of `L`, indexed by the fields of `0` and `1`. -/
def photL : Fin 2 → PhotonLine cL :=
  ![⟨ps5 0, by decide +kernel⟩, ⟨ps5 1, by decide +kernel⟩]

theorem lineL_bijective : Function.Bijective lineL := by decide +kernel

theorem photL_bijective : Function.Bijective photL := by decide +kernel

theorem ends_lineL : (Line.ends (.inl (lineL 0) : Line cL)) = (0, 1) ∧
    (Line.ends (.inl (lineL 1) : Line cL)) = (1, 2) ∧
    (Line.ends (.inl (lineL 2) : Line cL)) = (2, 3) ∧
    (Line.ends (.inl (lineL 3) : Line cL)) = (3, 4) := by decide +kernel

theorem ends_photL : (Line.ends (.inr (photL 0) : Line cL)) = (0, 4) ∧
    (Line.ends (.inr (photL 1) : Line cL)) = (1, 3) := by decide +kernel

theorem prod_fermionLine_L {M : Type*} [CommMonoid M] [Fintype (FermionLine cL)]
    (g : FermionLine cL → M) :
    ∏ f, g f = g (lineL 0) * g (lineL 1) * g (lineL 2) * g (lineL 3) := by
  rw [← (Equiv.ofBijective _ lineL_bijective).prod_comp, Fin.prod_univ_four]
  rfl

theorem prod_photonLine_L {M : Type*} [CommMonoid M] [Fintype (PhotonLine cL)]
    (g : PhotonLine cL → M) : ∏ f, g f = g (photL 0) * g (photL 1) := by
  rw [← (Equiv.ofBijective _ photL_bijective).prod_comp, Fin.prod_univ_two]
  rfl

theorem sum_line_L {M : Type*} [AddCommMonoid M] [Fintype (FermionLine cL)]
    [Fintype (PhotonLine cL)] (g : Line cL → M) :
    ∑ f, g f = g (.inl (lineL 0)) + g (.inl (lineL 1)) + g (.inl (lineL 2)) +
      g (.inl (lineL 3)) + (g (.inr (photL 0)) + g (.inr (photL 1))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ lineL_bijective).sum_comp,
    ← (Equiv.ofBijective _ photL_bijective).sum_comp, Fin.sum_univ_four, Fin.sum_univ_two]
  rfl

theorem card_fermionLine_L [Fintype (FermionLine cL)] : Fintype.card (FermionLine cL) = 4 := by
  rw [← Fintype.card_of_bijective lineL_bijective, Fintype.card_fin]

theorem lineIdx_L : lineIdx (.inl (lineL 0) : Line cL) = 0 ∧
    lineIdx (.inl (lineL 1) : Line cL) = 1 ∧
    lineIdx (.inl (lineL 2) : Line cL) = 2 ∧ lineIdx (.inl (lineL 3) : Line cL) = 3 ∧
    lineIdx (.inr (photL 0) : Line cL) = 4 ∧ lineIdx (.inr (photL 1) : Line cL) = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The ladder `L`: external momenta and the class routing -/

theorem extPsi_iff_L (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cL.1.1 (.inr t) = .inl 0) ↔ v = 0 := by
  revert v
  decide +kernel

theorem extA_iff_L (v : Fin 5) :
    (∃ a : PS, a.1 = v ∧ cL.1.2 (.inl 0) = .inr a) ↔ v = 2 := by
  revert v
  decide +kernel

theorem extPsiBar_iff_L (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cL.1.1 (.inl 0) = .inr t) ↔ v = 4 := by
  revert v
  decide +kernel

/-- The external momenta (X₁₉) of `L`: `pIn` flows in at `0`, `kIn` at `2`, `pOut` out at `4`. -/
theorem externalMomentum_cL (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cL pOut pIn kIn v =
      (if v = 0 then pIn 0 else 0) + (if v = 2 then kIn 0 else 0) -
        (if v = 4 then pOut 0 else 0) := by
  unfold externalMomentum
  simp only [Fin.sum_univ_one, extPsi_iff_L, extA_iff_L, extPsiBar_iff_L]

/-- The class routing of `L` is conserved at every vertex, for all loop momenta, under momentum
conservation. -/
theorem isConserved_classMom_L {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved cL pOut pIn kIn (classMom .L (pIn 0) (pOut 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3⟩ := ends_lineL
  obtain ⟨g0, g1⟩ := ends_photL
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := lineIdx_L
  intro v
  rw [inflow, sum_line_L, externalMomentum_cL, hmom]
  simp only [classMom, e0, e1, e2, e3, g0, g1, i0, i1, i2, i3, i4, i5]
  funext μ
  fin_cases v <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, classLXMomenta, Fin.sum_univ_two] <;>
    ring

/-! ### The ladder `L`: chords and the frozen routing -/

theorem isChord_cL_iff : ∀ f : Line cL, IsChord f ↔ f = .inl (lineL 0) ∨ f = .inl (lineL 1) := by
  decide +kernel

open scoped Classical in
theorem card_chordsBelow_L : (Finset.univ.filter fun g : Line cL =>
      IsChord g ∧ g.label < (Line.label (.inl (lineL 0) : Line cL))).card = 0 ∧
    (Finset.univ.filter fun g : Line cL =>
      IsChord g ∧ g.label < (Line.label (.inl (lineL 1) : Line cL))).card = 1 := by
  have l0 : (Line.label (.inl (lineL 0) : Line cL)) = 1 := rfl
  have l1 : (Line.label (.inl (lineL 1) : Line cL)) = 2 := rfl
  constructor
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (isChord_cL_iff g).mp hg with rfl | rfl
    · simp [l0] at hl
    · simp [l0, l1] at hl
  · rw [Finset.card_eq_one]
    refine ⟨.inl (lineL 0), Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (isChord_cL_iff g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(isChord_cL_iff _).mpr (Or.inl rfl), by simp [l0, l1]⟩

theorem chordMomentum_lineL (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (lineL 0) : Line cL) = ℓ 0 ∧
      chordMomentum ℓ (.inl (lineL 1) : Line cL) = ℓ 1 := by
  classical
  obtain ⟨h0, h1⟩ := card_chordsBelow_L
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

/-- The unimodular change of loop momenta from the frozen routing of `L` to its class routing. -/
def matL : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem isUnit_det_matL : IsUnit matL.det := by
  rw [Matrix.det_fin_two]
  simp [matL]

/-- The class loop momenta of `L` in terms of the frozen ones: `(ℓ₁ - p, ℓ₀ - p)`. -/
def chgL (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  (fun s => ∑ r, matL s r • ℓ r) + ![-p, -p]

/-- **The frozen routing of `L` is the class routing** at the loop momenta `chgL p ℓ`, under
momentum conservation. -/
theorem lineMomentum₂_cL {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ cL pOut pIn kIn ℓ = classMom .L (pIn 0) (pOut 0) (chgL (pIn 0) ℓ) := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (isConserved_classMom_L hmom _) (fun g hg => ?_) f).symm
  obtain ⟨c0, c1⟩ := chordMomentum_lineL ℓ
  obtain ⟨i0, i1, -⟩ := lineIdx_L
  rcases (isChord_cL_iff g).mp hg with rfl | rfl
  · rw [c0, classMom, i0]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, classLXMomenta, chgL, matL,
      Fin.sum_univ_two]
  · rw [c1, classMom, i1]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, classLXMomenta, chgL, matL,
      Fin.sum_univ_two]

/-- The loop matrix of the frozen routing of `L` (rows `v₀v₁, v₁v₂, v₂v₃, v₃v₄`, photons
`0 → 4`, `1 → 3`; columns the chord momenta `ℓ₀`, `ℓ₁`). -/
def frozenLoopMatrixL : Fin 6 → Fin 2 → ℤ :=
  ![![1, 0], ![0, 1], ![0, 1], ![1, 0], ![-1, 0], ![1, -1]]

/-- The external momenta of the frozen routing of `L`. -/
def frozenMomentaL (p k : Fin 4 → ℝ) : Fin 6 → Fin 4 → ℝ := ![0, 0, k, k, p, 0]

theorem frozenLoopMatrixL_eq :
    frozenLoopMatrixL = fun i s => ∑ r, class5LoopMatrix .L i r * matL r s := by
  decide

/-- **The frozen routing of `L` with its loop matrix**: `k_f(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ` with
`α = frozenLoopMatrixL`, `i = lineIdx f`. -/
theorem lineMomentum₂_cL_eq_frozen {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line cL) :
    lineMomentum₂ cL pOut pIn kIn ℓ f =
      lineMomentum (castLoopMatrix frozenLoopMatrixL) (frozenMomentaL (pIn 0) (kIn 0))
        (lineIdx f) ℓ := by
  rw [lineMomentum₂_cL hmom, classMom, hmom]
  generalize lineIdx f = i
  funext μ
  fin_cases i <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, classLXMomenta, chgL, matL,
      frozenLoopMatrixL, frozenMomentaL, Fin.sum_univ_two] <;>
    ring

theorem intNoSubdivergence_frozenLoopMatrixL : IntNoSubdivergence frozenLoopMatrixL := by
  decide

theorem intNoSubdivergence_frozenLoopMatrixL_PV :
    IntNoSubdivergence fun i => frozenLoopMatrixL (pvLines i) := by
  decide

/-! ### The ladder `L`: flavorings and the amplitude -/

theorem cL_pow_six : cL.1.1 ^ 6 = 1 := by decide +kernel

theorem cL_orbit : ∀ x : Fin 1 ⊕ FV, ∃ i : Fin 6, (cL.1.1 ^ (i : ℕ)) x = .inl 0 := by
  decide +kernel

theorem sameCycle_cL (x : Fin 1 ⊕ FV) : Equiv.Perm.SameCycle cL.1.1 x (.inl 0) := by
  obtain ⟨i, hi⟩ := cL_orbit x
  exact ⟨(i : ℕ), by rw [zpow_natCast]; exact hi⟩

/-- `L` has no closed fermion loop. -/
theorem isEmpty_closedLoop_L : IsEmpty (ClosedLoop cL) := by
  refine ⟨fun ⟨q, hq⟩ => ?_⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact hq 0 (Quotient.sound (sameCycle_cL x).symm)

theorem preserves_iff_L (φ : Flavoring (gauges 5)) : Preserves cL φ ↔ φ = zeroFlavoring := by
  refine ⟨fun hφ => Subtype.ext (funext fun t => ?_), fun h => h ▸ preserves_zeroFlavoring⟩
  exact fermionFlavor_eq_of_sameCycle hφ (sameCycle_cL (.inr t))

open scoped Classical in
/-- The regulated amplitude (T₈) of `L` is its amplitude (T₇) at flavour `0`. -/
theorem regulatedAmplitude₂_cL (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line cL → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P cL pIn kIn k αOut βIn μ =
      contractionAmplitude₂ P cL zeroFlavoring pIn kIn k αOut βIn μ := by
  have hfil : (Finset.univ : Finset (Flavoring (gauges 5))).filter (Preserves cL) =
      {zeroFlavoring} := Finset.ext fun φ => by simp [preserves_iff_L]
  have hw : loopWeight P cL zeroFlavoring = 1 := by
    have := isEmpty_closedLoop_L
    simp [loopWeight]
  rw [regulatedAmplitude₂, hfil, Finset.sum_singleton, hw, Complex.ofReal_one, one_mul]

/-- The denominators of `L` in the class routing are the eight Pauli–Villars line denominators. -/
theorem amplitudeDenominator_cL (P : Params) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    amplitudeDenominator P cL zeroFlavoring (classMom .L p p' ℓ) =
      ∏ i : Fin 8, (pvDenom .L P p p' i ℓ)⁻¹ := by
  have h : amplitudeDenominator P cL zeroFlavoring (classMom .L p p' ℓ) =
      (pvDenom .L P p p' 0 ℓ)⁻¹ * (pvDenom .L P p p' 1 ℓ)⁻¹ * (pvDenom .L P p p' 2 ℓ)⁻¹ *
        (pvDenom .L P p p' 3 ℓ)⁻¹ * (((pvDenom .L P p p' 4 ℓ)⁻¹ * (pvDenom .L P p p' 6 ℓ)⁻¹) *
          ((pvDenom .L P p p' 5 ℓ)⁻¹ * (pvDenom .L P p p' 7 ℓ)⁻¹)) := by
    rw [amplitudeDenominator, prod_fermionLine_L, prod_photonLine_L]
    rfl
  rw [h, Fin.prod_univ_eight]
  ring

/-- **The integrand of `L` in parametric form**: for `ε ≠ 0`, the regulated amplitude (T₈) in the
class routing is the numerator times the eight Pauli–Villars line denominators. -/
theorem regulatedAmplitude₂_classMom_L (P : Params) (hε : P.ε ≠ 0)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cL pIn kIn (classMom .L (pIn 0) (pOut 0) ℓ) αOut βIn μ =
      classNumerator .L P pOut pIn kIn αOut βIn μ ℓ *
        ∏ i : Fin 8, (pvDenom .L P (pIn 0) (pOut 0) i ℓ)⁻¹ := by
  rw [regulatedAmplitude₂_cL, contractionAmplitude₂_eq P hε, amplitudeDenominator_cL]
  rfl

/-- **The value of `L` in parametric form.** For `ε ≠ 0` and under momentum conservation, the
value (T₁₀) of the ladder class is the joint energy-first integral of `(2π)⁻⁸` times the class
numerator times the product of the eight Pauli–Villars line denominators for the loop matrix
`class5LoopMatrixPV .L`. No integrability is needed. -/
theorem contractionValue₂_L_eq (P : Params) (hε : P.ε ≠ 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.L.rep pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          (classNumerator .L P pOut pIn kIn αOut βIn μ ℓ *
            ∏ i : Fin 8, (pvDenom .L P (pIn 0) (pOut 0) i ℓ)⁻¹) := by
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .L)]
  simp only [lineMomentum₂_cL hmom]
  have h := JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
    (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cL pIn kIn (classMom .L (pIn 0) (pOut 0) ℓ) αOut βIn μ)
    matL isUnit_det_matL ![-(pIn 0), -(pIn 0)]
  refine h.trans ?_
  refine congrArg (QED.TwoLoop.jointEnergyFirstIntegral 2) (funext fun ℓ => ?_)
  rw [regulatedAmplitude₂_classMom_L P hε]

/-- The numerator of `L` is a polynomial of total degree at most `4` in the loop momenta. -/
theorem isLoopPoly_classNumerator_L (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 (classNumerator .L P pOut pIn kIn αOut βIn μ) := by
  have h := isLoopPoly_amplitudeNumerator P cL zeroFlavoring pIn kIn
    (classMom .L (pIn 0) (pOut 0)) (fun f => isLoopAffine_lineMomentum _ _ _) αOut βIn μ
  rwa [card_fermionLine_L] at h

/-! ### The crossed ladder `X`: lines -/

/-- The representative of the crossed-ladder class. -/
abbrev cX : Contraction 1 1 (gauges 5) := Class5.X.rep

/-- The fermion lines of `X`, by head `1, 2, 3, 4` (tails `0, 1, 2, 3`). -/
def lineX : Fin 4 → FermionLine cX :=
  ![⟨fv5 1, by decide +kernel⟩, ⟨fv5 2, by decide +kernel⟩, ⟨fv5 3, by decide +kernel⟩,
    ⟨fv5 4, by decide +kernel⟩]

/-- The photon lines `0 → 3` and `1 → 4` of `X`, indexed by the fields of `0` and `1`. -/
def photX : Fin 2 → PhotonLine cX :=
  ![⟨ps5 0, by decide +kernel⟩, ⟨ps5 1, by decide +kernel⟩]

theorem lineX_bijective : Function.Bijective lineX := by decide +kernel

theorem photX_bijective : Function.Bijective photX := by decide +kernel

theorem ends_lineX : (Line.ends (.inl (lineX 0) : Line cX)) = (0, 1) ∧
    (Line.ends (.inl (lineX 1) : Line cX)) = (1, 2) ∧
    (Line.ends (.inl (lineX 2) : Line cX)) = (2, 3) ∧
    (Line.ends (.inl (lineX 3) : Line cX)) = (3, 4) := by decide +kernel

theorem ends_photX : (Line.ends (.inr (photX 0) : Line cX)) = (0, 3) ∧
    (Line.ends (.inr (photX 1) : Line cX)) = (1, 4) := by decide +kernel

theorem prod_fermionLine_X {M : Type*} [CommMonoid M] [Fintype (FermionLine cX)]
    (g : FermionLine cX → M) :
    ∏ f, g f = g (lineX 0) * g (lineX 1) * g (lineX 2) * g (lineX 3) := by
  rw [← (Equiv.ofBijective _ lineX_bijective).prod_comp, Fin.prod_univ_four]
  rfl

theorem prod_photonLine_X {M : Type*} [CommMonoid M] [Fintype (PhotonLine cX)]
    (g : PhotonLine cX → M) : ∏ f, g f = g (photX 0) * g (photX 1) := by
  rw [← (Equiv.ofBijective _ photX_bijective).prod_comp, Fin.prod_univ_two]
  rfl

theorem sum_line_X {M : Type*} [AddCommMonoid M] [Fintype (FermionLine cX)]
    [Fintype (PhotonLine cX)] (g : Line cX → M) :
    ∑ f, g f = g (.inl (lineX 0)) + g (.inl (lineX 1)) + g (.inl (lineX 2)) +
      g (.inl (lineX 3)) + (g (.inr (photX 0)) + g (.inr (photX 1))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ lineX_bijective).sum_comp,
    ← (Equiv.ofBijective _ photX_bijective).sum_comp, Fin.sum_univ_four, Fin.sum_univ_two]
  rfl

theorem card_fermionLine_X [Fintype (FermionLine cX)] : Fintype.card (FermionLine cX) = 4 := by
  rw [← Fintype.card_of_bijective lineX_bijective, Fintype.card_fin]

theorem lineIdx_X : lineIdx (.inl (lineX 0) : Line cX) = 0 ∧
    lineIdx (.inl (lineX 1) : Line cX) = 1 ∧
    lineIdx (.inl (lineX 2) : Line cX) = 2 ∧ lineIdx (.inl (lineX 3) : Line cX) = 3 ∧
    lineIdx (.inr (photX 0) : Line cX) = 4 ∧ lineIdx (.inr (photX 1) : Line cX) = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The crossed ladder `X`: external momenta and the class routing -/

theorem extPsi_iff_X (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cX.1.1 (.inr t) = .inl 0) ↔ v = 0 := by
  revert v
  decide +kernel

theorem extA_iff_X (v : Fin 5) :
    (∃ a : PS, a.1 = v ∧ cX.1.2 (.inl 0) = .inr a) ↔ v = 2 := by
  revert v
  decide +kernel

theorem extPsiBar_iff_X (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cX.1.1 (.inl 0) = .inr t) ↔ v = 4 := by
  revert v
  decide +kernel

/-- The external momenta (X₁₉) of `X`: `pIn` flows in at `0`, `kIn` at `2`, `pOut` out at `4`. -/
theorem externalMomentum_cX (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cX pOut pIn kIn v =
      (if v = 0 then pIn 0 else 0) + (if v = 2 then kIn 0 else 0) -
        (if v = 4 then pOut 0 else 0) := by
  unfold externalMomentum
  simp only [Fin.sum_univ_one, extPsi_iff_X, extA_iff_X, extPsiBar_iff_X]

/-- The class routing of `X` is conserved at every vertex, for all loop momenta, under momentum
conservation. -/
theorem isConserved_classMom_X {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved cX pOut pIn kIn (classMom .X (pIn 0) (pOut 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3⟩ := ends_lineX
  obtain ⟨g0, g1⟩ := ends_photX
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := lineIdx_X
  intro v
  rw [inflow, sum_line_X, externalMomentum_cX, hmom]
  simp only [classMom, e0, e1, e2, e3, g0, g1, i0, i1, i2, i3, i4, i5]
  funext μ
  fin_cases v <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, classLXMomenta, Fin.sum_univ_two] <;>
    ring

/-! ### The crossed ladder `X`: chords and the frozen routing -/

theorem isChord_cX_iff : ∀ f : Line cX, IsChord f ↔ f = .inl (lineX 0) ∨ f = .inl (lineX 1) := by
  decide +kernel

open scoped Classical in
theorem card_chordsBelow_X : (Finset.univ.filter fun g : Line cX =>
      IsChord g ∧ g.label < (Line.label (.inl (lineX 0) : Line cX))).card = 0 ∧
    (Finset.univ.filter fun g : Line cX =>
      IsChord g ∧ g.label < (Line.label (.inl (lineX 1) : Line cX))).card = 1 := by
  have l0 : (Line.label (.inl (lineX 0) : Line cX)) = 1 := rfl
  have l1 : (Line.label (.inl (lineX 1) : Line cX)) = 2 := rfl
  constructor
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (isChord_cX_iff g).mp hg with rfl | rfl
    · simp [l0] at hl
    · simp [l0, l1] at hl
  · rw [Finset.card_eq_one]
    refine ⟨.inl (lineX 0), Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (isChord_cX_iff g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(isChord_cX_iff _).mpr (Or.inl rfl), by simp [l0, l1]⟩

theorem chordMomentum_lineX (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (lineX 0) : Line cX) = ℓ 0 ∧
      chordMomentum ℓ (.inl (lineX 1) : Line cX) = ℓ 1 := by
  classical
  obtain ⟨h0, h1⟩ := card_chordsBelow_X
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

/-- The unimodular change of loop momenta from the frozen routing of `X` to its class routing. -/
def matX : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 1]

theorem isUnit_det_matX : IsUnit matX.det := by
  rw [Matrix.det_fin_two]
  simp [matX]

/-- The class loop momenta of `X` in terms of the frozen ones: `(ℓ₁ - p, ℓ₁ - ℓ₀)`. -/
def chgX (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  (fun s => ∑ r, matX s r • ℓ r) + ![-p, 0]

/-- **The frozen routing of `X` is the class routing** at the loop momenta `chgX p ℓ`, under
momentum conservation. -/
theorem lineMomentum₂_cX {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ cX pOut pIn kIn ℓ = classMom .X (pIn 0) (pOut 0) (chgX (pIn 0) ℓ) := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (isConserved_classMom_X hmom _) (fun g hg => ?_) f).symm
  obtain ⟨c0, c1⟩ := chordMomentum_lineX ℓ
  obtain ⟨i0, i1, -⟩ := lineIdx_X
  rcases (isChord_cX_iff g).mp hg with rfl | rfl
  · rw [c0, classMom, i0]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, classLXMomenta, chgX, matX,
      Fin.sum_univ_two]
    ring
  · rw [c1, classMom, i1]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, classLXMomenta, chgX, matX,
      Fin.sum_univ_two]

/-- The loop matrix of the frozen routing of `X` (rows `v₀v₁, v₁v₂, v₂v₃, v₃v₄`, photons
`0 → 3`, `1 → 4`; columns the chord momenta `ℓ₀`, `ℓ₁`). -/
def frozenLoopMatrixX : Fin 6 → Fin 2 → ℤ :=
  ![![1, 0], ![0, 1], ![0, 1], ![-1, 1], ![-1, 0], ![1, -1]]

/-- The external momenta of the frozen routing of `X`. -/
def frozenMomentaX (p k : Fin 4 → ℝ) : Fin 6 → Fin 4 → ℝ := ![0, 0, k, k + p, p, 0]

theorem frozenLoopMatrixX_eq :
    frozenLoopMatrixX = fun i s => ∑ r, class5LoopMatrix .X i r * matX r s := by
  decide

/-- **The frozen routing of `X` with its loop matrix**: `k_f(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ` with
`α = frozenLoopMatrixX`, `i = lineIdx f`. -/
theorem lineMomentum₂_cX_eq_frozen {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line cX) :
    lineMomentum₂ cX pOut pIn kIn ℓ f =
      lineMomentum (castLoopMatrix frozenLoopMatrixX) (frozenMomentaX (pIn 0) (kIn 0))
        (lineIdx f) ℓ := by
  rw [lineMomentum₂_cX hmom, classMom, hmom]
  generalize lineIdx f = i
  funext μ
  fin_cases i <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, classLXMomenta, chgX, matX,
      frozenLoopMatrixX, frozenMomentaX, Fin.sum_univ_two] <;>
    ring

theorem intNoSubdivergence_frozenLoopMatrixX : IntNoSubdivergence frozenLoopMatrixX := by
  decide

theorem intNoSubdivergence_frozenLoopMatrixX_PV :
    IntNoSubdivergence fun i => frozenLoopMatrixX (pvLines i) := by
  decide

/-! ### The crossed ladder `X`: flavorings and the amplitude -/

theorem cX_pow_six : cX.1.1 ^ 6 = 1 := by decide +kernel

theorem cX_orbit : ∀ x : Fin 1 ⊕ FV, ∃ i : Fin 6, (cX.1.1 ^ (i : ℕ)) x = .inl 0 := by
  decide +kernel

theorem sameCycle_cX (x : Fin 1 ⊕ FV) : Equiv.Perm.SameCycle cX.1.1 x (.inl 0) := by
  obtain ⟨i, hi⟩ := cX_orbit x
  exact ⟨(i : ℕ), by rw [zpow_natCast]; exact hi⟩

/-- `X` has no closed fermion loop. -/
theorem isEmpty_closedLoop_X : IsEmpty (ClosedLoop cX) := by
  refine ⟨fun ⟨q, hq⟩ => ?_⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact hq 0 (Quotient.sound (sameCycle_cX x).symm)

theorem preserves_iff_X (φ : Flavoring (gauges 5)) : Preserves cX φ ↔ φ = zeroFlavoring := by
  refine ⟨fun hφ => Subtype.ext (funext fun t => ?_), fun h => h ▸ preserves_zeroFlavoring⟩
  exact fermionFlavor_eq_of_sameCycle hφ (sameCycle_cX (.inr t))

open scoped Classical in
/-- The regulated amplitude (T₈) of `X` is its amplitude (T₇) at flavour `0`. -/
theorem regulatedAmplitude₂_cX (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line cX → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P cX pIn kIn k αOut βIn μ =
      contractionAmplitude₂ P cX zeroFlavoring pIn kIn k αOut βIn μ := by
  have hfil : (Finset.univ : Finset (Flavoring (gauges 5))).filter (Preserves cX) =
      {zeroFlavoring} := Finset.ext fun φ => by simp [preserves_iff_X]
  have hw : loopWeight P cX zeroFlavoring = 1 := by
    have := isEmpty_closedLoop_X
    simp [loopWeight]
  rw [regulatedAmplitude₂, hfil, Finset.sum_singleton, hw, Complex.ofReal_one, one_mul]

/-- The denominators of `X` in the class routing are the eight Pauli–Villars line denominators. -/
theorem amplitudeDenominator_cX (P : Params) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    amplitudeDenominator P cX zeroFlavoring (classMom .X p p' ℓ) =
      ∏ i : Fin 8, (pvDenom .X P p p' i ℓ)⁻¹ := by
  have h : amplitudeDenominator P cX zeroFlavoring (classMom .X p p' ℓ) =
      (pvDenom .X P p p' 0 ℓ)⁻¹ * (pvDenom .X P p p' 1 ℓ)⁻¹ * (pvDenom .X P p p' 2 ℓ)⁻¹ *
        (pvDenom .X P p p' 3 ℓ)⁻¹ * (((pvDenom .X P p p' 4 ℓ)⁻¹ * (pvDenom .X P p p' 6 ℓ)⁻¹) *
          ((pvDenom .X P p p' 5 ℓ)⁻¹ * (pvDenom .X P p p' 7 ℓ)⁻¹)) := by
    rw [amplitudeDenominator, prod_fermionLine_X, prod_photonLine_X]
    rfl
  rw [h, Fin.prod_univ_eight]
  ring

/-- **The integrand of `X` in parametric form**: for `ε ≠ 0`, the regulated amplitude (T₈) in the
class routing is the numerator times the eight Pauli–Villars line denominators. -/
theorem regulatedAmplitude₂_classMom_X (P : Params) (hε : P.ε ≠ 0)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cX pIn kIn (classMom .X (pIn 0) (pOut 0) ℓ) αOut βIn μ =
      classNumerator .X P pOut pIn kIn αOut βIn μ ℓ *
        ∏ i : Fin 8, (pvDenom .X P (pIn 0) (pOut 0) i ℓ)⁻¹ := by
  rw [regulatedAmplitude₂_cX, contractionAmplitude₂_eq P hε, amplitudeDenominator_cX]
  rfl

/-- **The value of `X` in parametric form.** For `ε ≠ 0` and under momentum conservation, the
value (T₁₀) of the crossed-ladder class is the joint energy-first integral of `(2π)⁻⁸` times the
class numerator times the product of the eight Pauli–Villars line denominators for the loop matrix
`class5LoopMatrixPV .X`. No integrability is needed. -/
theorem contractionValue₂_X_eq (P : Params) (hε : P.ε ≠ 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.X.rep pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          (classNumerator .X P pOut pIn kIn αOut βIn μ ℓ *
            ∏ i : Fin 8, (pvDenom .X P (pIn 0) (pOut 0) i ℓ)⁻¹) := by
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .X)]
  simp only [lineMomentum₂_cX hmom]
  have h := JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
    (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cX pIn kIn (classMom .X (pIn 0) (pOut 0) ℓ) αOut βIn μ)
    matX isUnit_det_matX ![-(pIn 0), 0]
  refine h.trans ?_
  refine congrArg (QED.TwoLoop.jointEnergyFirstIntegral 2) (funext fun ℓ => ?_)
  rw [regulatedAmplitude₂_classMom_X P hε]

/-- The numerator of `X` is a polynomial of total degree at most `4` in the loop momenta. -/
theorem isLoopPoly_classNumerator_X (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 (classNumerator .X P pOut pIn kIn αOut βIn μ) := by
  have h := isLoopPoly_amplitudeNumerator P cX zeroFlavoring pIn kIn
    (classMom .X (pIn 0) (pOut 0)) (fun f => isLoopAffine_lineMomentum _ _ _) αOut βIn μ
  rwa [card_fermionLine_X] at h

/-! ### Summary for `L` and `X` -/

theorem noSubdivergence_frozenLoopMatrixL : NoSubdivergence (castLoopMatrix frozenLoopMatrixL) :=
  (QED.Integration.TwoLoop.noSubdivergence_castLoopMatrix_iff _).mpr
    intNoSubdivergence_frozenLoopMatrixL

theorem noSubdivergence_frozenLoopMatrixX : NoSubdivergence (castLoopMatrix frozenLoopMatrixX) :=
  (QED.Integration.TwoLoop.noSubdivergence_castLoopMatrix_iff _).mpr
    intNoSubdivergence_frozenLoopMatrixX

/-- The integrand of `L` at the frozen routing, in the frozen loop momenta. -/
theorem regulatedAmplitude₂_lineMomentum₂_L (P : Params) (hε : P.ε ≠ 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cL pIn kIn (lineMomentum₂ cL pOut pIn kIn ℓ) αOut βIn μ =
      classNumerator .L P pOut pIn kIn αOut βIn μ (chgL (pIn 0) ℓ) *
        ∏ i : Fin 8, (pvDenom .L P (pIn 0) (pOut 0) i (chgL (pIn 0) ℓ))⁻¹ := by
  rw [lineMomentum₂_cL hmom, regulatedAmplitude₂_classMom_L P hε]

/-- The integrand of `X` at the frozen routing, in the frozen loop momenta. -/
theorem regulatedAmplitude₂_lineMomentum₂_X (P : Params) (hε : P.ε ≠ 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cX pIn kIn (lineMomentum₂ cX pOut pIn kIn ℓ) αOut βIn μ =
      classNumerator .X P pOut pIn kIn αOut βIn μ (chgX (pIn 0) ℓ) *
        ∏ i : Fin 8, (pvDenom .X P (pIn 0) (pOut 0) i (chgX (pIn 0) ℓ))⁻¹ := by
  rw [lineMomentum₂_cX hmom, regulatedAmplitude₂_classMom_X P hε]

/-- **Parametric form of `L` and `X`.** For `ε ≠ 0` and under momentum conservation, the value
(T₁₀) is the joint energy-first integral of `(2π)⁻⁸ N(ℓ) ∏ᵢ₌₀⁷ Dᵢ(ℓ)⁻¹` with `N` a polynomial of
total degree at most `4` in the loop momenta and `Dᵢ` the line denominators of the Pauli–Villars
form of the class, whose loop matrix `class5LoopMatrixPV c` satisfies the no-subdivergence
criterion. -/
theorem parametricForm_LX {c : Class5} (hc : c = .L ∨ c = .X) (P : Params) (hε : P.ε ≠ 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ =
        QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
          (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
            (classNumerator c P pOut pIn kIn αOut βIn μ ℓ *
              ∏ i : Fin 8, (pvDenom c P (pIn 0) (pOut 0) i ℓ)⁻¹)) ∧
      IsLoopPoly 2 4 (classNumerator c P pOut pIn kIn αOut βIn μ) ∧
      NoSubdivergence (castLoopMatrix (class5LoopMatrixPV c)) := by
  rcases hc with rfl | rfl
  · exact ⟨contractionValue₂_L_eq P hε hmom αOut βIn μ,
      isLoopPoly_classNumerator_L P pOut pIn kIn αOut βIn μ,
      QED.Integration.TwoLoop.noSubdivergence_loopMatrixPV (by decide)⟩
  · exact ⟨contractionValue₂_X_eq P hε hmom αOut βIn μ,
      isLoopPoly_classNumerator_X P pOut pIn kIn αOut βIn μ,
      QED.Integration.TwoLoop.noSubdivergence_loopMatrixPV (by decide)⟩

end QED.TwoLoop.Bridge

end
