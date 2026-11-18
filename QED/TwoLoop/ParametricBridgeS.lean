/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ParametricBridgeC

/-!
# The self-energy classes in parametric form

Part of obligations O2-7 and O2-10 (`docs/TWO-LOOP-DERIVATION.md`, sections 4.1–4.4) for the
self-energy classes `S₊`, `S₋` of five gauge vertices (`QED.TwoLoop.Enumeration.Class5.Sp`,
`.Sm`), with the common data of `QED/TwoLoop/ParametricBridgeC.lean`. Their representatives have
the open line `0 → 1 → 2 → 3 → 4` and

| class | external photon at | internal photons | chords (T₁) |
| --- | --- | --- | --- |
| `S₊` | `1` | `(0 4)`, the subloop photon `(2 3)` | `v₀v₁` (`ℓ 0`), `v₂v₃` (`ℓ 1`) |
| `S₋` | `3` | `(0 4)`, the subloop photon `(1 2)` | `v₀v₁` (`ℓ 0`), `v₁v₂` (`ℓ 1`) |

**The frozen routing** is the class routing at `M ℓ + a` with `M` integer unimodular
(`lineMomentum₂_cSp`, `lineMomentum₂_cSm`; `frozenLoopMatrixSp_eq`, `frozenLoopMatrixSm_eq`,
kernel-checked). With one denominator per line the frozen loop matrices **violate** the
no-subdivergence criterion (`not_intNoSubdivergence_frozenLoopMatrixSp`, `…Sm`: the self-energy
subgraph has two lines). With the Pauli–Villars pair of each photon combined, in particular of
the subloop photon, as two denominators with the same momentum, they satisfy it
(`intNoSubdivergence_frozenLoopMatrixSp_PV`, `…Sm_PV`), as do the class matrices
`class5LoopMatrixPV` (`noSubdivergence_loopMatrixPV`). The combination is exact at `ε ≠ 0`
(`QED.TwoLoop.Bridge.photonPropagator_eq_mul`): the photon propagator is
`g_{μν} (Λ² - m_γ²) (k² + m_γ² - iε)⁻¹ (k² + Λ² - iε)⁻¹`, and the constant `Λ² - m_γ²` is part of
the numerator.

**The value in parametric form** (`contractionValue₂_Sp_eq`, `contractionValue₂_Sm_eq`,
`parametricForm_S`): for `ε ≠ 0` and under momentum conservation, the value (T₁₀) is the joint
energy-first integral of `(2π)⁻⁸ N(ℓ) ∏ᵢ₌₀⁷ Dᵢ(ℓ)⁻¹` with the eight Pauli–Villars line
denominators `Dᵢ = pvDenomE c …` and `N` of total degree at most `4`, in the class and in the
frozen loop momenta. `parametricForm_open` collects the six open-line classes `L`, `X`, `C±`,
`S±`.
-/

@[expose] public section

namespace QED.TwoLoop.Bridge

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Relabel
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix
  class5LoopMatrixPV classCpSpMomenta classCmSmMomenta pvLines IntNoSubdivergence
  NoSubdivergence)

/-- The fermion fields of the five gauge vertices. -/
local notation "FV" => Wick.FermionVertex (gauges 5)

/-- The photon fields of the five gauge vertices. -/
local notation "PS" => Wick.PhotonSlot (gauges 5)

/-! ### `S₊`: lines -/

/-- The representative of the class `S₊`. -/
abbrev cSp : Contraction 1 1 (gauges 5) := Class5.Sp.rep

/-- The fermion lines of `S₊`, by head `1, 2, 3, 4` (tails `0, 1, 2, 3`). -/
def lineSp : Fin 4 → FermionLine cSp :=
  ![⟨fv5 1, by decide +kernel⟩, ⟨fv5 2, by decide +kernel⟩, ⟨fv5 3, by decide +kernel⟩,
    ⟨fv5 4, by decide +kernel⟩]

/-- The photon lines `0 → 4` and `2 → 3` of `S₊`, indexed by the fields of `0` and `2`. -/
def photSp : Fin 2 → PhotonLine cSp :=
  ![⟨ps5 0, by decide +kernel⟩, ⟨ps5 2, by decide +kernel⟩]

theorem lineSp_bijective : Function.Bijective lineSp := by decide +kernel

theorem photSp_bijective : Function.Bijective photSp := by decide +kernel

theorem ends_lineSp : (Line.ends (.inl (lineSp 0) : Line cSp)) = (0, 1) ∧
    (Line.ends (.inl (lineSp 1) : Line cSp)) = (1, 2) ∧
    (Line.ends (.inl (lineSp 2) : Line cSp)) = (2, 3) ∧
    (Line.ends (.inl (lineSp 3) : Line cSp)) = (3, 4) := by decide +kernel

theorem ends_photSp : (Line.ends (.inr (photSp 0) : Line cSp)) = (0, 4) ∧
    (Line.ends (.inr (photSp 1) : Line cSp)) = (2, 3) := by decide +kernel

theorem prod_fermionLine_Sp {M : Type*} [CommMonoid M] [Fintype (FermionLine cSp)]
    (g : FermionLine cSp → M) :
    ∏ f, g f = g (lineSp 0) * g (lineSp 1) * g (lineSp 2) * g (lineSp 3) := by
  rw [← (Equiv.ofBijective _ lineSp_bijective).prod_comp, Fin.prod_univ_four]
  rfl

theorem prod_photonLine_Sp {M : Type*} [CommMonoid M] [Fintype (PhotonLine cSp)]
    (g : PhotonLine cSp → M) : ∏ f, g f = g (photSp 0) * g (photSp 1) := by
  rw [← (Equiv.ofBijective _ photSp_bijective).prod_comp, Fin.prod_univ_two]
  rfl

theorem sum_line_Sp {M : Type*} [AddCommMonoid M] [Fintype (FermionLine cSp)]
    [Fintype (PhotonLine cSp)] (g : Line cSp → M) :
    ∑ f, g f = g (.inl (lineSp 0)) + g (.inl (lineSp 1)) + g (.inl (lineSp 2)) +
      g (.inl (lineSp 3)) + (g (.inr (photSp 0)) + g (.inr (photSp 1))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ lineSp_bijective).sum_comp,
    ← (Equiv.ofBijective _ photSp_bijective).sum_comp, Fin.sum_univ_four, Fin.sum_univ_two]
  rfl

theorem card_fermionLine_Sp [Fintype (FermionLine cSp)] : Fintype.card (FermionLine cSp) = 4 := by
  rw [← Fintype.card_of_bijective lineSp_bijective, Fintype.card_fin]

theorem lineIdx_Sp : lineIdx (.inl (lineSp 0) : Line cSp) = 0 ∧
    lineIdx (.inl (lineSp 1) : Line cSp) = 1 ∧
    lineIdx (.inl (lineSp 2) : Line cSp) = 2 ∧ lineIdx (.inl (lineSp 3) : Line cSp) = 3 ∧
    lineIdx (.inr (photSp 0) : Line cSp) = 4 ∧ lineIdx (.inr (photSp 1) : Line cSp) = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### `S₊`: external momenta and the class routing -/

theorem extPsi_iff_Sp (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cSp.1.1 (.inr t) = .inl 0) ↔ v = 0 := by
  revert v
  decide +kernel

theorem extA_iff_Sp (v : Fin 5) :
    (∃ a : PS, a.1 = v ∧ cSp.1.2 (.inl 0) = .inr a) ↔ v = 1 := by
  revert v
  decide +kernel

theorem extPsiBar_iff_Sp (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cSp.1.1 (.inl 0) = .inr t) ↔ v = 4 := by
  revert v
  decide +kernel

/-- The external momenta (X₁₉) of `S₊`: `pIn` flows in at `0`, `kIn` at `1`, `pOut` out at `4`. -/
theorem externalMomentum_cSp (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cSp pOut pIn kIn v =
      (if v = 0 then pIn 0 else 0) + (if v = 1 then kIn 0 else 0) -
        (if v = 4 then pOut 0 else 0) := by
  unfold externalMomentum
  simp only [Fin.sum_univ_one, extPsi_iff_Sp, extA_iff_Sp, extPsiBar_iff_Sp]

/-- The class routing of `S₊` is conserved at every vertex, for all loop momenta, under momentum
conservation. -/
theorem isConserved_classMomE_Sp {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved cSp pOut pIn kIn (classMomE .Sp (pIn 0) (pOut 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3⟩ := ends_lineSp
  obtain ⟨g0, g1⟩ := ends_photSp
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := lineIdx_Sp
  intro v
  rw [inflow, sum_line_Sp, externalMomentum_cSp, hmom]
  simp only [classMomE, e0, e1, e2, e3, g0, g1, i0, i1, i2, i3, i4, i5]
  funext μ
  fin_cases v <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCpSpMomenta,
      Fin.sum_univ_two] <;>
    ring

/-! ### `S₊`: chords and the frozen routing -/

theorem isChord_cSp_iff :
    ∀ f : Line cSp, IsChord f ↔ f = .inl (lineSp 0) ∨ f = .inl (lineSp 2) := by
  decide +kernel

open scoped Classical in
theorem card_chordsBelow_Sp : (Finset.univ.filter fun g : Line cSp =>
      IsChord g ∧ g.label < (Line.label (.inl (lineSp 0) : Line cSp))).card = 0 ∧
    (Finset.univ.filter fun g : Line cSp =>
      IsChord g ∧ g.label < (Line.label (.inl (lineSp 2) : Line cSp))).card = 1 := by
  have l0 : (Line.label (.inl (lineSp 0) : Line cSp)) = 1 := rfl
  have l1 : (Line.label (.inl (lineSp 2) : Line cSp)) = 3 := rfl
  constructor
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (isChord_cSp_iff g).mp hg with rfl | rfl
    · simp [l0] at hl
    · simp [l0, l1] at hl
  · rw [Finset.card_eq_one]
    refine ⟨.inl (lineSp 0), Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (isChord_cSp_iff g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(isChord_cSp_iff _).mpr (Or.inl rfl), by simp [l0, l1]⟩

theorem chordMomentum_lineSp (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (lineSp 0) : Line cSp) = ℓ 0 ∧
      chordMomentum ℓ (.inl (lineSp 2) : Line cSp) = ℓ 1 := by
  classical
  obtain ⟨h0, h1⟩ := card_chordsBelow_Sp
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

/-- The unimodular change of loop momenta from the frozen routing of `S₊` to its class routing. -/
def matSp : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, -1]

theorem isUnit_det_matSp : IsUnit matSp.det := by
  rw [Matrix.det_fin_two]
  simp [matSp]

/-- The class loop momenta of `S₊` in terms of the frozen ones: `(ℓ₁ - p', ℓ₀ - ℓ₁ + p' - p)`. -/
def chgSp (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  (fun s => ∑ r, matSp s r • ℓ r) + ![-p', p' - p]

/-- **The frozen routing of `S₊` is the class routing** at the loop momenta `chgSp p p' ℓ`, under
momentum conservation. -/
theorem lineMomentum₂_cSp {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ cSp pOut pIn kIn ℓ =
      classMomE .Sp (pIn 0) (pOut 0) (chgSp (pIn 0) (pOut 0) ℓ) := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (isConserved_classMomE_Sp hmom _) (fun g hg => ?_)
    f).symm
  obtain ⟨c0, c1⟩ := chordMomentum_lineSp ℓ
  obtain ⟨i0, i1, i2, -⟩ := lineIdx_Sp
  rcases (isChord_cSp_iff g).mp hg with rfl | rfl
  · rw [c0, classMomE, i0]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCpSpMomenta, chgSp,
      matSp, Fin.sum_univ_two]
    ring
  · rw [c1, classMomE, i2]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCpSpMomenta, chgSp,
      matSp, Fin.sum_univ_two]

/-- The loop matrix of the frozen routing of `S₊` (rows `v₀v₁, v₁v₂, v₂v₃, v₃v₄`, photons
`0 → 4`, `2 → 3`; columns the chord momenta `ℓ₀`, `ℓ₁`). -/
def frozenLoopMatrixSp : Fin 6 → Fin 2 → ℤ :=
  ![![1, 0], ![1, 0], ![0, 1], ![1, 0], ![-1, 0], ![1, -1]]

/-- The external momenta of the frozen routing of `S₊`. -/
def frozenMomentaSp (p k : Fin 4 → ℝ) : Fin 6 → Fin 4 → ℝ := ![0, k, 0, k, p, k]

theorem frozenLoopMatrixSp_eq :
    frozenLoopMatrixSp = fun i s => ∑ r, class5LoopMatrix .Sp i r * matSp r s := by
  decide

/-- **The frozen routing of `S₊` with its loop matrix**: `k_f(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ` with
`α = frozenLoopMatrixSp`, `i = lineIdx f`. -/
theorem lineMomentum₂_cSp_eq_frozen {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line cSp) :
    lineMomentum₂ cSp pOut pIn kIn ℓ f =
      lineMomentum (castLoopMatrix frozenLoopMatrixSp) (frozenMomentaSp (pIn 0) (kIn 0))
        (lineIdx f) ℓ := by
  rw [lineMomentum₂_cSp hmom, classMomE, hmom]
  generalize lineIdx f = i
  funext μ
  fin_cases i <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCpSpMomenta, chgSp,
      matSp, frozenLoopMatrixSp, frozenMomentaSp, Fin.sum_univ_two] <;>
    ring

theorem not_intNoSubdivergence_frozenLoopMatrixSp : ¬ IntNoSubdivergence frozenLoopMatrixSp := by
  decide

theorem intNoSubdivergence_frozenLoopMatrixSp_PV :
    IntNoSubdivergence fun i => frozenLoopMatrixSp (pvLines i) := by
  decide

/-! ### `S₊`: flavorings and the amplitude -/

theorem cSp_orbit : ∀ x : Fin 1 ⊕ FV, ∃ i : Fin 6, (cSp.1.1 ^ (i : ℕ)) x = .inl 0 := by
  decide +kernel

theorem sameCycle_cSp (x : Fin 1 ⊕ FV) : Equiv.Perm.SameCycle cSp.1.1 x (.inl 0) := by
  obtain ⟨i, hi⟩ := cSp_orbit x
  exact ⟨(i : ℕ), by rw [zpow_natCast]; exact hi⟩

/-- `S₊` has no closed fermion loop. -/
theorem isEmpty_closedLoop_Sp : IsEmpty (ClosedLoop cSp) := by
  refine ⟨fun ⟨q, hq⟩ => ?_⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact hq 0 (Quotient.sound (sameCycle_cSp x).symm)

theorem preserves_iff_Sp (φ : Flavoring (gauges 5)) : Preserves cSp φ ↔ φ = zeroFlavoring := by
  refine ⟨fun hφ => Subtype.ext (funext fun t => ?_), fun h => h ▸ preserves_zeroFlavoring⟩
  exact fermionFlavor_eq_of_sameCycle hφ (sameCycle_cSp (.inr t))

open scoped Classical in
/-- The regulated amplitude (T₈) of `S₊` is its amplitude (T₇) at flavour `0`. -/
theorem regulatedAmplitude₂_cSp (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line cSp → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P cSp pIn kIn k αOut βIn μ =
      contractionAmplitude₂ P cSp zeroFlavoring pIn kIn k αOut βIn μ := by
  have hfil : (Finset.univ : Finset (Flavoring (gauges 5))).filter (Preserves cSp) =
      {zeroFlavoring} := Finset.ext fun φ => by simp [preserves_iff_Sp]
  have hw : loopWeight P cSp zeroFlavoring = 1 := by
    have := isEmpty_closedLoop_Sp
    simp [loopWeight]
  rw [regulatedAmplitude₂, hfil, Finset.sum_singleton, hw, Complex.ofReal_one, one_mul]

/-- The denominators of `S₊` in the class routing are the eight Pauli–Villars line denominators. -/
theorem amplitudeDenominator_cSp (P : Params) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    amplitudeDenominator P cSp zeroFlavoring (classMomE .Sp p p' ℓ) =
      ∏ i : Fin 8, (pvDenomE .Sp P p p' i ℓ)⁻¹ := by
  have h : amplitudeDenominator P cSp zeroFlavoring (classMomE .Sp p p' ℓ) =
      (pvDenomE .Sp P p p' 0 ℓ)⁻¹ * (pvDenomE .Sp P p p' 1 ℓ)⁻¹ * (pvDenomE .Sp P p p' 2 ℓ)⁻¹ *
        (pvDenomE .Sp P p p' 3 ℓ)⁻¹ *
          (((pvDenomE .Sp P p p' 4 ℓ)⁻¹ * (pvDenomE .Sp P p p' 6 ℓ)⁻¹) *
            ((pvDenomE .Sp P p p' 5 ℓ)⁻¹ * (pvDenomE .Sp P p p' 7 ℓ)⁻¹)) := by
    rw [amplitudeDenominator, prod_fermionLine_Sp, prod_photonLine_Sp]
    rfl
  rw [h, Fin.prod_univ_eight]
  ring

/-- **The integrand of `S₊` in parametric form**: for `ε ≠ 0`, the regulated amplitude (T₈) in
the class routing is the numerator times the eight Pauli–Villars line denominators. -/
theorem regulatedAmplitude₂_classMomE_Sp (P : Params) (hε : P.ε ≠ 0)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cSp pIn kIn (classMomE .Sp (pIn 0) (pOut 0) ℓ) αOut βIn μ =
      classNumeratorE .Sp P pOut pIn kIn αOut βIn μ ℓ *
        ∏ i : Fin 8, (pvDenomE .Sp P (pIn 0) (pOut 0) i ℓ)⁻¹ := by
  rw [regulatedAmplitude₂_cSp, contractionAmplitude₂_eq P hε, amplitudeDenominator_cSp]
  rfl

/-- **The value of `S₊` in parametric form.** For `ε ≠ 0` and under momentum conservation, the
value (T₁₀) of the class is the joint energy-first integral of `(2π)⁻⁸` times the class numerator
times the product of the eight Pauli–Villars line denominators for the loop matrix
`class5LoopMatrixPV .Sp`. No integrability is needed. -/
theorem contractionValue₂_Sp_eq (P : Params) (hε : P.ε ≠ 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.Sp.rep pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          (classNumeratorE .Sp P pOut pIn kIn αOut βIn μ ℓ *
            ∏ i : Fin 8, (pvDenomE .Sp P (pIn 0) (pOut 0) i ℓ)⁻¹) := by
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .Sp)]
  simp only [lineMomentum₂_cSp hmom]
  have h := JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
    (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cSp pIn kIn (classMomE .Sp (pIn 0) (pOut 0) ℓ) αOut βIn μ)
    matSp isUnit_det_matSp ![-(pOut 0), pOut 0 - pIn 0]
  refine h.trans ?_
  refine congrArg (QED.TwoLoop.jointEnergyFirstIntegral 2) (funext fun ℓ => ?_)
  rw [regulatedAmplitude₂_classMomE_Sp P hε]

/-- The numerator of `S₊` is a polynomial of total degree at most `4` in the loop momenta. -/
theorem isLoopPoly_classNumeratorE_Sp (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 (classNumeratorE .Sp P pOut pIn kIn αOut βIn μ) := by
  have h := isLoopPoly_amplitudeNumerator P cSp zeroFlavoring pIn kIn
    (classMomE .Sp (pIn 0) (pOut 0)) (fun f => isLoopAffine_lineMomentum _ _ _) αOut βIn μ
  rwa [card_fermionLine_Sp] at h

/-- The integrand of `S₊` at the frozen routing, in the frozen loop momenta. -/
theorem regulatedAmplitude₂_lineMomentum₂_Sp (P : Params) (hε : P.ε ≠ 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cSp pIn kIn (lineMomentum₂ cSp pOut pIn kIn ℓ) αOut βIn μ =
      classNumeratorE .Sp P pOut pIn kIn αOut βIn μ (chgSp (pIn 0) (pOut 0) ℓ) *
        ∏ i : Fin 8, (pvDenomE .Sp P (pIn 0) (pOut 0) i (chgSp (pIn 0) (pOut 0) ℓ))⁻¹ := by
  rw [lineMomentum₂_cSp hmom, regulatedAmplitude₂_classMomE_Sp P hε]

/-- The numerator of `S₊` in the frozen loop momenta also has total degree at most `4`. -/
theorem isLoopPoly_classNumeratorE_Sp_frozen (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 fun ℓ =>
      classNumeratorE .Sp P pOut pIn kIn αOut βIn μ (chgSp (pIn 0) (pOut 0) ℓ) :=
  (isLoopPoly_classNumeratorE_Sp P pOut pIn kIn αOut βIn μ).comp_intAffine matSp _

/-! ### `S₋`: lines -/

/-- The representative of the class `S₋`. -/
abbrev cSm : Contraction 1 1 (gauges 5) := Class5.Sm.rep

/-- The fermion lines of `S₋`, by head `1, 2, 3, 4` (tails `0, 1, 2, 3`). -/
def lineSm : Fin 4 → FermionLine cSm :=
  ![⟨fv5 1, by decide +kernel⟩, ⟨fv5 2, by decide +kernel⟩, ⟨fv5 3, by decide +kernel⟩,
    ⟨fv5 4, by decide +kernel⟩]

/-- The photon lines `0 → 4` and `1 → 2` of `S₋`, indexed by the fields of `0` and `1`. -/
def photSm : Fin 2 → PhotonLine cSm :=
  ![⟨ps5 0, by decide +kernel⟩, ⟨ps5 1, by decide +kernel⟩]

theorem lineSm_bijective : Function.Bijective lineSm := by decide +kernel

theorem photSm_bijective : Function.Bijective photSm := by decide +kernel

theorem ends_lineSm : (Line.ends (.inl (lineSm 0) : Line cSm)) = (0, 1) ∧
    (Line.ends (.inl (lineSm 1) : Line cSm)) = (1, 2) ∧
    (Line.ends (.inl (lineSm 2) : Line cSm)) = (2, 3) ∧
    (Line.ends (.inl (lineSm 3) : Line cSm)) = (3, 4) := by decide +kernel

theorem ends_photSm : (Line.ends (.inr (photSm 0) : Line cSm)) = (0, 4) ∧
    (Line.ends (.inr (photSm 1) : Line cSm)) = (1, 2) := by decide +kernel

theorem prod_fermionLine_Sm {M : Type*} [CommMonoid M] [Fintype (FermionLine cSm)]
    (g : FermionLine cSm → M) :
    ∏ f, g f = g (lineSm 0) * g (lineSm 1) * g (lineSm 2) * g (lineSm 3) := by
  rw [← (Equiv.ofBijective _ lineSm_bijective).prod_comp, Fin.prod_univ_four]
  rfl

theorem prod_photonLine_Sm {M : Type*} [CommMonoid M] [Fintype (PhotonLine cSm)]
    (g : PhotonLine cSm → M) : ∏ f, g f = g (photSm 0) * g (photSm 1) := by
  rw [← (Equiv.ofBijective _ photSm_bijective).prod_comp, Fin.prod_univ_two]
  rfl

theorem sum_line_Sm {M : Type*} [AddCommMonoid M] [Fintype (FermionLine cSm)]
    [Fintype (PhotonLine cSm)] (g : Line cSm → M) :
    ∑ f, g f = g (.inl (lineSm 0)) + g (.inl (lineSm 1)) + g (.inl (lineSm 2)) +
      g (.inl (lineSm 3)) + (g (.inr (photSm 0)) + g (.inr (photSm 1))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ lineSm_bijective).sum_comp,
    ← (Equiv.ofBijective _ photSm_bijective).sum_comp, Fin.sum_univ_four, Fin.sum_univ_two]
  rfl

theorem card_fermionLine_Sm [Fintype (FermionLine cSm)] : Fintype.card (FermionLine cSm) = 4 := by
  rw [← Fintype.card_of_bijective lineSm_bijective, Fintype.card_fin]

theorem lineIdx_Sm : lineIdx (.inl (lineSm 0) : Line cSm) = 0 ∧
    lineIdx (.inl (lineSm 1) : Line cSm) = 1 ∧
    lineIdx (.inl (lineSm 2) : Line cSm) = 2 ∧ lineIdx (.inl (lineSm 3) : Line cSm) = 3 ∧
    lineIdx (.inr (photSm 0) : Line cSm) = 4 ∧ lineIdx (.inr (photSm 1) : Line cSm) = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### `S₋`: external momenta and the class routing -/

theorem extPsi_iff_Sm (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cSm.1.1 (.inr t) = .inl 0) ↔ v = 0 := by
  revert v
  decide +kernel

theorem extA_iff_Sm (v : Fin 5) :
    (∃ a : PS, a.1 = v ∧ cSm.1.2 (.inl 0) = .inr a) ↔ v = 3 := by
  revert v
  decide +kernel

theorem extPsiBar_iff_Sm (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cSm.1.1 (.inl 0) = .inr t) ↔ v = 4 := by
  revert v
  decide +kernel

/-- The external momenta (X₁₉) of `S₋`: `pIn` flows in at `0`, `kIn` at `3`, `pOut` out at `4`. -/
theorem externalMomentum_cSm (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cSm pOut pIn kIn v =
      (if v = 0 then pIn 0 else 0) + (if v = 3 then kIn 0 else 0) -
        (if v = 4 then pOut 0 else 0) := by
  unfold externalMomentum
  simp only [Fin.sum_univ_one, extPsi_iff_Sm, extA_iff_Sm, extPsiBar_iff_Sm]

/-- The class routing of `S₋` is conserved at every vertex, for all loop momenta, under momentum
conservation. -/
theorem isConserved_classMomE_Sm {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved cSm pOut pIn kIn (classMomE .Sm (pIn 0) (pOut 0) ℓ) := by
  obtain ⟨e0, e1, e2, e3⟩ := ends_lineSm
  obtain ⟨g0, g1⟩ := ends_photSm
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := lineIdx_Sm
  intro v
  rw [inflow, sum_line_Sm, externalMomentum_cSm, hmom]
  simp only [classMomE, e0, e1, e2, e3, g0, g1, i0, i1, i2, i3, i4, i5]
  funext μ
  fin_cases v <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCmSmMomenta,
      Fin.sum_univ_two]
  ring

/-! ### `S₋`: chords and the frozen routing -/

theorem isChord_cSm_iff :
    ∀ f : Line cSm, IsChord f ↔ f = .inl (lineSm 0) ∨ f = .inl (lineSm 1) := by
  decide +kernel

open scoped Classical in
theorem card_chordsBelow_Sm : (Finset.univ.filter fun g : Line cSm =>
      IsChord g ∧ g.label < (Line.label (.inl (lineSm 0) : Line cSm))).card = 0 ∧
    (Finset.univ.filter fun g : Line cSm =>
      IsChord g ∧ g.label < (Line.label (.inl (lineSm 1) : Line cSm))).card = 1 := by
  have l0 : (Line.label (.inl (lineSm 0) : Line cSm)) = 1 := rfl
  have l1 : (Line.label (.inl (lineSm 1) : Line cSm)) = 2 := rfl
  constructor
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (isChord_cSm_iff g).mp hg with rfl | rfl
    · simp [l0] at hl
    · simp [l0, l1] at hl
  · rw [Finset.card_eq_one]
    refine ⟨.inl (lineSm 0), Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (isChord_cSm_iff g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(isChord_cSm_iff _).mpr (Or.inl rfl), by simp [l0, l1]⟩

theorem chordMomentum_lineSm (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (lineSm 0) : Line cSm) = ℓ 0 ∧
      chordMomentum ℓ (.inl (lineSm 1) : Line cSm) = ℓ 1 := by
  classical
  obtain ⟨h0, h1⟩ := card_chordsBelow_Sm
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

/-- The unimodular change of loop momenta from the frozen routing of `S₋` to its class routing. -/
def matSm : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, -1]

theorem isUnit_det_matSm : IsUnit matSm.det := by
  rw [Matrix.det_fin_two]
  simp [matSm]

/-- The class loop momenta of `S₋` in terms of the frozen ones: `(ℓ₀ - p, ℓ₀ - ℓ₁)`. -/
def chgSm (p _p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  (fun s => ∑ r, matSm s r • ℓ r) + ![-p, 0]

/-- **The frozen routing of `S₋` is the class routing** at the loop momenta `chgSm p p' ℓ`, under
momentum conservation. -/
theorem lineMomentum₂_cSm {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ cSm pOut pIn kIn ℓ =
      classMomE .Sm (pIn 0) (pOut 0) (chgSm (pIn 0) (pOut 0) ℓ) := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (isConserved_classMomE_Sm hmom _) (fun g hg => ?_)
    f).symm
  obtain ⟨c0, c1⟩ := chordMomentum_lineSm ℓ
  obtain ⟨i0, i1, i2, -⟩ := lineIdx_Sm
  rcases (isChord_cSm_iff g).mp hg with rfl | rfl
  · rw [c0, classMomE, i0]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCmSmMomenta, chgSm,
      matSm, Fin.sum_univ_two]
  · rw [c1, classMomE, i1]
    funext μ
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCmSmMomenta, chgSm,
      matSm, Fin.sum_univ_two]
    ring

/-- The loop matrix of the frozen routing of `S₋` (rows `v₀v₁, v₁v₂, v₂v₃, v₃v₄`, photons
`0 → 4`, `1 → 2`; columns the chord momenta `ℓ₀`, `ℓ₁`). -/
def frozenLoopMatrixSm : Fin 6 → Fin 2 → ℤ :=
  ![![1, 0], ![0, 1], ![1, 0], ![1, 0], ![-1, 0], ![1, -1]]

/-- The external momenta of the frozen routing of `S₋`. -/
def frozenMomentaSm (p k : Fin 4 → ℝ) : Fin 6 → Fin 4 → ℝ := ![0, 0, 0, k, p, 0]

theorem frozenLoopMatrixSm_eq :
    frozenLoopMatrixSm = fun i s => ∑ r, class5LoopMatrix .Sm i r * matSm r s := by
  decide

/-- **The frozen routing of `S₋` with its loop matrix**: `k_f(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ` with
`α = frozenLoopMatrixSm`, `i = lineIdx f`. -/
theorem lineMomentum₂_cSm_eq_frozen {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line cSm) :
    lineMomentum₂ cSm pOut pIn kIn ℓ f =
      lineMomentum (castLoopMatrix frozenLoopMatrixSm) (frozenMomentaSm (pIn 0) (kIn 0))
        (lineIdx f) ℓ := by
  rw [lineMomentum₂_cSm hmom, classMomE, hmom]
  generalize lineIdx f = i
  funext μ
  fin_cases i <;>
    simp [lineMomentum, castLoopMatrix, class5LoopMatrix, extMomenta, classCmSmMomenta, chgSm,
      matSm, frozenLoopMatrixSm, frozenMomentaSm, Fin.sum_univ_two] <;>
    ring

theorem not_intNoSubdivergence_frozenLoopMatrixSm : ¬ IntNoSubdivergence frozenLoopMatrixSm := by
  decide

theorem intNoSubdivergence_frozenLoopMatrixSm_PV :
    IntNoSubdivergence fun i => frozenLoopMatrixSm (pvLines i) := by
  decide

/-! ### `S₋`: flavorings and the amplitude -/

theorem cSm_orbit : ∀ x : Fin 1 ⊕ FV, ∃ i : Fin 6, (cSm.1.1 ^ (i : ℕ)) x = .inl 0 := by
  decide +kernel

theorem sameCycle_cSm (x : Fin 1 ⊕ FV) : Equiv.Perm.SameCycle cSm.1.1 x (.inl 0) := by
  obtain ⟨i, hi⟩ := cSm_orbit x
  exact ⟨(i : ℕ), by rw [zpow_natCast]; exact hi⟩

/-- `S₋` has no closed fermion loop. -/
theorem isEmpty_closedLoop_Sm : IsEmpty (ClosedLoop cSm) := by
  refine ⟨fun ⟨q, hq⟩ => ?_⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact hq 0 (Quotient.sound (sameCycle_cSm x).symm)

theorem preserves_iff_Sm (φ : Flavoring (gauges 5)) : Preserves cSm φ ↔ φ = zeroFlavoring := by
  refine ⟨fun hφ => Subtype.ext (funext fun t => ?_), fun h => h ▸ preserves_zeroFlavoring⟩
  exact fermionFlavor_eq_of_sameCycle hφ (sameCycle_cSm (.inr t))

open scoped Classical in
/-- The regulated amplitude (T₈) of `S₋` is its amplitude (T₇) at flavour `0`. -/
theorem regulatedAmplitude₂_cSm (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line cSm → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P cSm pIn kIn k αOut βIn μ =
      contractionAmplitude₂ P cSm zeroFlavoring pIn kIn k αOut βIn μ := by
  have hfil : (Finset.univ : Finset (Flavoring (gauges 5))).filter (Preserves cSm) =
      {zeroFlavoring} := Finset.ext fun φ => by simp [preserves_iff_Sm]
  have hw : loopWeight P cSm zeroFlavoring = 1 := by
    have := isEmpty_closedLoop_Sm
    simp [loopWeight]
  rw [regulatedAmplitude₂, hfil, Finset.sum_singleton, hw, Complex.ofReal_one, one_mul]

/-- The denominators of `S₋` in the class routing are the eight Pauli–Villars line denominators. -/
theorem amplitudeDenominator_cSm (P : Params) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    amplitudeDenominator P cSm zeroFlavoring (classMomE .Sm p p' ℓ) =
      ∏ i : Fin 8, (pvDenomE .Sm P p p' i ℓ)⁻¹ := by
  have h : amplitudeDenominator P cSm zeroFlavoring (classMomE .Sm p p' ℓ) =
      (pvDenomE .Sm P p p' 0 ℓ)⁻¹ * (pvDenomE .Sm P p p' 1 ℓ)⁻¹ * (pvDenomE .Sm P p p' 2 ℓ)⁻¹ *
        (pvDenomE .Sm P p p' 3 ℓ)⁻¹ *
          (((pvDenomE .Sm P p p' 4 ℓ)⁻¹ * (pvDenomE .Sm P p p' 6 ℓ)⁻¹) *
            ((pvDenomE .Sm P p p' 5 ℓ)⁻¹ * (pvDenomE .Sm P p p' 7 ℓ)⁻¹)) := by
    rw [amplitudeDenominator, prod_fermionLine_Sm, prod_photonLine_Sm]
    rfl
  rw [h, Fin.prod_univ_eight]
  ring

/-- **The integrand of `S₋` in parametric form**: for `ε ≠ 0`, the regulated amplitude (T₈) in
the class routing is the numerator times the eight Pauli–Villars line denominators. -/
theorem regulatedAmplitude₂_classMomE_Sm (P : Params) (hε : P.ε ≠ 0)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cSm pIn kIn (classMomE .Sm (pIn 0) (pOut 0) ℓ) αOut βIn μ =
      classNumeratorE .Sm P pOut pIn kIn αOut βIn μ ℓ *
        ∏ i : Fin 8, (pvDenomE .Sm P (pIn 0) (pOut 0) i ℓ)⁻¹ := by
  rw [regulatedAmplitude₂_cSm, contractionAmplitude₂_eq P hε, amplitudeDenominator_cSm]
  rfl

/-- **The value of `S₋` in parametric form.** For `ε ≠ 0` and under momentum conservation, the
value (T₁₀) of the class is the joint energy-first integral of `(2π)⁻⁸` times the class numerator
times the product of the eight Pauli–Villars line denominators for the loop matrix
`class5LoopMatrixPV .Sm`. No integrability is needed. -/
theorem contractionValue₂_Sm_eq (P : Params) (hε : P.ε ≠ 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.Sm.rep pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
        (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          (classNumeratorE .Sm P pOut pIn kIn αOut βIn μ ℓ *
            ∏ i : Fin 8, (pvDenomE .Sm P (pIn 0) (pOut 0) i ℓ)⁻¹) := by
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .Sm)]
  simp only [lineMomentum₂_cSm hmom]
  have h := JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
    (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cSm pIn kIn (classMomE .Sm (pIn 0) (pOut 0) ℓ) αOut βIn μ)
    matSm isUnit_det_matSm ![-(pIn 0), 0]
  refine h.trans ?_
  refine congrArg (QED.TwoLoop.jointEnergyFirstIntegral 2) (funext fun ℓ => ?_)
  rw [regulatedAmplitude₂_classMomE_Sm P hε]

/-- The numerator of `S₋` is a polynomial of total degree at most `4` in the loop momenta. -/
theorem isLoopPoly_classNumeratorE_Sm (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 (classNumeratorE .Sm P pOut pIn kIn αOut βIn μ) := by
  have h := isLoopPoly_amplitudeNumerator P cSm zeroFlavoring pIn kIn
    (classMomE .Sm (pIn 0) (pOut 0)) (fun f => isLoopAffine_lineMomentum _ _ _) αOut βIn μ
  rwa [card_fermionLine_Sm] at h

/-- The integrand of `S₋` at the frozen routing, in the frozen loop momenta. -/
theorem regulatedAmplitude₂_lineMomentum₂_Sm (P : Params) (hε : P.ε ≠ 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    regulatedAmplitude₂ P cSm pIn kIn (lineMomentum₂ cSm pOut pIn kIn ℓ) αOut βIn μ =
      classNumeratorE .Sm P pOut pIn kIn αOut βIn μ (chgSm (pIn 0) (pOut 0) ℓ) *
        ∏ i : Fin 8, (pvDenomE .Sm P (pIn 0) (pOut 0) i (chgSm (pIn 0) (pOut 0) ℓ))⁻¹ := by
  rw [lineMomentum₂_cSm hmom, regulatedAmplitude₂_classMomE_Sm P hε]

/-- The numerator of `S₋` in the frozen loop momenta also has total degree at most `4`. -/
theorem isLoopPoly_classNumeratorE_Sm_frozen (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    IsLoopPoly 2 4 fun ℓ =>
      classNumeratorE .Sm P pOut pIn kIn αOut βIn μ (chgSm (pIn 0) (pOut 0) ℓ) :=
  (isLoopPoly_classNumeratorE_Sm P pOut pIn kIn αOut βIn μ).comp_intAffine matSm _


/-! ### Summary for `S₊`, `S₋` and the open-line classes -/

theorem noSubdivergence_frozenLoopMatrixSp_PV :
    NoSubdivergence (castLoopMatrix fun i => frozenLoopMatrixSp (pvLines i)) :=
  (QED.Integration.TwoLoop.noSubdivergence_castLoopMatrix_iff _).mpr
    intNoSubdivergence_frozenLoopMatrixSp_PV

theorem noSubdivergence_frozenLoopMatrixSm_PV :
    NoSubdivergence (castLoopMatrix fun i => frozenLoopMatrixSm (pvLines i)) :=
  (QED.Integration.TwoLoop.noSubdivergence_castLoopMatrix_iff _).mpr
    intNoSubdivergence_frozenLoopMatrixSm_PV

/-- **Parametric form of `S₊` and `S₋`.** For `ε ≠ 0` and under momentum conservation, the value
(T₁₀) is the joint energy-first integral of `(2π)⁻⁸ N(ℓ) ∏ᵢ₌₀⁷ Dᵢ(ℓ)⁻¹` with `N` a polynomial of
total degree at most `4` in the loop momenta and `Dᵢ` the line denominators of the Pauli–Villars
form of the class (both photons, in particular the subloop photon, combined), whose loop matrix
`class5LoopMatrixPV c` satisfies the no-subdivergence criterion. -/
theorem parametricForm_S {c : Class5} (hc : c = .Sp ∨ c = .Sm) (P : Params) (hε : P.ε ≠ 0)
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
  · exact ⟨contractionValue₂_Sp_eq P hε hmom αOut βIn μ,
      isLoopPoly_classNumeratorE_Sp P pOut pIn kIn αOut βIn μ,
      QED.Integration.TwoLoop.noSubdivergence_loopMatrixPV (by decide)⟩
  · exact ⟨contractionValue₂_Sm_eq P hε hmom αOut βIn μ,
      isLoopPoly_classNumeratorE_Sm P pOut pIn kIn αOut βIn μ,
      QED.Integration.TwoLoop.noSubdivergence_loopMatrixPV (by decide)⟩

/-- **Parametric form of the six open-line classes** `L`, `X`, `C₊`, `C₋`, `S₊`, `S₋`, in the
common notation `classNumeratorE`, `pvDenomE`. -/
theorem parametricForm_open {c : Class5}
    (hc : c ∈ ({.L, .X, .Cp, .Cm, .Sp, .Sm} : Finset Class5)) (P : Params) (hε : P.ε ≠ 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ =
        QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ =>
          (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
            (classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ *
              ∏ i : Fin 8, (pvDenomE c P (pIn 0) (pOut 0) i ℓ)⁻¹)) ∧
      IsLoopPoly 2 4 (classNumeratorE c P pOut pIn kIn αOut βIn μ) ∧
      NoSubdivergence (castLoopMatrix (class5LoopMatrixPV c)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact parametricForm_LX (Or.inl rfl) P hε hmom αOut βIn μ
  · exact parametricForm_LX (Or.inr rfl) P hε hmom αOut βIn μ
  · exact parametricForm_C (Or.inl rfl) P hε hmom αOut βIn μ
  · exact parametricForm_C (Or.inr rfl) P hε hmom αOut βIn μ
  · exact parametricForm_S (Or.inl rfl) P hε hmom αOut βIn μ
  · exact parametricForm_S (Or.inr rfl) P hε hmom αOut βIn μ

end QED.TwoLoop.Bridge

end
