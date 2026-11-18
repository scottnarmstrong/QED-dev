/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.FurryPair
public import QED.TwoLoop.ClassIntegrableVP

/-!
# The Furry triangle `F₊`: frozen routing and flavorings

Part of obligation O2-7 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3), its fixed-`ε` part, for the
class `Fp` of five gauge vertices (`QED.TwoLoop.Enumeration.Class5.Fp`): the open line `0 → 1`,
the closed fermion loop `2 → 3 → 4 → 2`, the external photon at `2` and the internal photons
`(0 3)`, `(1 4)`.

**The frozen routing** (`lineMomentum₂_cP`). The chords (T₁) are the fermion lines `0 → 1`
(`ℓ 0`) and `4 → 2` (`ℓ 1`). Ordering the six lines as `v₀v₁, v₄v₂, v₂v₃, v₃v₄`, then the photons
`0 → 3`, `1 → 4` (`QED.TwoLoop.Bridge.lineIdx`, by label), the frozen routing (T₄) is, under
momentum conservation `p' = p + k` (`p = pIn 0`, `k = kIn 0`):

| line | `v₀v₁` | `v₄v₂` | `v₂v₃` | `v₃v₄` | photon `0 → 3` | photon `1 → 4` |
| --- | --- | --- | --- | --- | --- | --- |
| momentum | `ℓ₀` | `ℓ₁` | `ℓ₁ + k` | `ℓ₁ - ℓ₀ + p + k` | `p - ℓ₀` | `ℓ₀ - p - k` |

that is, the loop matrix `furryMatrix` and the external momenta `furryMomenta p k`.

**The flavorings** (`sum_preserves`, `loopWeight_flavF`): the flavorings preserved by `F₊` are
the `flavF f`, `f ∈ {0, 1, 2}`, with the open line of flavour `0` and the loop of flavour `f`; the
regulator weight (X₇) of `flavF f` is `c_f`.
-/

@[expose] public section

namespace QED.TwoLoop.FurryIntegrable

open Complex QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Relabel
open QED.TwoLoop.Furry (cP lineP lineP_bijective tail_lineP val_lineP cP_pow_three
  sameCycle_iff_of_pow_three)
open QED.TwoLoop.Bridge (lineIdx)
open QED.Integration.TwoLoop (lineMomentum castLoopMatrix)

/-- The fermion fields of the five gauge vertices. -/
local notation "FV" => Wick.FermionVertex (gauges 5)

/-- The photon fields of the five gauge vertices. -/
local notation "PS" => Wick.PhotonSlot (gauges 5)

/-! ### Lines -/

/-- The photon lines `0 → 3` and `1 → 4` of `F₊`, indexed by the fields of `0` and `1`. -/
def photP : Fin 2 → PhotonLine cP :=
  ![⟨ps5 0, by decide +kernel⟩, ⟨ps5 1, by decide +kernel⟩]

theorem photP_bijective : Function.Bijective photP := by decide +kernel

theorem ends_lineP : (Line.ends (.inl (lineP 0) : Line cP)) = (0, 1) ∧
    (Line.ends (.inl (lineP 1) : Line cP)) = (4, 2) ∧
    (Line.ends (.inl (lineP 2) : Line cP)) = (2, 3) ∧
    (Line.ends (.inl (lineP 3) : Line cP)) = (3, 4) := by decide +kernel

theorem ends_photP : (Line.ends (.inr (photP 0) : Line cP)) = (0, 3) ∧
    (Line.ends (.inr (photP 1) : Line cP)) = (1, 4) := by decide +kernel

theorem prod_photonLine {M : Type*} [CommMonoid M] [Fintype (PhotonLine cP)]
    (g : PhotonLine cP → M) : ∏ f, g f = g (photP 0) * g (photP 1) := by
  rw [← (Equiv.ofBijective _ photP_bijective).prod_comp, Fin.prod_univ_two]
  rfl

theorem sum_line {M : Type*} [AddCommMonoid M] [Fintype (FermionLine cP)]
    [Fintype (PhotonLine cP)] (g : Line cP → M) :
    ∑ f, g f = g (.inl (lineP 0)) + g (.inl (lineP 1)) + g (.inl (lineP 2)) +
      g (.inl (lineP 3)) + (g (.inr (photP 0)) + g (.inr (photP 1))) := by
  rw [Fintype.sum_sum_type, ← (Equiv.ofBijective _ lineP_bijective).sum_comp,
    ← (Equiv.ofBijective _ photP_bijective).sum_comp, Fin.sum_univ_four, Fin.sum_univ_two]
  rfl

theorem card_fermionLine [Fintype (FermionLine cP)] : Fintype.card (FermionLine cP) = 4 := by
  rw [← Fintype.card_of_bijective lineP_bijective, Fintype.card_fin]

theorem lineIdx_P : lineIdx (.inl (lineP 0) : Line cP) = 0 ∧
    lineIdx (.inl (lineP 1) : Line cP) = 1 ∧
    lineIdx (.inl (lineP 2) : Line cP) = 2 ∧ lineIdx (.inl (lineP 3) : Line cP) = 3 ∧
    lineIdx (.inr (photP 0) : Line cP) = 4 ∧ lineIdx (.inr (photP 1) : Line cP) = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fermion lines of `F₊` are the lines `0, 1, 2, 3`, each once. -/
theorem lineIdx_fermion_injective :
    Function.Injective (fun f : FermionLine cP => lineIdx (.inl f : Line cP)) := by
  decide +kernel

theorem lineIdx_fermion_lt : ∀ f : FermionLine cP, (lineIdx (.inl f : Line cP) : ℕ) < 4 := by
  decide +kernel

/-! ### External momenta and the frozen routing -/

theorem extPsi_iff (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cP.1.1 (.inr t) = .inl 0) ↔ v = 0 := by
  revert v
  decide +kernel

theorem extA_iff (v : Fin 5) :
    (∃ a : PS, a.1 = v ∧ cP.1.2 (.inl 0) = .inr a) ↔ v = 2 := by
  revert v
  decide +kernel

theorem extPsiBar_iff (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cP.1.1 (.inl 0) = .inr t) ↔ v = 1 := by
  revert v
  decide +kernel

/-- The external momenta (X₁₉) of `F₊`: `pIn` flows in at `0`, `kIn` at `2`, `pOut` out at `1`. -/
theorem externalMomentum_cP (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cP pOut pIn kIn v =
      (if v = 0 then pIn 0 else 0) + (if v = 2 then kIn 0 else 0) -
        (if v = 1 then pOut 0 else 0) := by
  unfold externalMomentum
  simp only [Fin.sum_univ_one, extPsi_iff, extA_iff, extPsiBar_iff]

/-- The loop matrix of the frozen routing of `F₊` (rows `v₀v₁, v₄v₂, v₂v₃, v₃v₄`, photons
`0 → 3`, `1 → 4`; columns the chord momenta `ℓ₀`, `ℓ₁`). -/
def furryMatrix : Fin 6 → Fin 2 → ℤ :=
  ![![1, 0], ![0, 1], ![0, 1], ![-1, 1], ![-1, 0], ![1, 0]]

/-- The external momenta of the frozen routing of `F₊`. -/
def furryMomenta (p k : Fin 4 → ℝ) : Fin 6 → Fin 4 → ℝ := ![0, 0, k, p + k, p, -(p + k)]

/-- The momentum of line `j` of `F₊` in the frozen routing. -/
def baseMom (p k : Fin 4 → ℝ) (j : Fin 6) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix furryMatrix) (furryMomenta p k) j ℓ

/-- The frozen routing of `F₊` is conserved at every vertex, under momentum conservation. -/
theorem isConserved_baseMom {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (ℓ : Fin 2 → Fin 4 → ℝ) :
    IsConserved cP pOut pIn kIn (fun f => baseMom (pIn 0) (kIn 0) (lineIdx f) ℓ) := by
  obtain ⟨e0, e1, e2, e3⟩ := ends_lineP
  obtain ⟨g0, g1⟩ := ends_photP
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := lineIdx_P
  intro v
  rw [inflow, sum_line, externalMomentum_cP, hmom]
  simp only [baseMom, e0, e1, e2, e3, g0, g1, i0, i1, i2, i3, i4, i5]
  funext μ
  fin_cases v <;>
    simp [QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, furryMatrix, furryMomenta,
      Fin.sum_univ_two] <;>
    ring

theorem isChord_cP_iff : ∀ f : Line cP, IsChord f ↔ f = .inl (lineP 0) ∨ f = .inl (lineP 1) := by
  decide +kernel

open scoped Classical in
theorem card_chordsBelow : (Finset.univ.filter fun g : Line cP =>
      IsChord g ∧ g.label < (Line.label (.inl (lineP 0) : Line cP))).card = 0 ∧
    (Finset.univ.filter fun g : Line cP =>
      IsChord g ∧ g.label < (Line.label (.inl (lineP 1) : Line cP))).card = 1 := by
  have l0 : (Line.label (.inl (lineP 0) : Line cP)) = 1 := rfl
  have l1 : (Line.label (.inl (lineP 1) : Line cP)) = 2 := rfl
  constructor
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (isChord_cP_iff g).mp hg with rfl | rfl
    · simp [l0] at hl
    · simp [l0, l1] at hl
  · rw [Finset.card_eq_one]
    refine ⟨.inl (lineP 0), Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (isChord_cP_iff g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(isChord_cP_iff _).mpr (Or.inl rfl), by simp [l0, l1]⟩

theorem chordMomentum_lineP (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (lineP 0) : Line cP) = ℓ 0 ∧
      chordMomentum ℓ (.inl (lineP 1) : Line cP) = ℓ 1 := by
  classical
  obtain ⟨h0, h1⟩ := card_chordsBelow
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

/-- **The frozen routing of `F₊`**: under momentum conservation, the momentum of line `f` is
`∑ₛ αᵢₛ ℓₛ + pᵢ` with `α = furryMatrix`, `p = furryMomenta (pIn 0) (kIn 0)`, `i = lineIdx f`. -/
theorem lineMomentum₂_cP {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) (f : Line cP) :
    lineMomentum₂ cP pOut pIn kIn ℓ f = baseMom (pIn 0) (kIn 0) (lineIdx f) ℓ := by
  refine (eq_lineMomentum₂_of_isConserved (isConserved_baseMom hmom ℓ) (fun g hg => ?_) f).symm
  obtain ⟨c0, c1⟩ := chordMomentum_lineP ℓ
  obtain ⟨i0, i1, -⟩ := lineIdx_P
  rcases (isChord_cP_iff g).mp hg with rfl | rfl
  · rw [c0, i0]
    funext μ
    simp [baseMom, QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, furryMatrix,
      furryMomenta, Fin.sum_univ_two]
  · rw [c1, i1]
    funext μ
    simp [baseMom, QED.Integration.TwoLoop.lineMomentum, castLoopMatrix, furryMatrix,
      furryMomenta, Fin.sum_univ_two]

/-! ### Flavorings -/

/-- The flavoring with the open line of flavour `0` and the loop `2, 3, 4` of flavour `f`. -/
def flavF (f : Fin 3) : Flavoring (gauges 5) :=
  ⟨fun t => if 2 ≤ t.1.val then f else 0, fun _ h => absurd rfl h⟩

theorem flavF_apply (f : Fin 3) : (flavF f).1 (fv5 0) = 0 ∧ (flavF f).1 (fv5 1) = 0 ∧
    (flavF f).1 (fv5 2) = f ∧ (flavF f).1 (fv5 3) = f ∧ (flavF f).1 (fv5 4) = f := by
  simp [flavF, fv5]

theorem preserves_flavF : ∀ f : Fin 3, Preserves cP (flavF f) := by
  unfold Preserves
  decide +kernel

theorem fermionPerm_cP : cP.1.1 (.inr (fv5 0)) = .inl 0 ∧ cP.1.1 (.inr (fv5 1)) = .inr (fv5 0) ∧
    cP.1.1 (.inl 0) = .inr (fv5 1) ∧ cP.1.1 (.inr (fv5 2)) = .inr (fv5 4) ∧
    cP.1.1 (.inr (fv5 3)) = .inr (fv5 2) ∧ cP.1.1 (.inr (fv5 4)) = .inr (fv5 3) := by
  decide +kernel

/-- **The preserved flavorings**: the open line has flavour `0`, the loop one flavour. -/
theorem preserves_iff (φ : Flavoring (gauges 5)) :
    Preserves cP φ ↔ φ = flavF (φ.1 (fv5 2)) := by
  refine ⟨fun hφ => ?_, fun h => h ▸ preserves_flavF _⟩
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := fermionPerm_cP
  have h0 := hφ (.inr (fv5 0))
  have h1 := hφ (.inr (fv5 1))
  have h3 := hφ (.inr (fv5 3))
  have h4 := hφ (.inr (fv5 4))
  rw [s0] at h0
  rw [s1] at h1
  rw [s4] at h3
  rw [s5] at h4
  simp only [fermionFlavor] at h0 h1 h3 h4
  apply Subtype.ext
  funext t
  obtain ⟨j, hj⟩ := t
  change φ.1 (fv5 j) = (flavF (φ.1 (fv5 2))).1 (fv5 j)
  fin_cases j
  · exact h0.symm.trans (flavF_apply _).1.symm
  · exact (h1.symm.trans h0.symm).trans (flavF_apply _).2.1.symm
  · exact (flavF_apply _).2.2.1.symm
  · exact h3.symm.trans (flavF_apply _).2.2.2.1.symm
  · exact (h4.symm.trans h3.symm).trans (flavF_apply _).2.2.2.2.symm

/-- **The sum over the preserved flavorings** is the sum over the flavour of the loop. -/
theorem sum_preserves {M : Type*} [AddCommMonoid M] [Fintype (Flavoring (gauges 5))]
    [DecidablePred (Preserves cP)] (F : Flavoring (gauges 5) → M) :
    ∑ φ ∈ (Finset.univ : Finset (Flavoring (gauges 5))).filter (Preserves cP), F φ =
      ∑ f : Fin 3, F (flavF f) :=
  Finset.sum_nbij' (fun φ => φ.1 (fv5 2)) flavF (fun _ _ => Finset.mem_univ _)
    (fun f _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, preserves_flavF f⟩)
    (fun φ hφ => ((preserves_iff φ).mp (Finset.mem_filter.mp hφ).2).symm)
    (fun f _ => (flavF_apply f).2.2.1)
    (fun φ hφ => by rw [← (preserves_iff φ).mp (Finset.mem_filter.mp hφ).2])

theorem not_sameCycle_ext_loop : ¬ Equiv.Perm.SameCycle cP.1.1 (.inl 0) (.inr (fv5 2)) := by
  rw [sameCycle_iff_of_pow_three cP_pow_three]
  decide +kernel

theorem sameCycle_ext_or_loop : ∀ x : Fin 1 ⊕ FV, Equiv.Perm.SameCycle cP.1.1 x (.inl 0) ∨
    Equiv.Perm.SameCycle cP.1.1 x (.inr (fv5 2)) := by
  simp only [sameCycle_iff_of_pow_three cP_pow_three]
  decide +kernel

/-- The closed fermion loop `2 → 3 → 4 → 2`. -/
def loopF : ClosedLoop cP :=
  ⟨Quotient.mk _ (.inr (fv5 2)), fun i h => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact not_sameCycle_ext_loop (Quotient.exact h)⟩

/-- The representative has one closed fermion loop. -/
theorem eq_loopF (q : ClosedLoop cP) : q = loopF := by
  obtain ⟨q, hq⟩ := q
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rcases sameCycle_ext_or_loop x with h | h
  · exact absurd (Quotient.sound h.symm) (hq 0)
  · exact Quotient.sound h

open scoped Classical in
/-- The regulator weight (X₇) of the flavour-`f` loop is `c_f`. -/
theorem loopWeight_flavF (P : Params) (f : Fin 3) : loopWeight P cP (flavF f) = P.loopCoeff f := by
  rw [loopWeight, Fintype.prod_eq_single loopF fun q hq => absurd (eq_loopF q) hq]
  have hq : (Quotient.mk _ loopF.1.out : Quotient (Equiv.Perm.SameCycle.setoid cP.1.1)) =
      Quotient.mk _ (.inr (fv5 2)) := Quotient.out_eq _
  have hsc : Equiv.Perm.SameCycle cP.1.1 loopF.1.out (.inr (fv5 2)) := Quotient.exact hq
  rw [fermionFlavor_eq_of_sameCycle (preserves_flavF f) hsc]
  simp only [fermionFlavor, (flavF_apply f).2.2.1]

end QED.TwoLoop.FurryIntegrable

end
