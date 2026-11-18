/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.EnumerationGauge5
public import QED.TwoLoop.RelabelInvariance

/-!
# The vacuum-polarization class in the nested routing

Part of obligation O2-8 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3) for the class `VP` of five
gauge vertices (`QED.TwoLoop.Enumeration.Class5.VP`). Its representative has the open line
`0 → 1 → 2` (external photon at `1`), the closed loop `3 → 4 → 3`, and the internal photons
`(0 3)` and `(2 4)`.

The frozen routing (T₄) puts the loop momenta on the chords, which are the fermion lines
`0 → 1` (`ℓ 0`) and `4 → 3` (`ℓ 1`). For the nested form we use instead the loop momentum `q` of
the fermion loop and the momentum `k` of the photon line:

| line | `0 → 1` | `1 → 2` | `4 → 3` | `3 → 4` | photon `0 → 3` | photon `2 → 4` |
| --- | --- | --- | --- | --- | --- | --- |
| momentum | `p - k` | `p + k_ext - k` | `q` | `q + k` | `k` | `-k` |

with `p = pIn 0`, `k_ext = kIn 0` (`nestedMom`).

* `QED.TwoLoop.NestedVP.isConserved_nestedMom`: under momentum conservation the nested routing is
  conserved at every vertex.
* `QED.TwoLoop.NestedVP.lineMomentum₂_cV`: the frozen routing at `ℓ` is the nested routing at
  `q = ℓ 1`, `k = p - ℓ 0`, by uniqueness (`QED.TwoLoop.Routing.eq_lineMomentum₂_of_isConserved`).
* `QED.TwoLoop.NestedVP.contractionValue₂_VP_eq_nested`: the value (T₁₀) of the class is the joint
  energy-first integral of the regulated amplitude in the nested routing, with `ℓ 0 = q` and
  `ℓ 1 = k`. The change of loop momenta `ℓ ↦ (ℓ 1, p - ℓ 0)` is integer unimodular, and the joint
  prescription is invariant under it for every integrand
  (`QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add`).
-/

@[expose] public section

namespace QED.TwoLoop.NestedVP

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Relabel

/-- The fermion fields of the five gauge vertices. -/
local notation "FV" => Wick.FermionVertex (gauges 5)

/-- The photon fields of the five gauge vertices. -/
local notation "PS" => Wick.PhotonSlot (gauges 5)

/-- The representative of the vacuum-polarization class. -/
abbrev cV : Contraction 1 1 (gauges 5) := Class5.VP.rep

/-! ### The lines of the representative -/

/-- The fermion lines, by head `1, 2, 3, 4` (tails `0, 1, 4, 3`). -/
def lineV : Fin 4 → FermionLine cV :=
  ![⟨fv5 1, by decide +kernel⟩, ⟨fv5 2, by decide +kernel⟩, ⟨fv5 3, by decide +kernel⟩,
    ⟨fv5 4, by decide +kernel⟩]

/-- The photon lines `0 → 3` and `2 → 4`, indexed by the fields of `0` and `2`. -/
def photV : Fin 2 → PhotonLine cV :=
  ![⟨ps5 0, by decide +kernel⟩, ⟨ps5 2, by decide +kernel⟩]

theorem lineV_bijective : Function.Bijective lineV := by decide +kernel

theorem photV_bijective : Function.Bijective photV := by decide +kernel

theorem val_lineV : (lineV 0).1 = fv5 1 ∧ (lineV 1).1 = fv5 2 ∧ (lineV 2).1 = fv5 3 ∧
    (lineV 3).1 = fv5 4 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem tail_lineV : (lineV 0).tail = fv5 0 ∧ (lineV 1).tail = fv5 1 ∧ (lineV 2).tail = fv5 4 ∧
    (lineV 3).tail = fv5 3 := by decide +kernel

theorem val_photV : (photV 0).1 = ps5 0 ∧ (photV 1).1 = ps5 2 := ⟨rfl, rfl⟩

theorem head_photV : (photV 0).head = ps5 3 ∧ (photV 1).head = ps5 4 := by decide +kernel

theorem ends_lineV : (Line.ends (.inl (lineV 0) : Line cV)) = (0, 1) ∧
    (Line.ends (.inl (lineV 1) : Line cV)) = (1, 2) ∧
    (Line.ends (.inl (lineV 2) : Line cV)) = (4, 3) ∧
    (Line.ends (.inl (lineV 3) : Line cV)) = (3, 4) := by decide +kernel

theorem ends_photV : (Line.ends (.inr (photV 0) : Line cV)) = (0, 3) ∧
    (Line.ends (.inr (photV 1) : Line cV)) = (2, 4) := by decide +kernel

theorem sum_fermionLine {M : Type*} [AddCommMonoid M] [Fintype (FermionLine cV)]
    (g : FermionLine cV → M) :
    ∑ f, g f = g (lineV 0) + g (lineV 1) + g (lineV 2) + g (lineV 3) := by
  rw [← (Equiv.ofBijective _ lineV_bijective).sum_comp, Fin.sum_univ_four]
  rfl

theorem prod_fermionLine {M : Type*} [CommMonoid M] [Fintype (FermionLine cV)]
    (g : FermionLine cV → M) :
    ∏ f, g f = g (lineV 0) * g (lineV 1) * g (lineV 2) * g (lineV 3) := by
  rw [← (Equiv.ofBijective _ lineV_bijective).prod_comp, Fin.prod_univ_four]
  rfl

theorem sum_photonLine {M : Type*} [AddCommMonoid M] [Fintype (PhotonLine cV)]
    (g : PhotonLine cV → M) : ∑ f, g f = g (photV 0) + g (photV 1) := by
  rw [← (Equiv.ofBijective _ photV_bijective).sum_comp, Fin.sum_univ_two]
  rfl

theorem prod_photonLine {M : Type*} [CommMonoid M] [Fintype (PhotonLine cV)]
    (g : PhotonLine cV → M) : ∏ f, g f = g (photV 0) * g (photV 1) := by
  rw [← (Equiv.ofBijective _ photV_bijective).prod_comp, Fin.prod_univ_two]
  rfl

theorem sum_line {M : Type*} [AddCommMonoid M] [Fintype (FermionLine cV)]
    [Fintype (PhotonLine cV)] (g : Line cV → M) :
    ∑ f, g f = g (.inl (lineV 0)) + g (.inl (lineV 1)) + g (.inl (lineV 2)) +
      g (.inl (lineV 3)) + (g (.inr (photV 0)) + g (.inr (photV 1))) := by
  rw [Fintype.sum_sum_type, sum_fermionLine, sum_photonLine]

/-! ### The external momenta -/

theorem extPsi_iff (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cV.1.1 (.inr t) = .inl 0) ↔ v = 0 := by
  revert v
  decide +kernel

theorem extA_iff (v : Fin 5) :
    (∃ a : PS, a.1 = v ∧ cV.1.2 (.inl 0) = .inr a) ↔ v = 1 := by
  revert v
  decide +kernel

theorem extPsiBar_iff (v : Fin 5) :
    (∃ t : FV, t.1 = v ∧ cV.1.1 (.inl 0) = .inr t) ↔ v = 2 := by
  revert v
  decide +kernel

/-- The external momenta (X₁₉) of the representative: `pIn` flows in at `0`, `kIn` at `1`, and
`pOut` flows out at `2`. -/
theorem externalMomentum_cV (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 5) :
    externalMomentum cV pOut pIn kIn v =
      (if v = 0 then pIn 0 else 0) + (if v = 1 then kIn 0 else 0) -
        (if v = 2 then pOut 0 else 0) := by
  unfold externalMomentum
  simp only [Fin.sum_univ_one, extPsi_iff, extA_iff, extPsiBar_iff]

/-! ### The nested routing -/

/-- **The nested routing** of the representative, with loop momentum `q` on the fermion loop and
`k` on the photon line (the table in the module docstring); `p = pIn 0`, `kext = kIn 0`. Lines
are recognized by their labels (X₂₀): `1, 2, 3, 4` for the fermion lines with heads `1, 2, 3, 4`,
`5` and `9` for the photon lines `0 → 3` and `2 → 4`. -/
def nestedMom (p kext q k : Fin 4 → ℝ) (f : Line cV) : Fin 4 → ℝ :=
  match f.label with
  | 1 => p - k
  | 2 => p + kext - k
  | 3 => q
  | 4 => q + k
  | 5 => k
  | _ => -k

theorem nestedMom_apply (p kext q k : Fin 4 → ℝ) :
    nestedMom p kext q k (.inl (lineV 0)) = p - k ∧
      nestedMom p kext q k (.inl (lineV 1)) = p + kext - k ∧
      nestedMom p kext q k (.inl (lineV 2)) = q ∧
      nestedMom p kext q k (.inl (lineV 3)) = q + k ∧
      nestedMom p kext q k (.inr (photV 0)) = k ∧
      nestedMom p kext q k (.inr (photV 1)) = -k :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The nested routing is conserved** at every vertex, under momentum conservation. -/
theorem isConserved_nestedMom {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (q k : Fin 4 → ℝ) :
    IsConserved cV pOut pIn kIn (nestedMom (pIn 0) (kIn 0) q k) := by
  obtain ⟨e0, e1, e2, e3⟩ := ends_lineV
  obtain ⟨g0, g1⟩ := ends_photV
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := nestedMom_apply (pIn 0) (kIn 0) q k
  intro v
  rw [inflow, sum_line, externalMomentum_cV, hmom]
  simp only [e0, e1, e2, e3, g0, g1, n0, n1, n2, n3, n4, n5]
  fin_cases v
  all_goals simp
  all_goals abel

/-! ### The chords -/

theorem isChord_cV_iff : ∀ f : Line cV, IsChord f ↔ f = .inl (lineV 0) ∨ f = .inl (lineV 2) := by
  decide +kernel

theorem label_lineV : (Line.label (.inl (lineV 0) : Line cV)) = 1 ∧
    (Line.label (.inl (lineV 2) : Line cV)) = 3 :=
  ⟨rfl, rfl⟩

open scoped Classical in
/-- The number of chords of label below that of a chord, for the two chords. -/
theorem card_chordsBelow : (Finset.univ.filter fun g : Line cV =>
      IsChord g ∧ g.label < (Line.label (.inl (lineV 0) : Line cV))).card = 0 ∧
    (Finset.univ.filter fun g : Line cV =>
      IsChord g ∧ g.label < (Line.label (.inl (lineV 2) : Line cV))).card = 1 := by
  constructor
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (isChord_cV_iff g).mp hg with rfl | rfl
    · simp [label_lineV.1] at hl
    · simp [label_lineV.1, label_lineV.2] at hl
  · rw [Finset.card_eq_one]
    refine ⟨.inl (lineV 0), Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (isChord_cV_iff g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(isChord_cV_iff _).mpr (Or.inl rfl), by simp [label_lineV.1, label_lineV.2]⟩

theorem chordMomentum_lineV (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (lineV 0) : Line cV) = ℓ 0 ∧
      chordMomentum ℓ (.inl (lineV 2) : Line cV) = ℓ 1 := by
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

/-- **The frozen routing in nested form**: the routing (T₄) of the representative at loop
momenta `ℓ` is the nested routing at `q = ℓ 1`, `k = p - ℓ 0`, under momentum conservation. -/
theorem lineMomentum₂_cV {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ cV pOut pIn kIn ℓ = nestedMom (pIn 0) (kIn 0) (ℓ 1) (pIn 0 - ℓ 0) := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (isConserved_nestedMom hmom _ _) (fun g hg => ?_) f).symm
  obtain ⟨c0, c1⟩ := chordMomentum_lineV ℓ
  obtain ⟨n0, -, n2, -⟩ := nestedMom_apply (pIn 0) (kIn 0) (ℓ 1) (pIn 0 - ℓ 0)
  rcases (isChord_cV_iff g).mp hg with rfl | rfl
  · rw [n0, c0, sub_sub_cancel]
  · rw [n2, c1]

/-! ### The value in the nested routing -/

/-- The integer unimodular change of loop momenta `ℓ ↦ (ℓ 1, -ℓ 0)`. -/
def swapMat : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

theorem isUnit_det_swapMat : IsUnit swapMat.det := by
  rw [Matrix.det_fin_two]
  simp [swapMat]

theorem swapMat_act (ℓ : Fin 2 → Fin 4 → ℝ) (p : Fin 4 → ℝ) :
    ((fun s => ∑ r, swapMat s r • ℓ r) + ![0, p]) 0 = ℓ 1 ∧
      ((fun s => ∑ r, swapMat s r • ℓ r) + ![0, p]) 1 = p - ℓ 0 := by
  simp [swapMat, Fin.sum_univ_two, sub_eq_neg_add]

/-- **The value of the vacuum-polarization class in the nested routing**: under momentum
conservation, the value (T₁₀) is the joint energy-first integral (T₉) of `(2π)⁻⁸` times the
regulated amplitude (T₈) at the nested routing with `q = ℓ 0` on the fermion loop and `k = ℓ 1` on
the photon line. No integrability is needed. -/
theorem contractionValue₂_VP_eq_nested (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P Class5.VP.rep pOut pIn kIn αOut βIn μ =
      jointEnergyFirstIntegral 2 fun ℓ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P cV pIn kIn (nestedMom (pIn 0) (kIn 0) (ℓ 0) (ℓ 1)) αOut βIn μ := by
  rw [contractionValue₂_eq_of_loopCount P (loopCount_rep .VP)]
  simp only [lineMomentum₂_cV hmom]
  have h := JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2
    (fun ℓ : Fin 2 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P cV pIn kIn (nestedMom (pIn 0) (kIn 0) (ℓ 0) (ℓ 1)) αOut βIn μ)
    swapMat isUnit_det_swapMat ![0, pIn 0]
  refine Eq.trans ?_ h
  refine congrArg (jointEnergyFirstIntegral 2) (funext fun ℓ => ?_)
  obtain ⟨h0, h1⟩ := swapMat_act ℓ (pIn 0)
  simp only [h0, h1]

end QED.TwoLoop.NestedVP

end
