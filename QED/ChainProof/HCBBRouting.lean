/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.EnumReps
public import QED.TwoLoop.CountertermInsertionBasic
public import QED.TwoLoop.NestedVPRouting
public import QED.TwoLoop.JointIntegralInvariance

/-!
# The bubble–bubble representative of set (b) in the nested routing

Helper level, Phase 5 Stage 1a, obligation O3-6 for the class of
`QED.ChainProof.Enum.repBB` (`docs/HIGHER-LOOP-PLAN.md`). The representative has the open line
`0 → 1 → 2` (external photon at `1`), the bubbles `3 ⇄ 4` and `5 ⇄ 6`, and the photon lines
`2 — 3`, `4 — 5`, `6 — 0`.

The frozen routing (T₄) puts the three loop momenta on the chords, which are the fermion lines
`0 → 1` (label `1`), `4 → 3` (label `3`) and `6 → 5` (label `5`). For the nested form we use
instead the loop momentum `q₂` of the bubble `5 ⇄ 6` (the one next to the vertex `0`), `q₁` of the
bubble `3 ⇄ 4` (next to the vertex `2`) and the photon momentum `k`:

| line | `0 → 1` | `1 → 2` | `4 → 3` | `3 → 4` | `6 → 5` | `5 → 6` | `0 — 6` | `2 — 3` | `4 — 5` |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| momentum | `p - k` | `p + k_ext - k` | `q₁ + k` | `q₁` | `q₂ + k` | `q₂` | `k` | `-k` | `-k` |

with `p = pIn 0`, `k_ext = kIn 0`, and each photon line oriented from its lower to its higher
vertex (`bbMom`).

* `isConserved_bbMom`: under momentum conservation the nested routing is conserved at every
  vertex.
* `isChord_repBB_iff`, `chordMomentum_bb`: the chords and their loop momenta `ℓ 0, ℓ 1, ℓ 2`.
* `lineMomentum₂_repBB`: the frozen routing at `ℓ` is the nested routing at
  `q₂ = ℓ 2 + ℓ 0 - p`, `q₁ = ℓ 1 + ℓ 0 - p`, `k = p - ℓ 0`, by uniqueness
  (`QED.TwoLoop.Routing.eq_lineMomentum₂_of_isConserved`).
* **`contractionValue₂_repBB_eq_nested`**: the value (T₁₀) of `repBB` is the joint energy-first
  integral (T₉) at three loops of `(2π)⁻¹²` times the regulated amplitude in the nested routing,
  with `ℓ 0 = q₂`, `ℓ 1 = q₁`, `ℓ 2 = k`. The change of loop momenta is integer unimodular
  (`bbMat`, determinant `1`), and the joint prescription is invariant under it for every
  integrand (`QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add`). No
  integrability is needed.
-/

@[expose] public section

namespace QED.ChainProof.HCBB

open QED.WickModel QED.TwoLoop.Routing QED.ChainProof.Enum
open scoped QED.TwoLoop.Enumeration

/-! ### The lines of the representative -/

/-- The fermion lines, by head `1, …, 6` (tails `0, 1, 4, 3, 6, 5`). -/
def lineBB : Fin 6 → FermionLine repBB :=
  ![⟨fv kBB 1, by decide +kernel⟩, ⟨fv kBB 2, by decide +kernel⟩, ⟨fv kBB 3, by decide +kernel⟩,
    ⟨fv kBB 4, by decide +kernel⟩, ⟨fv kBB 5, by decide +kernel⟩, ⟨fv kBB 6, by decide +kernel⟩]

/-- The photon lines `0 — 6`, `2 — 3`, `4 — 5`, indexed by the fields of `0`, `2`, `4`. -/
def photBB : Fin 3 → PhotonLine repBB :=
  ![⟨pg kBB 0, by decide +kernel⟩, ⟨pg kBB 2, by decide +kernel⟩, ⟨pg kBB 4, by decide +kernel⟩]

theorem lineBB_bijective : Function.Bijective lineBB := by decide +kernel

theorem photBB_bijective : Function.Bijective photBB := by decide +kernel

theorem val_lineBB : (lineBB 0).1 = fv kBB 1 ∧ (lineBB 1).1 = fv kBB 2 ∧
    (lineBB 2).1 = fv kBB 3 ∧ (lineBB 3).1 = fv kBB 4 ∧ (lineBB 4).1 = fv kBB 5 ∧
    (lineBB 5).1 = fv kBB 6 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tail_lineBB : (lineBB 0).tail = fv kBB 0 ∧ (lineBB 1).tail = fv kBB 1 ∧
    (lineBB 2).tail = fv kBB 4 ∧ (lineBB 3).tail = fv kBB 3 ∧ (lineBB 4).tail = fv kBB 6 ∧
    (lineBB 5).tail = fv kBB 5 := by decide +kernel

theorem val_photBB : (photBB 0).1 = pg kBB 0 ∧ (photBB 1).1 = pg kBB 2 ∧
    (photBB 2).1 = pg kBB 4 :=
  ⟨rfl, rfl, rfl⟩

theorem head_photBB : (photBB 0).head = pg kBB 6 ∧ (photBB 1).head = pg kBB 3 ∧
    (photBB 2).head = pg kBB 5 := by decide +kernel

theorem ends_lineBB : (Line.ends (.inl (lineBB 0) : Line repBB)) = (0, 1) ∧
    (Line.ends (.inl (lineBB 1) : Line repBB)) = (1, 2) ∧
    (Line.ends (.inl (lineBB 2) : Line repBB)) = (4, 3) ∧
    (Line.ends (.inl (lineBB 3) : Line repBB)) = (3, 4) ∧
    (Line.ends (.inl (lineBB 4) : Line repBB)) = (6, 5) ∧
    (Line.ends (.inl (lineBB 5) : Line repBB)) = (5, 6) := by decide +kernel

theorem ends_photBB : (Line.ends (.inr (photBB 0) : Line repBB)) = (0, 6) ∧
    (Line.ends (.inr (photBB 1) : Line repBB)) = (2, 3) ∧
    (Line.ends (.inr (photBB 2) : Line repBB)) = (4, 5) := by decide +kernel

theorem sum_fermionLine {M : Type*} [AddCommMonoid M] [Fintype (FermionLine repBB)]
    (g : FermionLine repBB → M) :
    ∑ f, g f = g (lineBB 0) + g (lineBB 1) + g (lineBB 2) + g (lineBB 3) + g (lineBB 4) +
      g (lineBB 5) := by
  rw [← (Equiv.ofBijective _ lineBB_bijective).sum_comp, Fin.sum_univ_six]
  rfl

theorem prod_fermionLine {M : Type*} [CommMonoid M] [Fintype (FermionLine repBB)]
    (g : FermionLine repBB → M) :
    ∏ f, g f = g (lineBB 0) * g (lineBB 1) * g (lineBB 2) * g (lineBB 3) * g (lineBB 4) *
      g (lineBB 5) := by
  rw [← (Equiv.ofBijective _ lineBB_bijective).prod_comp, Fin.prod_univ_six]
  rfl

theorem sum_photonLine {M : Type*} [AddCommMonoid M] [Fintype (PhotonLine repBB)]
    (g : PhotonLine repBB → M) : ∑ f, g f = g (photBB 0) + g (photBB 1) + g (photBB 2) := by
  rw [← (Equiv.ofBijective _ photBB_bijective).sum_comp, Fin.sum_univ_three]
  rfl

theorem prod_photonLine {M : Type*} [CommMonoid M] [Fintype (PhotonLine repBB)]
    (g : PhotonLine repBB → M) : ∏ f, g f = g (photBB 0) * g (photBB 1) * g (photBB 2) := by
  rw [← (Equiv.ofBijective _ photBB_bijective).prod_comp, Fin.prod_univ_three]
  rfl

theorem sum_line {M : Type*} [AddCommMonoid M] [Fintype (FermionLine repBB)]
    [Fintype (PhotonLine repBB)] (g : Line repBB → M) :
    ∑ f, g f = g (.inl (lineBB 0)) + g (.inl (lineBB 1)) + g (.inl (lineBB 2)) +
      g (.inl (lineBB 3)) + g (.inl (lineBB 4)) + g (.inl (lineBB 5)) +
      (g (.inr (photBB 0)) + g (.inr (photBB 1)) + g (.inr (photBB 2))) := by
  rw [Fintype.sum_sum_type, sum_fermionLine, sum_photonLine]

/-! ### The external momenta -/

theorem extPsi_iff (v : Fin 7) :
    (∃ t : Wick.FermionVertex kBB, t.1 = v ∧ repBB.1.1 (.inr t) = .inl 0) ↔ v = 0 := by
  revert v
  decide +kernel

theorem extA_iff (v : Fin 7) :
    (∃ a : Wick.PhotonSlot kBB, a.1 = v ∧ repBB.1.2 (.inl 0) = .inr a) ↔ v = 1 := by
  revert v
  decide +kernel

theorem extPsiBar_iff (v : Fin 7) :
    (∃ t : Wick.FermionVertex kBB, t.1 = v ∧ repBB.1.1 (.inl 0) = .inr t) ↔ v = 2 := by
  revert v
  decide +kernel

/-- The external momenta (X₁₉) of the representative: `pIn` flows in at `0`, `kIn` at `1`, and
`pOut` flows out at `2`. -/
theorem externalMomentum_repBB (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (v : Fin 7) :
    externalMomentum repBB pOut pIn kIn v =
      (if v = 0 then pIn 0 else 0) + (if v = 1 then kIn 0 else 0) -
        (if v = 2 then pOut 0 else 0) := by
  rw [QED.TwoLoop.Insertion.externalMomentum_one_one]
  simp only [extPsi_iff, extA_iff, extPsiBar_iff]

/-! ### The nested routing -/

/-- **The nested routing** of the representative (the table in the module docstring), with `q₂` on
the bubble `5 ⇄ 6`, `q₁` on the bubble `3 ⇄ 4` and `k` on the photon lines; `p = pIn 0`,
`kext = kIn 0`. Lines are recognized by their labels (X₂₀): `1, …, 6` for the fermion lines with
heads `1, …, 6`, and `7`, `11`, `15` for the photon lines `0 — 6`, `2 — 3`, `4 — 5`. -/
def bbMom (p kext q₂ q₁ k : Fin 4 → ℝ) (f : Line repBB) : Fin 4 → ℝ :=
  match f.label with
  | 1 => p - k
  | 2 => p + kext - k
  | 3 => q₁ + k
  | 4 => q₁
  | 5 => q₂ + k
  | 6 => q₂
  | 7 => k
  | _ => -k

theorem bbMom_apply (p kext q₂ q₁ k : Fin 4 → ℝ) :
    bbMom p kext q₂ q₁ k (.inl (lineBB 0)) = p - k ∧
      bbMom p kext q₂ q₁ k (.inl (lineBB 1)) = p + kext - k ∧
      bbMom p kext q₂ q₁ k (.inl (lineBB 2)) = q₁ + k ∧
      bbMom p kext q₂ q₁ k (.inl (lineBB 3)) = q₁ ∧
      bbMom p kext q₂ q₁ k (.inl (lineBB 4)) = q₂ + k ∧
      bbMom p kext q₂ q₁ k (.inl (lineBB 5)) = q₂ ∧
      bbMom p kext q₂ q₁ k (.inr (photBB 0)) = k ∧
      bbMom p kext q₂ q₁ k (.inr (photBB 1)) = -k ∧
      bbMom p kext q₂ q₁ k (.inr (photBB 2)) = -k :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The nested routing is conserved** at every vertex, under momentum conservation. -/
theorem isConserved_bbMom {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (q₂ q₁ k : Fin 4 → ℝ) :
    IsConserved repBB pOut pIn kIn (bbMom (pIn 0) (kIn 0) q₂ q₁ k) := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := ends_lineBB
  obtain ⟨g0, g1, g2⟩ := ends_photBB
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8⟩ := bbMom_apply (pIn 0) (kIn 0) q₂ q₁ k
  intro v
  rw [inflow, sum_line, externalMomentum_repBB, hmom]
  simp only [e0, e1, e2, e3, e4, e5, g0, g1, g2, n0, n1, n2, n3, n4, n5, n6, n7, n8]
  fin_cases v
  all_goals simp
  all_goals abel

/-! ### The chords -/

theorem isChord_repBB_iff : ∀ f : Line repBB,
    IsChord f ↔ f = .inl (lineBB 0) ∨ f = .inl (lineBB 2) ∨ f = .inl (lineBB 4) := by
  decide +kernel

theorem label_lineBB : (Line.label (.inl (lineBB 0) : Line repBB)) = 1 ∧
    (Line.label (.inl (lineBB 2) : Line repBB)) = 3 ∧
    (Line.label (.inl (lineBB 4) : Line repBB)) = 5 :=
  ⟨rfl, rfl, rfl⟩

open scoped Classical in
/-- The number of chords of label below that of each chord. -/
theorem card_chordsBelow : (Finset.univ.filter fun g : Line repBB =>
      IsChord g ∧ g.label < (Line.label (.inl (lineBB 0) : Line repBB))).card = 0 ∧
    (Finset.univ.filter fun g : Line repBB =>
      IsChord g ∧ g.label < (Line.label (.inl (lineBB 2) : Line repBB))).card = 1 ∧
    (Finset.univ.filter fun g : Line repBB =>
      IsChord g ∧ g.label < (Line.label (.inl (lineBB 4) : Line repBB))).card = 2 := by
  obtain ⟨l0, l2, l4⟩ := label_lineBB
  have h02 : (.inl (lineBB 0) : Line repBB) ≠ .inl (lineBB 2) := by
    intro h
    have := congrArg Line.label h
    rw [l0, l2] at this
    exact absurd this (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (isChord_repBB_iff g).mp hg with rfl | rfl | rfl <;> simp [l0, l2, l4] at hl
  · rw [Finset.card_eq_one]
    refine ⟨.inl (lineBB 0), Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (isChord_repBB_iff g).mp hg with rfl | rfl | rfl
      · rfl
      · simp [l2] at hl
      · simp [l2, l4] at hl
    · subst h
      exact ⟨(isChord_repBB_iff _).mpr (Or.inl rfl), by simp [l0, l2]⟩
  · rw [Finset.card_eq_two]
    refine ⟨.inl (lineBB 0), .inl (lineBB 2), h02, Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (isChord_repBB_iff g).mp hg with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp [l4] at hl
    · rcases h with rfl | rfl
      · exact ⟨(isChord_repBB_iff _).mpr (Or.inl rfl), by simp [l0, l4]⟩
      · exact ⟨(isChord_repBB_iff _).mpr (Or.inr (Or.inl rfl)), by simp [l2, l4]⟩

theorem chordMomentum_bb (ℓ : Fin 3 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (lineBB 0) : Line repBB) = ℓ 0 ∧
      chordMomentum ℓ (.inl (lineBB 2) : Line repBB) = ℓ 1 ∧
      chordMomentum ℓ (.inl (lineBB 4) : Line repBB) = ℓ 2 := by
  classical
  obtain ⟨h0, h1, h2⟩ := card_chordsBelow
  refine ⟨?_, ?_, ?_⟩
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by convert h0; rfl)
    · exact absurd (by convert (show 0 < 3 by norm_num) using 2; convert h0) h
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by convert h1; rfl)
    · exact absurd (by convert (show 1 < 3 by norm_num) using 2; convert h1) h
  · unfold chordMomentum
    split_ifs with h
    · congr 1
      exact Fin.ext (by convert h2; rfl)
    · exact absurd (by convert (show 2 < 3 by norm_num) using 2; convert h2) h

/-- **The frozen routing in nested form**: the routing (T₄) of the representative at loop
momenta `ℓ` is the nested routing at `q₂ = ℓ 2 + ℓ 0 - p`, `q₁ = ℓ 1 + ℓ 0 - p`, `k = p - ℓ 0`,
under momentum conservation. -/
theorem lineMomentum₂_repBB {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 3 → Fin 4 → ℝ) :
    lineMomentum₂ repBB pOut pIn kIn ℓ =
      bbMom (pIn 0) (kIn 0) (ℓ 2 + ℓ 0 - pIn 0) (ℓ 1 + ℓ 0 - pIn 0) (pIn 0 - ℓ 0) := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (isConserved_bbMom hmom _ _ _) (fun g hg => ?_) f).symm
  obtain ⟨c0, c1, c2⟩ := chordMomentum_bb ℓ
  obtain ⟨n0, -, n2, -, n4, -⟩ :=
    bbMom_apply (pIn 0) (kIn 0) (ℓ 2 + ℓ 0 - pIn 0) (ℓ 1 + ℓ 0 - pIn 0) (pIn 0 - ℓ 0)
  rcases (isChord_repBB_iff g).mp hg with rfl | rfl | rfl
  · rw [n0, c0, sub_sub_cancel]
  · rw [n2, c1]
    abel
  · rw [n4, c2]
    abel

/-! ### The value in the nested routing -/

/-- The integer unimodular change of loop momenta `ℓ ↦ (ℓ 0 + ℓ 2, ℓ 0 + ℓ 1, -ℓ 0)`. -/
def bbMat : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 1; 1, 1, 0; -1, 0, 0]

theorem isUnit_det_bbMat : IsUnit bbMat.det := by
  rw [Matrix.det_fin_three]
  simp [bbMat]

theorem bbMat_act (ℓ : Fin 3 → Fin 4 → ℝ) (p : Fin 4 → ℝ) :
    ((fun s => ∑ r, bbMat s r • ℓ r) + ![-p, -p, p]) 0 = ℓ 2 + ℓ 0 - p ∧
      ((fun s => ∑ r, bbMat s r • ℓ r) + ![-p, -p, p]) 1 = ℓ 1 + ℓ 0 - p ∧
      ((fun s => ∑ r, bbMat s r • ℓ r) + ![-p, -p, p]) 2 = p - ℓ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [Pi.add_apply, Fin.sum_univ_three, bbMat]
      simp
      abel

/-- **The value of the bubble–bubble representative in the nested routing**: under momentum
conservation, the value (T₁₀) is the joint energy-first integral (T₉) at three loops of
`(2π)⁻¹²` times the regulated amplitude (T₈) at the nested routing with `q₂ = ℓ 0`, `q₁ = ℓ 1` on
the bubbles and `k = ℓ 2` on the photon lines. No integrability is needed. -/
theorem contractionValue₂_repBB_eq_nested (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionValue₂ P repBB pOut pIn kIn αOut βIn μ =
      QED.TwoLoop.jointEnergyFirstIntegral 3 fun ℓ =>
        (((2 * Real.pi) ^ (4 * 3) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ P repBB pIn kIn (bbMom (pIn 0) (kIn 0) (ℓ 0) (ℓ 1) (ℓ 2))
            αOut βIn μ := by
  rw [QED.TwoLoop.Relabel.contractionValue₂_eq_of_loopCount P loopCount_repBB]
  simp only [lineMomentum₂_repBB hmom]
  have h := QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 3
    (fun ℓ : Fin 3 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 3) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P repBB pIn kIn (bbMom (pIn 0) (kIn 0) (ℓ 0) (ℓ 1) (ℓ 2)) αOut βIn μ)
    bbMat isUnit_det_bbMat ![-pIn 0, -pIn 0, pIn 0]
  refine Eq.trans ?_ h
  refine congrArg (QED.TwoLoop.jointEnergyFirstIntegral 3) (funext fun ℓ => ?_)
  obtain ⟨h0, h1, h2⟩ := bbMat_act ℓ (pIn 0)
  simp only [h0, h1, h2]

end QED.ChainProof.HCBB

end
