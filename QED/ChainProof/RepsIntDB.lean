/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntBD

/-!
# The `δ₃`–bubble representatives of set (b): lines, routing and amplitude

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53). For the two-loop
representatives `repDB s` (`photonCt` vertex `3` next to `a`, with field `s` towards `a`; bubble
`4 ⇄ 5` next to `c`), this file gives, as `QED/ChainProof/RepsIntBD.lean` does for `repBD s`:

* the lines and the nested routing `dbMom`, with the photon momentum `k` and the loop momentum `q`:
  | line | `0 → 1` | `1 → 2` | `5 → 4` | `4 → 5` | `2 → 3` | `3 → 4` | `0 → 5` |
  | --- | --- | --- | --- | --- | --- | --- | --- |
  | momentum | `p - k` | `p + k_ext - k` | `q + k` | `q` | `-k` | `-k` | `k` |
  conserved under momentum conservation (`dbMom_isConserved`);
* the frozen routing (T₄) in these variables (`lineMomentum₂_repDB`);
* the amplitude (T₇) of the loop flavour `f` (`db_amplitude`) and the regulated amplitude (T₈) as
  the sum over the loop flavour (`regulatedAmplitude₂_repDB`);
* the split into the transverse part (`-(δ₃/2) k² d(k)` times the amplitude of `VP`) and the
  longitudinal part (`db_amplitude_split`), and the flavour-summed longitudinal part as three
  products of numerators of degree four and denominators (`dbLong_sum`).
-/

@[expose] public section

open MeasureTheory Complex

namespace QED.ChainProof.RepsInt

open QED.WickModel QED.ChainProof.Enum QED.TwoLoop.Routing QED.TwoLoop.Enumeration
  QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge

/-! ### The lines of `repDB s` -/

section Lines

variable (s : Fin 2)

/-- The fermion line `0 → 1`, a chord. -/
def dbF1 : FermionLine (repDB s) := ⟨fv kDB 1, by revert s; decide +kernel⟩
/-- The fermion line `1 → 2`. -/
def dbF2 : FermionLine (repDB s) := ⟨fv kDB 2, by revert s; decide +kernel⟩
/-- The loop line `5 → 4`, a chord. -/
def dbF4 : FermionLine (repDB s) := ⟨fv kDB 4, by revert s; decide +kernel⟩
/-- The loop line `4 → 5`. -/
def dbF5 : FermionLine (repDB s) := ⟨fv kDB 5, by revert s; decide +kernel⟩
/-- The photon line `2 → 3` (from `a` to the field `s` of the `photonCt` vertex). -/
def dbGA : PhotonLine (repDB s) := ⟨pg kDB 2, by revert s; decide +kernel⟩
/-- The photon line `3 → 4` (from the field `s.rev` of the `photonCt` vertex to the loop). -/
def dbGB : PhotonLine (repDB s) := ⟨pc kDB 3 s.rev, by revert s; decide +kernel⟩
/-- The photon line `0 → 5` (from `c` to the loop). -/
def dbGC : PhotonLine (repDB s) := ⟨pg kDB 0, by revert s; decide +kernel⟩

theorem db_fermionLine_cases : ∀ s (f : FermionLine (repDB s)),
    f = dbF1 s ∨ f = dbF2 s ∨ f = dbF4 s ∨ f = dbF5 s := by
  decide +kernel

theorem db_photonLine_cases : ∀ s (g : PhotonLine (repDB s)),
    g = dbGA s ∨ g = dbGB s ∨ g = dbGC s := by
  decide +kernel

theorem db_fermion_ne : [dbF1 s, dbF2 s, dbF4 s, dbF5 s].Nodup := by
  simp [dbF1, dbF2, dbF4, dbF5, fv]

theorem db_photon_ne : [dbGA s, dbGB s, dbGC s].Nodup := by
  simp [dbGA, dbGB, dbGC, pg, pc]

theorem db_isChord_iff : ∀ s (g : Line (repDB s)),
    IsChord g ↔ g = .inl (dbF1 s) ∨ g = .inl (dbF4 s) := by
  decide +kernel

theorem db_ends : ∀ s,
    (Line.ends (.inl (dbF1 s) : Line (repDB s))) = (0, 1) ∧
    (Line.ends (.inl (dbF2 s) : Line (repDB s))) = (1, 2) ∧
    (Line.ends (.inl (dbF4 s) : Line (repDB s))) = (5, 4) ∧
    (Line.ends (.inl (dbF5 s) : Line (repDB s))) = (4, 5) ∧
    (Line.ends (.inr (dbGA s) : Line (repDB s))) = (2, 3) ∧
    (Line.ends (.inr (dbGB s) : Line (repDB s))) = (3, 4) ∧
    (Line.ends (.inr (dbGC s) : Line (repDB s))) = (0, 5) := by
  decide +kernel

theorem db_tails : ∀ s, (dbF1 s).tail = fv kDB 0 ∧ (dbF2 s).tail = fv kDB 1 ∧
    (dbF4 s).tail = fv kDB 5 ∧ (dbF5 s).tail = fv kDB 4 ∧
    (dbGA s).head = pc kDB 3 s ∧ (dbGB s).head = pg kDB 4 ∧ (dbGC s).head = pg kDB 5 := by
  decide +kernel

theorem db_ext : ∀ s (v : Fin 6),
    ((∃ t : Wick.FermionVertex kDB, t.1 = v ∧ (repDB s).1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot kDB, a.1 = v ∧ (repDB s).1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex kDB, t.1 = v ∧ (repDB s).1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  decide +kernel

theorem db_sum_line {M : Type*} [AddCommMonoid M] (g : Line (repDB s) → M) :
    ∑ f, g f = g (.inl (dbF1 s)) + g (.inl (dbF2 s)) + g (.inl (dbF4 s)) + g (.inl (dbF5 s)) +
      (g (.inr (dbGA s)) + g (.inr (dbGB s)) + g (.inr (dbGC s))) := by
  have hf := db_fermion_ne s
  have hg := db_photon_ne s
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hf hg
  obtain ⟨⟨f12, f13, f14⟩, ⟨f23, f24⟩, f34⟩ := hf
  obtain ⟨⟨gab, gac⟩, gbc⟩ := hg
  rw [Fintype.sum_sum_type, sum_eq_of_four f12 f13 f14 f23 f24 f34 (db_fermionLine_cases s),
    sum_eq_of_three gab gac gbc (db_photonLine_cases s)]

end Lines

/-! ### The nested routing -/

section Routing

variable (s : Fin 2)

/-- **The nested routing** of `repDB s` (the table of the module docstring). -/
def dbMom (p kext q k : Fin 4 → ℝ) (f : Line (repDB s)) : Fin 4 → ℝ :=
  match f with
  | .inl f => if f = dbF1 s then p - k else if f = dbF2 s then p + kext - k
      else if f = dbF4 s then q + k else q
  | .inr g => if g = dbGC s then k else -k

theorem dbMom_apply (p kext q k : Fin 4 → ℝ) :
    dbMom s p kext q k (.inl (dbF1 s)) = p - k ∧ dbMom s p kext q k (.inl (dbF2 s)) = p + kext - k ∧
    dbMom s p kext q k (.inl (dbF4 s)) = q + k ∧ dbMom s p kext q k (.inl (dbF5 s)) = q ∧
    dbMom s p kext q k (.inr (dbGA s)) = -k ∧ dbMom s p kext q k (.inr (dbGB s)) = -k ∧
    dbMom s p kext q k (.inr (dbGC s)) = k := by
  have hf := db_fermion_ne s
  have hg := db_photon_ne s
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hf hg
  obtain ⟨⟨f12, f13, f14⟩, ⟨f23, f24⟩, f34⟩ := hf
  obtain ⟨⟨gab, gac⟩, gbc⟩ := hg
  simp [dbMom, Ne.symm f12, Ne.symm f13, Ne.symm f14, Ne.symm f23, Ne.symm f24, Ne.symm f34,
    gac, gbc]

theorem dbMom_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (q k : Fin 4 → ℝ) :
    IsConserved (repDB s) pOut pIn kIn (dbMom s (pIn 0) (kIn 0) q k) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := db_ends s
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := dbMom_apply s (pIn 0) (kIn 0) q k
  intro v
  rw [inflow, db_sum_line, externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := db_ext s v
  simp only [e1, e2, e3, e4, e5, e6, e7, x1, x2, x3, m1, m2, m3, m4, m5, m6, m7]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem db_card_chordsBelow :
    (Finset.univ.filter fun g : Line (repDB s) =>
      IsChord g ∧ g.label < (Line.label (.inl (dbF1 s) : Line (repDB s)))).card = 0 ∧
    (Finset.univ.filter fun g : Line (repDB s) =>
      IsChord g ∧ g.label < (Line.label (.inl (dbF4 s) : Line (repDB s)))).card = 1 := by
  have l1 : (Line.label (.inl (dbF1 s) : Line (repDB s))) = 1 := rfl
  have l3 : (Line.label (.inl (dbF4 s) : Line (repDB s))) = 4 := rfl
  constructor
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (db_isChord_iff s g).mp hg with rfl | rfl
    · simp [l1] at hl
    · simp [l1, l3] at hl
  · rw [Finset.card_eq_one]
    refine ⟨.inl (dbF1 s), Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (db_isChord_iff s g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(db_isChord_iff s _).mpr (Or.inl rfl), by simp [l1, l3]⟩

theorem db_chordMomentum (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (dbF1 s) : Line (repDB s)) = ℓ 0 ∧
      chordMomentum ℓ (.inl (dbF4 s) : Line (repDB s)) = ℓ 1 := by
  obtain ⟨h0, h1⟩ := db_card_chordsBelow s
  have e : ∀ (f : Line (repDB s)) (i : Fin 2), (Finset.univ.filter fun g : Line (repDB s) =>
      IsChord g ∧ g.label < f.label).card = i → chordMomentum ℓ f = ℓ i := by
    intro f i hi
    have e := card_filter_univ_irrel (fun g : Line (repDB s) => IsChord g ∧ g.label < f.label)
    unfold chordMomentum
    split_ifs with h
    · revert h
      rw [e (d' := fun g => instDecidableAnd) (fi' := inferInstance), hi]
      intro h
      rfl
    · rw [e (d' := fun g => instDecidableAnd) (fi' := inferInstance), hi] at h
      exact absurd i.2 h
  exact ⟨e _ 0 h0, e _ 1 h1⟩

/-- **The frozen routing in nested form**: the routing (T₄) of `repDB s` at `ℓ` is the nested
routing at `q = ℓ₀ + ℓ₁ - p`, `k = p - ℓ₀`. -/
theorem lineMomentum₂_repDB {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ (repDB s) pOut pIn kIn ℓ =
      dbMom s (pIn 0) (kIn 0) (ℓ 0 + ℓ 1 - pIn 0) (pIn 0 - ℓ 0) := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (dbMom_isConserved s hmom _ _) (fun g hg => ?_) f).symm
  obtain ⟨c0, c1⟩ := db_chordMomentum s ℓ
  obtain ⟨n1, -, n3, -⟩ := dbMom_apply s (pIn 0) (kIn 0) (ℓ 0 + ℓ 1 - pIn 0) (pIn 0 - ℓ 0)
  rcases (db_isChord_iff s g).mp hg with rfl | rfl
  · rw [n1, c0, sub_sub_cancel]
  · rw [n3, c1]
    abel

end Routing

/-! ### The flavour sum and the amplitude -/

section Amplitude

variable (s : Fin 2)

/-- The fermion fields of the loop `3 ⇄ 4`. -/
def dbL (t : Wick.FermionVertex kDB) : Bool := decide (4 ≤ t.1.val)

theorem dbL_gauge : ∀ t, dbL t = true → kDB t.1 = .gauge := by decide

theorem db_pow_four : ∀ s, (repDB s).1.1 ^ 4 = 1 := by decide +kernel

theorem db_preserves : ∀ s f, Preserves (repDB s) (flavL dbL dbL_gauge f) := by
  unfold Preserves
  decide +kernel

open scoped Classical in
/-- **The regulated amplitude of `repDB s`** is the sum over the loop flavour. -/
theorem regulatedAmplitude₂_repDB (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line (repDB s) → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P (repDB s) pIn kIn k αOut βIn μ =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude₂ P (repDB s) (flavL dbL dbL_gauge f) pIn kIn k αOut βIn μ := by
  have hsc := fun x y => QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (n := 4) (by norm_num)
    (db_pow_four s) x y
  have hin : ∀ s t, dbL t = true → ∃ i : Fin 4, ((repDB s).1.1 ^ (i : ℕ)) (.inr t) =
      .inr (fv kDB 4) := by decide +kernel
  have hout : ∀ s (x : Fin 1 ⊕ Wick.FermionVertex kDB),
      (∀ t, x = .inr t → dbL t = false) → ∃ i : Fin 4, ((repDB s).1.1 ^ (i : ℕ)) x = .inl 0 := by
    decide +kernel
  have hsep : ∀ s, ¬ ∃ i : Fin 4, ((repDB s).1.1 ^ (i : ℕ)) (.inl 0) = .inr (fv kDB 4) := by
    decide +kernel
  exact regulatedAmplitude₂_eq_sum_loopFlavour P (repDB s) dbL dbL_gauge (fv kDB 4) rfl
    (db_preserves s) (fun t ht => (hsc _ _).mpr (hin s t ht))
    (fun x hx => (hsc _ _).mpr (hout s x hx)) (fun h => hsep s ((hsc _ _).mp h)) pIn kIn k
    αOut βIn μ

theorem db_cond (α β : Wick.FermionVertex kDB → Fin 4) (lor : Wick.PhotonSlot kDB → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, (repDB s).1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, (repDB s).1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, (repDB s).1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (pg kDB 1) = μ 0 ∧ (α (fv kDB 2) = αOut 0 ∧ β (fv kDB 0) = βIn 0) := by
  have h1 : ∀ s t, (repDB s).1.1 (.inl 0) = .inr t ↔ t = fv kDB 2 := by decide +kernel
  have h2 : ∀ s t, (repDB s).1.1 (.inr t) = .inl 0 ↔ t = fv kDB 0 := by decide +kernel
  have h3 : ∀ s a, (repDB s).1.2 (.inl 0) = .inr a ↔ a = pg kDB 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

/-- In the nested routing the momentum entering the field `0` of the `photonCt` vertex is `±k`. -/
theorem db_photonMomentum (kIn : Fin 1 → Fin 4 → ℝ) (p kext q k : Fin 4 → ℝ) :
    photonMomentum₂ (repDB s) kIn (dbMom s p kext q k) ⟨3, ⟨0, by decide⟩⟩ = k ∨
      photonMomentum₂ (repDB s) kIn (dbMom s p kext q k) ⟨3, ⟨0, by decide⟩⟩ = -k := by
  obtain ⟨-, -, -, -, m5, m6, m7⟩ := dbMom_apply s p kext q k
  obtain ⟨-, -, -, -, t5, t6, t7⟩ := db_tails s
  have hext : ∀ s, ¬ (repDB s).1.2 (.inl 0) = .inr ⟨3, ⟨0, by decide⟩⟩ := by decide +kernel
  have hg := db_photon_ne s
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hg
  obtain ⟨⟨gab, gac⟩, gbc⟩ := hg
  have hA1 : (dbGA s).1 = pg kDB 2 := rfl
  have hB1 : (dbGB s).1 = pc kDB 3 s.rev := rfl
  have hC1 : (dbGC s).1 = pg kDB 0 := rfl
  unfold photonMomentum₂
  rw [Fin.sum_univ_one, ite_eq_right (hext s),
    sum_eq_of_three gab gac gbc (db_photonLine_cases s), t5, t6, t7, hA1, hB1, hC1, m5, m6, m7]
  fin_cases s <;> simp +decide

/-- **The amplitude of `repDB s` for the loop flavour `f`** in the nested routing: the open-line
chain, the singly inserted photon line from `a` to the loop, the loop trace of flavour `f`, and the
photon propagator from the loop to `c`. -/
theorem db_amplitude (P : Params) (f : Fin 3) (pIn kIn : Fin 1 → Fin 4 → ℝ) (q k : Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P (repDB s) (flavL dbL dbL_gauge f) pIn kIn
        (dbMom s (pIn 0) (kIn 0) q k) αOut βIn μ =
      (I * P.e) ^ 5 * (1 / I) ^ 6 * ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l4 : Fin 4, ∑ l5 : Fin 4,
        QED.TwoLoop.NestedVP.outerChain P (pIn 0) (kIn 0) k (μ 0) l0 l2 (αOut 0) (βIn 0) *
          photonInsertion P.δ₃ P.mγ P.Λ P.ε k l2 l4 *
          Matrix.trace (Dirac.gamma l4 * QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k) *
            Dirac.gamma l5 * QED.OneLoop.electronPropagator (P.mass f) P.ε q) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k l0 l5 := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := dbMom_apply s (pIn 0) (kIn 0) q k
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := db_tails s
  have hct : ∀ (α β : Wick.FermionVertex kDB → Fin 4) (lor : Wick.PhotonSlot kDB → Fin 4),
      Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
          (psiMomentum₂ (repDB s) pIn (dbMom s (pIn 0) (kIn 0) q k))
          (photonMomentum₂ (repDB s) kIn (dbMom s (pIn 0) (kIn 0) q k)) 3 =
        photonCtFactor P.δ₃ k (lor ⟨3, ⟨0, by decide⟩⟩) (lor ⟨3, ⟨1, by decide⟩⟩) := by
    intro α β lor
    rw [QED.TwoLoop.Relabel.vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _
      (show kDB 3 = .photonCt from rfl)]
    rcases db_photonMomentum s kIn (pIn 0) (kIn 0) q k with e | e
    · rw [e]; rfl
    · rw [e, ← photonCtFactor_neg]; rfl
  have hfl : ∀ t, (flavL dbL dbL_gauge f).1 t = if dbL t then f else 0 := fun _ => rfl
  have hf := db_fermion_ne s
  have hg := db_photon_ne s
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hf hg
  obtain ⟨⟨f12, f13, f14⟩, ⟨f23, f24⟩, f34⟩ := hf
  obtain ⟨⟨gab, gac⟩, gbc⟩ := hg
  have hprodf : ∀ (g : FermionLine (repDB s) → ℂ),
      ∏ x, g x = g (dbF1 s) * g (dbF2 s) * g (dbF4 s) * g (dbF5 s) := by
    intro g
    have : (Finset.univ : Finset (FermionLine (repDB s))) = {dbF1 s, dbF2 s, dbF4 s, dbF5 s} := by
      ext x; simpa using db_fermionLine_cases s x
    rw [this, Finset.prod_insert (by simp [f12, f13, f14]),
      Finset.prod_insert (by simp [f23, f24]), Finset.prod_pair f34]
    ring
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex kDB → Fin 4, ∑ β : Wick.FermionVertex kDB → Fin 4,
      ∑ lor : Wick.PhotonSlot kDB → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot kDB → Fin 4,
    (if lor (pg kDB 1) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) ^ 5 * (1 / I) ^ 7 *
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k (lor (pg kDB 2)) (lor (pc kDB 3 s)) *
          photonCtFactor P.δ₃ k (lor ⟨3, ⟨0, by decide⟩⟩) (lor ⟨3, ⟨1, by decide⟩⟩) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k (lor (pc kDB 3 s.rev)) (lor (pg kDB 4)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k (lor (pg kDB 0)) (lor (pg kDB 5))) *
        (((Dirac.gamma (lor (pg kDB 2)) *
            QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + kIn 0 - k) *
          Dirac.gamma (lor (pg kDB 1)) * QED.OneLoop.electronPropagator P.m P.ε (pIn 0 - k) *
          Dirac.gamma (lor (pg kDB 0))) (αOut 0) (βIn 0) *
        Matrix.trace (Dirac.gamma (lor (pg kDB 4)) *
            QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k) *
          Dirac.gamma (lor (pg kDB 5)) * QED.OneLoop.electronPropagator (P.mass f) P.ε q)))) = _)
  · have hsp := sum_spinor_chain3_loop2 (x₁ := fv kDB 2) (x₂ := fv kDB 1) (x₃ := fv kDB 0)
      (y₁ := fv kDB 4) (y₂ := fv kDB 5) (by decide) (by decide +kernel)
      (Dirac.gamma (lor (pg kDB 2))) (Dirac.gamma (lor (pg kDB 1))) (Dirac.gamma (lor (pg kDB 0)))
      (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + kIn 0 - k))
      (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 - k))
      (Dirac.gamma (lor (pg kDB 4))) (Dirac.gamma (lor (pg kDB 5)))
      (QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k))
      (QED.OneLoop.electronPropagator (P.mass f) P.ε q) (αOut 0) (βIn 0)
    rw [← hsp, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [db_cond, Fin.prod_univ_six, hprodf,
      prod_eq_of_three' gab gac gbc (db_photonLine_cases s),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kDB 0 = .gauge from rfl),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kDB 1 = .gauge from rfl),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kDB 2 = .gauge from rfl),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kDB 4 = .gauge from rfl),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kDB 5 = .gauge from rfl),
      hct, t1, t2, t3, t4, t5, t6, t7, m1, m2, m3, m4, m5, m6, m7,
      photonPropagator_neg', ite_and_eq_mul]
    simp only [show (dbF1 s).1 = fv kDB 1 from rfl, show (dbF2 s).1 = fv kDB 2 from rfl,
      show (dbF4 s).1 = fv kDB 4 from rfl, show (dbF5 s).1 = fv kDB 5 from rfl,
      show (dbGA s).1 = pg kDB 2 from rfl, show (dbGB s).1 = pc kDB 3 s.rev from rfl,
      show (dbGC s).1 = pg kDB 0 from rfl, hfl, dbL, fv, pg]
    simp only [Params.mass, show decide (4 ≤ ((4 : Fin 6) : ℕ)) = true from rfl,
      show decide (4 ≤ ((5 : Fin 6) : ℕ)) = true from rfl,
      show decide (4 ≤ ((1 : Fin 6) : ℕ)) = false from rfl,
      show decide (4 ≤ ((2 : Fin 6) : ℕ)) = false from rfl, ite_true, Bool.false_eq_true,
      ite_false, Matrix.cons_val_zero]
    ring
  · have hd : ∀ s, [pg kDB 0, pg kDB 1, pg kDB 2, pg kDB 4, pg kDB 5, pc kDB 3 s,
        pc kDB 3 s.rev].Nodup := by decide +kernel
    have hX : ∀ s (x : Wick.PhotonSlot kDB), x = pg kDB 0 ∨ x = pg kDB 1 ∨ x = pg kDB 2 ∨
        x = pg kDB 4 ∨ x = pg kDB 5 ∨ x = pc kDB 3 s ∨ x = pc kDB 3 s.rev := by
      decide +kernel
    rw [sum_pi_seven (hd s) (hX s)]
    simp only [photonInsertion, QED.TwoLoop.NestedVP.outerChain, Finset.mul_sum, Finset.sum_mul]
    fin_cases s <;>
    · simp +decide only [ite_true, ite_false, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
        Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ]
      refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
        Finset.sum_congr rfl fun l4 _ => Finset.sum_congr rfl fun l5 _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      try simp only [photonCtFactor_comm P.δ₃ k b a]
      rw [photonPropagator_comm' P.mγ P.Λ P.ε k b l4]
      ring

end Amplitude

/-! ### Transverse and longitudinal parts -/

section Split

/-- The longitudinal part of the amplitude of `repDB s` for the loop flavour `f`: the
`photonCt` insertion replaced by `d(k)² k_ν k_ρ`. -/
noncomputable def dbLong (P : Params) (f : Fin 3) (p kext q k : Fin 4 → ℝ) (α β μ : Fin 4) : ℂ :=
  (I * P.e) ^ 5 * (1 / I) ^ 6 * ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l4 : Fin 4, ∑ l5 : Fin 4,
    QED.TwoLoop.NestedVP.outerChain P p kext k μ l0 l2 α β *
      longitudinalPhoton P.mγ P.Λ P.ε k l2 l4 *
      Matrix.trace (Dirac.gamma l4 * QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k) *
        Dirac.gamma l5 * QED.OneLoop.electronPropagator (P.mass f) P.ε q) *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k l0 l5

/-- **The split of the amplitude of `repDB s`**: the transverse part of the `photonCt` insertion
gives `-(δ₃/2) k² d(k)` times the amplitude of the vacuum-polarization class `VP` (same nested
momenta), and the longitudinal part gives `(δ₃/2) dbLong`. -/
theorem db_amplitude_split (s : Fin 2) (P : Params) (f : Fin 3) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (q k : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P (repDB s) (flavL dbL dbL_gauge f) pIn kIn
        (dbMom s (pIn 0) (kIn 0) q k) αOut βIn μ =
      (-(P.δ₃ / 2 : ℂ) * (((Minkowski.dot k k : ℝ) : ℂ) * photonScalar P.mγ P.Λ P.ε k)) *
          contractionAmplitude₂ P QED.TwoLoop.NestedVP.cV (QED.TwoLoop.NestedVP.flavV f) pIn kIn
            (QED.TwoLoop.NestedVP.nestedMom (pIn 0) (kIn 0) q k) αOut βIn μ +
        (P.δ₃ / 2 : ℂ) * dbLong P f (pIn 0) (kIn 0) q k (αOut 0) (βIn 0) (μ 0) := by
  rw [db_amplitude, QED.TwoLoop.NestedVP.contractionAmplitude₂_flavV, dbLong]
  simp only [photonInsertion_eq, mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have hneg : photonScalar P.mγ P.Λ P.ε (-k) = photonScalar P.mγ P.Λ P.ε k := by
      simp [photonScalar, Minkowski.dot]
    simp only [transversePhoton, photonPropagator_eq_metric_mul, hneg,
      bd_trace_rotate (Dirac.gamma x) (QED.OneLoop.electronPropagator (P.mass f) P.ε q)]
    ring
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring

end Split

/-! ### The longitudinal part -/

section Longitudinal

/-- The loop trace contracted with the photon momentum at its first vertex. -/
theorem sum_trace_lower_eq' (M : ℝ) {ε : ℝ} (hε : ε ≠ 0) (q k : Fin 4 → ℝ) (σ : Fin 4) :
    ∑ l4 : Fin 4, Matrix.trace (Dirac.gamma l4 * QED.OneLoop.electronPropagator M ε (q + k) *
        Dirac.gamma σ * QED.OneLoop.electronPropagator M ε q) * ((Minkowski.lower k l4 : ℝ) : ℂ) =
      4 * ((q σ : ℝ) : ℂ) * ((propDenom M ε q)⁻¹ +
          (ε : ℂ) * I * ((propDenom M ε (q + k))⁻¹ * (propDenom M ε q)⁻¹)) -
        4 * (((q + k) σ : ℝ) : ℂ) * ((propDenom M ε (q + k))⁻¹ +
          (ε : ℂ) * I * ((propDenom M ε (q + k))⁻¹ * (propDenom M ε q)⁻¹)) := by
  have hslash : ∑ l4 : Fin 4, Matrix.trace (Dirac.gamma l4 *
        QED.OneLoop.electronPropagator M ε (q + k) * Dirac.gamma σ *
          QED.OneLoop.electronPropagator M ε q) * ((Minkowski.lower k l4 : ℝ) : ℂ) =
      Matrix.trace (Dirac.gamma σ * QED.OneLoop.electronPropagator M ε q *
        Dirac.slash k * QED.OneLoop.electronPropagator M ε (q + k)) := by
    rw [bd_trace_rotate (Dirac.gamma σ)]
    simp only [Dirac.slash, Matrix.sum_mul, Matrix.trace_sum,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => by rw [bd_trace_rotate (Dirac.gamma _)]; ring
  have hk : Dirac.slash k = -Dirac.slash (q - (q + k)) := by
    rw [show q - (q + k) = -k by abel]
    simp [Dirac.slash, Minkowski.lower]
  have hD : ∀ X : Fin 4 → ℝ, (((Minkowski.dot X X + M ^ 2 : ℝ) : ℂ)) =
      propDenom M ε X + (ε : ℂ) * I := fun X => by simp only [propDenom]; ring
  have hP := propDenom_ne_zero (M := M) hε (q + k)
  have hQ := propDenom_ne_zero (M := M) hε q
  rw [hslash, QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul,
    QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [show Dirac.gamma σ * electronNumerator M q * Dirac.slash k * electronNumerator M (q + k) =
      -(Dirac.gamma σ * (electronNumerator M q * Dirac.slash (q - (q + k)) *
        electronNumerator M (q + k))) by
      rw [hk]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc],
    Matrix.trace_neg, trace_ward, hD, hD]
  field_simp
  ring

end Longitudinal

section LongSum

variable (P : Params)

/-- The numerators of the longitudinal part of `repDB`: the open-line numerator contracted with
`k` at `a` and with `v` at `c`: `∑ ON^{l₀ l₂} k_{l₂} g_{l₀ l₅} v^{l₅}`. -/
noncomputable def dbN (p kext : Fin 4 → ℝ) (μ α β : Fin 4) (k v : Fin 4 → ℝ) : ℂ :=
  ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l5 : Fin 4, bdON P p kext k μ l0 l2 α β *
    ((Minkowski.lower k l2 : ℝ) : ℂ) * ((Minkowski.metric l0 l5 : ℝ) : ℂ) * ((v l5 : ℝ) : ℂ)

/-- **The flavour-summed longitudinal part of `repDB`** as three products of a numerator of
degree four and propagator denominators. -/
theorem dbLong_sum (hε : P.ε ≠ 0) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (p kext q k : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    ∑ f : Fin 3, (P.loopCoeff f : ℂ) * dbLong P f p kext q k α β μ =
      (I * P.e) ^ 5 * (1 / I) ^ 6 * (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) ^ 3 *
        ((propDenom P.mγ P.ε k)⁻¹ * (propDenom P.Λ P.ε k)⁻¹) ^ 3 *
        ((propDenom P.m P.ε (p + kext - k))⁻¹ * (propDenom P.m P.ε (p - k))⁻¹) *
        (4 * vpBubbleCoeff P) *
        (dbN P p kext μ α β k q *
            ((propDenom P.m P.ε q)⁻¹ * (propDenom P.M₁ P.ε q)⁻¹ * (propDenom P.M₂ P.ε q)⁻¹) -
          dbN P p kext μ α β k (q + k) * ((propDenom P.m P.ε (q + k))⁻¹ *
            (propDenom P.M₁ P.ε (q + k))⁻¹ * (propDenom P.M₂ P.ε (q + k))⁻¹) -
          (P.ε : ℂ) * I * dbN P p kext μ α β k k *
            ((propDenom P.m P.ε (q + k))⁻¹ * (propDenom P.m P.ε q)⁻¹ * (propDenom P.M₁ P.ε q)⁻¹ *
                (propDenom P.M₂ P.ε q)⁻¹ +
              (propDenom P.m P.ε (q + k))⁻¹ * (propDenom P.M₁ P.ε (q + k))⁻¹ *
                (propDenom P.M₁ P.ε q)⁻¹ * (propDenom P.M₂ P.ε q)⁻¹ +
              (propDenom P.m P.ε (q + k))⁻¹ * (propDenom P.M₁ P.ε (q + k))⁻¹ *
                (propDenom P.M₂ P.ε (q + k))⁻¹ * (propDenom P.M₂ P.ε q)⁻¹)) := by
  set d := photonScalar P.mγ P.Λ P.ε k with hd
  have hdd : d = ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) *
      ((propDenom P.mγ P.ε k)⁻¹ * (propDenom P.Λ P.ε k)⁻¹) := by
    have h1 := propDenom_ne_zero (M := P.mγ) hε k
    have h2 := propDenom_ne_zero (M := P.Λ) hε k
    rw [hd, photonScalar]
    simp only [propDenom] at h1 h2 ⊢
    field_simp
    push_cast
    ring
  set Y : Fin 4 → Fin 4 → Fin 4 → ℂ := fun l0 l2 l5 => (I * P.e) ^ 5 * (1 / I) ^ 6 *
    ((propDenom P.m P.ε (p + kext - k))⁻¹ * (propDenom P.m P.ε (p - k))⁻¹) *
    bdON P p kext k μ l0 l2 α β * ((Minkowski.metric l0 l5 : ℝ) : ℂ) * d ^ 3 *
    ((Minkowski.lower k l2 : ℝ) : ℂ) with hY
  -- step A: the contraction with `k` at the loop
  have hA : ∀ f, dbLong P f p kext q k α β μ = ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l5 : Fin 4,
      Y l0 l2 l5 * ∑ l4 : Fin 4, Matrix.trace (Dirac.gamma l4 *
        QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k) * Dirac.gamma l5 *
          QED.OneLoop.electronPropagator (P.mass f) P.ε q) * ((Minkowski.lower k l4 : ℝ) : ℂ) := by
    intro f
    simp only [dbLong, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l5 _ => Finset.sum_congr rfl fun l4 _ => ?_
    simp only [hY, QED.TwoLoop.NestedVP.outerChain, bdON, longitudinalPhoton,
      photonPropagator_eq_metric_mul, QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, ← hd]
    ring
  simp only [hA, sum_trace_lower_eq' _ hε, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun l0 _ => ?_).trans (?_ : ∑ l0 : Fin 4, ∑ l2 : Fin 4,
    ∑ l5 : Fin 4, Y l0 l2 l5 * (4 * vpBubbleCoeff P * (((q l5 : ℝ) : ℂ) *
          ((propDenom P.m P.ε q)⁻¹ * (propDenom P.M₁ P.ε q)⁻¹ * (propDenom P.M₂ P.ε q)⁻¹) -
        (((q + k) l5 : ℝ) : ℂ) * ((propDenom P.m P.ε (q + k))⁻¹ * (propDenom P.M₁ P.ε (q + k))⁻¹ *
          (propDenom P.M₂ P.ε (q + k))⁻¹) -
        (P.ε : ℂ) * I * ((k l5 : ℝ) : ℂ) *
          ((propDenom P.m P.ε (q + k))⁻¹ * (propDenom P.m P.ε q)⁻¹ * (propDenom P.M₁ P.ε q)⁻¹ *
              (propDenom P.M₂ P.ε q)⁻¹ +
            (propDenom P.m P.ε (q + k))⁻¹ * (propDenom P.M₁ P.ε (q + k))⁻¹ *
              (propDenom P.M₁ P.ε q)⁻¹ * (propDenom P.M₂ P.ε q)⁻¹ +
            (propDenom P.m P.ε (q + k))⁻¹ * (propDenom P.M₁ P.ε (q + k))⁻¹ *
              (propDenom P.M₂ P.ε (q + k))⁻¹ * (propDenom P.M₂ P.ε q)⁻¹))) = _)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l2 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l5 _ => ?_
    rw [← bd_flavour_W P hε hc₁ hc₂ q k l5, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  · simp only [dbN, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
      Finset.sum_congr rfl fun l5 _ => ?_
    simp only [hY, hdd, Pi.add_apply, ofReal_add]
    ring

end LongSum

end QED.ChainProof.RepsInt

end
