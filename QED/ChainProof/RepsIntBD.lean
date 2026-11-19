/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntLoop

/-!
# The bubble–`δ₃` representatives of set (b): lines, routing and amplitude

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53). For the two-loop
representatives `repBD s` (bubble `3 ⇄ 4` next to `a`, `photonCt` vertex `5` with field `s`
towards the bubble), this file gives:

* the lines and the nested routing `bdMom`, with the photon momentum `k` and the loop momentum `q`:
  | line | `0 → 1` | `1 → 2` | `4 → 3` | `3 → 4` | `2 → 3` | `4 → 5` | `0 → 5` |
  | --- | --- | --- | --- | --- | --- | --- | --- |
  | momentum | `p - k` | `p + k_ext - k` | `q + k` | `q` | `-k` | `-k` | `k` |
  conserved under momentum conservation (`bdMom_isConserved`);
* the frozen routing (T₄) in these variables (`lineMomentum₂_repBD`);
* the amplitude (T₇) of the loop flavour `f` (`bd_amplitude`): the open-line chain, the photon
  propagator from `a` to the loop, the loop trace and the singly inserted photon line
  `photonInsertion`, and the regulated amplitude (T₈) as the sum over the loop flavour
  (`regulatedAmplitude₂_repBD`).
-/

@[expose] public section

open MeasureTheory Complex

namespace QED.ChainProof.RepsInt

open QED.WickModel QED.ChainProof.Enum QED.TwoLoop.Routing QED.TwoLoop.Enumeration
  QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge

/-! ### The lines of `repBD s` -/

section Lines

variable (s : Fin 2)

/-- The fermion line `0 → 1`, a chord. -/
def bdF1 : FermionLine (repBD s) := ⟨fv kBD 1, by revert s; decide +kernel⟩
/-- The fermion line `1 → 2`. -/
def bdF2 : FermionLine (repBD s) := ⟨fv kBD 2, by revert s; decide +kernel⟩
/-- The loop line `4 → 3`, a chord. -/
def bdF3 : FermionLine (repBD s) := ⟨fv kBD 3, by revert s; decide +kernel⟩
/-- The loop line `3 → 4`. -/
def bdF4 : FermionLine (repBD s) := ⟨fv kBD 4, by revert s; decide +kernel⟩
/-- The photon line `2 → 3` (from `a` to the loop). -/
def bdGA : PhotonLine (repBD s) := ⟨pg kBD 2, by revert s; decide +kernel⟩
/-- The photon line `4 → 5` (from the loop to the field `s` of the `photonCt` vertex). -/
def bdGB : PhotonLine (repBD s) := ⟨pg kBD 4, by revert s; decide +kernel⟩
/-- The photon line `0 → 5` (from `c` to the field `s.rev` of the `photonCt` vertex). -/
def bdGC : PhotonLine (repBD s) := ⟨pg kBD 0, by revert s; decide +kernel⟩

theorem bd_fermionLine_cases : ∀ s (f : FermionLine (repBD s)),
    f = bdF1 s ∨ f = bdF2 s ∨ f = bdF3 s ∨ f = bdF4 s := by
  decide +kernel

theorem bd_photonLine_cases : ∀ s (g : PhotonLine (repBD s)),
    g = bdGA s ∨ g = bdGB s ∨ g = bdGC s := by
  decide +kernel

theorem bd_fermion_ne : [bdF1 s, bdF2 s, bdF3 s, bdF4 s].Nodup := by
  simp [bdF1, bdF2, bdF3, bdF4, fv]

theorem bd_photon_ne : [bdGA s, bdGB s, bdGC s].Nodup := by
  simp [bdGA, bdGB, bdGC, pg]

theorem bd_isChord_iff : ∀ s (g : Line (repBD s)),
    IsChord g ↔ g = .inl (bdF1 s) ∨ g = .inl (bdF3 s) := by
  decide +kernel

theorem bd_ends : ∀ s,
    (Line.ends (.inl (bdF1 s) : Line (repBD s))) = (0, 1) ∧
    (Line.ends (.inl (bdF2 s) : Line (repBD s))) = (1, 2) ∧
    (Line.ends (.inl (bdF3 s) : Line (repBD s))) = (4, 3) ∧
    (Line.ends (.inl (bdF4 s) : Line (repBD s))) = (3, 4) ∧
    (Line.ends (.inr (bdGA s) : Line (repBD s))) = (2, 3) ∧
    (Line.ends (.inr (bdGB s) : Line (repBD s))) = (4, 5) ∧
    (Line.ends (.inr (bdGC s) : Line (repBD s))) = (0, 5) := by
  decide +kernel

theorem bd_tails : ∀ s, (bdF1 s).tail = fv kBD 0 ∧ (bdF2 s).tail = fv kBD 1 ∧
    (bdF3 s).tail = fv kBD 4 ∧ (bdF4 s).tail = fv kBD 3 ∧
    (bdGA s).head = pg kBD 3 ∧ (bdGB s).head = pc kBD 5 s ∧ (bdGC s).head = pc kBD 5 s.rev := by
  decide +kernel

theorem bd_ext : ∀ s (v : Fin 6),
    ((∃ t : Wick.FermionVertex kBD, t.1 = v ∧ (repBD s).1.1 (.inr t) = .inl 0) ↔ v = 0) ∧
    ((∃ a : Wick.PhotonSlot kBD, a.1 = v ∧ (repBD s).1.2 (.inl 0) = .inr a) ↔ v = 1) ∧
    ((∃ t : Wick.FermionVertex kBD, t.1 = v ∧ (repBD s).1.1 (.inl 0) = .inr t) ↔ v = 2) := by
  decide +kernel

theorem bd_sum_line {M : Type*} [AddCommMonoid M] (g : Line (repBD s) → M) :
    ∑ f, g f = g (.inl (bdF1 s)) + g (.inl (bdF2 s)) + g (.inl (bdF3 s)) + g (.inl (bdF4 s)) +
      (g (.inr (bdGA s)) + g (.inr (bdGB s)) + g (.inr (bdGC s))) := by
  have hf := bd_fermion_ne s
  have hg := bd_photon_ne s
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hf hg
  obtain ⟨⟨f12, f13, f14⟩, ⟨f23, f24⟩, f34⟩ := hf
  obtain ⟨⟨gab, gac⟩, gbc⟩ := hg
  rw [Fintype.sum_sum_type, sum_eq_of_four f12 f13 f14 f23 f24 f34 (bd_fermionLine_cases s),
    sum_eq_of_three gab gac gbc (bd_photonLine_cases s)]

end Lines

/-! ### The nested routing -/

section Routing

variable (s : Fin 2)

/-- **The nested routing** of `repBD s` (the table of the module docstring). -/
def bdMom (p kext q k : Fin 4 → ℝ) (f : Line (repBD s)) : Fin 4 → ℝ :=
  match f with
  | .inl f => if f = bdF1 s then p - k else if f = bdF2 s then p + kext - k
      else if f = bdF3 s then q + k else q
  | .inr g => if g = bdGC s then k else -k

theorem bdMom_apply (p kext q k : Fin 4 → ℝ) :
    bdMom s p kext q k (.inl (bdF1 s)) = p - k ∧ bdMom s p kext q k (.inl (bdF2 s)) = p + kext - k ∧
    bdMom s p kext q k (.inl (bdF3 s)) = q + k ∧ bdMom s p kext q k (.inl (bdF4 s)) = q ∧
    bdMom s p kext q k (.inr (bdGA s)) = -k ∧ bdMom s p kext q k (.inr (bdGB s)) = -k ∧
    bdMom s p kext q k (.inr (bdGC s)) = k := by
  have hf := bd_fermion_ne s
  have hg := bd_photon_ne s
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hf hg
  obtain ⟨⟨f12, f13, f14⟩, ⟨f23, f24⟩, f34⟩ := hf
  obtain ⟨⟨gab, gac⟩, gbc⟩ := hg
  simp [bdMom, Ne.symm f12, Ne.symm f13, Ne.symm f14, Ne.symm f23, Ne.symm f24, Ne.symm f34,
    gac, gbc]

theorem bdMom_isConserved {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (q k : Fin 4 → ℝ) :
    IsConserved (repBD s) pOut pIn kIn (bdMom s (pIn 0) (kIn 0) q k) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := bd_ends s
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := bdMom_apply s (pIn 0) (kIn 0) q k
  intro v
  rw [inflow, bd_sum_line, externalMomentum_one_one, hmom]
  obtain ⟨x1, x2, x3⟩ := bd_ext s v
  simp only [e1, e2, e3, e4, e5, e6, e7, x1, x2, x3, m1, m2, m3, m4, m5, m6, m7]
  funext μ
  fin_cases v <;> first | (simp; done) | (simp; ring)

theorem bd_card_chordsBelow :
    (Finset.univ.filter fun g : Line (repBD s) =>
      IsChord g ∧ g.label < (Line.label (.inl (bdF1 s) : Line (repBD s)))).card = 0 ∧
    (Finset.univ.filter fun g : Line (repBD s) =>
      IsChord g ∧ g.label < (Line.label (.inl (bdF3 s) : Line (repBD s)))).card = 1 := by
  have l1 : (Line.label (.inl (bdF1 s) : Line (repBD s))) = 1 := rfl
  have l3 : (Line.label (.inl (bdF3 s) : Line (repBD s))) = 3 := rfl
  constructor
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hg, hl⟩
    rcases (bd_isChord_iff s g).mp hg with rfl | rfl
    · simp [l1] at hl
    · simp [l1, l3] at hl
  · rw [Finset.card_eq_one]
    refine ⟨.inl (bdF1 s), Finset.ext fun g => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun ⟨hg, hl⟩ => ?_, fun h => ?_⟩
    · rcases (bd_isChord_iff s g).mp hg with rfl | rfl
      · rfl
      · simp at hl
    · subst h
      exact ⟨(bd_isChord_iff s _).mpr (Or.inl rfl), by simp [l1, l3]⟩

/-- The cardinality of a filter of `univ` does not depend on the instances. -/
theorem card_filter_univ_irrel {α : Type*} (p : α → Prop) (fi fi' : Fintype α)
    (d d' : DecidablePred p) :
    (@Finset.filter α p d (@Finset.univ α fi)).card =
      (@Finset.filter α p d' (@Finset.univ α fi')).card := by
  cases Subsingleton.elim fi fi'
  cases Subsingleton.elim d d'
  rfl

theorem bd_chordMomentum (ℓ : Fin 2 → Fin 4 → ℝ) :
    chordMomentum ℓ (.inl (bdF1 s) : Line (repBD s)) = ℓ 0 ∧
      chordMomentum ℓ (.inl (bdF3 s) : Line (repBD s)) = ℓ 1 := by
  obtain ⟨h0, h1⟩ := bd_card_chordsBelow s
  have e : ∀ (f : Line (repBD s)) (i : Fin 2), (Finset.univ.filter fun g : Line (repBD s) =>
      IsChord g ∧ g.label < f.label).card = i → chordMomentum ℓ f = ℓ i := by
    intro f i hi
    have e := card_filter_univ_irrel (fun g : Line (repBD s) => IsChord g ∧ g.label < f.label)
    unfold chordMomentum
    split_ifs with h
    · revert h
      rw [e (d' := fun g => instDecidableAnd) (fi' := inferInstance), hi]
      intro h
      rfl
    · rw [e (d' := fun g => instDecidableAnd) (fi' := inferInstance), hi] at h
      exact absurd i.2 h
  exact ⟨e _ 0 h0, e _ 1 h1⟩

/-- **The frozen routing in nested form**: the routing (T₄) of `repBD s` at `ℓ` is the nested
routing at `q = ℓ₀ + ℓ₁ - p`, `k = p - ℓ₀`. -/
theorem lineMomentum₂_repBD {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum₂ (repBD s) pOut pIn kIn ℓ =
      bdMom s (pIn 0) (kIn 0) (ℓ 0 + ℓ 1 - pIn 0) (pIn 0 - ℓ 0) := by
  funext f
  refine (eq_lineMomentum₂_of_isConserved (bdMom_isConserved s hmom _ _) (fun g hg => ?_) f).symm
  obtain ⟨c0, c1⟩ := bd_chordMomentum s ℓ
  obtain ⟨n1, -, n3, -⟩ := bdMom_apply s (pIn 0) (kIn 0) (ℓ 0 + ℓ 1 - pIn 0) (pIn 0 - ℓ 0)
  rcases (bd_isChord_iff s g).mp hg with rfl | rfl
  · rw [n1, c0, sub_sub_cancel]
  · rw [n3, c1]
    abel

end Routing

/-! ### The flavour sum and the amplitude -/

section Amplitude

variable (s : Fin 2)

/-- The fermion fields of the loop `3 ⇄ 4`. -/
def bdL (t : Wick.FermionVertex kBD) : Bool := decide (3 ≤ t.1.val)

theorem bdL_gauge : ∀ t, bdL t = true → kBD t.1 = .gauge := by decide

theorem bd_pow_four : ∀ s, (repBD s).1.1 ^ 4 = 1 := by decide +kernel

theorem bd_preserves : ∀ s f, Preserves (repBD s) (flavL bdL bdL_gauge f) := by
  unfold Preserves
  decide +kernel

open scoped Classical in
/-- **The regulated amplitude of `repBD s`** is the sum over the loop flavour. -/
theorem regulatedAmplitude₂_repBD (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (k : Line (repBD s) → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P (repBD s) pIn kIn k αOut βIn μ =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude₂ P (repBD s) (flavL bdL bdL_gauge f) pIn kIn k αOut βIn μ := by
  have hsc := fun x y => QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (n := 4) (by norm_num)
    (bd_pow_four s) x y
  have hin : ∀ s t, bdL t = true → ∃ i : Fin 4, ((repBD s).1.1 ^ (i : ℕ)) (.inr t) =
      .inr (fv kBD 3) := by decide +kernel
  have hout : ∀ s (x : Fin 1 ⊕ Wick.FermionVertex kBD),
      (∀ t, x = .inr t → bdL t = false) → ∃ i : Fin 4, ((repBD s).1.1 ^ (i : ℕ)) x = .inl 0 := by
    decide +kernel
  have hsep : ∀ s, ¬ ∃ i : Fin 4, ((repBD s).1.1 ^ (i : ℕ)) (.inl 0) = .inr (fv kBD 3) := by
    decide +kernel
  exact regulatedAmplitude₂_eq_sum_loopFlavour P (repBD s) bdL bdL_gauge (fv kBD 3) rfl
    (bd_preserves s) (fun t ht => (hsc _ _).mpr (hin s t ht))
    (fun x hx => (hsc _ _).mpr (hout s x hx)) (fun h => hsep s ((hsc _ _).mp h)) pIn kIn k
    αOut βIn μ

theorem bd_cond (α β : Wick.FermionVertex kBD → Fin 4) (lor : Wick.PhotonSlot kBD → Fin 4)
    (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, (repBD s).1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, (repBD s).1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, (repBD s).1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (pg kBD 1) = μ 0 ∧ (α (fv kBD 2) = αOut 0 ∧ β (fv kBD 0) = βIn 0) := by
  have h1 : ∀ s t, (repBD s).1.1 (.inl 0) = .inr t ↔ t = fv kBD 2 := by decide +kernel
  have h2 : ∀ s t, (repBD s).1.1 (.inr t) = .inl 0 ↔ t = fv kBD 0 := by decide +kernel
  have h3 : ∀ s a, (repBD s).1.2 (.inl 0) = .inr a ↔ a = pg kBD 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

/-- In the nested routing the momentum entering the field `0` of the `photonCt` vertex is `±k`. -/
theorem bd_photonMomentum (kIn : Fin 1 → Fin 4 → ℝ) (p kext q k : Fin 4 → ℝ) :
    photonMomentum₂ (repBD s) kIn (bdMom s p kext q k) ⟨5, ⟨0, by decide⟩⟩ = k ∨
      photonMomentum₂ (repBD s) kIn (bdMom s p kext q k) ⟨5, ⟨0, by decide⟩⟩ = -k := by
  obtain ⟨-, -, -, -, m5, m6, m7⟩ := bdMom_apply s p kext q k
  obtain ⟨-, -, -, -, t5, t6, t7⟩ := bd_tails s
  have hext : ∀ s, ¬ (repBD s).1.2 (.inl 0) = .inr ⟨5, ⟨0, by decide⟩⟩ := by decide +kernel
  have hg := bd_photon_ne s
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hg
  obtain ⟨⟨gab, gac⟩, gbc⟩ := hg
  have hA1 : (bdGA s).1 = pg kBD 2 := rfl
  have hB1 : (bdGB s).1 = pg kBD 4 := rfl
  have hC1 : (bdGC s).1 = pg kBD 0 := rfl
  unfold photonMomentum₂
  rw [Fin.sum_univ_one, ite_eq_right (hext s),
    sum_eq_of_three gab gac gbc (bd_photonLine_cases s), t5, t6, t7, hA1, hB1, hC1, m5, m6, m7]
  fin_cases s <;> simp +decide

theorem bd_trace_rotate (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (A * B * C * D) = Matrix.trace (C * D * A * B) := by
  rw [show A * B * C * D = (A * B) * (C * D) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **The amplitude of `repBD s` for the loop flavour `f`** in the nested routing: the open-line
chain, the photon propagator from `a` to the loop, the loop trace of flavour `f`, and the singly
inserted photon line from the loop to `c`. -/
theorem bd_amplitude (P : Params) (f : Fin 3) (pIn kIn : Fin 1 → Fin 4 → ℝ) (q k : Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P (repBD s) (flavL bdL bdL_gauge f) pIn kIn
        (bdMom s (pIn 0) (kIn 0) q k) αOut βIn μ =
      (I * P.e) ^ 5 * (1 / I) ^ 6 * ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4, ∑ l4 : Fin 4,
        QED.TwoLoop.NestedVP.outerChain P (pIn 0) (kIn 0) k (μ 0) l0 l2 (αOut 0) (βIn 0) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k l2 l3 *
          Matrix.trace (Dirac.gamma l3 * QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k) *
            Dirac.gamma l4 * QED.OneLoop.electronPropagator (P.mass f) P.ε q) *
          photonInsertion P.δ₃ P.mγ P.Λ P.ε k l4 l0 := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := bdMom_apply s (pIn 0) (kIn 0) q k
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := bd_tails s
  have hct : ∀ (α β : Wick.FermionVertex kBD → Fin 4) (lor : Wick.PhotonSlot kBD → Fin 4),
      Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
          (psiMomentum₂ (repBD s) pIn (bdMom s (pIn 0) (kIn 0) q k))
          (photonMomentum₂ (repBD s) kIn (bdMom s (pIn 0) (kIn 0) q k)) 5 =
        photonCtFactor P.δ₃ k (lor ⟨5, ⟨0, by decide⟩⟩) (lor ⟨5, ⟨1, by decide⟩⟩) := by
    intro α β lor
    rw [QED.TwoLoop.Relabel.vertexFactor_eq_of_photonCt _ _ _ _ _ _ _ _ _ _ _
      (show kBD 5 = .photonCt from rfl)]
    rcases bd_photonMomentum s kIn (pIn 0) (kIn 0) q k with e | e
    · rw [e]; rfl
    · rw [e, ← photonCtFactor_neg]; rfl
  have hfl : ∀ t, (flavL bdL bdL_gauge f).1 t = if bdL t then f else 0 := fun _ => rfl
  have hf := bd_fermion_ne s
  have hg := bd_photon_ne s
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hf hg
  obtain ⟨⟨f12, f13, f14⟩, ⟨f23, f24⟩, f34⟩ := hf
  obtain ⟨⟨gab, gac⟩, gbc⟩ := hg
  have hprodf : ∀ (g : FermionLine (repBD s) → ℂ),
      ∏ x, g x = g (bdF1 s) * g (bdF2 s) * g (bdF3 s) * g (bdF4 s) := by
    intro g
    have : (Finset.univ : Finset (FermionLine (repBD s))) = {bdF1 s, bdF2 s, bdF3 s, bdF4 s} := by
      ext x; simpa using bd_fermionLine_cases s x
    rw [this, Finset.prod_insert (by simp [f12, f13, f14]),
      Finset.prod_insert (by simp [f23, f24]), Finset.prod_pair f34]
    ring
  unfold contractionAmplitude₂
  rw [show (∑ α : Wick.FermionVertex kBD → Fin 4, ∑ β : Wick.FermionVertex kBD → Fin 4,
      ∑ lor : Wick.PhotonSlot kBD → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : Wick.PhotonSlot kBD → Fin 4,
    (if lor (pg kBD 1) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) ^ 5 * (1 / I) ^ 7 *
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k (lor (pg kBD 2)) (lor (pg kBD 3)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k (lor (pg kBD 4)) (lor (pc kBD 5 s)) *
          photonCtFactor P.δ₃ k (lor ⟨5, ⟨0, by decide⟩⟩) (lor ⟨5, ⟨1, by decide⟩⟩) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k (lor (pg kBD 0)) (lor (pc kBD 5 s.rev))) *
        (((Dirac.gamma (lor (pg kBD 2)) *
            QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + kIn 0 - k) *
          Dirac.gamma (lor (pg kBD 1)) * QED.OneLoop.electronPropagator P.m P.ε (pIn 0 - k) *
          Dirac.gamma (lor (pg kBD 0))) (αOut 0) (βIn 0) *
        Matrix.trace (Dirac.gamma (lor (pg kBD 3)) *
            QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k) *
          Dirac.gamma (lor (pg kBD 4)) * QED.OneLoop.electronPropagator (P.mass f) P.ε q)))) = _)
  · have hsp := sum_spinor_chain3_loop2 (x₁ := fv kBD 2) (x₂ := fv kBD 1) (x₃ := fv kBD 0)
      (y₁ := fv kBD 3) (y₂ := fv kBD 4) (by decide) (by decide +kernel)
      (Dirac.gamma (lor (pg kBD 2))) (Dirac.gamma (lor (pg kBD 1))) (Dirac.gamma (lor (pg kBD 0)))
      (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + kIn 0 - k))
      (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 - k))
      (Dirac.gamma (lor (pg kBD 3))) (Dirac.gamma (lor (pg kBD 4)))
      (QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k))
      (QED.OneLoop.electronPropagator (P.mass f) P.ε q) (αOut 0) (βIn 0)
    rw [← hsp, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [bd_cond, Fin.prod_univ_six, hprodf,
      prod_eq_of_three' gab gac gbc (bd_photonLine_cases s),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kBD 0 = .gauge from rfl),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kBD 1 = .gauge from rfl),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kBD 2 = .gauge from rfl),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kBD 3 = .gauge from rfl),
      QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _
        (show kBD 4 = .gauge from rfl),
      hct, t1, t2, t3, t4, t5, t6, t7, m1, m2, m3, m4, m5, m6, m7,
      photonPropagator_neg', ite_and_eq_mul]
    simp only [show (bdF1 s).1 = fv kBD 1 from rfl, show (bdF2 s).1 = fv kBD 2 from rfl,
      show (bdF3 s).1 = fv kBD 3 from rfl, show (bdF4 s).1 = fv kBD 4 from rfl,
      show (bdGA s).1 = pg kBD 2 from rfl, show (bdGB s).1 = pg kBD 4 from rfl,
      show (bdGC s).1 = pg kBD 0 from rfl, hfl, bdL, fv, pg]
    simp only [Params.mass, show decide (3 ≤ ((3 : Fin 6) : ℕ)) = true from rfl,
      show decide (3 ≤ ((4 : Fin 6) : ℕ)) = true from rfl,
      show decide (3 ≤ ((1 : Fin 6) : ℕ)) = false from rfl,
      show decide (3 ≤ ((2 : Fin 6) : ℕ)) = false from rfl, ite_true, Bool.false_eq_true,
      ite_false, Matrix.cons_val_zero]
    ring
  · have hd : ∀ s, [pg kBD 0, pg kBD 1, pg kBD 2, pg kBD 3, pg kBD 4, pc kBD 5 s,
        pc kBD 5 s.rev].Nodup := by decide +kernel
    have hX : ∀ s (x : Wick.PhotonSlot kBD), x = pg kBD 0 ∨ x = pg kBD 1 ∨ x = pg kBD 2 ∨
        x = pg kBD 3 ∨ x = pg kBD 4 ∨ x = pc kBD 5 s ∨ x = pc kBD 5 s.rev := by
      decide +kernel
    rw [sum_pi_seven (hd s) (hX s)]
    simp only [photonInsertion, QED.TwoLoop.NestedVP.outerChain, Finset.mul_sum]
    fin_cases s <;>
    · simp +decide only [ite_true, ite_false, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
        Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ]
      refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
        Finset.sum_congr rfl fun l3 _ => Finset.sum_congr rfl fun l4 _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      try simp only [photonCtFactor_comm P.δ₃ k b a]
      ring

end Amplitude

/-! ### Transverse and longitudinal parts -/

section Split

/-- The longitudinal part of the amplitude of `repBD s` for the loop flavour `f`: the
`photonCt` insertion replaced by `d(k)² k_ν k_ρ`. -/
noncomputable def bdLong (P : Params) (f : Fin 3) (p kext q k : Fin 4 → ℝ) (α β μ : Fin 4) : ℂ :=
  (I * P.e) ^ 5 * (1 / I) ^ 6 * ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4, ∑ l4 : Fin 4,
    QED.TwoLoop.NestedVP.outerChain P p kext k μ l0 l2 α β *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k l2 l3 *
      Matrix.trace (Dirac.gamma l3 * QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k) *
        Dirac.gamma l4 * QED.OneLoop.electronPropagator (P.mass f) P.ε q) *
      longitudinalPhoton P.mγ P.Λ P.ε k l4 l0

/-- **The split of the amplitude of `repBD s`**: the transverse part of the `photonCt` insertion
gives `-(δ₃/2) k² d(k)` times the amplitude of the vacuum-polarization class `VP` (same nested
momenta), and the longitudinal part gives `(δ₃/2) bdLong`. -/
theorem bd_amplitude_split (s : Fin 2) (P : Params) (f : Fin 3) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (q k : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P (repBD s) (flavL bdL bdL_gauge f) pIn kIn
        (bdMom s (pIn 0) (kIn 0) q k) αOut βIn μ =
      (-(P.δ₃ / 2 : ℂ) * (((Minkowski.dot k k : ℝ) : ℂ) * photonScalar P.mγ P.Λ P.ε k)) *
          contractionAmplitude₂ P QED.TwoLoop.NestedVP.cV (QED.TwoLoop.NestedVP.flavV f) pIn kIn
            (QED.TwoLoop.NestedVP.nestedMom (pIn 0) (kIn 0) q k) αOut βIn μ +
        (P.δ₃ / 2 : ℂ) * bdLong P f (pIn 0) (kIn 0) q k (αOut 0) (βIn 0) (μ 0) := by
  rw [bd_amplitude, QED.TwoLoop.NestedVP.contractionAmplitude₂_flavV, bdLong]
  simp only [photonInsertion_eq, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have hneg : photonScalar P.mγ P.Λ P.ε (-k) = photonScalar P.mγ P.Λ P.ε k := by
      simp [photonScalar, Minkowski.dot]
    simp only [transversePhoton, photonPropagator_eq_metric_mul, hneg,
      bd_trace_rotate (Dirac.gamma x) (QED.OneLoop.electronPropagator (P.mass f) P.ε q)]
    rw [QED.Minkowski.metric_symm l0 x]
    ring
  · refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring

end Split

/-! ### The longitudinal part: Ward identity and flavour sum -/

section Longitudinal

/-- The loop trace contracted with the photon momentum, by the Ward identity of the loop. -/
theorem sum_trace_lower_eq (M : ℝ) {ε : ℝ} (hε : ε ≠ 0) (q k : Fin 4 → ℝ) (σ : Fin 4) :
    ∑ l4 : Fin 4, Matrix.trace (Dirac.gamma σ * QED.OneLoop.electronPropagator M ε (q + k) *
        Dirac.gamma l4 * QED.OneLoop.electronPropagator M ε q) * ((Minkowski.lower k l4 : ℝ) : ℂ) =
      4 * ((q σ : ℝ) : ℂ) * ((propDenom M ε q)⁻¹ +
          (ε : ℂ) * I * ((propDenom M ε (q + k))⁻¹ * (propDenom M ε q)⁻¹)) -
        4 * (((q + k) σ : ℝ) : ℂ) * ((propDenom M ε (q + k))⁻¹ +
          (ε : ℂ) * I * ((propDenom M ε (q + k))⁻¹ * (propDenom M ε q)⁻¹)) := by
  have hslash : ∑ l4 : Fin 4, Matrix.trace (Dirac.gamma σ *
        QED.OneLoop.electronPropagator M ε (q + k) * Dirac.gamma l4 *
          QED.OneLoop.electronPropagator M ε q) * ((Minkowski.lower k l4 : ℝ) : ℂ) =
      Matrix.trace (Dirac.gamma σ * QED.OneLoop.electronPropagator M ε (q + k) *
        Dirac.slash k * QED.OneLoop.electronPropagator M ε q) := by
    simp only [Dirac.slash, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hk : k = (q + k) - q := by abel
  have hD : ∀ X : Fin 4 → ℝ, (((Minkowski.dot X X + M ^ 2 : ℝ) : ℂ)) =
      propDenom M ε X + (ε : ℂ) * I := fun X => by simp only [propDenom]; ring
  have hP := propDenom_ne_zero (M := M) hε (q + k)
  have hQ := propDenom_ne_zero (M := M) hε q
  rw [hslash, QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul,
    QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [show Dirac.gamma σ * electronNumerator M (q + k) * Dirac.slash k * electronNumerator M q =
      Dirac.gamma σ * (electronNumerator M (q + k) * Dirac.slash ((q + k) - q) *
        electronNumerator M q) by rw [← hk]; simp only [Matrix.mul_assoc],
    trace_ward, hD, hD]
  field_simp

end Longitudinal

section LongSum

variable (P : Params)

/-- The flavour sum of the contracted loop trace, under the Pauli–Villars conditions. -/
theorem bd_flavour_W {ε : ℝ} (hε : ε ≠ 0) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (q k : Fin 4 → ℝ) (σ : Fin 4) :
    ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
      (4 * ((q σ : ℝ) : ℂ) * ((propDenom (P.mass f) ε q)⁻¹ +
          (ε : ℂ) * I * ((propDenom (P.mass f) ε (q + k))⁻¹ * (propDenom (P.mass f) ε q)⁻¹)) -
        4 * (((q + k) σ : ℝ) : ℂ) * ((propDenom (P.mass f) ε (q + k))⁻¹ +
          (ε : ℂ) * I * ((propDenom (P.mass f) ε (q + k))⁻¹ * (propDenom (P.mass f) ε q)⁻¹))) =
      4 * vpBubbleCoeff P * (((q σ : ℝ) : ℂ) *
          ((propDenom P.m ε q)⁻¹ * (propDenom P.M₁ ε q)⁻¹ * (propDenom P.M₂ ε q)⁻¹) -
        (((q + k) σ : ℝ) : ℂ) * ((propDenom P.m ε (q + k))⁻¹ * (propDenom P.M₁ ε (q + k))⁻¹ *
          (propDenom P.M₂ ε (q + k))⁻¹) -
        (ε : ℂ) * I * ((k σ : ℝ) : ℂ) *
          ((propDenom P.m ε (q + k))⁻¹ * (propDenom P.m ε q)⁻¹ * (propDenom P.M₁ ε q)⁻¹ *
              (propDenom P.M₂ ε q)⁻¹ +
            (propDenom P.m ε (q + k))⁻¹ * (propDenom P.M₁ ε (q + k))⁻¹ * (propDenom P.M₁ ε q)⁻¹ *
              (propDenom P.M₂ ε q)⁻¹ +
            (propDenom P.m ε (q + k))⁻¹ * (propDenom P.M₁ ε (q + k))⁻¹ *
              (propDenom P.M₂ ε (q + k))⁻¹ * (propDenom P.M₂ ε q)⁻¹)) := by
  have h1 := flavourSum_single_propDenom hε q hc₁ hc₂
  have h2 := flavourSum_single_propDenom hε (q + k) hc₁ hc₂
  have h3 := flavourSum_propDenom hε (q + k) q hc₁ hc₂ 1 0
  simp only [mul_zero, add_zero, sub_zero, zero_mul] at h3
  have hqk : (((q + k) σ : ℝ) : ℂ) = ((q σ : ℝ) : ℂ) + ((k σ : ℝ) : ℂ) := by
    simp only [Pi.add_apply, ofReal_add]
  have c0 : P.loopCoeff 0 = 1 := rfl
  have c1 : P.loopCoeff 1 = P.c₁ := rfl
  have c2 : P.loopCoeff 2 = P.c₂ := rfl
  have n0 : P.mass 0 = P.m := rfl
  have n1 : P.mass 1 = P.M₁ := rfl
  have n2 : P.mass 2 = P.M₂ := rfl
  simp only [Fin.sum_univ_three, c0, c1, c2, n0, n1, n2, ofReal_one, one_mul, vpBubbleCoeff]
  rw [hqk]
  linear_combination (4 * ((q σ : ℝ) : ℂ)) * h1 -
    (4 * (((q σ : ℝ) : ℂ) + ((k σ : ℝ) : ℂ))) * h2 -
    (4 * (ε : ℂ) * I * ((k σ : ℝ) : ℂ)) * h3

/-- The numerator of the open-line chain `γ^{l₂} (m - (p + k_ext - k)̸) γ^μ (m - (p - k)̸) γ^{l₀}`. -/
noncomputable def bdON (p kext k : Fin 4 → ℝ) (μ l0 l2 α β : Fin 4) : ℂ :=
  (Dirac.gamma l2 * electronNumerator P.m (p + kext - k) * Dirac.gamma μ *
    electronNumerator P.m (p - k) * Dirac.gamma l0) α β

/-- The numerators of the longitudinal part: the open-line numerator contracted with `k` at `c`
and with `v` at `a`: `∑ ON^{l₀ l₂} g_{l₂ l₃} k_{l₀} v^{l₃}`. -/
noncomputable def bdN (p kext : Fin 4 → ℝ) (μ α β : Fin 4) (k v : Fin 4 → ℝ) : ℂ :=
  ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4, bdON P p kext k μ l0 l2 α β *
    ((Minkowski.metric l2 l3 : ℝ) : ℂ) * ((Minkowski.lower k l0 : ℝ) : ℂ) * ((v l3 : ℝ) : ℂ)

/-- **The flavour-summed longitudinal part of `repBD`** as three products of a numerator of
degree four and propagator denominators. -/
theorem bdLong_sum (hε : P.ε ≠ 0) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (p kext q k : Fin 4 → ℝ)
    (α β μ : Fin 4) :
    ∑ f : Fin 3, (P.loopCoeff f : ℂ) * bdLong P f p kext q k α β μ =
      (I * P.e) ^ 5 * (1 / I) ^ 6 * (((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) ^ 3 *
        ((propDenom P.mγ P.ε k)⁻¹ * (propDenom P.Λ P.ε k)⁻¹) ^ 3 *
        ((propDenom P.m P.ε (p + kext - k))⁻¹ * (propDenom P.m P.ε (p - k))⁻¹) *
        (4 * vpBubbleCoeff P) *
        (bdN P p kext μ α β k q *
            ((propDenom P.m P.ε q)⁻¹ * (propDenom P.M₁ P.ε q)⁻¹ * (propDenom P.M₂ P.ε q)⁻¹) -
          bdN P p kext μ α β k (q + k) * ((propDenom P.m P.ε (q + k))⁻¹ *
            (propDenom P.M₁ P.ε (q + k))⁻¹ * (propDenom P.M₂ P.ε (q + k))⁻¹) -
          (P.ε : ℂ) * I * bdN P p kext μ α β k k *
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
  set Y : Fin 4 → Fin 4 → Fin 4 → ℂ := fun l0 l2 l3 => (I * P.e) ^ 5 * (1 / I) ^ 6 *
    ((propDenom P.m P.ε (p + kext - k))⁻¹ * (propDenom P.m P.ε (p - k))⁻¹) *
    bdON P p kext k μ l0 l2 α β * ((Minkowski.metric l2 l3 : ℝ) : ℂ) * d ^ 3 *
    ((Minkowski.lower k l0 : ℝ) : ℂ) with hY
  -- step A: the contraction with `k` at the loop
  have hA : ∀ f, bdLong P f p kext q k α β μ = ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4,
      Y l0 l2 l3 * ∑ l4 : Fin 4, Matrix.trace (Dirac.gamma l3 *
        QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k) * Dirac.gamma l4 *
          QED.OneLoop.electronPropagator (P.mass f) P.ε q) * ((Minkowski.lower k l4 : ℝ) : ℂ) := by
    intro f
    simp only [bdLong, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
      Finset.sum_congr rfl fun l3 _ => Finset.sum_congr rfl fun l4 _ => ?_
    simp only [hY, QED.TwoLoop.NestedVP.outerChain, bdON, longitudinalPhoton,
      photonPropagator_eq_metric_mul, QED.TwoLoop.CountertermLimit.electronPropagator_eq_smul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, ← hd]
    ring
  simp only [hA, sum_trace_lower_eq _ hε, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun l0 _ => ?_).trans (?_ : ∑ l0 : Fin 4, ∑ l2 : Fin 4,
    ∑ l3 : Fin 4, Y l0 l2 l3 * (4 * vpBubbleCoeff P * (((q l3 : ℝ) : ℂ) *
          ((propDenom P.m P.ε q)⁻¹ * (propDenom P.M₁ P.ε q)⁻¹ * (propDenom P.M₂ P.ε q)⁻¹) -
        (((q + k) l3 : ℝ) : ℂ) * ((propDenom P.m P.ε (q + k))⁻¹ * (propDenom P.M₁ P.ε (q + k))⁻¹ *
          (propDenom P.M₂ P.ε (q + k))⁻¹) -
        (P.ε : ℂ) * I * ((k l3 : ℝ) : ℂ) *
          ((propDenom P.m P.ε (q + k))⁻¹ * (propDenom P.m P.ε q)⁻¹ * (propDenom P.M₁ P.ε q)⁻¹ *
              (propDenom P.M₂ P.ε q)⁻¹ +
            (propDenom P.m P.ε (q + k))⁻¹ * (propDenom P.M₁ P.ε (q + k))⁻¹ *
              (propDenom P.M₁ P.ε q)⁻¹ * (propDenom P.M₂ P.ε q)⁻¹ +
            (propDenom P.m P.ε (q + k))⁻¹ * (propDenom P.M₁ P.ε (q + k))⁻¹ *
              (propDenom P.M₂ P.ε (q + k))⁻¹ * (propDenom P.M₂ P.ε q)⁻¹))) = _)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l2 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l3 _ => ?_
    rw [← bd_flavour_W P hε hc₁ hc₂ q k l3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  · simp only [bdN, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ =>
      Finset.sum_congr rfl fun l3 _ => ?_
    simp only [hY, hdd, Pi.add_apply, ofReal_add]
    ring

end LongSum

end QED.ChainProof.RepsInt

end
