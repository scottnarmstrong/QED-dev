/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointClassificationSelfEnergy
public import QED.WickModel.ThreePointClassificationPolarization

/-!
# Three gauge vertices: counting and summing the leg corrections

The connected contractions of three gauge vertices that are not 1PI (packet 6a, decision D-24),
counted and summed:

* Each ordering of the three vertices gives exactly one incoming-leg self-energy loop, one
  outgoing-leg self-energy loop and one vacuum polarization loop (`card_isSEin`,
  `card_isSEout`, `card_isVP`: six of each).
* `sum_nonOnePI_gauge3`: the sum of the signed values of the connected contractions that are not
  1PI is six times the incoming-leg self-energy, plus six times the outgoing-leg self-energy,
  plus six times the photon-leg vacuum polarization; the twelve tadpoles contribute `0`.
-/

@[expose] public section

open Complex

namespace QED.WickModel

open Wick (gauge3)

/-! ### Constructions -/

/-- The fermion pairing of the chain `Ψ̄(y) → c → b → a → Ψ(x)`. -/
def chainPerm (a b c : Fin 3) : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex gauge3) :=
  Equiv.swap (.inl 0) (.inr (Wick.fv c)) * Equiv.swap (.inl 0) (.inr (Wick.fv b)) *
    Equiv.swap (.inl 0) (.inr (Wick.fv a))

/-- The fermion pairing of a vacuum polarization loop: `Ψ̄(y) → a → Ψ(x)` and the closed loop
through `v` and `w`. -/
def vpPerm (a v w : Fin 3) : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex gauge3) :=
  Equiv.swap (.inl 0) (.inr (Wick.fv a)) * Equiv.swap (.inr (Wick.fv v)) (.inr (Wick.fv w))

/-- The photon pairing with the external photon at `u`: the photon fields of the other two
vertices are contracted with each other. -/
def photonPairing3 (u : Fin 3) : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot gauge3) :=
  Equiv.swap (.inl 0) (.inr (Wick.ps u)) *
    Equiv.swap (.inr (Wick.ps (u + 1))) (.inr (Wick.ps (u + 2)))

/-- The photon pairing is a fixed-point-free involution. -/
theorem photonPairing3_involutive (u : Fin 3) (x : Fin 1 ⊕ Wick.PhotonSlot gauge3) :
    photonPairing3 u (photonPairing3 u x) = x ∧ photonPairing3 u x ≠ x := by
  have h1 : u ≠ u + 1 := by fin_cases u <;> decide
  have h2 : u + 1 ≠ u + 2 := by fin_cases u <;> decide
  have h3 : u ≠ u + 2 := by fin_cases u <;> decide
  have hne : ∀ s t : Fin 3, s ≠ t → (Sum.inr (Wick.ps s) : Fin 1 ⊕ Wick.PhotonSlot gauge3) ≠
      .inr (Wick.ps t) := fun s t h h' => h (ps3_injective (Sum.inr_injective h'))
  refine swap_mul_swap_involutive Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr (hne _ _ h1)
    (hne _ _ h3) (hne _ _ h2) (fun y => ?_) x
  rcases y with i | s
  · exact Or.inl (by rw [Subsingleton.elim i 0])
  · rcases ps3_cases h1 h2 h3 s with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- The incoming-leg self-energy loop with the chain `Ψ̄(y) → c → b → a → Ψ(x)`. -/
def seInContraction (a b c : Fin 3) : Contraction 1 1 gauge3 :=
  ⟨(chainPerm a b c, photonPairing3 a), photonPairing3_involutive a⟩

/-- The outgoing-leg self-energy loop with the chain `Ψ̄(y) → c → b → a → Ψ(x)`. -/
def seOutContraction (a b c : Fin 3) : Contraction 1 1 gauge3 :=
  ⟨(chainPerm a b c, photonPairing3 c), photonPairing3_involutive c⟩

/-- The vacuum polarization loop with open line through `a`, closed loop through `v` and `w`,
and the external photon at `v`. -/
def vpContraction (a v w : Fin 3) : Contraction 1 1 gauge3 :=
  ⟨(vpPerm a v w, photonPairing3 v), photonPairing3_involutive v⟩

/-- The photon pairing `photonPairing3 u` has the external photon at `u`. -/
theorem photonPairing3_inl (u : Fin 3) : photonPairing3 u (.inl 0) = .inr (Wick.ps u) := by
  rw [photonPairing3, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr
    Sum.inl_ne_inr, Equiv.swap_apply_left]

/-- Two contractions with the external photon at the same vertex have the same photon pairing. -/
theorem snd_eq_of_photonAt {C C' : Contraction 1 1 gauge3} {u : Fin 3} (h : PhotonAt C u)
    (h' : PhotonAt C' u) : C.1.2 = C'.1.2 := by
  have h1 : u ≠ u + 1 := by fin_cases u <;> decide
  have h2 : u + 1 ≠ u + 2 := by fin_cases u <;> decide
  have h3 : u ≠ u + 2 := by fin_cases u <;> decide
  ext1 x
  rcases x with i | s
  · rw [Subsingleton.elim i 0, h, h']
  · rcases ps3_cases h1 h2 h3 s with rfl | rfl | rfl
    · rw [h.snd_self, h'.snd_self]
    · rw [h.snd_pair h1 h2 h3, h'.snd_pair h1 h2 h3]
    · rw [h.snd_pair h3 h2.symm h1, h'.snd_pair h3 h2.symm h1]

/-- The values of the chain pairing. -/
theorem isChain3_of_chainPerm {C : Contraction 1 1 gauge3} {a b c : Fin 3} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) (h : C.1.1 = chainPerm a b c) : IsChain3 C a b c := by
  have hne : ∀ s t : Fin 3, s ≠ t → (Sum.inr (Wick.fv s) : Fin 1 ⊕ Wick.FermionVertex gauge3) ≠
      .inr (Wick.fv t) := fun s t h h' => h (fv3_injective (Sum.inr_injective h'))
  refine ⟨hab, hbc, hac, ?_, ?_, ?_, ?_⟩ <;> rw [h] <;> simp only [chainPerm, Equiv.Perm.mul_apply]
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne a b hab),
      Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne a c hac)]
  · rw [Equiv.swap_apply_right, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne b c hbc)]
  · rw [Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne b a hab.symm), Equiv.swap_apply_right,
      Equiv.swap_apply_left]
  · rw [Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne c a hac.symm),
      Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne c b hbc.symm), Equiv.swap_apply_right]

/-- `seInContraction a b c` is an incoming-leg self-energy loop. -/
theorem isSEin_seInContraction {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    IsSEin (seInContraction a b c) a b c :=
  ⟨isChain3_of_chainPerm hab hbc hac rfl, photonPairing3_inl a⟩

/-- `seOutContraction a b c` is an outgoing-leg self-energy loop. -/
theorem isSEout_seOutContraction {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    IsSEout (seOutContraction a b c) a b c :=
  ⟨isChain3_of_chainPerm hab hbc hac rfl, photonPairing3_inl c⟩

/-- `vpContraction a v w` is a vacuum polarization loop. -/
theorem isVP_vpContraction {a v w : Fin 3} (hav : a ≠ v) (hvw : v ≠ w) (haw : a ≠ w) :
    IsVP (vpContraction a v w) a v w := by
  have hne : ∀ s t : Fin 3, s ≠ t → (Sum.inr (Wick.fv s) : Fin 1 ⊕ Wick.FermionVertex gauge3) ≠
      .inr (Wick.fv t) := fun s t h h' => h (fv3_injective (Sum.inr_injective h'))
  refine ⟨hav, hvw, haw, ?_, ?_, ?_, ?_, photonPairing3_inl v⟩ <;>
    simp only [vpContraction, vpPerm, Equiv.Perm.mul_apply]
  · rw [Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr Sum.inl_ne_inr, Equiv.swap_apply_left]
  · rw [Equiv.swap_apply_of_ne_of_ne (hne a v hav) (hne a w haw), Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne w a haw.symm)]
  · rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (hne v a hav.symm)]

/-! ### Uniqueness -/

/-- The roles of a chain are determined by the contraction. -/
theorem IsChain3.roles_eq {C : Contraction 1 1 gauge3} {a b c a' b' c' : Fin 3}
    (h : IsChain3 C a b c) (h' : IsChain3 C a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have ha : a = a' := fv3_injective (Sum.inr_injective (h.out.symm.trans h'.out))
  subst ha
  have hb : b = b' := fv3_injective (Sum.inr_injective (h.ab.symm.trans h'.ab))
  subst hb
  exact ⟨rfl, rfl, fv3_injective (Sum.inr_injective (h.bc.symm.trans h'.bc))⟩

/-- The roles of a vacuum polarization loop are determined by the contraction. -/
theorem IsVP.roles_eq {C : Contraction 1 1 gauge3} {a v w a' v' w' : Fin 3} (h : IsVP C a v w)
    (h' : IsVP C a' v' w') : a = a' ∧ v = v' ∧ w = w' := by
  have ha : a = a' := fv3_injective (Sum.inr_injective (h.out.symm.trans h'.out))
  have hv : v = v' := ps3_injective (Sum.inr_injective (h.photon.symm.trans h'.photon))
  subst ha hv
  exact ⟨rfl, rfl, fv3_injective (Sum.inr_injective (h.vw.symm.trans h'.vw))⟩

/-- An incoming-leg self-energy loop is the constructed one. -/
theorem IsSEin.eq_seInContraction {C : Contraction 1 1 gauge3} {a b c : Fin 3}
    (h : IsSEin C a b c) : C = seInContraction a b c :=
  Subtype.ext (Prod.ext h.chain.fst_eq
    (snd_eq_of_photonAt h.photon
      (isSEin_seInContraction h.chain.hab h.chain.hbc h.chain.hac).photon))

/-- An outgoing-leg self-energy loop is the constructed one. -/
theorem IsSEout.eq_seOutContraction {C : Contraction 1 1 gauge3} {a b c : Fin 3}
    (h : IsSEout C a b c) : C = seOutContraction a b c :=
  Subtype.ext (Prod.ext h.chain.fst_eq (snd_eq_of_photonAt h.photon
    (isSEout_seOutContraction h.chain.hab h.chain.hbc h.chain.hac).photon))

/-- A vacuum polarization loop is the constructed one. -/
theorem IsVP.eq_vpContraction {C : Contraction 1 1 gauge3} {a v w : Fin 3} (h : IsVP C a v w) :
    C = vpContraction a v w :=
  Subtype.ext (Prod.ext h.fst_eq
    (snd_eq_of_photonAt h.photon (isVP_vpContraction h.hav h.hvw h.haw).photon))

/-! ### Counting -/

/-- The ordered triples of distinct vertices. -/
def distinctTriples : Finset (Fin 3 × Fin 3 × Fin 3) :=
  Finset.univ.filter fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2

/-- There are six orderings of the three vertices. -/
theorem card_distinctTriples : distinctTriples.card = 6 := by
  decide

/-- A set of contractions in bijection with the orderings of the vertices has six elements. -/
theorem card_filter_eq_six {P : Contraction 1 1 gauge3 → Fin 3 → Fin 3 → Fin 3 → Prop}
    [Fintype (Contraction 1 1 gauge3)] [DecidablePred fun C => ∃ a b c, P C a b c]
    (F : Fin 3 → Fin 3 → Fin 3 → Contraction 1 1 gauge3)
    (hF : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → P (F a b c) a b c)
    (hP : ∀ C a b c, P C a b c → a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ C = F a b c)
    (hroles : ∀ C a b c a' b' c', P C a b c → P C a' b' c' → a = a' ∧ b = b' ∧ c = c') :
    ((Finset.univ : Finset (Contraction 1 1 gauge3)).filter fun C => ∃ a b c, P C a b c).card =
      6 := by
  classical
  have himage : ((Finset.univ : Finset (Contraction 1 1 gauge3)).filter
      fun C => ∃ a b c, P C a b c) = distinctTriples.image fun t => F t.1 t.2.1 t.2.2 := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, distinctTriples,
      Prod.exists]
    constructor
    · rintro ⟨a, b, c, h⟩
      obtain ⟨hab, hbc, hac, rfl⟩ := hP C a b c h
      exact ⟨a, b, c, ⟨hab, hbc, hac⟩, rfl⟩
    · rintro ⟨a, b, c, ⟨hab, hbc, hac⟩, rfl⟩
      exact ⟨a, b, c, hF a b c hab hbc hac⟩
  rw [himage, Finset.card_image_of_injOn, card_distinctTriples]
  rintro ⟨a, b, c⟩ ht ⟨a', b', c'⟩ ht' heq
  simp only [distinctTriples, Finset.coe_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq] at ht ht'
  have h := hF a b c ht.1 ht.2.1 ht.2.2
  have h' := hF a' b' c' ht'.1 ht'.2.1 ht'.2.2
  simp only at heq
  rw [heq] at h
  obtain ⟨rfl, rfl, rfl⟩ := hroles _ _ _ _ _ _ _ h h'
  rfl

/-- There are six incoming-leg self-energy loops. -/
theorem card_isSEin [Fintype (Contraction 1 1 gauge3)]
    [DecidablePred fun C : Contraction 1 1 gauge3 => ∃ a b c, IsSEin C a b c] :
    ((Finset.univ : Finset (Contraction 1 1 gauge3)).filter
      fun C => ∃ a b c, IsSEin C a b c).card = 6 :=
  card_filter_eq_six seInContraction (fun _ _ _ hab hbc hac => isSEin_seInContraction hab hbc hac)
    (fun _ _ _ _ h => ⟨h.chain.hab, h.chain.hbc, h.chain.hac, h.eq_seInContraction⟩)
    (fun _ _ _ _ _ _ _ h h' => h.chain.roles_eq h'.chain)

/-- There are six outgoing-leg self-energy loops. -/
theorem card_isSEout [Fintype (Contraction 1 1 gauge3)]
    [DecidablePred fun C : Contraction 1 1 gauge3 => ∃ a b c, IsSEout C a b c] :
    ((Finset.univ : Finset (Contraction 1 1 gauge3)).filter
      fun C => ∃ a b c, IsSEout C a b c).card = 6 :=
  card_filter_eq_six seOutContraction
    (fun _ _ _ hab hbc hac => isSEout_seOutContraction hab hbc hac)
    (fun _ _ _ _ h => ⟨h.chain.hab, h.chain.hbc, h.chain.hac, h.eq_seOutContraction⟩)
    (fun _ _ _ _ _ _ _ h h' => h.chain.roles_eq h'.chain)

/-- There are six vacuum polarization loops. -/
theorem card_isVP [Fintype (Contraction 1 1 gauge3)]
    [DecidablePred fun C : Contraction 1 1 gauge3 => ∃ a v w, IsVP C a v w] :
    ((Finset.univ : Finset (Contraction 1 1 gauge3)).filter
      fun C => ∃ a v w, IsVP C a v w).card = 6 :=
  card_filter_eq_six vpContraction (fun _ _ _ hav hvw haw => isVP_vpContraction hav hvw haw)
    (fun _ _ _ _ h => ⟨h.hav, h.hvw, h.haw, h.eq_vpContraction⟩)
    (fun _ _ _ _ _ _ _ h h' => h.roles_eq h')

/-! ### The sum over the connected contractions that are not 1PI -/

open scoped Classical in
/-- **Assembly of the classification.** A function on the contractions of three gauge vertices
that takes the value `Vin` on the incoming-leg self-energy loops, `Vout` on the outgoing-leg
ones, `Vvp` on the vacuum polarization loops and `0` on the tadpoles sums, over the connected
contractions that are not 1PI, to `6 Vin + 6 Vout + 6 Vvp`. -/
theorem sum_nonOnePI_gauge3_of [Fintype (Contraction 1 1 gauge3)]
    [DecidablePred fun C : Contraction 1 1 gauge3 =>
      (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C]
    (F : Contraction 1 1 gauge3 → ℂ) (Vin Vout Vvp : ℂ)
    (hin : ∀ C a b c, IsSEin C a b c → F C = Vin) (hout : ∀ C a b c, IsSEout C a b c → F C = Vout)
    (hvp : ∀ C a v w, IsVP C a v w → F C = Vvp) (htp : ∀ C a b c u, IsTP C a b c u → F C = 0) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 gauge3)).filter
        (fun C => (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C), F C =
      6 * Vin + 6 * Vout + 6 * Vvp := by
  have hF : ∀ C ∈ (Finset.univ : Finset (Contraction 1 1 gauge3)).filter
      (fun C => (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C), F C =
      (if ∃ a b c, IsSEin C a b c then Vin else 0) +
        (if ∃ a b c, IsSEout C a b c then Vout else 0) +
        (if ∃ a v w, IsVP C a v w then Vvp else 0) := by
    intro C hC
    rcases isNonOnePIShape_of (Finset.mem_filter.mp hC).2 with
      ⟨a, b, c, h⟩ | ⟨a, b, c, h⟩ | ⟨a, v, w, h⟩ | ⟨a, b, c, u, h⟩
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨a, b, c, h⟩),
        ite_eq_right_of_eq_false _ _ (eq_false fun ⟨_, _, _, h'⟩ => h.not_isSEout h'),
        ite_eq_right_of_eq_false _ _ (eq_false fun ⟨_, _, _, h'⟩ => h.chain.not_isVP h'),
        hin C a b c h, add_zero, add_zero]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun ⟨_, _, _, h'⟩ => h'.not_isSEout h),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨a, b, c, h⟩),
        ite_eq_right_of_eq_false _ _ (eq_false fun ⟨_, _, _, h'⟩ => h.chain.not_isVP h'),
        hout C a b c h, zero_add, add_zero]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun ⟨_, _, _, h'⟩ => h'.chain.not_isVP h),
        ite_eq_right_of_eq_false _ _ (eq_false fun ⟨_, _, _, h'⟩ => h'.chain.not_isVP h),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨a, v, w, h⟩), hvp C a v w h, zero_add, zero_add]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun ⟨_, _, _, h'⟩ => h'.chain.not_isTP h),
        ite_eq_right_of_eq_false _ _ (eq_false fun ⟨_, _, _, h'⟩ => h'.chain.not_isTP h),
        ite_eq_right_of_eq_false _ _ (eq_false fun ⟨_, _, _, h'⟩ => h'.not_isTP h), htp C a b c u h,
        add_zero, add_zero]
  have hcount : ∀ (Q : Contraction 1 1 gauge3 → Prop) [DecidablePred Q],
      (∀ C, Q C → (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C) → ∀ V : ℂ,
      ((Finset.univ : Finset (Contraction 1 1 gauge3)).filter Q).card = 6 →
      ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 gauge3)).filter
        (fun C => (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C),
          (if Q C then V else 0) = 6 * V := by
    intro Q _ hQ V hcard
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
    have hs : ((Finset.univ : Finset (Contraction 1 1 gauge3)).filter
        fun C => ((ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C) ∧ Q C) =
        (Finset.univ : Finset (Contraction 1 1 gauge3)).filter Q := by
      ext C
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hQ C h, h⟩⟩
    rw [hs, hcard]
    norm_num
  rw [Finset.sum_congr rfl hF, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hcount _ (fun C ⟨_, _, _, h⟩ => h.connected_not_isOnePI) Vin card_isSEin,
    hcount _ (fun C ⟨_, _, _, h⟩ => h.connected_not_isOnePI) Vout card_isSEout,
    hcount _ (fun C ⟨_, _, _, h⟩ => h.connected_not_isOnePI) Vvp card_isVP]

/-- **The connected contractions of three gauge vertices that are not 1PI**, summed with their
signs: six incoming-leg self-energy loops (sign `+1`), six outgoing-leg self-energy loops (sign
`+1`), six vacuum polarization loops (sign `-1`, absorbed in the vacuum polarization integrand)
and twelve tadpoles (value `0`). -/
theorem sum_nonOnePI_gauge3 (P : Params) [Fintype (Contraction 1 1 gauge3)]
    [DecidablePred fun C : Contraction 1 1 gauge3 =>
      (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C]
    (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 gauge3)).filter
        (fun C => (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C),
      ((fermionSign C : ℤ) : ℂ) * contractionValue P C ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      6 * QED.OneLoop.energyFirstIntegral (fun ℓ =>
          ∑ γ, ((I * P.e) • Dirac.gamma μ *
            ((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p)) α γ *
              selfEnergyIntegrand P P.ε p ℓ γ β) +
        6 * QED.OneLoop.energyFirstIntegral (fun ℓ =>
          ∑ γ, selfEnergyIntegrand P P.ε p' ℓ α γ *
            (((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p') *
              (I * P.e) • Dirac.gamma μ) γ β) +
        6 * QED.OneLoop.energyFirstIntegral (fun ℓ =>
          ∑ ν, ∑ ρ, (I * P.e) * Dirac.gamma ν α β *
            ((1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (p' - p) ν ρ) *
              vacuumPolarizationIntegrand P P.ε (p' - p) ℓ μ ρ) := by
  refine sum_nonOnePI_gauge3_of _ _ _ _ (fun C a b c h => ?_) (fun C a b c h => ?_)
    (fun C a v w h => ?_) (fun C a b c u h => ?_)
  · rw [h.chain.fermionSign_eq, h.contractionValue_eq, Int.cast_one, one_mul]
  · rw [h.chain.fermionSign_eq, h.contractionValue_eq, Int.cast_one, one_mul]
  · rw [h.fermionSign_eq, ← h.neg_contractionValue_eq]
    push_cast
    ring
  · rw [h.contractionValue_eq_zero, mul_zero]

end QED.WickModel

end
