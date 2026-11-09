/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Wick.ClassificationBasic
public import QED.Wick.Gauge3

/-!
# The one-particle-irreducible contractions of three gauge vertices

For the vertex sequence `gauge3` of three `gauge` vertices (packet 5, decision D-20):

* `isOnePI_iff_exists_isChain`: a contraction is 1PI exactly when it is a vertex correction
  `IsChain C a b c`. A 1PI contraction has two distinct internal lines through every vertex,
  which leaves only the triangle `a – b – c` with the fermion chain `c → b → a`, the external
  photon at `b` and the internal photon joining `a` and `c`.
* `IsChain.fermionSign_eq_one`: each vertex correction has fermionic sign `+1`.
* `chainContraction`, `IsChain.ext`, `IsChain.unique`: each ordering of the three vertices gives
  exactly one vertex correction, and it determines the ordering.
-/

@[expose] public section

namespace QED.Wick

/-- Distinct vertices of `gauge3` are distinct fermion vertices. -/
private theorem fv_injective : Function.Injective fv := fun _ _ h => congrArg Subtype.val h

/-- Distinct vertices of `gauge3` have distinct photon fields. -/
private theorem ps_injective : Function.Injective ps := fun _ _ h => congrArg Sigma.fst h

/-- Every fermion vertex of `gauge3` is `fv t`. -/
private theorem fv_val (x : FermionVertex gauge3) : fv x.1 = x := rfl

/-- Every photon field of `gauge3` is `ps t`. -/
private theorem ps_fst (x : PhotonSlot gauge3) : ps x.1 = x := by
  obtain ⟨t, k, hk⟩ := x
  obtain rfl : k = 0 := by simp only [VertexKind.photonSlots] at hk; omega
  rfl

/-- The key of the photon field of vertex `t` of `gauge3`. -/
private theorem photonKey_ps (t : Fin 3) : photonKey (ps t) = 2 * t.val := rfl

/-- Three distinct elements of `Fin 3` exhaust it. -/
private theorem fin_three_eq_or {a b c : Fin 3} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (x : Fin 3) : x = a ∨ x = b ∨ x = c := by
  omega

/-- A `Ψ̄` field of the contraction of `gauge3`: the external `Ψ̄(y)` or a vertex field. -/
private theorem option_fv_cases (x : Option (FermionVertex gauge3)) :
    x = none ∨ ∃ t, x = some (fv t) := by
  rcases x with _ | x
  · exact Or.inl rfl
  · exact Or.inr ⟨x.1, rfl⟩

/-- A photon field of the contraction of `gauge3`: the external `A(z)` or a vertex field. -/
private theorem option_ps_cases (x : Option (PhotonSlot gauge3)) :
    x = none ∨ ∃ t, x = some (ps t) := by
  rcases x with _ | x
  · exact Or.inl rfl
  · exact Or.inr ⟨x.1, by rw [ps_fst]⟩

variable {C : Contraction gauge3}

/-- A crossing internal photon line of `gauge3` at `v` uses the photon field of `v`. -/
theorem PhotonLine.mem_of_crosses_gauge3 (g : PhotonLine C) {v : Fin 3}
    (h : Line.Crosses (Sum.inr g : Line C) v) : g.1 = ps v ∨ C.1.2 (some g.1) = some (ps v) := by
  obtain ⟨x, y, hy, hk⟩ := g
  rw [Line.crosses_inr_iff _ hy] at h
  dsimp only at h ⊢
  rcases h.2 with h | h
  · exact Or.inl (by rw [← h, ps_fst])
  · exact Or.inr (by rw [hy, ← h, ps_fst])

/-- No internal photon line ends at the vertex whose photon field is contracted with `A(z)`. -/
theorem PhotonLine.not_crosses_of_external {b : Fin 3} (hb : C.1.2 none = some (ps b))
    (g : PhotonLine C) : ¬ Line.Crosses (Sum.inr g : Line C) b := by
  intro h
  obtain ⟨x, y, hy, hk⟩ := g
  rcases PhotonLine.mem_of_crosses_gauge3 _ h with h | h
  · dsimp only at h hy
    subst h
    rw [← hb, (C.2 none).1] at hy
    exact Option.some_ne_none _ hy.symm
  · dsimp only at h
    rw [← hb] at h
    exact Option.some_ne_none _ (C.1.2.injective h)

/-- A crossing internal fermion line of `gauge3`, in terms of vertex labels. -/
theorem FermionLine.exists_of_crosses_gauge3 (f : FermionLine C) {v : Fin 3}
    (h : Line.Crosses (Sum.inl f : Line C) v) :
    ∃ t s : Fin 3, f.1 = fv t ∧ C.1.1 (some (fv t)) = some (fv s) ∧ s ≠ t ∧ (s = v ∨ t = v) := by
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp f.2
  rw [Line.crosses_inl_iff _ hs] at h
  exact ⟨f.1.1, s.1, rfl, hs, h.1, h.2⟩

/-- At the vertex `b` whose photon field is contracted with `A(z)`, a 1PI contraction has an
internal fermion line in and out of `b`. -/
theorem IsOnePI.vertex_external_photon (hC : IsOnePI C) {b : Fin 3}
    (hb : C.1.2 none = some (ps b)) :
    (∃ s, s ≠ b ∧ C.1.1 (some (fv b)) = some (fv s)) ∧
      ∃ t, t ≠ b ∧ C.1.1 (some (fv t)) = some (fv b) := by
  obtain ⟨w, hw⟩ : ∃ w, b ≠ w := ⟨b + 1, by omega⟩
  obtain ⟨f₁, f₂, hne, h₁, h₂⟩ := hC.exists_crosses_ne hw
  rcases f₁ with f₁ | g₁
  swap; · exact absurd h₁ (PhotonLine.not_crosses_of_external hb _)
  rcases f₂ with f₂ | g₂
  swap; · exact absurd h₂ (PhotonLine.not_crosses_of_external hb _)
  obtain ⟨t₁, s₁, hf₁, hs₁, hst₁, h₁⟩ := FermionLine.exists_of_crosses_gauge3 f₁ h₁
  obtain ⟨t₂, s₂, hf₂, hs₂, hst₂, h₂⟩ := FermionLine.exists_of_crosses_gauge3 f₂ h₂
  have ht : t₁ ≠ t₂ := by
    rintro rfl
    exact hne (congrArg Sum.inl (Subtype.ext (hf₁.trans hf₂.symm)))
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact absurd (fv_injective (Option.some_injective _ (C.1.1.injective
      (by rw [hs₁, hs₂, h₁, h₂])))) ht
  · rw [h₂] at hs₂ hst₂
    rw [h₁] at hs₁ hst₁
    exact ⟨⟨s₂, hst₂, hs₂⟩, ⟨t₁, Ne.symm hst₁, hs₁⟩⟩
  · rw [h₁] at hs₁ hst₁
    rw [h₂] at hs₂ hst₂
    exact ⟨⟨s₁, hst₁, hs₁⟩, ⟨t₂, Ne.symm hst₂, hs₂⟩⟩
  · exact absurd (h₁.trans h₂.symm) ht

/-- At the vertex `a` whose `Ψ̄` is contracted with `Ψ(x)`, the `Ψ` of a 1PI contraction is
contracted with the `Ψ̄` of another vertex. -/
theorem IsOnePI.vertex_external_psibar (hC : IsOnePI C) {a : Fin 3}
    (ha : C.1.1 none = some (fv a)) : ∃ s, s ≠ a ∧ C.1.1 (some (fv a)) = some (fv s) := by
  obtain ⟨w, hw⟩ : ∃ w, a ≠ w := ⟨a + 1, by omega⟩
  obtain ⟨f₁, f₂, hne, h₁, h₂⟩ := hC.exists_crosses_ne hw
  have hinl : ∀ f : FermionLine C, Line.Crosses (Sum.inl f : Line C) a →
      ∃ s, s ≠ a ∧ C.1.1 (some (fv a)) = some (fv s) := by
    intro f hf
    obtain ⟨t, s, -, hs, hst, h⟩ := FermionLine.exists_of_crosses_gauge3 f hf
    rcases h with h | h
    · rw [h, ← ha] at hs
      exact absurd (C.1.1.injective hs) (Option.some_ne_none _)
    · rw [h] at hs hst
      exact ⟨s, hst, hs⟩
  rcases f₁ with f₁ | g₁
  · exact hinl f₁ h₁
  rcases f₂ with f₂ | g₂
  · exact hinl f₂ h₂
  exact absurd (PhotonLine.eq_of_mem (PhotonLine.mem_of_crosses_gauge3 g₁ h₁)
    (PhotonLine.mem_of_crosses_gauge3 g₂ h₂)) fun h => hne (congrArg Sum.inr h)

/-- A 1PI contraction of three gauge vertices is a vertex correction. -/
theorem IsOnePI.exists_isChain (hC : IsOnePI C) : ∃ a b c, IsChain C a b c := by
  obtain ⟨a, ha⟩ : ∃ a, C.1.1 none = some (fv a) := by
    rcases option_fv_cases (C.1.1 none) with h | h
    · exact absurd h hC.1
    · exact h
  obtain ⟨b, hb⟩ : ∃ b, C.1.2 none = some (ps b) := by
    rcases option_ps_cases (C.1.2 none) with h | h
    · exact absurd h (C.2 none).2
    · exact h
  obtain ⟨c, hc⟩ : ∃ c, C.1.1 (some (fv c)) = none := by
    rcases option_fv_cases (C.1.1.symm none) with h | ⟨c, hc⟩
    · exact absurd ((Equiv.symm_apply_eq _).mp h).symm hC.1
    · exact ⟨c, by rw [← hc, Equiv.apply_symm_apply]⟩
  obtain ⟨⟨s, hsb, hs⟩, ⟨t, -, ht⟩⟩ := hC.vertex_external_photon hb
  obtain ⟨s', hs'a, hs'⟩ := hC.vertex_external_psibar ha
  have hab : a ≠ b := by
    rintro rfl
    exact Option.some_ne_none _ (C.1.1.injective (ht.trans ha.symm))
  have hbc : b ≠ c := by
    rintro rfl
    rw [hs] at hc
    exact Option.some_ne_none _ hc
  have hac : a ≠ c := by
    rintro rfl
    rw [hs'] at hc
    exact Option.some_ne_none _ hc
  have hsc : s = c := by
    rcases fin_three_eq_or hab hbc hac s with h | h | h
    · rw [h] at hs
      exact absurd (C.1.1.injective (hs.trans ha.symm)) (Option.some_ne_none _)
    · exact absurd h hsb
    · exact h
  rw [hsc] at hs
  have hs'b : s' = b := by
    rcases fin_three_eq_or hab hbc hac s' with h | h | h
    · exact absurd h hs'a
    · exact h
    · rw [h, ← hs] at hs'
      exact absurd (fv_injective (Option.some_injective _ (C.1.1.injective hs'))) hab
  rw [hs'b] at hs'
  have hτ : C.1.2 (some (ps a)) = some (ps c) := by
    have hτb : C.1.2 (some (ps b)) = none := by rw [← hb, (C.2 none).1]
    rcases option_ps_cases (C.1.2 (some (ps a))) with h | ⟨y, hy⟩
    · rw [← hτb] at h
      exact absurd (ps_injective (Option.some_injective _ (C.1.2.injective h))) hab
    · rcases fin_three_eq_or hab hbc hac y with h | h | h
      · rw [h] at hy
        exact absurd hy (C.2 _).2
      · rw [h, ← hb] at hy
        exact absurd (C.1.2.injective hy) (Option.some_ne_none _)
      · rw [hy, h]
  exact ⟨a, b, c, hab, hbc, hac, ha, hs', hs, hc, hb, hτ⟩

/-- A vertex correction is 1PI: its three internal lines form a triangle. -/
theorem IsChain.isOnePI {a b c : Fin 3} (h : IsChain C a b c) : IsOnePI C := by
  obtain ⟨hab, hbc, hac, h1, h2, h3, -, -, h6⟩ := h
  refine ⟨by rw [h1]; exact Option.some_ne_none _, fun g u w => ?_⟩
  obtain ⟨La, hLa⟩ : ∃ La : Line C, Line.ends La = (b, a) :=
    ⟨_, Line.ends_inl ⟨fv a, by rw [h2]; exact Option.some_ne_none _⟩ h2⟩
  obtain ⟨Lb, hLb⟩ : ∃ Lb : Line C, Line.ends Lb = (c, b) :=
    ⟨_, Line.ends_inl ⟨fv b, by rw [h3]; exact Option.some_ne_none _⟩ h3⟩
  obtain ⟨Lp, hLp⟩ : ∃ Lp : Line C, Line.ends Lp = (a, c) ∨ Line.ends Lp = (c, a) := by
    rcases lt_or_gt_of_ne hac with hlt | hlt
    · exact ⟨_, Or.inl (Line.ends_inr ⟨ps a, ps c, h6, by simp only [photonKey_ps]; omega⟩ h6)⟩
    · have h6' : C.1.2 (some (ps c)) = some (ps a) := by rw [← h6, (C.2 _).1]
      exact ⟨_, Or.inr (Line.ends_inr ⟨ps c, ps a, h6', by simp only [photonKey_ps]; omega⟩ h6')⟩
  have hab' : La ≠ Lb := fun h => hbc (congrArg Prod.fst (hLa.symm.trans (h ▸ hLb)))
  have hpa : Lp ≠ La := by
    rintro rfl
    rcases hLp with h | h <;> rw [h] at hLa <;> simp only [Prod.mk.injEq] at hLa
    · exact hab hLa.1
    · exact hbc hLa.1.symm
  have hpb : Lp ≠ Lb := by
    rintro rfl
    rcases hLp with h | h <;> rw [h] at hLb <;> simp only [Prod.mk.injEq] at hLb
    · exact hac hLb.1
    · exact hab hLb.2
  have hall := fin_three_eq_or hab hbc hac
  have hsymm : ∀ x y, Joined C {f | g = some f} x y → Joined C {f | g = some f} y x :=
    fun _ _ h => h.symm
  have jab : g ≠ some La → Joined C {f | g = some f} a b := fun hS => ⟨La, hS, Or.inr hLa⟩
  have jbc : g ≠ some Lb → Joined C {f | g = some f} b c := fun hS => ⟨Lb, hS, Or.inr hLb⟩
  have jac : g ≠ some Lp → Joined C {f | g = some f} a c := fun hS => ⟨Lp, hS, hLp⟩
  by_cases hgA : g = some La
  · have hb' : g ≠ some Lb := by rw [hgA]; simpa using hab'
    have hp' : g ≠ some Lp := by rw [hgA]; simpa using hpa.symm
    refine reflTransGen_of_forall_eq_or hsymm c (fun x => ?_) u w
    rcases hall x with rfl | rfl | rfl
    · exact Or.inr (jac hp').symm
    · exact Or.inr (jbc hb').symm
    · exact Or.inl rfl
  by_cases hgB : g = some Lb
  · have hp' : g ≠ some Lp := by rw [hgB]; simpa using hpb.symm
    refine reflTransGen_of_forall_eq_or hsymm a (fun x => ?_) u w
    rcases hall x with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (jab hgA)
    · exact Or.inr (jac hp')
  · refine reflTransGen_of_forall_eq_or hsymm b (fun x => ?_) u w
    rcases hall x with rfl | rfl | rfl
    · exact Or.inr (jab hgA).symm
    · exact Or.inl rfl
    · exact Or.inr (jbc hgB)

/-- The 1PI contractions of three gauge vertices are exactly the vertex corrections. -/
theorem isOnePI_iff_exists_isChain (C : Contraction gauge3) :
    IsOnePI C ↔ ∃ a b c, IsChain C a b c :=
  ⟨IsOnePI.exists_isChain, fun ⟨_, _, _, h⟩ => h.isOnePI⟩

/-- The fermion pairing of a vertex correction `c → b → a` is the 4-cycle
`none ↦ a ↦ b ↦ c ↦ none`, a product of three transpositions. -/
theorem IsChain.perm_eq {a b c : Fin 3} (h : IsChain C a b c) :
    C.1.1 = Equiv.swap none (some (fv c)) * Equiv.swap none (some (fv b)) *
      Equiv.swap none (some (fv a)) := by
  obtain ⟨hab, hbc, hac, h1, h2, h3, h4, -, -⟩ := h
  ext1 x
  rcases option_fv_cases x with rfl | ⟨t, rfl⟩
  · simp [Equiv.swap_apply_def, fv_injective.eq_iff, h1, hab, hac]
  · rcases fin_three_eq_or hab hbc hac t with rfl | rfl | rfl <;>
      simp [Equiv.swap_apply_def, fv_injective.eq_iff, h2, h3, h4, hbc, hab.symm, hbc.symm,
        hac.symm]

/-- A vertex correction has fermionic sign `+1`: `(-1)³` from the three vertices times the sign
`-1` of a 4-cycle. -/
theorem IsChain.fermionSign_eq_one {a b c : Fin 3} (h : IsChain C a b c) : fermionSign C = 1 := by
  have hcard : Fintype.card (FermionVertex gauge3) = 3 := by decide
  rw [fermionSign, h.perm_eq, hcard]
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']

/-- The vertex correction with fermion order `c → b → a`, as a contraction. -/
def chainContraction (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Contraction gauge3 :=
  ⟨(Equiv.swap none (some (fv c)) * Equiv.swap none (some (fv b)) * Equiv.swap none (some (fv a)),
    Equiv.swap none (some (ps b)) * Equiv.swap (some (ps a)) (some (ps c))), fun x => by
    rcases option_ps_cases x with rfl | ⟨t, rfl⟩
    · simp [Equiv.swap_apply_def, ps_injective.eq_iff, hbc, hab.symm]
    · rcases fin_three_eq_or hab hbc hac t with rfl | rfl | rfl <;>
        simp [Equiv.swap_apply_def, ps_injective.eq_iff, hab, hbc, hac, hab.symm, hbc.symm,
          hac.symm]⟩

/-- `chainContraction a b c` is the vertex correction with fermion order `c → b → a`. -/
theorem isChain_chainContraction (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    IsChain (chainContraction a b c hab hbc hac) a b c := by
  refine ⟨hab, hbc, hac, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [chainContraction, Equiv.swap_apply_def, fv_injective.eq_iff, ps_injective.eq_iff, hab,
      hbc, hac, hab.symm, hbc.symm, hac.symm]

/-- A vertex correction is determined by its fermion order. -/
theorem IsChain.ext {C' : Contraction gauge3} {a b c : Fin 3} (h : IsChain C a b c)
    (h' : IsChain C' a b c) : C = C' := by
  obtain ⟨hab, hbc, hac, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨-, -, -, h1', h2', h3', h4', h5', h6'⟩ := h'
  have h7 : C.1.2 (some (ps b)) = none := by rw [← h5, (C.2 none).1]
  have h7' : C'.1.2 (some (ps b)) = none := by rw [← h5', (C'.2 none).1]
  have h8 : C.1.2 (some (ps c)) = some (ps a) := by rw [← h6, (C.2 _).1]
  have h8' : C'.1.2 (some (ps c)) = some (ps a) := by rw [← h6', (C'.2 _).1]
  apply Subtype.ext
  apply Prod.ext <;> ext1 x
  · rcases option_fv_cases x with rfl | ⟨t, rfl⟩
    · rw [h1, h1']
    · rcases fin_three_eq_or hab hbc hac t with rfl | rfl | rfl
      · rw [h2, h2']
      · rw [h3, h3']
      · rw [h4, h4']
  · rcases option_ps_cases x with rfl | ⟨t, rfl⟩
    · rw [h5, h5']
    · rcases fin_three_eq_or hab hbc hac t with rfl | rfl | rfl
      · rw [h6, h6']
      · rw [h7, h7']
      · rw [h8, h8']

/-- The fermion order of a vertex correction is determined by the contraction. -/
theorem IsChain.unique {a b c a' b' c' : Fin 3} (h : IsChain C a b c)
    (h' : IsChain C a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨-, -, -, h1, -, -, h4, h5, -⟩ := h
  obtain ⟨-, -, -, h1', -, -, h4', h5', -⟩ := h'
  exact ⟨fv_injective (Option.some_injective _ (h1.symm.trans h1')),
    ps_injective (Option.some_injective _ (h5.symm.trans h5')),
    fv_injective (Option.some_injective _ (C.1.1.injective (h4.trans h4'.symm)))⟩

/-- There are six orderings of the three vertices. -/
theorem card_distinct_triples :
    ((Finset.univ : Finset (Fin 3 × Fin 3 × Fin 3)).filter
      fun p => p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.1 ≠ p.2.2).card = 6 := by
  decide

end QED.Wick

end
