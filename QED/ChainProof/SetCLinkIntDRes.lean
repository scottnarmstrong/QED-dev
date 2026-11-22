/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkIntDMom

/-!
# Set (c), family `D`: resummation and index updates

Helper for the Phase 5 Stage 3 goal (HS₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setC`
(decision D-58), family `D` of set (c): `QED.ChainProof.SetCLink.repD i s`, two loops, a
`photonCt` vertex `5` on a photon line of a two-loop vertex skeleton, grading `0`.

Resummation of index sums over coordinates a summand reads only once (`sum_resum_one`,
`sum_resum_pair`, `sum_resum_four`), splitting off four line factors (`lineProd_mod4`), the
invariance of the remaining factors under index updates, and the resummed Ward sum
`ward_sum_D`.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetCLink

open QED.GradedProof.X0 QED.Graded QED.WickModel QED.ChainProof.SetALink
open QED.ChainProof.Enum (fv pc)
open QED.TwoLoop.Enumeration (lineData)
open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero electronNumerator electronPropagator_apply
  photonPropagator_eq_mul)

variable {F : Type}

/-! ### Resummation -/

/-- **Averaging over one coordinate.** -/
theorem sum_avg {V : Type*} [Fintype V] [DecidableEq V] (s : V) (G : (V → Fin 4) → ℂ) :
    ∑ f, G f = ∑ f, (1 / 4 : ℂ) * ∑ x, G (Function.update f s x) := by
  set e := Equiv.piSplitAt s (fun _ : V => Fin 4)
  have hu : ∀ c x r, Function.update (e.symm (c, r)) s x = e.symm (x, r) := fun c x r => by
    funext j
    by_cases hj : j = s
    · subst hj; simp [e, Equiv.piSplitAt_symm_apply]
    · simp [e, Equiv.piSplitAt_symm_apply, hj]
  have hL : ∑ f, G f = ∑ c : Fin 4, ∑ r : {j // j ≠ s} → Fin 4, G (e.symm (c, r)) := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have hR : ∑ f, (1 / 4 : ℂ) * ∑ x, G (Function.update f s x) =
      ∑ c : Fin 4, ∑ r : {j // j ≠ s} → Fin 4, (1 / 4 : ℂ) * ∑ x, G (e.symm (x, r)) := by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [hu]
  rw [hL, hR, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_comm,
    ← Finset.mul_sum, nsmul_eq_mul]
  ring

/-- **Resummation over one coordinate** of a summand that reads it only through its last
argument. -/
theorem sum_resum_one {V : Type*} [Fintype V] [DecidableEq V] (s : V)
    (H : (V → Fin 4) → Fin 4 → ℂ) (hH : ∀ f x, H (Function.update f s x) = H f) :
    ∑ f, H f (f s) = ∑ f, (1 / 4 : ℂ) * ∑ x, H f x := by
  rw [sum_avg s]
  simp only [Function.update_self, hH]

/-- **Resummation over two coordinates of one index function.** -/
theorem sum_resum_pair {W : Type*} [Fintype W] [DecidableEq W] {p q : W} (hpq : p ≠ q)
    (Ψ : (W → Fin 4) → Fin 4 → Fin 4 → ℂ)
    (hp : ∀ lor x, Ψ (Function.update lor p x) = Ψ lor)
    (hq : ∀ lor x, Ψ (Function.update lor q x) = Ψ lor) :
    ∑ lor, Ψ lor (lor p) (lor q) = ∑ lor, (1 / 16 : ℂ) * ∑ x, ∑ y, Ψ lor x y := by
  rw [sum_resum_one p (fun lor x => Ψ lor x (lor q)) fun lor x => by
    simp only [hp, Function.update_of_ne hpq.symm]]
  rw [sum_resum_one q (fun lor y => (1 / 4 : ℂ) * ∑ x, Ψ lor x y) fun lor y => by
    simp only [hq]]
  refine Finset.sum_congr rfl fun lor _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **Resummation over the spinor indices of one fermion vertex and two photon fields.** -/
theorem sum_resum_four {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (s : V) {p q : W} (hpq : p ≠ q)
    (Ψ : (V → Fin 4) → (V → Fin 4) → (W → Fin 4) → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
    (hα : ∀ α β lor a, Ψ (Function.update α s a) β lor = Ψ α β lor)
    (hβ : ∀ α β lor b, Ψ α (Function.update β s b) lor = Ψ α β lor)
    (hp : ∀ α β lor x, Ψ α β (Function.update lor p x) = Ψ α β lor)
    (hq : ∀ α β lor x, Ψ α β (Function.update lor q x) = Ψ α β lor) :
    ∑ α, ∑ β, ∑ lor, Ψ α β lor (α s) (β s) (lor p) (lor q) =
      ∑ α, ∑ β, ∑ lor, (1 / 256 : ℂ) * ∑ a, ∑ b, ∑ x, ∑ y, Ψ α β lor a b x y := by
  have h1 : ∀ α β, ∑ lor, Ψ α β lor (α s) (β s) (lor p) (lor q) =
      ∑ lor, (1 / 16 : ℂ) * ∑ x, ∑ y, Ψ α β lor (α s) (β s) x y := fun α β =>
    sum_resum_pair hpq (fun lor x y => Ψ α β lor (α s) (β s) x y)
      (fun lor x => by simp only [hp]) (fun lor x => by simp only [hq])
  simp only [h1]
  have h2 := QED.GradedProof.X0Deg6.sum_sum_resum s
    (fun α β a b => ∑ lor, (1 / 16 : ℂ) * ∑ x, ∑ y, Ψ α β lor a b x y)
    (fun α β _ _ => (1 / 16 : ℂ) * ∑ a, ∑ b, ∑ lor, (1 / 16 : ℂ) * ∑ x, ∑ y, Ψ α β lor a b x y)
    (fun α β a b => by funext a' b'; simp only [hα, hβ])
    (fun α β a b => by simp only [hα, hβ])
    (fun α β => by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring)
  rw [h2]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  have e1 : (1 / 16 : ℂ) * ∑ a, ∑ b, ∑ lor, (1 / 16 : ℂ) * ∑ x, ∑ y, Ψ α β lor a b x y =
      ∑ a, ∑ b, ∑ lor, (1 / 256 : ℂ) * ∑ x, ∑ y, Ψ α β lor a b x y := by
    simp only [Finset.mul_sum, ← mul_assoc]
    norm_num
  have e2 : ∑ lor, (1 / 256 : ℂ) * ∑ a, ∑ b, ∑ x, ∑ y, Ψ α β lor a b x y =
      ∑ lor, ∑ a, ∑ b, (1 / 256 : ℂ) * ∑ x, ∑ y, Ψ α β lor a b x y := by
    simp only [Finset.mul_sum]
  rw [e1, e2]
  exact (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm

/-! ### Splitting off four lines -/

/-- The line factors off a set `L` of lines. -/
noncomputable def rest {C : Contraction 1 1 kD} (L : Finset (Line C)) (ε : ℝ)
    (Nf : Line C → (Fin 4 → ℝ) → ℂ)
    (ms : Line C → List ℝ) (k : Line C → Fin 4 → ℝ) : ℂ :=
  ∏ l, if l ∈ L then 1 else Nf l (k l) * dProd ε (ms l) (k l)

theorem lineProd_eq_rest {C : Contraction 1 1 kD} (L : Finset (Line C)) (ε : ℝ)
    (Nf : Line C → (Fin 4 → ℝ) → ℂ)
    (ms : Line C → List ℝ) (k : Line C → Fin 4 → ℝ) :
    lineProd ε Nf ms k = (∏ l ∈ L, Nf l (k l) * dProd ε (ms l) (k l)) * rest L ε Nf ms k := by
  rw [lineProd, rest, Finset.prod_ite, Finset.prod_const_one, one_mul,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun l => l ∈ L)]
  congr 2
  ext l
  simp

theorem rest_congr {C : Contraction 1 1 kD} (L : Finset (Line C)) (ε : ℝ)
    (Nf Nf' : Line C → (Fin 4 → ℝ) → ℂ)
    (ms ms' : Line C → List ℝ) (k : Line C → Fin 4 → ℝ)
    (h : ∀ l, l ∉ L → Nf l = Nf' l ∧ ms l = ms' l) :
    rest L ε Nf ms k = rest L ε Nf' ms' k :=
  Finset.prod_congr rfl fun l _ => by
    split_ifs with hl
    · rfl
    · rw [(h l hl).1, (h l hl).2]

/-- `f` with the values at four lines replaced. -/
def mod4 {C : Contraction 1 1 kD} {X : Type*} (a b c d : Line C) (xa xb xc xd : X)
    (f : Line C → X) : Line C → X :=
  fun l => if l = a then xa else if l = b then xb else if l = c then xc else if l = d then xd
    else f l

theorem lineProd_mod4 {C : Contraction 1 1 kD} (ε : ℝ) {a b c d : Line C} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (Na Nb Nc Nd : (Fin 4 → ℝ) → ℂ)
    (ma mb mc md : List ℝ) (Nf : Line C → (Fin 4 → ℝ) → ℂ) (ms : Line C → List ℝ)
    (k : Line C → Fin 4 → ℝ) :
    lineProd ε (mod4 a b c d Na Nb Nc Nd Nf) (mod4 a b c d ma mb mc md ms) k =
      (Na (k a) * dProd ε ma (k a)) * ((Nb (k b) * dProd ε mb (k b)) *
        ((Nc (k c) * dProd ε mc (k c)) * ((Nd (k d) * dProd ε md (k d)) *
          rest {a, b, c, d} ε Nf ms k))) := by
  rw [lineProd_eq_rest {a, b, c, d}, Finset.prod_insert (by simp [hab, hac, had]),
    Finset.prod_insert (by simp [hbc, hbd]), Finset.prod_insert (by simp [hcd]),
    Finset.prod_singleton]
  have hr : rest {a, b, c, d} ε (mod4 a b c d Na Nb Nc Nd Nf) (mod4 a b c d ma mb mc md ms) k =
      rest {a, b, c, d} ε Nf ms k := rest_congr _ _ _ _ _ _ _ fun l hl => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    simp [mod4, hl.1, hl.2.1, hl.2.2.1, hl.2.2.2]
  rw [hr]
  simp only [mod4, ↓reduceIte, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
  ring

theorem lineProd_four {C : Contraction 1 1 kD} (ε : ℝ) {a b c d : Line C} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (Nf : Line C → (Fin 4 → ℝ) → ℂ)
    (ms : Line C → List ℝ) (k : Line C → Fin 4 → ℝ) :
    lineProd ε Nf ms k =
      (Nf a (k a) * dProd ε (ms a) (k a)) * ((Nf b (k b) * dProd ε (ms b) (k b)) *
        ((Nf c (k c) * dProd ε (ms c) (k c)) * ((Nf d (k d) * dProd ε (ms d) (k d)) *
          rest {a, b, c, d} ε Nf ms k))) := by
  have h : ∀ {X : Type} (f : Line C → X), mod4 a b c d (f a) (f b) (f c) (f d) f = f :=
    fun f => by
      funext l
      unfold mod4
      split_ifs <;> simp_all
  have := lineProd_mod4 ε hab hac had hbc hbd hcd (Nf a) (Nf b) (Nf c) (Nf d) (ms a) (ms b)
    (ms c) (ms d) Nf ms k
  rwa [h, h] at this


/-! ### Invariance under index updates -/

/-- The `gauge` vertex factors off a set `T` of vertices. -/
noncomputable def gVx (T : Finset (Fin 6)) (e : ℝ) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) : ℂ :=
  ∏ t : Fin 6, if t ∈ T then 1 else Wick.vertexFactor e 0 0 1 0 1 α β lor 0 0 t

theorem gV_eq_gVx (e : ℝ) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) : gV e α β lor = gVx {5} e α β lor :=
  Finset.prod_congr rfl fun t _ => by simp only [Finset.mem_singleton]

theorem gVx_split (T : Finset (Fin 6)) (e : ℝ) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) (v : Wick.FermionVertex kD) (hv : v.1 ∉ T) :
    gVx T e α β lor = I * e * Dirac.gamma (lor (slD v)) (α v) (β v) *
      gVx (insert v.1 T) e α β lor := by
  rw [gVx, QED.GradedProof.X0Deg6.prod_split_one _ v.1, ite_eq_right_iff.mpr (fun h => absurd h hv),
    vertexFactor_kD_gauge]
  congr 1
  refine Finset.prod_congr rfl fun t _ => ?_
  by_cases h : t = v.1
  · simp [h]
  · simp [h]

theorem gVx_update_α (T : Finset (Fin 6)) (e : ℝ) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) (w : Wick.FermionVertex kD) (hw : w.1 ∈ T) (a : Fin 4) :
    gVx T e (Function.update α w a) β lor = gVx T e α β lor :=
  Finset.prod_congr rfl fun t _ => by
    split_ifs with ht
    · rfl
    · exact QED.GradedProof.X0Deg6.vertexFactor_congr₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (fun p => Function.update_of_ne (fun h => ht (by rw [← h] at hw; exact hw))
          _ _) fun _ => rfl

theorem gVx_update_β (T : Finset (Fin 6)) (e : ℝ) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) (w : Wick.FermionVertex kD) (hw : w.1 ∈ T) (b : Fin 4) :
    gVx T e α (Function.update β w b) lor = gVx T e α β lor :=
  Finset.prod_congr rfl fun t _ => by
    split_ifs with ht
    · rfl
    · exact QED.GradedProof.X0Deg6.vertexFactor_congr₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (fun _ => rfl) fun p =>
          Function.update_of_ne (fun h => ht (by rw [← h] at hw; exact hw)) _ _

theorem gVx_update_lor (T : Finset (Fin 6)) (h5 : (5 : Fin 6) ∈ T) (e : ℝ)
    (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4)
    (s : Wick.PhotonSlot kD) (hs : s.1 ∈ T) (x : Fin 4) :
    gVx T e α β (Function.update lor s x) = gVx T e α β lor :=
  Finset.prod_congr rfl fun t _ => by
    split_ifs with ht
    · rfl
    · have h5' : kD t ≠ .photonCt := by
        intro h
        apply ht
        have h' : ∀ u : Fin 6, kD u = .photonCt → u = 5 := by decide
        rw [h' t h]; exact h5
      have e1 := vertexFactor_kD_gauge e 0 0 1 0 1 α β (Function.update lor s x) 0 0 ⟨t, h5'⟩
      have e2 := vertexFactor_kD_gauge e 0 0 1 0 1 α β lor 0 0 ⟨t, h5'⟩
      simp only at e1 e2
      rw [e1, e2, Function.update_of_ne]
      intro h
      apply ht
      rw [← h] at hs
      exact hs

theorem extI_update_α (C : Contraction 1 1 kD) (αOut βIn μ : Fin 1 → Fin 4)
    (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4)
    (w : Wick.FermionVertex kD) (hw : ∀ i, C.1.1 (.inl i) ≠ .inr w) (a : Fin 4) :
    extI C αOut βIn μ (Function.update α w a) β lor = extI C αOut βIn μ α β lor := by
  have hiff : (∀ i t, C.1.1 (.inl i) = .inr t → Function.update α w a t = αOut i) ↔
      (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) := by
    constructor <;> intro h i t hit <;> have := h i t hit <;>
      simpa [Function.update_of_ne (fun e : t = w => hw i (by rw [← e]; exact hit))] using this
  unfold extI
  simp only [hiff]

theorem extI_update_β (C : Contraction 1 1 kD) (αOut βIn μ : Fin 1 → Fin 4)
    (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4)
    (w : Wick.FermionVertex kD) (hw : ∀ i, C.1.1 (.inr w) ≠ .inl i) (b : Fin 4) :
    extI C αOut βIn μ α (Function.update β w b) lor = extI C αOut βIn μ α β lor := by
  have hiff : (∀ t i, C.1.1 (.inr t) = .inl i → Function.update β w b t = βIn i) ↔
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) := by
    constructor <;> intro h t i hti <;> have := h t i hti <;>
      simpa [Function.update_of_ne (fun e : t = w => hw i (by rw [← e]; exact hti))] using this
  unfold extI
  simp only [hiff]

theorem extI_update_lor (C : Contraction 1 1 kD) (αOut βIn μ : Fin 1 → Fin 4)
    (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4)
    (s : Wick.PhotonSlot kD) (hs : ∀ j, C.1.2 (.inl j) ≠ .inr s) (x : Fin 4) :
    extI C αOut βIn μ α β (Function.update lor s x) = extI C αOut βIn μ α β lor := by
  have hiff : (∀ j a, C.1.2 (.inl j) = .inr a → Function.update lor s x a = μ j) ↔
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) := by
    constructor <;> intro h j a hja <;> have := h j a hja <;>
      simpa [Function.update_of_ne (fun e : a = s => hs j (by rw [← e]; exact hja))] using this
  unfold extI
  simp only [hiff]

theorem rest_update_α (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
    (L : Finset (Line C)) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) (k : Line C → Fin 4 → ℝ) (w : Wick.FermionVertex kD)
    (hw : ∀ f : FermionLine C, f.tail = w → (Sum.inl f : Line C) ∈ L) (a : Fin 4) :
    rest L P.ε (dNum P Φ (Function.update α w a) β lor) (dMs P Φ) k =
      rest L P.ε (dNum P Φ α β lor) (dMs P Φ) k :=
  rest_congr _ _ _ _ _ _ _ fun l hl => by
    refine ⟨?_, rfl⟩
    rcases l with f | g
    · have hf : f.tail ≠ w := fun h => hl (hw f h)
      funext q
      simp only [dNum, Function.update_of_ne hf]
    · rfl

theorem rest_update_β (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
    (L : Finset (Line C)) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) (k : Line C → Fin 4 → ℝ) (w : Wick.FermionVertex kD)
    (hw : ∀ f : FermionLine C, f.1 = w → (Sum.inl f : Line C) ∈ L) (b : Fin 4) :
    rest L P.ε (dNum P Φ α (Function.update β w b) lor) (dMs P Φ) k =
      rest L P.ε (dNum P Φ α β lor) (dMs P Φ) k :=
  rest_congr _ _ _ _ _ _ _ fun l hl => by
    refine ⟨?_, rfl⟩
    rcases l with f | g
    · have hf : f.1 ≠ w := fun h => hl (hw f h)
      funext q
      simp only [dNum, Function.update_of_ne hf]
    · rfl

theorem rest_update_lor (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
    (L : Finset (Line C)) (α β : Wick.FermionVertex kD → Fin 4)
    (lor : Wick.PhotonSlot kD → Fin 4) (k : Line C → Fin 4 → ℝ) (s : Wick.PhotonSlot kD)
    (hs : ∀ g : PhotonLine C, (g.1 = s ∨ g.head = s) → (Sum.inr g : Line C) ∈ L) (x : Fin 4) :
    rest L P.ε (dNum P Φ α β (Function.update lor s x)) (dMs P Φ) k =
      rest L P.ε (dNum P Φ α β lor) (dMs P Φ) k :=
  rest_congr _ _ _ _ _ _ _ fun l hl => by
    refine ⟨?_, rfl⟩
    rcases l with f | g
    · rfl
    · have h1 : g.1 ≠ s := fun h => hl (hs g (Or.inl h))
      have h2 : g.head ≠ s := fun h => hl (hs g (Or.inr h))
      funext q
      simp only [dNum, Function.update_of_ne h1, Function.update_of_ne h2]

/-! ### The Ward identity in the index sums -/

/-- **The resummed Ward sum**: `∑ A₁(X,a) γ^x_{ab} g_{xy} q^y A₂(b,Y) = σ ((D₁ + iε) A₂ - (D₂ + iε)
A₁)_{XY}` for `q = σ (p₁ - p₂)`. -/
theorem ward_sum_D (M ε σ : ℝ) (p₁ p₂ q : Fin 4 → ℝ) (hq : q = σ • (p₁ - p₂)) (X Y : Fin 4) :
    ∑ a, ∑ b, ∑ x, ∑ y, electronNumerator M p₁ X a *
        (Dirac.gamma x a b * (((Minkowski.metric x y : ℝ) : ℂ) * (q y : ℂ))) *
          electronNumerator M p₂ b Y =
      σ * ((propDenom M ε p₁ + (ε : ℂ) * I) * electronNumerator M p₂ X Y -
        (propDenom M ε p₂ + (ε : ℂ) * I) * electronNumerator M p₁ X Y) := by
  have hs : ∀ a b, ∑ x, ∑ y, Dirac.gamma x a b * (((Minkowski.metric x y : ℝ) : ℂ) *
      (q y : ℂ)) = Dirac.slash q a b := fun a b => by
    rw [← QED.GradedProof.X0Deg6.sum_gamma_metric q a b]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  have h1 : ∑ a, ∑ b, ∑ x, ∑ y, electronNumerator M p₁ X a *
      (Dirac.gamma x a b * (((Minkowski.metric x y : ℝ) : ℂ) * (q y : ℂ))) *
        electronNumerator M p₂ b Y =
      (electronNumerator M p₁ * Dirac.slash q * electronNumerator M p₂) X Y := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    rw [← hs a b, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [h1, hq, Dirac.slash_smul, Matrix.mul_smul, Matrix.smul_mul,
    QED.GradedProof.X0Deg6.electronNumerator_slash_electronNumerator M ε]
  simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

/-! ### Line-factor lemmas -/

theorem dNum_inl (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
    (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4) (f : FermionLine C)
    (k : Fin 4 → ℝ) :
    dNum P Φ α β lor (.inl f) k =
      (1 / I) * electronNumerator (Φ.mass Φ.openLine) k (β f.1) (α f.tail) := rfl

theorem dNum_inr (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
    (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4) (g : PhotonLine C)
    (k : Fin 4 → ℝ) :
    dNum P Φ α β lor (.inr g) k = (1 / I) * (((Minkowski.metric (lor g.1) (lor g.head) : ℝ) : ℂ) *
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)) := by
  simp only [dNum]
  push_cast
  ring

theorem dMs_inr (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD} (g : PhotonLine C) :
    dMs P Φ (.inr g) = [P.mγ, P.Λ] := rfl

theorem dProd_single (ε M : ℝ) (k : Fin 4 → ℝ) : dProd ε [M] k = (propDenom M ε k)⁻¹ := by
  simp [dProd]

theorem ctKD_eq (δ₃ : ℝ) (lor : Wick.PhotonSlot kD → Fin 4) (q : Fin 4 → ℝ) (s : Fin 2) :
    ctKD δ₃ lor q =
      (I / 2) * (δ₃ : ℂ) * ((q (lor (pc kD 5 s)) : ℂ) * (q (lor (pc kD 5 s.rev)) : ℂ)) := by
  fin_cases s
  · rfl
  · show _ = (I / 2) * (δ₃ : ℂ) * ((q (lor (pc kD 5 1)) : ℂ) * (q (lor (pc kD 5 0)) : ℂ))
    simp only [ctKD]
    ring

theorem ne_five (v : Wick.FermionVertex kD) : v.1 ≠ 5 := by
  obtain ⟨t, ht⟩ := v
  have h : ∀ u : Fin 6, kD u ≠ .photonCt → u ≠ 5 := by decide
  exact h t ht

theorem affPoly_coord (c : ℝ) (ν : Fin 4) : AffPoly 1 fun k => ((c * k ν : ℝ) : ℂ) := by
  refine (congrArg (AffPoly 1) (funext fun k => ?_)).mp
    (AffPoly.aff 0 fun ν' => if ν' = ν then (c : ℂ) else 0)
  simp

theorem affPoly_mod4 {C : Contraction 1 1 kD} (a b c d : Line C) (Na Nb Nc Nd : (Fin 4 → ℝ) → ℂ)
    (da db dc dd : ℕ) (Nf : Line C → (Fin 4 → ℝ) → ℂ) (dl : Line C → ℕ) (ha : AffPoly da Na)
    (hb : AffPoly db Nb) (hc : AffPoly dc Nc) (hd : AffPoly dd Nd)
    (hN : ∀ l, AffPoly (dl l) (Nf l)) (l : Line C) :
    AffPoly (mod4 a b c d da db dc dd dl l) (mod4 a b c d Na Nb Nc Nd Nf l) := by
  unfold mod4
  split_ifs
  exacts [ha, hb, hc, hd, hN l]

theorem length_mod4 (P : Params) (Φ : Lepton.Flavors F) {C : Contraction 1 1 kD}
    (a b c d : Line C) (ma mb mc md : List ℝ) :
    (fun l => (mod4 a b c d ma mb mc md (dMs P Φ) l).length) =
      mod4 a b c d ma.length mb.length mc.length md.length dN := by
  funext l
  unfold mod4
  split_ifs <;> first | rfl | exact congrFun (length_dMs P Φ C) l

end QED.ChainProof.SetCLink

end
