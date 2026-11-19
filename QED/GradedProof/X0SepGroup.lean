/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0ClosedTerm

/-!
# (X₀): a closed fermion loop carrying one loop momentum, summed over the flavours

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), for the two-loop
contractions of `TwoLoopClosedGoal` whose two loops share no line. On a closed loop `Z` of
`gauge` vertices the vertex factors are constants `I e γ^μ_{ab}`, nonzero only on index pairs in
different chirality blocks (`vertexFactor_gauge_eq_zero_of_blk`). If all of them are in
different blocks, the sign product of the propagator entries of the loop is `(-1)^r`
(`prod_sgn_zLine`), so an even number of them are same-block, and the flavour sum
`∑_f c_f ∏_{l ∈ Z} S_{M_f}(c_l ℓ + q_l)_{ab}` satisfies (T₉′) at one loop for `1 ≤ r ≤ 4`, at
any masses (`jointEnergyFirstIntegrable_zGroup`, from `jointEnergyFirstIntegrable_entrySum`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel
open QED.TwoLoop.Bridge (propDenom electronNumerator electronPropagator_apply)
open QED.TwoLoop.FurryIntegrable (sgn)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type}

/-- At a `gauge` vertex the level-`0` vertex factor is `I e γ^μ_{ab}`, whatever the flavour, the
mass and the momenta. -/
theorem vf0_gauge (P : Params) (D : Counterterms F) (x : F) (M : ℝ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N)
    (h : κ t = .gauge) :
    vf0 P D x M α β lor kψ kA t = Wick.vertexFactor P.e 0 0 0 0 0 α β lor 0 0 t := by
  unfold vf0 Wick.vertexFactor
  split <;> rename_i h' <;> simp_all

/-- A `gauge` vertex factor vanishes on a same-block index pair. -/
theorem vertexFactor_gauge_eq_zero_of_blk (e : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (s : Wick.FermionVertex κ) (hs : κ s.1 = .gauge)
    (h : blk (α s) = blk (β s)) : Wick.vertexFactor e 0 0 0 0 0 α β lor 0 0 s.1 = 0 := by
  rw [vertexFactor_pure]
  simp [h, hs]

/-- The sign product of a family of index pairs counts the different-block pairs. -/
theorem prod_sgn_eq {E : Type*} [Fintype E] (a b : E → Fin 4) :
    ∏ e, sgn (a e) * sgn (b e) =
      (-1 : ℂ) ^ (Finset.univ.filter fun e => ¬ blk (a e) = blk (b e)).card := by
  classical
  simp only [sgn_mul_sgn]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

theorem neg_one_pow_eq_ite (n : ℕ) : (-1 : ℂ) ^ n = if Even n then 1 else -1 := by
  rcases Nat.even_or_odd n with h | h
  · simp [h.neg_one_pow, h]
  · simp [h.neg_one_pow, Nat.not_even_iff_odd.mpr h]

/-- **Parity**: if the sign product is `(-1)^{#entries}`, an even number of entries are
same-block. -/
theorem even_card_blk_of_prod {E : Type*} [Fintype E] (a b : E → Fin 4)
    (h : ∏ e, sgn (a e) * sgn (b e) = (-1 : ℂ) ^ Fintype.card E) :
    Even (Finset.univ.filter fun e => blk (a e) = blk (b e)).card := by
  classical
  rw [prod_sgn_eq, neg_one_pow_eq_ite, neg_one_pow_eq_ite] at h
  have hiff : Even (Finset.univ.filter fun e => ¬ blk (a e) = blk (b e)).card ↔
      Even (Fintype.card E) := by
    by_cases h1 : Even (Finset.univ.filter fun e => ¬ blk (a e) = blk (b e)).card <;>
      by_cases h2 : Even (Fintype.card E) <;> simp only [h1, h2, ite_true, ite_false] at h <;>
      norm_num at h <;> tauto
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset E)) (fun e => blk (a e) = blk (b e))
  rw [Finset.card_univ] at hsum
  have := Nat.even_add (m := (Finset.univ.filter fun e => blk (a e) = blk (b e)).card)
    (n := (Finset.univ.filter fun e => ¬ blk (a e) = blk (b e)).card)
  rw [hsum] at this
  tauto

variable [Fintype F] [DecidableEq F]

/-- **A block-summed loop of propagator entries** with the sign condition: (T₉′) at one loop for
`1 ≤ r ≤ 4` lines, at any masses. -/
theorem jointEnergyFirstIntegrable_propLoop (Φ : Lepton.Flavors F) (rep : F → F)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    {L : Type*} [Fintype L] [DecidableEq L] (c : L → ℝ) (hc : ∀ l, c l ≠ 0)
    (q : L → Fin 4 → ℝ) {ε : ℝ} (hε : 0 < ε) (a b : L → Fin 4)
    (hsgn : ∏ l, sgn (a l) * sgn (b l) = (-1 : ℂ) ^ Fintype.card L)
    (h1 : 1 ≤ Fintype.card L) (h4 : Fintype.card L ≤ 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * ∏ l, (1 / I) *
        QED.OneLoop.electronPropagator (Φ.mass f) ε (c l • ℓ 0 + q l) (a l) (b l) := by
  classical
  have hsum : ∑ _l : L, (1 : ℕ) = Fintype.card L := by simp
  have h := jointEnergyFirstIntegrable_entrySum Φ rep hrep hPV₁ hPV₂ c hc q hε a b
    (even_card_blk_of_prod a b hsgn) (fun _ => 1)
    (fun _ l => (1 / I) * (1 : Matrix (Fin 4) (Fin 4) ℂ) (a l) (b l))
    (fun _ l k => (1 / I) * electronNumerator 0 (c l • k + q l) (a l) (b l))
    (fun _ l => (AffPoly.comp_affine (electronNumerator_affine 0 _ _) _ _).const_mul _)
    (fun _ _ h => absurd h one_ne_zero) (fun _ => 1) (AffPoly.const 1) (by rw [hsum]; exact h4)
    (by rw [hsum]; omega)
  refine (congrArg _ (funext fun ℓ => Finset.sum_congr rfl fun f _ => ?_)).mp h
  congr 1
  rw [one_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [electronPropagator_apply, electronNumerator_eq_ite, electronNumerator_eq_ite]
  split_ifs <;> ring

variable {Z : Wick.FermionVertex κ → Prop} [DecidablePred Z] {C : Contraction 1 nA κ}

/-- **The sign product of the lines of a closed loop** whose vertex pairs are all
different-block is `(-1)^r`. -/
theorem prod_sgn_zLine (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x)
    (α β : Wick.FermionVertex κ → Fin 4) (hd : ∀ s : {s // Z s}, ¬ blk (α s.1) = blk (β s.1)) :
    ∏ f : ZLine C Z, sgn (β f.1.1) * sgn (α f.1.tail) =
      (-1 : ℂ) ^ Fintype.card (ZLine C Z) := by
  have h := prod_sgn_closed hZ α β
  have h1 : ∏ s : {s // Z s}, sgn (α s.1) * sgn (β s.1) =
      (-1 : ℂ) ^ Fintype.card (ZLine C Z) := by
    rw [card_zLine hZ, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [sgn_mul_sgn]
    simp [hd s]
  rw [h1] at h
  have h2 : ((-1 : ℂ) ^ Fintype.card (ZLine C Z)) * (-1) ^ Fintype.card (ZLine C Z) = 1 := by
    rw [← mul_pow]; norm_num
  calc _ = ((-1 : ℂ) ^ Fintype.card (ZLine C Z) * (-1) ^ Fintype.card (ZLine C Z)) *
        ∏ f : ZLine C Z, sgn (β f.1.1) * sgn (α f.1.tail) := by rw [h2, one_mul]
    _ = _ := by rw [mul_comm ((-1 : ℂ) ^ _) ((-1 : ℂ) ^ _), mul_assoc, h, mul_one]

/-- **(T₉′) of a closed loop carrying one loop momentum, summed over the flavours**, at any
masses: the loop has `1 ≤ r ≤ 4` lines and all its vertex pairs are different-block. -/
theorem jointEnergyFirstIntegrable_zGroup (Φ : Lepton.Flavors F) (rep : F → F)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    {ε : ℝ} (hε : 0 < ε) (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x)
    (α β : Wick.FermionVertex κ → Fin 4) (hd : ∀ s : {s // Z s}, ¬ blk (α s.1) = blk (β s.1))
    (c : ZLine C Z → ℝ) (hc : ∀ l, c l ≠ 0) (q : ZLine C Z → Fin 4 → ℝ)
    (h1 : 1 ≤ Fintype.card (ZLine C Z)) (h4 : Fintype.card (ZLine C Z) ≤ 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      ∑ f, (Φ.coeff f : ℂ) * ∏ l : ZLine C Z, (1 / I) *
        QED.OneLoop.electronPropagator (Φ.mass f) ε (c l • ℓ 0 + q l) (β l.1.1)
          (α l.1.tail) := by
  classical
  exact jointEnergyFirstIntegrable_propLoop Φ rep hrep hPV₁ hPV₂ c hc q hε _ _
    (prod_sgn_zLine hZ α β hd) h1 h4

end QED.GradedProof.X0

end
