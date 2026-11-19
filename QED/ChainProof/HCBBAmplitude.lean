/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBBRouting
public import QED.ChainProof.HCLimitDD
public import QED.TwoLoop.NestedVPAmplitude
public import QED.TwoLoop.RelabelCountertermValue

/-!
# The bubble–bubble representative: flavorings, spinor sums and the amplitude

Helper level, Phase 5 Stage 1a, obligation O3-6 for `QED.ChainProof.Enum.repBB`, continuing
`QED/ChainProof/HCBBRouting.lean`.

* `preserves_iff`, `sum_preserves`, `loopWeight_flavBB`: the flavorings preserved by the
  representative are those with the open line of flavour `0`, the bubble `5 ⇄ 6` of one flavour
  `a` and the bubble `3 ⇄ 4` of one flavour `b`; the regulator weight (X₇) is `c_a c_b`.
* `spinSumBB`: the sum over the spinor indices of the seven vertices, with the external indices
  fixed, is the open-line chain times the traces of the two bubbles.
* `contractionAmplitude₂_flavBB`: the amplitude (T₇) for the bubble flavours `a`, `b` in the
  nested routing: the open-line chain `QED.TwoLoop.NestedVP.outerChain`, the photon propagators of
  momenta `k`, `-k`, `-k` and the two bubble traces.

The factorization into the outer factor and the two vacuum polarization integrands is in
`QED/ChainProof/HCBBWick.lean`.
-/

@[expose] public section

namespace QED.ChainProof.HCBB

open QED.WickModel QED.TwoLoop.Routing QED.ChainProof.Enum Complex

/-- The fermion fields of the seven gauge vertices. -/
local notation "FV" => Wick.FermionVertex kBB

/-- The photon fields of the seven gauge vertices. -/
local notation "PS" => Wick.PhotonSlot kBB

/-! ### Flavorings -/

/-- The flavoring with the open line of flavour `0`, the bubble `5 ⇄ 6` of flavour `a` and the
bubble `3 ⇄ 4` of flavour `b`. -/
def flavBB (a b : Fin 3) : Flavoring kBB :=
  ⟨fun t => if 5 ≤ t.1.val then a else if 3 ≤ t.1.val then b else 0, fun _ h => absurd rfl h⟩

theorem flavBB_apply (a b : Fin 3) : (flavBB a b).1 (fv kBB 0) = 0 ∧
    (flavBB a b).1 (fv kBB 1) = 0 ∧ (flavBB a b).1 (fv kBB 2) = 0 ∧
    (flavBB a b).1 (fv kBB 3) = b ∧ (flavBB a b).1 (fv kBB 4) = b ∧
    (flavBB a b).1 (fv kBB 5) = a ∧ (flavBB a b).1 (fv kBB 6) = a := by
  simp [flavBB, fv]

theorem preserves_flavBB : ∀ a b : Fin 3, Preserves repBB (flavBB a b) := by
  unfold Preserves
  decide +kernel

theorem fermionPerm_repBB : repBB.1.1 (.inr (fv kBB 0)) = .inl 0 ∧
    repBB.1.1 (.inr (fv kBB 1)) = .inr (fv kBB 0) ∧
    repBB.1.1 (.inr (fv kBB 2)) = .inr (fv kBB 1) ∧ repBB.1.1 (.inl 0) = .inr (fv kBB 2) ∧
    repBB.1.1 (.inr (fv kBB 4)) = .inr (fv kBB 3) ∧
    repBB.1.1 (.inr (fv kBB 6)) = .inr (fv kBB 5) := by decide +kernel

/-- **The preserved flavorings**: the open line has flavour `0`, each bubble one flavour. -/
theorem preserves_iff (φ : Flavoring kBB) :
    Preserves repBB φ ↔ φ = flavBB (φ.1 (fv kBB 5)) (φ.1 (fv kBB 3)) := by
  refine ⟨fun hφ => ?_, fun h => h ▸ preserves_flavBB _ _⟩
  obtain ⟨s0, s1, s2, s3, s4, s6⟩ := fermionPerm_repBB
  have h0 := hφ (.inr (fv kBB 0))
  have h1 := hφ (.inr (fv kBB 1))
  have h3 := hφ (.inl 0)
  have h4 := hφ (.inr (fv kBB 4))
  have h6 := hφ (.inr (fv kBB 6))
  rw [s0] at h0
  rw [s1] at h1
  rw [s3] at h3
  rw [s4] at h4
  rw [s6] at h6
  simp only [fermionFlavor] at h0 h1 h3 h4 h6
  obtain ⟨f0, f1, f2, f3, f4, f5, f6⟩ := flavBB_apply (φ.1 (fv kBB 5)) (φ.1 (fv kBB 3))
  apply Subtype.ext
  funext t
  obtain ⟨j, hj⟩ := t
  fin_cases j
  · exact h0.symm.trans f0.symm
  · exact (h1.symm.trans h0.symm).trans f1.symm
  · exact h3.trans f2.symm
  · exact f3.symm
  · exact h4.symm.trans f4.symm
  · exact f5.symm
  · exact h6.symm.trans f6.symm

/-- **The sum over the preserved flavorings** is the sum over the flavours of the two bubbles. -/
theorem sum_preserves {M : Type*} [AddCommMonoid M] [Fintype (Flavoring kBB)]
    [DecidablePred (Preserves repBB)] (F : Flavoring kBB → M) :
    ∑ φ ∈ (Finset.univ : Finset (Flavoring kBB)).filter (Preserves repBB), F φ =
      ∑ a : Fin 3, ∑ b : Fin 3, F (flavBB a b) := by
  rw [← Fintype.sum_prod_type']
  exact Finset.sum_nbij' (fun φ => (φ.1 (fv kBB 5), φ.1 (fv kBB 3))) (fun x => flavBB x.1 x.2)
    (fun _ _ => Finset.mem_univ _)
    (fun x _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, preserves_flavBB x.1 x.2⟩)
    (fun φ hφ => ((preserves_iff φ).mp (Finset.mem_filter.mp hφ).2).symm)
    (fun x _ => Prod.ext (flavBB_apply x.1 x.2).2.2.2.2.2.1 (flavBB_apply x.1 x.2).2.2.2.1)
    (fun φ hφ => by rw [← (preserves_iff φ).mp (Finset.mem_filter.mp hφ).2])

/-! ### The two closed loops -/

theorem repBB_pow_four : repBB.1.1 ^ 4 = 1 := by decide +kernel

theorem not_sameCycle_bb : ¬ Equiv.Perm.SameCycle repBB.1.1 (.inl 0) (.inr (fv kBB 3)) ∧
    ¬ Equiv.Perm.SameCycle repBB.1.1 (.inl 0) (.inr (fv kBB 5)) ∧
    ¬ Equiv.Perm.SameCycle repBB.1.1 (.inr (fv kBB 5)) (.inr (fv kBB 3)) := by
  simp only [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (by norm_num : 0 < 4) repBB_pow_four]
  decide +kernel

theorem sameCycle_bb_cases : ∀ x : Fin 1 ⊕ FV, Equiv.Perm.SameCycle repBB.1.1 x (.inl 0) ∨
    Equiv.Perm.SameCycle repBB.1.1 x (.inr (fv kBB 5)) ∨
    Equiv.Perm.SameCycle repBB.1.1 x (.inr (fv kBB 3)) := by
  simp only [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (by norm_num : 0 < 4) repBB_pow_four]
  decide +kernel

/-- The closed fermion loop `5 → 6 → 5`. -/
def loop56 : ClosedLoop repBB :=
  ⟨Quotient.mk _ (.inr (fv kBB 5)), fun i h => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact not_sameCycle_bb.2.1 (Quotient.exact h)⟩

/-- The closed fermion loop `3 → 4 → 3`. -/
def loop34 : ClosedLoop repBB :=
  ⟨Quotient.mk _ (.inr (fv kBB 3)), fun i h => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact not_sameCycle_bb.1 (Quotient.exact h)⟩

theorem loop56_ne_loop34 : loop56 ≠ loop34 := fun h =>
  not_sameCycle_bb.2.2 (Quotient.exact (congrArg Subtype.val h))

/-- The representative has exactly the two closed fermion loops of its bubbles. -/
theorem eq_loop56_or_loop34 (q : ClosedLoop repBB) : q = loop56 ∨ q = loop34 := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rcases sameCycle_bb_cases x with h | h | h
  · exact absurd (Quotient.sound h.symm) (hq 0)
  · exact Or.inl (Subtype.ext (Quotient.sound h))
  · exact Or.inr (Subtype.ext (Quotient.sound h))

theorem fermionFlavor_out {φ : Flavoring kBB} (hφ : Preserves repBB φ) {x : Fin 1 ⊕ FV}
    {q : ClosedLoop repBB} (hq : q.1 = Quotient.mk _ x) :
    fermionFlavor φ q.1.out = fermionFlavor φ x := by
  have h : (Quotient.mk _ q.1.out : Quotient (Equiv.Perm.SameCycle.setoid repBB.1.1)) =
      Quotient.mk _ x := by rw [Quotient.out_eq, hq]
  exact QED.TwoLoop.Relabel.fermionFlavor_eq_of_sameCycle hφ (Quotient.exact h)

open scoped Classical in
/-- The regulator weight (X₇) of the bubble flavours `a`, `b` is `c_a c_b`. -/
theorem loopWeight_flavBB (P : Params) (a b : Fin 3) :
    loopWeight P repBB (flavBB a b) = P.loopCoeff a * P.loopCoeff b := by
  rw [loopWeight, Fintype.prod_eq_mul loop56 loop34 loop56_ne_loop34 fun q hq =>
    absurd (eq_loop56_or_loop34 q) (not_or.mpr hq)]
  rw [fermionFlavor_out (preserves_flavBB a b) (x := .inr (fv kBB 5)) rfl,
    fermionFlavor_out (preserves_flavBB a b) (x := .inr (fv kBB 3)) rfl]
  simp only [fermionFlavor, (flavBB_apply a b).2.2.2.2.2.1, (flavBB_apply a b).2.2.2.1]

/-! ### The spinor index sum -/

/-- Four spinor indices. -/
abbrev Spin4 : Type := Fin 4 × Fin 4 × Fin 4 × Fin 4

/-- The two spinor index families as the external pair `(a₂, b₀)`, the open line
`(a₀, b₁, a₁, b₂)`, the bubble `3 ⇄ 4` as `(a₃, b₄, a₄, b₃)` and the bubble `5 ⇄ 6` as
`(a₅, b₆, a₆, b₅)`. -/
def spinEquivBB : ((Fin 4 × Fin 4) × Spin4 × Spin4 × Spin4) ≃ (FV → Fin 4) × (FV → Fin 4) where
  toFun := fun ⟨⟨a2, b0⟩, ⟨a0, b1, a1, b2⟩, ⟨a3, b4, a4, b3⟩, ⟨a5, b6, a6, b5⟩⟩ =>
    (fun t => ![a0, a1, a2, a3, a4, a5, a6] t.1, fun t => ![b0, b1, b2, b3, b4, b5, b6] t.1)
  invFun p := ((p.1 (fv kBB 2), p.2 (fv kBB 0)),
    (p.1 (fv kBB 0), p.2 (fv kBB 1), p.1 (fv kBB 1), p.2 (fv kBB 2)),
    (p.1 (fv kBB 3), p.2 (fv kBB 4), p.1 (fv kBB 4), p.2 (fv kBB 3)),
    (p.1 (fv kBB 5), p.2 (fv kBB 6), p.1 (fv kBB 6), p.2 (fv kBB 5)))
  left_inv x := by
    obtain ⟨⟨_, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩ := x
    rfl
  right_inv p := by
    obtain ⟨α, β⟩ := p
    refine Prod.ext (funext fun t => ?_) (funext fun t => ?_) <;>
      · obtain ⟨j, hj⟩ := t
        fin_cases j <;> rfl

theorem spinEquivBB_apply (a2 b0 a0 b1 a1 b2 a3 b4 a4 b3 a5 b6 a6 b5 : Fin 4) :
    let x := spinEquivBB ((a2, b0), (a0, b1, a1, b2), (a3, b4, a4, b3), (a5, b6, a6, b5))
    x.1 (fv kBB 0) = a0 ∧ x.1 (fv kBB 1) = a1 ∧ x.1 (fv kBB 2) = a2 ∧ x.1 (fv kBB 3) = a3 ∧
      x.1 (fv kBB 4) = a4 ∧ x.1 (fv kBB 5) = a5 ∧ x.1 (fv kBB 6) = a6 ∧
      x.2 (fv kBB 0) = b0 ∧ x.2 (fv kBB 1) = b1 ∧ x.2 (fv kBB 2) = b2 ∧ x.2 (fv kBB 3) = b3 ∧
      x.2 (fv kBB 4) = b4 ∧ x.2 (fv kBB 5) = b5 ∧ x.2 (fv kBB 6) = b6 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The summand of the spinor index sum: the external indices `αe` (the `Ψ̄` of vertex `2`) and
`βe` (the `Ψ` of vertex `0`) fixed, the seven vertex matrices `G t`, the open-line propagators
`S₀₁`, `S₁₂` and the bubble propagators `S₄₃`, `S₃₄`, `S₆₅`, `S₅₆` (`Sᵤᵥ` on the line `u → v`). -/
def spinTermBB (G : Fin 7 → Matrix (Fin 4) (Fin 4) ℂ)
    (S01 S12 S43 S34 S65 S56 : Matrix (Fin 4) (Fin 4) ℂ) (αe βe : Fin 4) (α β : FV → Fin 4) : ℂ :=
  (if α (fv kBB 2) = αe ∧ β (fv kBB 0) = βe then (1 : ℂ) else 0) *
    (G 0 (α (fv kBB 0)) (β (fv kBB 0)) * G 1 (α (fv kBB 1)) (β (fv kBB 1)) *
      G 2 (α (fv kBB 2)) (β (fv kBB 2)) * G 3 (α (fv kBB 3)) (β (fv kBB 3)) *
      G 4 (α (fv kBB 4)) (β (fv kBB 4)) * G 5 (α (fv kBB 5)) (β (fv kBB 5)) *
      G 6 (α (fv kBB 6)) (β (fv kBB 6)) *
      (S01 (β (fv kBB 1)) (α (fv kBB 0)) * S12 (β (fv kBB 2)) (α (fv kBB 1)) *
        S43 (β (fv kBB 3)) (α (fv kBB 4)) * S34 (β (fv kBB 4)) (α (fv kBB 3)) *
        S65 (β (fv kBB 5)) (α (fv kBB 6)) * S56 (β (fv kBB 6)) (α (fv kBB 5))))

/-- The open chain `A S B T C` as a sum over four spinor indices. -/
theorem chain_eq_sum (A S B T C : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    (A * S * B * T * C) i j = ∑ x : Spin4, C x.1 j * T x.2.1 x.1 * B x.2.2.1 x.2.1 *
      S x.2.2.2 x.2.2.1 * A i x.2.2.2 := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- The trace of a loop `G S H T` as a sum over four spinor indices. -/
theorem trace_eq_sum (G S H T : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (G * S * H * T) = ∑ x : Spin4, G x.1 x.2.2.2 * S x.2.2.2 x.2.2.1 *
      H x.2.2.1 x.2.1 * T x.2.1 x.1 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]

theorem sum_mul_mul_prod {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] (X : A → ℂ)
    (Y : B → ℂ) (Z : C → ℂ) :
    ∑ x : A × B × C, X x.1 * Y x.2.1 * Z x.2.2 = (∑ a, X a) * (∑ b, Y b) * ∑ c, Z c := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]

/-- **The spinor index sum** of the seven gauge vertices, the spinor index `αe` of the outgoing
`Ψ̄` at vertex `2` and `βe` of the incoming `Ψ` at vertex `0` fixed: the open-line chain
`G₂ S₁₂ G₁ S₀₁ G₀` times the traces `Tr[G₃ S₄₃ G₄ S₃₄]` and `Tr[G₅ S₆₅ G₆ S₅₆]` of the two
bubbles. -/
theorem spinSumBB (G : Fin 7 → Matrix (Fin 4) (Fin 4) ℂ)
    (S01 S12 S43 S34 S65 S56 : Matrix (Fin 4) (Fin 4) ℂ) (αe βe : Fin 4) :
    ∑ α : FV → Fin 4, ∑ β : FV → Fin 4, spinTermBB G S01 S12 S43 S34 S65 S56 αe βe α β =
      (G 2 * S12 * G 1 * S01 * G 0) αe βe * Matrix.trace (G 3 * S43 * G 4 * S34) *
        Matrix.trace (G 5 * S65 * G 6 * S56) := by
  rw [← Fintype.sum_prod_type', ← spinEquivBB.sum_comp, Fintype.sum_prod_type]
  have hx : ∀ (e : Fin 4 × Fin 4) (x : Spin4 × Spin4 × Spin4),
      spinTermBB G S01 S12 S43 S34 S65 S56 αe βe (spinEquivBB (e, x)).1 (spinEquivBB (e, x)).2 =
        (if e.1 = αe ∧ e.2 = βe then (1 : ℂ) else 0) *
          ((G 0 x.1.1 e.2 * S01 x.1.2.1 x.1.1 * G 1 x.1.2.2.1 x.1.2.1 *
              S12 x.1.2.2.2 x.1.2.2.1 * G 2 e.1 x.1.2.2.2) *
            (G 3 x.2.1.1 x.2.1.2.2.2 * S43 x.2.1.2.2.2 x.2.1.2.2.1 *
              G 4 x.2.1.2.2.1 x.2.1.2.1 * S34 x.2.1.2.1 x.2.1.1) *
            (G 5 x.2.2.1 x.2.2.2.2.2 * S65 x.2.2.2.2.2 x.2.2.2.2.1 *
              G 6 x.2.2.2.2.1 x.2.2.2.1 * S56 x.2.2.2.1 x.2.2.1)) := by
    rintro ⟨a2, b0⟩ ⟨⟨a0, b1, a1, b2⟩, ⟨a3, b4, a4, b3⟩, ⟨a5, b6, a6, b5⟩⟩
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, y0, y1, y2, y3, y4, y5, y6⟩ :=
      spinEquivBB_apply a2 b0 a0 b1 a1 b2 a3 b4 a4 b3 a5 b6 a6 b5
    simp only [spinTermBB, x0, x1, x2, x3, x4, x5, x6, y0, y1, y2, y3, y4, y5, y6]
    ring
  simp only [hx]
  rw [Fintype.sum_prod_type]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [sum_mul_mul_prod (fun x : Spin4 => G 0 x.1 βe * S01 x.2.1 x.1 * G 1 x.2.2.1 x.2.1 *
      S12 x.2.2.2 x.2.2.1 * G 2 αe x.2.2.2)
    (fun x : Spin4 => G 3 x.1 x.2.2.2 * S43 x.2.2.2 x.2.2.1 * G 4 x.2.2.1 x.2.1 * S34 x.2.1 x.1)
    (fun x : Spin4 => G 5 x.1 x.2.2.2 * S65 x.2.2.2 x.2.2.1 * G 6 x.2.2.1 x.2.1 * S56 x.2.1 x.1),
    chain_eq_sum, trace_eq_sum, trace_eq_sum]

/-! ### The amplitude -/

/-- The photon field of the gauge vertex `t`. -/
def pgBB (t : Fin 7) : PS := ⟨t, ⟨0, Nat.one_pos⟩⟩

theorem vertexFactor_bb (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : FV → Fin 4) (lor : PS → Fin 4)
    (kψ : FV → Fin 4 → ℝ) (kA : PS → Fin 4 → ℝ) (t : Fin 7) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * e * Dirac.gamma (lor (pgBB t)) (α ⟨t, fun h => nomatch h⟩) (β ⟨t, fun h => nomatch h⟩) :=
  QED.TwoLoop.Relabel.vertexFactor_eq_of_gauge e δ₁ δ₂ δm δ₃ m α β lor kψ kA rfl

theorem bb_cond (α β : FV → Fin 4) (lor : PS → Fin 4) (αOut βIn μ : Fin 1 → Fin 4) :
    ((∀ i t, repBB.1.1 (.inl i) = .inr t → α t = αOut i) ∧
        (∀ t i, repBB.1.1 (.inr t) = .inl i → β t = βIn i) ∧
        (∀ j a, repBB.1.2 (.inl j) = .inr a → lor a = μ j)) ↔
      lor (pgBB 1) = μ 0 ∧ (α (fv kBB 2) = αOut 0 ∧ β (fv kBB 0) = βIn 0) := by
  have h1 : ∀ t, repBB.1.1 (.inl 0) = .inr t ↔ t = fv kBB 2 := by decide +kernel
  have h2 : ∀ t, repBB.1.1 (.inr t) = .inl 0 ↔ t = fv kBB 0 := by decide +kernel
  have h3 : ∀ a, repBB.1.2 (.inl 0) = .inr a ↔ a = pgBB 1 := by decide +kernel
  simp only [Fin.forall_fin_one, h1, h2, h3, forall_eq]
  tauto

theorem bb_slots_nodup : [pgBB 1, pgBB 0, pgBB 2, pgBB 6, pgBB 5, pgBB 4, pgBB 3].Nodup := by
  decide +kernel

theorem bb_slots_cover : ∀ x : PS, x = pgBB 1 ∨ x = pgBB 0 ∨ x = pgBB 2 ∨ x = pgBB 6 ∨
    x = pgBB 5 ∨ x = pgBB 4 ∨ x = pgBB 3 := by
  decide +kernel

theorem head_photBB' : (photBB 0).head = pgBB 6 ∧ (photBB 1).head = pgBB 3 ∧
    (photBB 2).head = pgBB 5 := head_photBB

/-- **The amplitude** (T₇) of the representative for the bubble flavours `a` (bubble `5 ⇄ 6`) and
`b` (bubble `3 ⇄ 4`), in the nested routing: the open-line chain, the photon propagators of
momenta `k` (line `0 — 6`), `-k` (line `2 — 3`) and `-k` (line `4 — 5`), and the traces of the two
bubbles. -/
theorem contractionAmplitude₂_flavBB (P : Params) (a b : Fin 3) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (q₂ q₁ k : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P repBB (flavBB a b) pIn kIn (bbMom (pIn 0) (kIn 0) q₂ q₁ k)
        αOut βIn μ =
      (I * P.e) ^ 7 * (1 / I) ^ 9 * ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l6 : Fin 4, ∑ l5 : Fin 4,
        ∑ l4 : Fin 4, ∑ l3 : Fin 4,
        QED.TwoLoop.NestedVP.outerChain P (pIn 0) (kIn 0) k (μ 0) l0 l2 (αOut 0) (βIn 0) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k l0 l6 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (-k) l2 l3 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (-k) l4 l5 *
          Matrix.trace (Dirac.gamma l3 * QED.OneLoop.electronPropagator (P.mass b) P.ε (q₁ + k) *
            Dirac.gamma l4 * QED.OneLoop.electronPropagator (P.mass b) P.ε q₁) *
          Matrix.trace (Dirac.gamma l5 * QED.OneLoop.electronPropagator (P.mass a) P.ε (q₂ + k) *
            Dirac.gamma l6 * QED.OneLoop.electronPropagator (P.mass a) P.ε q₂) := by
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := val_lineBB
  obtain ⟨t0, t1, t2, t3, t4, t5⟩ := tail_lineBB
  obtain ⟨w0, w1, w2⟩ := val_photBB
  obtain ⟨h0, h1, h2⟩ := head_photBB'
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8⟩ := bbMom_apply (pIn 0) (kIn 0) q₂ q₁ k
  obtain ⟨f0, f1, f2, f3, f4, f5, f6⟩ := flavBB_apply a b
  have hm0 : P.mass 0 = P.m := rfl
  unfold contractionAmplitude₂
  rw [show (∑ α : FV → Fin 4, ∑ β : FV → Fin 4, ∑ lor : PS → Fin 4, _) = ∑ lor, ∑ α, ∑ β, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  refine (Finset.sum_congr rfl fun lor _ => ?_).trans (?_ : ∑ lor : PS → Fin 4,
    (if lor (pgBB 1) = μ 0 then (1 : ℂ) else 0) *
      ((I * P.e) ^ 7 * (1 / I) ^ 9 *
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k (lor (pgBB 0)) (lor (pgBB 6)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (-k) (lor (pgBB 2)) (lor (pgBB 3)) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (-k) (lor (pgBB 4)) (lor (pgBB 5)))) *
      ((Dirac.gamma (lor (pgBB 2)) *
            QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + kIn 0 - k) *
            Dirac.gamma (lor (pgBB 1)) * QED.OneLoop.electronPropagator P.m P.ε (pIn 0 - k) *
          Dirac.gamma (lor (pgBB 0))) (αOut 0) (βIn 0) *
        Matrix.trace (Dirac.gamma (lor (pgBB 3)) *
          QED.OneLoop.electronPropagator (P.mass b) P.ε (q₁ + k) * Dirac.gamma (lor (pgBB 4)) *
          QED.OneLoop.electronPropagator (P.mass b) P.ε q₁) *
        Matrix.trace (Dirac.gamma (lor (pgBB 5)) *
          QED.OneLoop.electronPropagator (P.mass a) P.ε (q₂ + k) * Dirac.gamma (lor (pgBB 6)) *
          QED.OneLoop.electronPropagator (P.mass a) P.ε q₂)) = _)
  · rw [← spinSumBB (fun t => Dirac.gamma (lor (pgBB t))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    unfold spinTermBB
    simp only [bb_cond, Fin.prod_univ_seven, prod_fermionLine, prod_photonLine, vertexFactor_bb,
      v0, v1, v2, v3, v4, v5, t0, t1, t2, t3, t4, t5, w0, w1, w2, h0, h1, h2, n0, n1, n2, n3, n4,
      n5, n6, n7, n8, f1, f2, f3, f4, f5, f6, hm0, QED.TwoLoop.Insertion.ite_and_eq_mul]
    simp only [fv, pg, pgBB]
    ring
  · have hnd := bb_slots_nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnd
    obtain ⟨⟨n10, n12, n16, n15, n14, n13⟩, ⟨n02, n06, n05, n04, n03⟩, ⟨n26, n25, n24, n23⟩,
      ⟨n65, n64, n63⟩, ⟨n54, n53⟩, n43, -⟩ := hnd
    rw [QED.ChainProof.HCLimit.sum_pi_seven bb_slots_nodup bb_slots_cover]
    simp only [ite_true, Ne.symm n10, Ne.symm n12, Ne.symm n13, Ne.symm n14, Ne.symm n15,
      Ne.symm n16, Ne.symm n02, Ne.symm n03, Ne.symm n04, Ne.symm n05, Ne.symm n06, Ne.symm n23,
      Ne.symm n24, Ne.symm n25, Ne.symm n26, Ne.symm n65, Ne.symm n64, Ne.symm n63, Ne.symm n54,
      Ne.symm n53, Ne.symm n43, ite_false, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    unfold QED.TwoLoop.NestedVP.outerChain
    ring

end QED.ChainProof.HCBB

end
