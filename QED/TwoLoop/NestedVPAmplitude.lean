/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.NestedVPRouting
public import QED.WickModel.TwoPoint

/-!
# The vacuum-polarization class: the integrand factorizes

Part of obligation O2-8 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3). In the nested routing
(`QED.TwoLoop.NestedVP.nestedMom`) the regulated amplitude (T₈) of the class `VP`, times the loop
measure `(2π)⁻⁸`, is a finite sum over two Lorentz indices `ρ, σ` of an outer factor depending only
on the photon momentum `k` times the one-loop vacuum polarization integrand
`QED.WickModel.vacuumPolarizationIntegrand P P.ε k q ρ σ` of (62.12), the Pauli–Villars flavours
summed inside it.

* `QED.TwoLoop.NestedVP.preserves_iff`, `sum_preserves`, `loopWeight_flavV`: the flavorings
  preserved by the representative are those with the open line of flavour `0` and the loop of a
  single flavour `f`; the regulator weight (X₇) is `c_f`.
* `QED.TwoLoop.NestedVP.spinSum`: the sum over the spinor indices of the five vertices, with the
  external indices fixed, is the open-line chain times the trace of the loop.
* `QED.TwoLoop.NestedVP.contractionAmplitude₂_flavV`: the amplitude (T₇) for the loop flavour
  `f`.
* `QED.TwoLoop.NestedVP.integrand_eq`: **the factorization**
  `(2π)⁻⁸ · regulatedAmplitude₂ = ∑ ρ σ, vpOuter … k ρ σ * vacuumPolarizationIntegrand P P.ε k q ρ σ`.

The factorization is an identity of integrands at every `ε`, with no hypothesis.
-/

@[expose] public section

namespace QED.TwoLoop.NestedVP

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Relabel Complex

/-- The fermion fields of the five gauge vertices. -/
local notation "FV" => Wick.FermionVertex (gauges 5)

/-- The photon fields of the five gauge vertices. -/
local notation "PS" => Wick.PhotonSlot (gauges 5)

/-! ### Flavorings -/

/-- The flavoring with the open line of flavour `0` and the loop `3, 4` of flavour `f`. -/
def flavV (f : Fin 3) : Flavoring (gauges 5) :=
  ⟨fun t => if 3 ≤ t.1.val then f else 0, fun _ h => absurd rfl h⟩

theorem flavV_apply (f : Fin 3) : (flavV f).1 (fv5 0) = 0 ∧ (flavV f).1 (fv5 1) = 0 ∧
    (flavV f).1 (fv5 2) = 0 ∧ (flavV f).1 (fv5 3) = f ∧ (flavV f).1 (fv5 4) = f := by
  simp [flavV, fv5]

theorem preserves_flavV : ∀ f : Fin 3, Preserves cV (flavV f) := by
  unfold Preserves
  decide +kernel

theorem fermionPerm_cV : cV.1.1 (.inr (fv5 0)) = .inl 0 ∧ cV.1.1 (.inr (fv5 1)) = .inr (fv5 0) ∧
    cV.1.1 (.inr (fv5 2)) = .inr (fv5 1) ∧ cV.1.1 (.inl 0) = .inr (fv5 2) ∧
    cV.1.1 (.inr (fv5 4)) = .inr (fv5 3) := by decide +kernel

/-- **The preserved flavorings**: the open line has flavour `0`, the loop one flavour. -/
theorem preserves_iff (φ : Flavoring (gauges 5)) :
    Preserves cV φ ↔ φ = flavV (φ.1 (fv5 3)) := by
  refine ⟨fun hφ => ?_, fun h => h ▸ preserves_flavV _⟩
  obtain ⟨s0, s1, s2, s3, s4⟩ := fermionPerm_cV
  have h0 := hφ (.inr (fv5 0))
  have h1 := hφ (.inr (fv5 1))
  have h2 := hφ (.inr (fv5 2))
  have h3 := hφ (.inl 0)
  have h4 := hφ (.inr (fv5 4))
  rw [s0] at h0
  rw [s1] at h1
  rw [s2] at h2
  rw [s3] at h3
  rw [s4] at h4
  simp only [fermionFlavor] at h0 h1 h2 h3 h4
  apply Subtype.ext
  funext t
  obtain ⟨j, hj⟩ := t
  change φ.1 (fv5 j) = (flavV (φ.1 (fv5 3))).1 (fv5 j)
  fin_cases j
  · exact h0.symm.trans (flavV_apply _).1.symm
  · exact (h1.symm.trans h0.symm).trans (flavV_apply _).2.1.symm
  · exact h3.trans (flavV_apply _).2.2.1.symm
  · exact (flavV_apply _).2.2.2.1.symm
  · exact h4.symm.trans (flavV_apply _).2.2.2.2.symm

/-- **The sum over the preserved flavorings** is the sum over the flavour of the loop. -/
theorem sum_preserves {M : Type*} [AddCommMonoid M] [Fintype (Flavoring (gauges 5))]
    [DecidablePred (Preserves cV)] (F : Flavoring (gauges 5) → M) :
    ∑ φ ∈ (Finset.univ : Finset (Flavoring (gauges 5))).filter (Preserves cV), F φ =
      ∑ f : Fin 3, F (flavV f) :=
  Finset.sum_nbij' (fun φ => φ.1 (fv5 3)) flavV (fun _ _ => Finset.mem_univ _)
    (fun f _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, preserves_flavV f⟩)
    (fun φ hφ => ((preserves_iff φ).mp (Finset.mem_filter.mp hφ).2).symm)
    (fun f _ => (flavV_apply f).2.2.2.1)
    (fun φ hφ => by rw [← (preserves_iff φ).mp (Finset.mem_filter.mp hφ).2])

section Cycles

variable {α : Type*}

/-- For a permutation of order dividing `n > 0`, being in the same cycle is a bounded search. -/
theorem sameCycle_iff_of_pow {f : Equiv.Perm α} {n : ℕ} (hn : 0 < n) (hf : f ^ n = 1) (x y : α) :
    f.SameCycle x y ↔ ∃ i : Fin n, (f ^ (i : ℕ)) x = y := by
  constructor
  · rintro ⟨k, rfl⟩
    have h0 : 0 ≤ k % n := Int.emod_nonneg k (by omega)
    have h3 : k % n < n := Int.emod_lt_of_pos k (by omega)
    refine ⟨⟨(k % n).toNat, by omega⟩, ?_⟩
    simp only
    have hf' : f ^ (n : ℤ) = 1 := by exact_mod_cast hf
    rw [← zpow_natCast, Int.toNat_of_nonneg h0, ← zpow_eq_zpow_emod k hf']
  · rintro ⟨i, rfl⟩
    exact ⟨(i : ℕ), by rw [zpow_natCast]⟩

end Cycles

theorem cV_pow_four : cV.1.1 ^ 4 = 1 := by decide +kernel

theorem not_sameCycle_ext_loop : ¬ Equiv.Perm.SameCycle cV.1.1 (.inl 0) (.inr (fv5 3)) := by
  rw [sameCycle_iff_of_pow (by norm_num) cV_pow_four]
  decide +kernel

theorem sameCycle_ext_or_loop : ∀ x : Fin 1 ⊕ FV, Equiv.Perm.SameCycle cV.1.1 x (.inl 0) ∨
    Equiv.Perm.SameCycle cV.1.1 x (.inr (fv5 3)) := by
  simp only [sameCycle_iff_of_pow (by norm_num : 0 < 4) cV_pow_four]
  decide +kernel

/-- The closed fermion loop `3 → 4 → 3`. -/
def loopV : ClosedLoop cV :=
  ⟨Quotient.mk _ (.inr (fv5 3)), fun i h => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact not_sameCycle_ext_loop (Quotient.exact h)⟩

/-- The representative has one closed fermion loop. -/
theorem eq_loopV (q : ClosedLoop cV) : q = loopV := by
  obtain ⟨q, hq⟩ := q
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rcases sameCycle_ext_or_loop x with h | h
  · exact absurd (Quotient.sound h.symm) (hq 0)
  · exact Quotient.sound h

open scoped Classical in
/-- The regulator weight (X₇) of the flavour-`f` loop is `c_f`. -/
theorem loopWeight_flavV (P : Params) (f : Fin 3) : loopWeight P cV (flavV f) = P.loopCoeff f := by
  rw [loopWeight, Fintype.prod_eq_single loopV fun q hq => absurd (eq_loopV q) hq]
  have hq : (Quotient.mk _ loopV.1.out : Quotient (Equiv.Perm.SameCycle.setoid cV.1.1)) =
      Quotient.mk _ (.inr (fv5 3)) := Quotient.out_eq _
  have hsc : Equiv.Perm.SameCycle cV.1.1 loopV.1.out (.inr (fv5 3)) := Quotient.exact hq
  rw [fermionFlavor_eq_of_sameCycle (preserves_flavV f) hsc]
  simp only [fermionFlavor, (flavV_apply f).2.2.2.1]

/-! ### Index sums -/

theorem fv5_val (t : Fin 5) : (fv5 t).1 = t := rfl

/-- Sums over the functions on the fermion fields are sums over the five values. -/
theorem sum_fv5 {R M : Type*} [Fintype R] [AddCommMonoid M] (g : (FV → R) → M) :
    ∑ α, g α = ∑ a : R × R × R × R × R,
      g (fun t => ![a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2] t.1) := by
  let e : (R × R × R × R × R) ≃ (FV → R) :=
    { toFun := fun a t => ![a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2] t.1
      invFun := fun α => (α (fv5 0), α (fv5 1), α (fv5 2), α (fv5 3), α (fv5 4))
      left_inv := fun _ => rfl
      right_inv := fun α => by
        funext t
        obtain ⟨j, hj⟩ := t
        fin_cases j <;> rfl }
  exact (e.sum_comp g).symm

/-- Sums over the functions on the photon fields are sums over the five values. -/
theorem sum_ps5 {R M : Type*} [Fintype R] [AddCommMonoid M] (g : (PS → R) → M) :
    ∑ lor, g lor = ∑ a : R × R × R × R × R,
      g (fun s => ![a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2] s.1) := by
  let e : (R × R × R × R × R) ≃ (PS → R) :=
    { toFun := fun a s => ![a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2] s.1
      invFun := fun lor => (lor (ps5 0), lor (ps5 1), lor (ps5 2), lor (ps5 3), lor (ps5 4))
      left_inv := fun _ => rfl
      right_inv := fun lor => by
        funext s
        obtain ⟨j, b⟩ := s
        have hb : b = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.mp b.2)
        subst hb
        fin_cases j <;> rfl }
  exact (e.sum_comp g).symm

/-- The two spinor index families as ten values: the loop `a₃ b₄ a₄ b₃`, the open line
`a₀ b₁ a₁ b₂`, and last the two indices fixed by the external fields, `a₂ b₀`. -/
def spinEquiv :
    (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (FV → Fin 4) × (FV → Fin 4) where
  toFun := fun ⟨a3, b4, a4, b3, a0, b1, a1, b2, a2, b0⟩ =>
    (fun t => ![a0, a1, a2, a3, a4] t.1, fun t => ![b0, b1, b2, b3, b4] t.1)
  invFun p := (p.1 (fv5 3), p.2 (fv5 4), p.1 (fv5 4), p.2 (fv5 3), p.1 (fv5 0), p.2 (fv5 1),
    p.1 (fv5 1), p.2 (fv5 2), p.1 (fv5 2), p.2 (fv5 0))
  left_inv x := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := x
    rfl
  right_inv p := by
    obtain ⟨α, β⟩ := p
    refine Prod.ext (funext fun t => ?_) (funext fun t => ?_) <;>
      · obtain ⟨j, hj⟩ := t
        fin_cases j <;> rfl

theorem spinEquiv_apply (a3 b4 a4 b3 a0 b1 a1 b2 a2 b0 : Fin 4) :
    (spinEquiv (a3, b4, a4, b3, a0, b1, a1, b2, a2, b0)).1 (fv5 0) = a0 ∧
    (spinEquiv (a3, b4, a4, b3, a0, b1, a1, b2, a2, b0)).1 (fv5 1) = a1 ∧
    (spinEquiv (a3, b4, a4, b3, a0, b1, a1, b2, a2, b0)).1 (fv5 2) = a2 ∧
    (spinEquiv (a3, b4, a4, b3, a0, b1, a1, b2, a2, b0)).1 (fv5 3) = a3 ∧
    (spinEquiv (a3, b4, a4, b3, a0, b1, a1, b2, a2, b0)).1 (fv5 4) = a4 ∧
    (spinEquiv (a3, b4, a4, b3, a0, b1, a1, b2, a2, b0)).2 (fv5 0) = b0 ∧
    (spinEquiv (a3, b4, a4, b3, a0, b1, a1, b2, a2, b0)).2 (fv5 1) = b1 ∧
    (spinEquiv (a3, b4, a4, b3, a0, b1, a1, b2, a2, b0)).2 (fv5 2) = b2 ∧
    (spinEquiv (a3, b4, a4, b3, a0, b1, a1, b2, a2, b0)).2 (fv5 3) = b3 ∧
    (spinEquiv (a3, b4, a4, b3, a0, b1, a1, b2, a2, b0)).2 (fv5 4) = b4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The summand of the spinor index sum: the external indices `αe` (the `Ψ̄` of vertex `2`) and
`βe` (the `Ψ` of vertex `0`) fixed, the five vertex matrices `G t`, the open-line propagators
`S₀₁`, `S₁₂` and the loop propagators `S₄₃`, `S₃₄`. -/
def spinTerm (G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ) (S01 S12 S43 S34 : Matrix (Fin 4) (Fin 4) ℂ)
    (αe βe : Fin 4) (α β : FV → Fin 4) : ℂ :=
  (if α (fv5 2) = αe ∧ β (fv5 0) = βe then (1 : ℂ) else 0) *
    (G 0 (α (fv5 0)) (β (fv5 0)) * G 1 (α (fv5 1)) (β (fv5 1)) *
      G 2 (α (fv5 2)) (β (fv5 2)) * G 3 (α (fv5 3)) (β (fv5 3)) *
      G 4 (α (fv5 4)) (β (fv5 4)) *
      (S01 (β (fv5 1)) (α (fv5 0)) * S12 (β (fv5 2)) (α (fv5 1)) *
        S43 (β (fv5 3)) (α (fv5 4)) * S34 (β (fv5 4)) (α (fv5 3))))

/-- **The spinor index sum** of the five gauge vertices, the spinor index `αe` of the outgoing
`Ψ̄` at vertex `2` and `βe` of the incoming `Ψ` at vertex `0` fixed: the open-line chain
`G₂ S₁₂ G₁ S₀₁ G₀` times the trace of the loop `Tr[G₃ S₄₃ G₄ S₃₄]`. -/
theorem spinSum (G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ) (S01 S12 S43 S34 : Matrix (Fin 4) (Fin 4) ℂ)
    (αe βe : Fin 4) :
    ∑ α : FV → Fin 4, ∑ β : FV → Fin 4, spinTerm G S01 S12 S43 S34 αe βe α β =
      (G 2 * S12 * G 1 * S01 * G 0) αe βe * Matrix.trace (G 3 * S43 * G 4 * S34) := by
  unfold spinTerm
  rw [← Fintype.sum_prod_type', ← spinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp only [spinEquiv_apply]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-! ### The amplitude -/

theorem vertexFactor_fv5 (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : FV → Fin 4) (lor : PS → Fin 4)
    (kψ : FV → Fin 4 → ℝ) (kA : PS → Fin 4 → ℝ) (t : Fin 5) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * e * Dirac.gamma (lor (ps5 t)) (α (fv5 t)) (β (fv5 t)) :=
  rfl

theorem ps5_eval {R : Type*} (l0 l1 l2 l3 l4 : R) :
    ![l0, l1, l2, l3, l4] (ps5 0).1 = l0 ∧ ![l0, l1, l2, l3, l4] (ps5 1).1 = l1 ∧
      ![l0, l1, l2, l3, l4] (ps5 2).1 = l2 ∧ ![l0, l1, l2, l3, l4] (ps5 3).1 = l3 ∧
      ![l0, l1, l2, l3, l4] (ps5 4).1 = l4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cV_inl : ∀ (i : Fin 1) (t : FV), cV.1.1 (.inl i) = .inr t ↔ t = fv5 2 := by
  decide +kernel

theorem cV_inr_inl : ∀ (t : FV) (i : Fin 1), cV.1.1 (.inr t) = .inl i ↔ t = fv5 0 := by
  decide +kernel

theorem cV_photon_inl : ∀ (j : Fin 1) (a : PS), cV.1.2 (.inl j) = .inr a ↔ a = ps5 1 := by
  decide +kernel

/-- The open-line chain `γ^ν S̃_m(p + k_ext - k) γ^μ S̃_m(p - k) γ^ρ`: the external photon index
`μ` at vertex `1`, the internal photon indices `ρ` at vertex `0` and `ν` at vertex `2`. -/
noncomputable def outerChain (P : Params) (p kext k : Fin 4 → ℝ) (μ ρ ν : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Dirac.gamma ν * QED.OneLoop.electronPropagator P.m P.ε (p + kext - k) * Dirac.gamma μ *
    QED.OneLoop.electronPropagator P.m P.ε (p - k) * Dirac.gamma ρ

theorem ite_and_one (A B : Prop) [Decidable A] [Decidable B] [Decidable (A ∧ B)] :
    (if A ∧ B then (1 : ℂ) else 0) = (if A then 1 else 0) * (if B then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

/-- **The amplitude** (T₇) of the representative for the loop flavour `f`, in the nested routing:
the open-line chain, the two photon propagators of momenta `k` and `-k`, and the trace of the loop
of flavour `f`. -/
theorem contractionAmplitude₂_flavV (P : Params) (f : Fin 3) (pIn kIn : Fin 1 → Fin 4 → ℝ)
    (q k : Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    contractionAmplitude₂ P cV (flavV f) pIn kIn (nestedMom (pIn 0) (kIn 0) q k) αOut βIn μ =
      (I * P.e) ^ 5 * (1 / I) ^ 6 * ∑ l0 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4, ∑ l4 : Fin 4,
        outerChain P (pIn 0) (kIn 0) k (μ 0) l0 l2 (αOut 0) (βIn 0) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k l0 l3 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (-k) l2 l4 *
          Matrix.trace (Dirac.gamma l3 * QED.OneLoop.electronPropagator (P.mass f) P.ε q *
            Dirac.gamma l4 * QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k)) := by
  obtain ⟨v0, v1, v2, v3⟩ := val_lineV
  obtain ⟨t0, t1, t2, t3⟩ := tail_lineV
  obtain ⟨w0, w1⟩ := val_photV
  obtain ⟨h0, h1⟩ := head_photV
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := nestedMom_apply (pIn 0) (kIn 0) q k
  obtain ⟨f0, f1, f2, f3, f4⟩ := flavV_apply f
  have hm0 : P.mass 0 = P.m := rfl
  unfold contractionAmplitude₂
  simp only [cV_inl, cV_inr_inl, cV_photon_inl, forall_eq, Fin.forall_fin_one]
  simp only [vertexFactor_fv5, Fin.prod_univ_five, prod_fermionLine, prod_photonLine, v0, v1, v2,
    v3, t0, t1, t2, t3, w0, w1, h0, h1, n0, n1, n2, n3, n4, n5, f1, f2, f3, f4, hm0]
  rw [(Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  have hterm : ∀ (lor : PS → Fin 4) (α β : FV → Fin 4),
      (if α (fv5 2) = αOut 0 ∧ β (fv5 0) = βIn 0 ∧ lor (ps5 1) = μ 0 then (1 : ℂ) else 0) *
        (I * P.e * Dirac.gamma (lor (ps5 0)) (α (fv5 0)) (β (fv5 0)) *
          (I * P.e * Dirac.gamma (lor (ps5 1)) (α (fv5 1)) (β (fv5 1))) *
          (I * P.e * Dirac.gamma (lor (ps5 2)) (α (fv5 2)) (β (fv5 2))) *
          (I * P.e * Dirac.gamma (lor (ps5 3)) (α (fv5 3)) (β (fv5 3))) *
          (I * P.e * Dirac.gamma (lor (ps5 4)) (α (fv5 4)) (β (fv5 4))) *
          (1 / I * QED.OneLoop.electronPropagator P.m P.ε (pIn 0 - k) (β (fv5 1)) (α (fv5 0)) *
            (1 / I * QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + kIn 0 - k)
              (β (fv5 2)) (α (fv5 1))) *
            (1 / I * QED.OneLoop.electronPropagator (P.mass f) P.ε q (β (fv5 3)) (α (fv5 4))) *
            (1 / I * QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k) (β (fv5 4)) (α (fv5 3)))) *
          (1 / I * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k (lor (ps5 0)) (lor (ps5 3)) *
            (1 / I * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (-k) (lor (ps5 2)) (lor (ps5 4))))) =
      ((if lor (ps5 1) = μ 0 then (1 : ℂ) else 0) * ((I * P.e) ^ 5 * (1 / I) ^ 6 *
          (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k (lor (ps5 0)) (lor (ps5 3)) *
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (-k) (lor (ps5 2)) (lor (ps5 4))))) *
        spinTerm (fun t => Dirac.gamma (lor (ps5 t)))
          (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 - k))
          (QED.OneLoop.electronPropagator P.m P.ε (pIn 0 + kIn 0 - k))
          (QED.OneLoop.electronPropagator (P.mass f) P.ε q)
          (QED.OneLoop.electronPropagator (P.mass f) P.ε (q + k)) (αOut 0) (βIn 0) α β := by
    intro lor α β
    unfold spinTerm
    simp only [← and_assoc]
    rw [ite_and_one]
    ring
  simp only [hterm, ← Finset.mul_sum, spinSum]
  rw [sum_ps5]
  simp only [Fintype.sum_prod_type, ps5_eval]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  unfold outerChain
  ring

open scoped Classical in
/-- The regulated amplitude (T₈) in the nested routing is the sum over the loop flavour `f` of
`c_f` times the amplitude (T₇). -/
theorem regulatedAmplitude₂_nested (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (q k : Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    regulatedAmplitude₂ P cV pIn kIn (nestedMom (pIn 0) (kIn 0) q k) αOut βIn μ =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude₂ P cV (flavV f) pIn kIn (nestedMom (pIn 0) (kIn 0) q k) αOut βIn μ := by
  rw [regulatedAmplitude₂, sum_preserves]
  simp only [loopWeight_flavV]

/-- **The outer factor** of the nested integrand of the class `VP`, for the Lorentz indices
`ρ, σ` of the two ends of the inserted vacuum polarization: the open-line chain
(`outerChain`) contracted with the photon propagators of momenta `k` (from vertex `0`) and `-k`
(from vertex `2`), times the constants of the three open-line vertices, of the four outer
propagators and of the outer loop measure `(2π)⁻⁴`, and `-1` (the vacuum polarization integrand
carries the sign of the closed loop). -/
noncomputable def vpOuter (P : Params) (p kext k : Fin 4 → ℝ) (α β μ ρ σ : Fin 4) : ℂ :=
  -(((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 3 * (1 / I) ^ 4 *
    ∑ l0 : Fin 4, ∑ l2 : Fin 4, outerChain P p kext k μ l0 l2 α β *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k l0 ρ *
      QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (-k) l2 σ

theorem trace_rotate (A B C D : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (A * B * C * D) = Matrix.trace (B * C * D * A) := by
  rw [show A * B * C * D = A * (B * C * D) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]

/-- **The integrand factorizes** (O2-8): in the nested routing, `(2π)⁻⁸` times the regulated
amplitude (T₈) of the class `VP` is `∑ ρ σ, vpOuter … k ρ σ * Π^{ρσ}`, where
`Π^{ρσ} = vacuumPolarizationIntegrand P P.ε k q ρ σ` is the one-loop vacuum polarization
integrand of (62.12) at the photon momentum `k` and the loop momentum `q`, with the
Pauli–Villars flavours summed inside it. An identity at every parameter set. -/
theorem integrand_eq (P : Params) (pIn kIn : Fin 1 → Fin 4 → ℝ) (q k : Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P cV pIn kIn (nestedMom (pIn 0) (kIn 0) q k) αOut βIn μ =
      ∑ ρ : Fin 4, ∑ σ : Fin 4, vpOuter P (pIn 0) (kIn 0) k (αOut 0) (βIn 0) (μ 0) ρ σ *
        vacuumPolarizationIntegrand P P.ε k q ρ σ := by
  rw [regulatedAmplitude₂_nested]
  simp only [contractionAmplitude₂_flavV]
  unfold vpOuter vacuumPolarizationIntegrand
  simp only [trace_rotate (QED.OneLoop.electronPropagator _ P.ε (q + k))]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b, 2, c]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

end QED.TwoLoop.NestedVP

end
