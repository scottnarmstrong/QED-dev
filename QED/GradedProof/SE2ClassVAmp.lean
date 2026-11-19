/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ClassRX
public import QED.TwoLoop.ClassIntegrableVP

/-!
# The class `V`: flavorings and the amplitude

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), step 2. The representative `repV` of `QED/GradedProof/SE2Classes.lean` has four
`gauge` vertices, the open electron line `0 → 1`, the closed loop `2 → 3 → 2` and the photon
lines `0 — 2`, `1 — 3`.

* `preserves_iff_V`, `sum_preserves_V`, `loopWeight_flavSE`: the preserved flavorings are those
  with the open line of flavour `0` and the loop of one flavour `f`, of regulator weight `c_f`.
* `spinSum4`: the spinor index sum is the open-line chain times the trace of the loop.
* `v_amplitude`: the amplitude (T₇) of flavour `f` at arbitrary line momenta.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel
open Complex

/-- The fermion fields of the four gauge vertices. -/
local notation "FV4" => Wick.FermionVertex k_gggg

/-- The photon fields of the four gauge vertices. -/
local notation "PS4" => Wick.PhotonSlot k_gggg

theorem k_gggg_gauge : ∀ t : Fin 4, k_gggg t = .gauge := by decide

theorem k_gggg_slots (t : Fin 4) : (k_gggg t).photonSlots = 1 := by
  rw [k_gggg_gauge]
  rfl

/-- The fermion field of vertex `t`. -/
def fv4 (t : Fin 4) : FV4 := ⟨t, by rw [k_gggg_gauge]; decide⟩

/-- The photon field of vertex `t`. -/
def ps4 (t : Fin 4) : PS4 := ⟨t, ⟨0, by rw [k_gggg_slots]; norm_num⟩⟩

/-! ### Flavorings -/

/-- The flavoring with the open line of flavour `0` and the loop `2, 3` of flavour `f`. -/
def flavSE (f : Fin 3) : Flavoring k_gggg :=
  ⟨fun t => if 2 ≤ t.1.val then f else 0, fun t h => absurd (k_gggg_gauge t.1) h⟩

theorem flavSE_apply (f : Fin 3) : (flavSE f).1 (fv4 0) = 0 ∧ (flavSE f).1 (fv4 1) = 0 ∧
    (flavSE f).1 (fv4 2) = f ∧ (flavSE f).1 (fv4 3) = f := by
  simp [flavSE, fv4]

theorem preserves_flavSE : ∀ f : Fin 3, Preserves repV (flavSE f) := by
  unfold Preserves
  decide +kernel

theorem fermionPerm_repV : repV.1.1 (.inl 0) = .inr (fv4 1) ∧
    repV.1.1 (.inr (fv4 1)) = .inr (fv4 0) ∧ repV.1.1 (.inr (fv4 3)) = .inr (fv4 2) := by
  decide +kernel

/-- **The preserved flavorings**: the open line has flavour `0`, the loop one flavour. -/
theorem preserves_iff_V (φ : Flavoring k_gggg) :
    Preserves repV φ ↔ φ = flavSE (φ.1 (fv4 2)) := by
  refine ⟨fun hφ => ?_, fun h => h ▸ preserves_flavSE _⟩
  obtain ⟨s0, s1, s3⟩ := fermionPerm_repV
  have h0 := hφ (.inl 0)
  have h1 := hφ (.inr (fv4 1))
  have h3 := hφ (.inr (fv4 3))
  rw [s0] at h0
  rw [s1] at h1
  rw [s3] at h3
  simp only [fermionFlavor] at h0 h1 h3
  apply Subtype.ext
  funext t
  obtain ⟨j, hj⟩ := t
  change φ.1 (fv4 j) = (flavSE (φ.1 (fv4 2))).1 (fv4 j)
  fin_cases j
  · exact (h1.trans h0).trans (flavSE_apply _).1.symm
  · exact h0.trans (flavSE_apply _).2.1.symm
  · exact (flavSE_apply _).2.2.1.symm
  · exact h3.symm.trans (flavSE_apply _).2.2.2.symm

/-- **The sum over the preserved flavorings** is the sum over the flavour of the loop. -/
theorem sum_preserves_V {M : Type*} [AddCommMonoid M] [Fintype (Flavoring k_gggg)]
    [DecidablePred (Preserves repV)] (F : Flavoring k_gggg → M) :
    ∑ φ ∈ (Finset.univ : Finset (Flavoring k_gggg)).filter (Preserves repV), F φ =
      ∑ f : Fin 3, F (flavSE f) :=
  Finset.sum_nbij' (fun φ => φ.1 (fv4 2)) flavSE (fun _ _ => Finset.mem_univ _)
    (fun f _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, preserves_flavSE f⟩)
    (fun φ hφ => ((preserves_iff_V φ).mp (Finset.mem_filter.mp hφ).2).symm)
    (fun f _ => (flavSE_apply f).2.2.1)
    (fun φ hφ => by rw [← (preserves_iff_V φ).mp (Finset.mem_filter.mp hφ).2])

theorem repV_pow_six : repV.1.1 ^ 6 = 1 := by decide +kernel

theorem not_sameCycle_ext_loop_V : ¬ Equiv.Perm.SameCycle repV.1.1 (.inl 0) (.inr (fv4 2)) := by
  rw [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (by norm_num) repV_pow_six]
  decide +kernel

theorem sameCycle_ext_or_loop_V : ∀ x : Fin 1 ⊕ FV4, Equiv.Perm.SameCycle repV.1.1 x (.inl 0) ∨
    Equiv.Perm.SameCycle repV.1.1 x (.inr (fv4 2)) := by
  simp only [QED.TwoLoop.NestedVP.sameCycle_iff_of_pow (by norm_num : 0 < 6) repV_pow_six]
  decide +kernel

/-- The closed fermion loop `2 → 3 → 2`. -/
def loopSE : ClosedLoop repV :=
  ⟨Quotient.mk _ (.inr (fv4 2)), fun i h => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact not_sameCycle_ext_loop_V (Quotient.exact h)⟩

theorem eq_loopSE (q : ClosedLoop repV) : q = loopSE := by
  obtain ⟨q, hq⟩ := q
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rcases sameCycle_ext_or_loop_V x with h | h
  · exact absurd (Quotient.sound h.symm) (hq 0)
  · exact Quotient.sound h

open scoped Classical in
/-- The regulator weight (X₇) of the flavour-`f` loop is `c_f`. -/
theorem loopWeight_flavSE (P : Params) (f : Fin 3) :
    loopWeight P repV (flavSE f) = P.loopCoeff f := by
  rw [loopWeight, Fintype.prod_eq_single loopSE fun q hq => absurd (eq_loopSE q) hq]
  have hq : (Quotient.mk _ loopSE.1.out : Quotient (Equiv.Perm.SameCycle.setoid repV.1.1)) =
      Quotient.mk _ (.inr (fv4 2)) := Quotient.out_eq _
  have hsc : Equiv.Perm.SameCycle repV.1.1 loopSE.1.out (.inr (fv4 2)) := Quotient.exact hq
  rw [QED.TwoLoop.Relabel.fermionFlavor_eq_of_sameCycle (preserves_flavSE f) hsc]
  simp only [fermionFlavor, (flavSE_apply f).2.2.1]

open scoped Classical in
/-- The regulated amplitude (T₈) of `repV` is the flavour sum of the amplitudes (T₇). -/
theorem regulatedAmplitude₂_repV (P : Params) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 0 → Fin 4 → ℝ) (k : Line repV → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin 0 → Fin 4) :
    regulatedAmplitude₂ P repV pIn kIn k αOut βIn μ =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude₂ P repV (flavSE f) pIn kIn k αOut βIn μ := by
  rw [regulatedAmplitude₂, sum_preserves_V]
  simp only [loopWeight_flavSE]

/-! ### Index sums -/

theorem sum_ps4 {R M : Type*} [Fintype R] [AddCommMonoid M] (g : (PS4 → R) → M) :
    ∑ lor, g lor = ∑ a : R × R × R × R,
      g (fun s => ![a.1, a.2.1, a.2.2.1, a.2.2.2] s.1) := by
  let e : (R × R × R × R) ≃ (PS4 → R) :=
    { toFun := fun a s => ![a.1, a.2.1, a.2.2.1, a.2.2.2] s.1
      invFun := fun lor => (lor (ps4 0), lor (ps4 1), lor (ps4 2), lor (ps4 3))
      left_inv := fun _ => rfl
      right_inv := fun lor => by
        funext s
        obtain ⟨j, b⟩ := s
        fin_cases j <;>
        · have hb : b = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp b.2)
          subst hb
          rfl }
  exact (e.sum_comp g).symm

/-- The spinor index families as eight values: the loop `a₂ b₃ a₃ b₂`, the open line `a₀ b₁`,
and last the two indices fixed by the external fields, `a₁ b₀`. -/
def spinEquiv4 :
    (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (FV4 → Fin 4) × (FV4 → Fin 4) where
  toFun := fun ⟨a2, b3, a3, b2, a0, b1, a1, b0⟩ =>
    (fun t => ![a0, a1, a2, a3] t.1, fun t => ![b0, b1, b2, b3] t.1)
  invFun p := (p.1 (fv4 2), p.2 (fv4 3), p.1 (fv4 3), p.2 (fv4 2), p.1 (fv4 0), p.2 (fv4 1),
    p.1 (fv4 1), p.2 (fv4 0))
  left_inv x := by
    obtain ⟨_, _, _, _, _, _, _, _⟩ := x
    rfl
  right_inv p := by
    obtain ⟨α, β⟩ := p
    refine Prod.ext (funext fun t => ?_) (funext fun t => ?_) <;>
      · obtain ⟨j, hj⟩ := t
        fin_cases j <;> rfl

theorem spinEquiv4_apply (a2 b3 a3 b2 a0 b1 a1 b0 : Fin 4) :
    (spinEquiv4 (a2, b3, a3, b2, a0, b1, a1, b0)).1 (fv4 0) = a0 ∧
    (spinEquiv4 (a2, b3, a3, b2, a0, b1, a1, b0)).1 (fv4 1) = a1 ∧
    (spinEquiv4 (a2, b3, a3, b2, a0, b1, a1, b0)).1 (fv4 2) = a2 ∧
    (spinEquiv4 (a2, b3, a3, b2, a0, b1, a1, b0)).1 (fv4 3) = a3 ∧
    (spinEquiv4 (a2, b3, a3, b2, a0, b1, a1, b0)).2 (fv4 0) = b0 ∧
    (spinEquiv4 (a2, b3, a3, b2, a0, b1, a1, b0)).2 (fv4 1) = b1 ∧
    (spinEquiv4 (a2, b3, a3, b2, a0, b1, a1, b0)).2 (fv4 2) = b2 ∧
    (spinEquiv4 (a2, b3, a3, b2, a0, b1, a1, b0)).2 (fv4 3) = b3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The summand of the spinor index sum of `repV`. -/
def spinTerm4 (G : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (S01 S32 S23 : Matrix (Fin 4) (Fin 4) ℂ)
    (αe βe : Fin 4) (α β : FV4 → Fin 4) : ℂ :=
  (if α (fv4 1) = αe ∧ β (fv4 0) = βe then (1 : ℂ) else 0) *
    (G 0 (α (fv4 0)) (β (fv4 0)) * G 1 (α (fv4 1)) (β (fv4 1)) *
      G 2 (α (fv4 2)) (β (fv4 2)) * G 3 (α (fv4 3)) (β (fv4 3)) *
      (S01 (β (fv4 1)) (α (fv4 0)) * S32 (β (fv4 2)) (α (fv4 3)) *
        S23 (β (fv4 3)) (α (fv4 2))))

/-- **The spinor index sum** of `repV`: the open-line chain `G₁ S₀₁ G₀` times the trace of the
loop `Tr[G₂ S₃₂ G₃ S₂₃]`. -/
theorem spinSum4 (G : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (S01 S32 S23 : Matrix (Fin 4) (Fin 4) ℂ)
    (αe βe : Fin 4) :
    ∑ α : FV4 → Fin 4, ∑ β : FV4 → Fin 4, spinTerm4 G S01 S32 S23 αe βe α β =
      (G 1 * S01 * G 0) αe βe * Matrix.trace (G 2 * S32 * G 3 * S23) := by
  unfold spinTerm4
  rw [← Fintype.sum_prod_type', ← spinEquiv4.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp only [spinEquiv4_apply]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-! ### The lines and the amplitude -/

/-- The open electron line `0 → 1` of `repV`. -/
def vf1 : FermionLine repV := ⟨fvK k_gggg 1, by decide +kernel⟩
/-- The loop line `3 → 2` of `repV`. -/
def vf2 : FermionLine repV := ⟨fvK k_gggg 2, by decide +kernel⟩
/-- The loop line `2 → 3` of `repV`. -/
def vf3 : FermionLine repV := ⟨fvK k_gggg 3, by decide +kernel⟩
/-- The photon line `0 → 2` of `repV`. -/
def vg1 : PhotonLine repV := ⟨psK k_gggg 0 0, by decide +kernel⟩
/-- The photon line `1 → 3` of `repV`. -/
def vg2 : PhotonLine repV := ⟨psK k_gggg 1 0, by decide +kernel⟩

theorem v_fermionLine_cases : ∀ f : FermionLine repV, f = vf1 ∨ f = vf2 ∨ f = vf3 := by
  decide +kernel

theorem v_photonLine_cases : ∀ g : PhotonLine repV, g = vg1 ∨ g = vg2 := by decide +kernel

theorem v_ne : vf1 ≠ vf2 ∧ vf1 ≠ vf3 ∧ vf2 ≠ vf3 ∧ vg1 ≠ vg2 := by decide +kernel

theorem v_tails : vf1.1 = fv4 1 ∧ vf2.1 = fv4 2 ∧ vf3.1 = fv4 3 ∧ vf1.tail = fv4 0 ∧
    vf2.tail = fv4 3 ∧ vf3.tail = fv4 2 ∧ vg1.1 = ps4 0 ∧ vg2.1 = ps4 1 ∧ vg1.head = ps4 2 ∧
    vg2.head = ps4 3 := by
  decide +kernel

theorem vertexFactor_fv4 (e δ₁ δ₂ δm δ₃ m : ℝ) (α β : FV4 → Fin 4) (lor : PS4 → Fin 4)
    (kψ : FV4 → Fin 4 → ℝ) (kA : PS4 → Fin 4 → ℝ) (t : Fin 4) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA t =
      I * e * Dirac.gamma (lor (ps4 t)) (α (fv4 t)) (β (fv4 t)) := by
  fin_cases t <;> rfl

theorem ps4_eval {R : Type*} (l0 l1 l2 l3 : R) :
    ![l0, l1, l2, l3] (ps4 0).1 = l0 ∧ ![l0, l1, l2, l3] (ps4 1).1 = l1 ∧
      ![l0, l1, l2, l3] (ps4 2).1 = l2 ∧ ![l0, l1, l2, l3] (ps4 3).1 = l3 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem repV_inl : ∀ (i : Fin 1) (t : FV4), repV.1.1 (.inl i) = .inr t ↔ t = fv4 1 := by
  decide +kernel

theorem repV_inr_inl : ∀ (t : FV4) (i : Fin 1), repV.1.1 (.inr t) = .inl i ↔ t = fv4 0 := by
  decide +kernel

/-- **The amplitude** (T₇) of `repV` for the loop flavour `f`, at arbitrary line momenta: the
open-line chain, the two photon propagators and the trace of the loop of flavour `f`. -/
theorem v_amplitude (P : Params) (f : Fin 3) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 0 → Fin 4 → ℝ) (k : Line repV → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin 0 → Fin 4) :
    contractionAmplitude₂ P repV (flavSE f) pIn kIn k αOut βIn μ =
      (I * P.e) ^ 4 * (1 / I) ^ 5 * ∑ l0 : Fin 4, ∑ l1 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4,
        (Dirac.gamma l1 * QED.OneLoop.electronPropagator P.m P.ε (k (.inl vf1)) *
            Dirac.gamma l0) (αOut 0) (βIn 0) *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr vg1)) l0 l2 *
          QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr vg2)) l1 l3 *
          Matrix.trace (Dirac.gamma l2 * QED.OneLoop.electronPropagator (P.mass f) P.ε
            (k (.inl vf2)) * Dirac.gamma l3 *
              QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl vf3))) := by
  obtain ⟨n12, n13, n23, n45⟩ := v_ne
  obtain ⟨v1, v2, v3, t1, t2, t3, w1, w2, h1, h2⟩ := v_tails
  obtain ⟨f0, f1, f2, f3⟩ := flavSE_apply f
  have hm0 : P.mass 0 = P.m := rfl
  unfold contractionAmplitude₂
  simp only [repV_inl, repV_inr_inl, forall_eq, Fin.forall_fin_one, IsEmpty.forall_iff,
    and_true]
  simp only [vertexFactor_fv4, Fin.prod_univ_four,
    prod_eq_of_three n12 n13 n23 v_fermionLine_cases, prod_eq_of_two n45 v_photonLine_cases,
    v1, v2, v3, t1, t2, t3, w1, w2, h1, h2, f1, f2, f3, hm0]
  rw [(Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  have hterm : ∀ (lor : PS4 → Fin 4) (α β : FV4 → Fin 4),
      (if α (fv4 1) = αOut 0 ∧ β (fv4 0) = βIn 0 then (1 : ℂ) else 0) *
        (I * P.e * Dirac.gamma (lor (ps4 0)) (α (fv4 0)) (β (fv4 0)) *
          (I * P.e * Dirac.gamma (lor (ps4 1)) (α (fv4 1)) (β (fv4 1))) *
          (I * P.e * Dirac.gamma (lor (ps4 2)) (α (fv4 2)) (β (fv4 2))) *
          (I * P.e * Dirac.gamma (lor (ps4 3)) (α (fv4 3)) (β (fv4 3))) *
          (1 / I * QED.OneLoop.electronPropagator P.m P.ε (k (.inl vf1)) (β (fv4 1))
              (α (fv4 0)) *
            (1 / I * QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl vf2)) (β (fv4 2))
              (α (fv4 3))) *
            (1 / I * QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl vf3)) (β (fv4 3))
              (α (fv4 2)))) *
          (1 / I * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr vg1)) (lor (ps4 0))
              (lor (ps4 2)) *
            (1 / I * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr vg2)) (lor (ps4 1))
              (lor (ps4 3))))) =
      ((I * P.e) ^ 4 * (1 / I) ^ 5 *
          (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr vg1)) (lor (ps4 0))
              (lor (ps4 2)) *
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr vg2)) (lor (ps4 1))
              (lor (ps4 3)))) *
        spinTerm4 (fun t => Dirac.gamma (lor (ps4 t)))
          (QED.OneLoop.electronPropagator P.m P.ε (k (.inl vf1)))
          (QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl vf2)))
          (QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl vf3))) (αOut 0) (βIn 0) α β := by
    intro lor α β
    unfold spinTerm4
    ring
  simp only [hterm, ← Finset.mul_sum, spinSum4]
  rw [sum_ps4]
  simp only [Fintype.sum_prod_type, ps4_eval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end QED.GradedProof.SE2

end
