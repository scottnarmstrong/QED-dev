/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Slot

/-!
# The Ward–Takahashi derivative of a one-slot piece

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6: `SEData.hasDerivAt_pvF_slotN`. On self-energy data whose external momentum flows only
through line `e₀`, the derivative along `t ↦ t r` of the parametric value of an entry of the
one-slot numerator `∑ₗ cₗ Aₗ (m - k̸₀) Bₗ` is minus the parametric value, over the data with `e₀`
doubled, of the numerator with the insertion `(m - k̸₀) (c_{e₀} r)̸ (m - k̸₀)` in the slot
(`SEData.hasDerivAt_pv_ray_ward`, the line terms collected over the fibres of the constant map
`Fin 1 → lines`, the insertion identity `SEData.slotV_eq`).
-/

@[expose] public section

open Complex Matrix Filter Topology

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassIntegrable QED.TwoLoop.Bridge QED.GradedProof.WI2
open QED.TwoLoop.LimitCovariance (qsum eval_qsum)

variable (D : SEData) (e₀ : Fin (D.m + 1)) (mass : ℝ) {ι : Type*} [Fintype ι]
  {A B : ι → Matrix (Fin 4) (Fin 4) ℂ} {c : ι → (Fin 2 → Fin 4 → ℝ) → ℂ}

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_slotN (r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (t₀ : ℝ) (a b : Fin 4) :
    HasDerivAt (fun t : ℝ => D.slotN e₀ mass A B c (t • r) ℓ a b)
      (-D.slotQ e₀ A B c r ℓ a b) t₀ := by
  have hE : ∀ t : ℝ, D.slotE e₀ mass (t • r) ℓ =
      electronNumerator mass (lineMomentum D.α (D.mom 0) e₀ ℓ) - t • Dirac.slash (D.mom r e₀) :=
    fun t => by
      simp only [slotE, electronNumerator]
      rw [sub_sub, ← Complex.coe_smul, ← Dirac.slash_smul, ← Dirac.slash_add]
      congr 2
      funext μ
      simp only [lineMomentum, mom, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
  have h1 := ((hasDerivAt_id t₀).smul_const (Dirac.slash (D.mom r e₀))).const_sub
    (electronNumerator mass (lineMomentum D.α (D.mom 0) e₀ ℓ))
  simp only [one_smul] at h1
  have hS := HasDerivAt.fun_sum (u := Finset.univ) fun l _ =>
    ((((hasDerivAt_const t₀ (A l)).mul h1).mul (hasDerivAt_const t₀ (B l))).const_smul (c l ℓ))
  have hS' : HasDerivAt (fun t => D.slotN e₀ mass A B c (t • r) ℓ)
      (-D.slotQ e₀ A B c r ℓ) t₀ := by
    refine (hS.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    · simp only [slotQ, ← Finset.sum_neg_distrib, ← smul_neg]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_neg,
        Matrix.neg_mul]
    · simp only [slotN, hE, id, Pi.smul_apply, Pi.mul_apply]
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).hasFDerivAt
    |>.comp_hasDerivAt t₀ hS'

end Deriv

/-- **The Ward–Takahashi derivative of a one-slot piece along a ray.** -/
theorem hasDerivAt_pvF_slotN {S : Finset (Fin (D.m + 1))} (hS : e₀ ∉ S)
    (hSE : insert e₀ S ⊆ D.E) (hcp : ∀ l, IsLoopPoly 2 2 (c l))
    (hcb : ∀ l, RefinedBound D.α S 2 (c l)) (hM : D.M e₀ = mass)
    (h0 : ∀ i, i ≠ e₀ → D.cs i = 0) (r : Fin 4 → ℝ) {t₀ : ℝ}
    (hV : ∀ᶠ t in 𝓝 t₀, D.VPos (D.mom (t • r))) (a b : Fin 4) :
    HasDerivAt (fun t => D.pvF (fun ℓ => D.slotN e₀ mass A B c (t • r) ℓ a b) (D.mom (t • r)))
      (-(D.dup e₀).pvF (fun ℓ => D.slotV e₀ mass A B c (t₀ • r) r ℓ a b)
        (dbl e₀ (D.mom (t₀ • r)))) t₀ := by
  classical
  have hV₀ := hV.self_of_nhds
  have hQ : ∀ p, ∃ Q : LoopQuartic, D.Good Q ∧ Q.quart = 0 ∧
      Q.eval = fun ℓ => D.slotN e₀ mass A B c p ℓ a b := fun p => by
    obtain ⟨Q, hq, hQ⟩ :=
      IsLoopPoly.exists_loopQuartic_cubic (D.isLoopPoly_slotN e₀ mass (A := A) (B := B) hcp p a b)
    refine ⟨Q, ⟨Or.inr hq, ?_⟩, hq, hQ⟩
    rw [hQ]
    exact (D.refinedBound_slotN e₀ mass (A := A) (B := B) hS hSE hcb p a b).mono subset_rfl
      (by norm_num)
  set Qf : ℝ → LoopQuartic := fun t => (hQ (t • r)).choose
  have hQf : ∀ t, D.Good (Qf t) ∧
      (Qf t).eval = fun ℓ => D.slotN e₀ mass A B c (t • r) ℓ a b :=
    fun t => ⟨(hQ _).choose_spec.1, (hQ _).choose_spec.2.2⟩
  have hQf0 : (Qf t₀).quart = 0 := (hQ _).choose_spec.2.1
  obtain ⟨Q2, hQ2q, hQ2e⟩ :=
    IsLoopPoly.exists_loopQuartic_cubic (D.isLoopPoly_slotQ e₀ (A := A) (B := B) hcp r a b)
  have hQ2g : D.Good Q2 := ⟨Or.inr hQ2q, by
    rw [hQ2e]
    exact D.refinedBound_slotQ e₀ (A := A) (B := B) hSE hcb r a b⟩
  obtain ⟨QVq, hQVe⟩ :=
    IsLoopPoly.exists_loopQuartic (D.isLoopPoly_slotV e₀ mass (A := A) (B := B) hcp (t₀ • r) r a b)
  have hVqg : (D.dup e₀).Good QVq := ⟨Or.inl (by change 7 ≤ D.m + 1; have := D.hm; omega),
    by rw [hQVe]; exact D.refinedBound_slotV e₀ mass (A := A) (B := B) hS hSE hcb (t₀ • r) r a b⟩
  set F : Fin (D.m + 1) → Finset (Fin 1) := fun i => Finset.univ.filter fun _ => e₀ = i
  have hF : ∀ i, (e₀ = i ∧ F i = Finset.univ) ∨ (e₀ ≠ i ∧ F i = ∅) := fun i => by
    by_cases h : e₀ = i
    · exact Or.inl ⟨h, Finset.filter_true_of_mem fun _ _ => h⟩
    · exact Or.inr ⟨h, Finset.filter_false_of_mem fun _ _ => h⟩
  set Q₂ : Fin (D.m + 1) → LoopQuartic := fun i => qsum (F i) (fun _ => 1) fun _ => Q2
  set QV : Fin (D.m + 1) → LoopQuartic := fun i => qsum (F i) (fun _ => 1) fun _ => QVq
  have hQ₂e : ∀ i ℓ, (Q₂ i).eval ℓ = ∑ _j ∈ F i, D.slotQ e₀ A B c r ℓ a b := fun i ℓ => by
    simp only [Q₂, eval_qsum, one_mul, hQ2e]
  have hQVe' : ∀ i ℓ, (QV i).eval ℓ = ∑ _j ∈ F i, D.slotV e₀ mass A B c (t₀ • r) r ℓ a b :=
    fun i ℓ => by simp only [QV, eval_qsum, one_mul, hQVe]
  have hQ₂g : ∀ i, D.Good (Q₂ i) := fun i => by
    refine ⟨Or.inr (quart_qsum _ _ _ fun _ _ => hQ2q), ?_⟩
    rw [show (Q₂ i).eval = fun ℓ => ∑ _j ∈ F i, Q2.eval ℓ from
      funext fun ℓ => by simp only [Q₂, eval_qsum, one_mul]]
    exact RefinedBound.sum _ fun _ _ => hQ2g.2
  have hQVg : ∀ i, (D.dup i).Good (QV i) := fun i => by
    refine ⟨Or.inl (by change 7 ≤ D.m + 1; have := D.hm; omega), ?_⟩
    rw [show (QV i).eval = fun ℓ => ∑ _j ∈ F i, QVq.eval ℓ from
      funext fun ℓ => by simp only [QV, eval_qsum, one_mul]]
    refine RefinedBound.sum _ fun j hj => ?_
    obtain rfl : e₀ = i := (Finset.mem_filter.mp hj).2
    exact hVqg.2
  have hsum : ∀ (f : Fin (D.m + 1) → ℂ), (∀ i, e₀ ≠ i → f i = 0) →
      ∑ i, f i = f e₀ := fun f hf =>
    Finset.sum_eq_single e₀ (fun i _ h => hf i (Ne.symm h)) (by simp)
  have hder : ∀ ℓ, deriv (fun t => D.slotN e₀ mass A B c (t • r) ℓ a b) t₀ =
      -∑ i, (Q₂ i).eval ℓ := fun ℓ => by
    rw [(D.hasDerivAt_slotN e₀ mass (A := A) (B := B) r ℓ t₀ a b).deriv, hsum _ fun i h => by
      rcases hF i with ⟨h', -⟩ | ⟨-, hFi⟩
      · exact absurd h' h
      · rw [hQ₂e, hFi, Finset.sum_empty]]
    rcases hF e₀ with ⟨-, hFi⟩ | ⟨h, -⟩
    · rw [hQ₂e, hFi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
    · exact absurd rfl h
  have hQVi : ∀ i ℓ, (QV i).eval ℓ =
      ((Minkowski.dot (lineMomentum D.α (D.mom (t₀ • r)) i ℓ)
        (lineMomentum D.α (D.mom (t₀ • r)) i ℓ) + D.M i ^ 2 : ℝ) : ℂ) * (Q₂ i).eval ℓ +
      D.slotN e₀ mass A B c (t₀ • r) ℓ a b * (dLineC (D.mom (t₀ • r) i) (D.mom r i) +
        linF (dLineL (D.α i) (D.mom r i)) (loopComp ℓ)) := fun i ℓ => by
    rw [hQVe' i ℓ, hQ₂e i ℓ]
    rcases hF i with ⟨rfl, hFi⟩ | ⟨hne, hFi⟩
    · rw [hFi, Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        one_smul, one_smul, slotV_eq, dLineC_add_linF, hM]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      have hd : Minkowski.dot (D.mom r e₀) (lineMomentum D.α (D.mom (t₀ • r)) e₀ ℓ) =
          Minkowski.dot (fun μ => ∑ s, D.α e₀ s * ℓ s μ + D.mom (t₀ • r) e₀ μ)
            (D.mom r e₀) := by
        simp only [Minkowski.dot_eq, lineMomentum]
        ring
      rw [hd]
      push_cast
      ring
    · have hr : D.mom r i = 0 := by simp [mom, h0 i (Ne.symm hne)]
      rw [hFi, Finset.sum_empty, Finset.sum_empty, hr]
      simp [dLineC, dLineL, linF, Minkowski.lower, Minkowski.dot_eq]
  have h := hasDerivAt_pv_ray_ward D
    (fun ℓ => D.isLoopPoly_slotN_mom e₀ mass (A := A) (B := B) ℓ a b)
    hQ (fun p => D.refinedBound_slotN e₀ mass (A := A) (B := B) hS hSE hcb p a b) r hV
    (Filter.Eventually.of_forall hQf) hQf0 hQ₂g hder hQVg hQVi
  have hfun : (fun t => D.pvF (fun ℓ => D.slotN e₀ mass A B c (t • r) ℓ a b)
      (D.mom (t • r))) =ᶠ[𝓝 t₀] fun t => D.pv (Qf t) (D.mom (t • r)) := by
    filter_upwards [hV] with t ht
    exact pvF_eq (hQf t).1 (hQf t).2 ht
  refine (h.congr_of_eventuallyEq hfun).congr_deriv ?_
  congr 1
  rw [hsum _ fun i h => by
    rcases hF i with ⟨h', -⟩ | ⟨-, hFi⟩
    · exact absurd h' h
    · rw [show QV i = qsum (F i) (fun _ => 1) fun _ => QVq from rfl, hFi]
      have hl := pv_qsum (D := D.dup i) (∅ : Finset (Fin 1)) (fun _ => 1) (fun _ => QVq)
        (q := dbl i (D.mom (t₀ • r))) fun j hj => absurd hj (Finset.notMem_empty j)
      rw [hl, Finset.sum_empty]]
  rcases hF e₀ with ⟨-, hFi⟩ | ⟨h, -⟩
  · rw [show QV e₀ = qsum (F e₀) (fun _ => 1) fun _ => QVq from rfl, hFi]
    have hl := pv_qsum (D := D.dup e₀) (Finset.univ : Finset (Fin 1)) (fun _ => 1)
      (fun _ => QVq) (q := dbl e₀ (D.mom (t₀ • r))) fun _ _ => integrableOn_pv hVqg (hV₀.dup _)
    rw [hl, Fin.sum_univ_one, one_mul, pvF_eq hVqg hQVe (hV₀.dup _)]
  · exact absurd rfl h

end QED.GradedProof.SE2.SEData

end
