/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Ward

/-!
# The Ward–Takahashi derivative with a remainder

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6 for the class `F`, whose numerator has a slot (the counterterm vertex `δ₂ k̸ + δ_m m`)
that depends on the external momentum without being an electron numerator of a line.

* `SEData.hasDerivAt_pv_ray_ward_add`: as `SEData.hasDerivAt_pv_ray_ward`, but with the
  derivative of the numerator along the ray `-∑ᵢ Q₂ᵢ + R`; the derivative of the parametric value
  gains the parametric value of `R` over the same data.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.GradedProof.WI2
open QED.TwoLoop.Bridge (IsLoopPoly)

/-- **The Ward–Takahashi derivative of a parametric value along a ray, with a remainder.** -/
theorem hasDerivAt_pv_ray_ward_add (D : SEData) {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ}
    {d : ℕ} (hpoly : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ)
    (hQ : ∀ p, ∃ Q : LoopQuartic, D.Good Q ∧ Q.quart = 0 ∧ Q.eval = N p)
    (hN3 : ∀ p, RefinedBound D.α D.E 3 (N p)) (w : Fin 4 → ℝ) {t₀ : ℝ}
    (hV : ∀ᶠ t in 𝓝 t₀, D.VPos (D.mom (t • w))) {Qf : ℝ → LoopQuartic}
    (hQf : ∀ᶠ t in 𝓝 t₀, D.Good (Qf t) ∧ (Qf t).eval = N (t • w)) (hQf0 : (Qf t₀).quart = 0)
    {Q₂ : Fin (D.m + 1) → LoopQuartic} (hQ₂ : ∀ i, D.Good (Q₂ i)) {R : LoopQuartic}
    (hR : D.Good R)
    (hder : ∀ ℓ, deriv (fun t => N (t • w) ℓ) t₀ = -∑ i, (Q₂ i).eval ℓ + R.eval ℓ)
    {QV : Fin (D.m + 1) → LoopQuartic} (hQV : ∀ i, (D.dup i).Good (QV i))
    (hQVe : ∀ i ℓ, (QV i).eval ℓ = ((Minkowski.dot (lineMomentum D.α (D.mom (t₀ • w)) i ℓ)
        (lineMomentum D.α (D.mom (t₀ • w)) i ℓ) + D.M i ^ 2 : ℝ) : ℂ) * (Q₂ i).eval ℓ +
      N (t₀ • w) ℓ * (dLineC (D.mom (t₀ • w) i) (D.mom w i) +
        linF (dLineL (D.α i) (D.mom w i)) (loopComp ℓ))) :
    HasDerivAt (fun t => D.pv (Qf t) (D.mom (t • w)))
      (D.pv R (D.mom (t₀ • w)) - ∑ i, (D.dup i).pv (QV i) (dbl i (D.mom (t₀ • w)))) t₀ := by
  have hV₀ := hV.self_of_nhds
  have hQf₀ := hQf.self_of_nhds
  set Q₀ := qsum Finset.univ (fun _ => (-1 : ℂ)) Q₂ with hQ₀
  have hQ₀g : D.Good Q₀ := by
    refine ⟨?_, ?_⟩
    · rcases Nat.lt_or_ge D.m 7 with h7 | h7
      · exact Or.inr (quart_qsum _ _ _ fun k _ => ((hQ₂ k).1.resolve_left (by omega)))
      · exact Or.inl h7
    · have e : Q₀.eval = fun ℓ => ∑ k, (-1 : ℂ) * (Q₂ k).eval ℓ :=
        funext fun ℓ => eval_qsum _ _ _ ℓ
      rw [e]
      exact RefinedBound.sum _ fun k _ => ((hQ₂ k).2).const_mul _
  set Qs : Fin 2 → LoopQuartic := ![Q₀, R]
  set Q' := qsum Finset.univ (fun _ => (1 : ℂ)) Qs with hQ'
  have hQs : ∀ k, D.Good (Qs k) := fun k => by fin_cases k; exacts [hQ₀g, hR]
  have hQ'e : Q'.eval = fun ℓ => deriv (fun t => N (t • w) ℓ) t₀ := by
    funext ℓ
    rw [hQ', eval_qsum, hder, Fin.sum_univ_two]
    simp only [Qs, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, hQ₀, eval_qsum,
      ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hQ'g : D.Good Q' := by
    refine ⟨?_, ?_⟩
    · rcases Nat.lt_or_ge D.m 7 with h7 | h7
      · exact Or.inr (quart_qsum _ _ _ fun k _ => ((hQs k).1.resolve_left (by omega)))
      · exact Or.inl h7
    · have e : Q'.eval = fun ℓ => ∑ k, (1 : ℂ) * (Qs k).eval ℓ :=
        funext fun ℓ => eval_qsum _ _ _ ℓ
      rw [e]
      exact RefinedBound.sum _ fun k _ => ((hQs k).2).const_mul _
  have h := hasDerivAt_pv_ray D hpoly hQ hN3 w hV hQf hQf0 hQ'g hQ'e
  have hP3 : RefinedBound D.α D.E 3 (Qf t₀).eval := by rw [hQf₀.2]; exact hN3 _
  have hsplit : ∀ i, (D.dup i).pv (QV i) (dbl i (D.mom (t₀ • w))) =
      D.pv (Q₂ i) (D.mom (t₀ • w)) + (D.dup i).pv (Cubic.mulLin (Qf t₀)
        (dLineC (D.mom (t₀ • w) i) (D.mom w i)) (dLineL (D.α i) (D.mom w i)))
        (dbl i (D.mom (t₀ • w))) := fun i =>
    pv_dup_split D i (hQV i) (hQ₂ i) hQf0 hP3 (D.mom w i) (fun ℓ => by
      rw [hQVe i ℓ, hQf₀.2]) hV₀
  have hpv₀ : D.pv Q₀ (D.mom (t₀ • w)) = -∑ i, D.pv (Q₂ i) (D.mom (t₀ • w)) := by
    rw [hQ₀, pv_qsum _ _ _ fun k _ => integrableOn_pv (hQ₂ k) hV₀, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hpv' : D.pv Q' (D.mom (t₀ • w)) = D.pv Q₀ (D.mom (t₀ • w)) + D.pv R (D.mom (t₀ • w)) := by
    rw [hQ', pv_qsum _ _ _ fun k _ => integrableOn_pv (hQs k) hV₀, Fin.sum_univ_two]
    simp only [Qs, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
  convert h using 1
  rw [hpv', hpv₀, Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib]
  ring

end QED.GradedProof.SE2.SEData

end
