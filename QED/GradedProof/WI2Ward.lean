/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Ray
public import QED.GradedProof.WI2Transfer

/-!
# The Ward–Takahashi derivative of a parametric value

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
steps A4 and A5 assembled on self-energy data.

* `SEData.pv_dup_split`: over the data with line `i` doubled, a numerator
  `(kᵢ·kᵢ + Mᵢ²) Q₂ + P · 2 kᵢ·r` has value `pv[Q₂] + pv^{dup i}[P · 2 kᵢ·r]` (linearity and
  `SEData.pv_dup_of_eval_eq`). On an electron line this is the insertion
  `(m - k̸) r̸ (m - k̸) = (k·k + m²) r̸ + 2 (r·k)(m - k̸)`
  (`QED.GradedProof.WI2.numerator_slash_numerator`).
* `SEData.hasDerivAt_pv_ray_ward`: if the derivative of the numerator along the ray is
  `-∑ᵢ Q₂ᵢ` and each `QVᵢ` is the insertion numerator above with `r = qᵢ`, then
  `d/dt pv[N(t w)](t w) = -∑ᵢ pv^{dup i}[QVᵢ](t w)`: the derivative of the self-energy piece is
  minus the sum over its lines of the zero-momentum insertions (Ward–Takahashi at `q = 0`).
-/

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.GradedProof.SE2.SEData

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.GradedProof.WI2
open QED.TwoLoop.Bridge (IsLoopPoly)

/-- **Splitting an insertion numerator over the doubled data.** -/
theorem pv_dup_split (D : SEData) (i : Fin (D.m + 1)) {QV Q₂ P : LoopQuartic}
    (hQV : (D.dup i).Good QV) (hQ₂ : D.Good Q₂) (hq : P.quart = 0)
    (hP : RefinedBound D.α D.E 3 P.eval) {q : Fin (D.m + 1) → Fin 4 → ℝ} (r : Fin 4 → ℝ)
    (he : ∀ ℓ, QV.eval ℓ = ((Minkowski.dot (lineMomentum D.α q i ℓ) (lineMomentum D.α q i ℓ) +
      D.M i ^ 2 : ℝ) : ℂ) * Q₂.eval ℓ +
        P.eval ℓ * (dLineC (q i) r + linF (dLineL (D.α i) r) (loopComp ℓ)))
    (hV : D.VPos q) :
    (D.dup i).pv QV (dbl i q) =
      D.pv Q₂ q + (D.dup i).pv (Cubic.mulLin P (dLineC (q i) r) (dLineL (D.α i) r)) (dbl i q) := by
  set ML := Cubic.mulLin P (dLineC (q i) r) (dLineL (D.α i) r) with hML
  -- `good_mulLin` with the external momenta `q` and `fun _ => r`
  have hMLg : (D.dup i).Good ML := good_mulLin D i hq hP q fun _ => r
  have hMLe : ∀ ℓ, ML.eval ℓ = P.eval ℓ * (dLineC (q i) r + linF (dLineL (D.α i) r) (loopComp ℓ)) :=
    fun ℓ => evalC_mulLin P hq _ _ _
  set c : Fin 2 → ℂ := ![1, -1]
  set Qs : Fin 2 → LoopQuartic := ![QV, ML]
  set Qa := qsum Finset.univ c Qs with hQa
  have hQae : ∀ ℓ, Qa.eval ℓ = QV.eval ℓ - ML.eval ℓ := fun ℓ => by
    rw [hQa, eval_qsum, Fin.sum_univ_two]
    simp [c, Qs]
    ring
  have hQag : (D.dup i).Good Qa := by
    refine ⟨Or.inl (by change 7 ≤ D.m + 1; have := D.hm; omega), ?_⟩
    have e : Qa.eval = fun ℓ => QV.eval ℓ - ML.eval ℓ := funext hQae
    rw [e]
    exact hQV.2.sub hMLg.2
  have hV' := hV.dup i
  have hlin := pv_qsum (D := D.dup i) Finset.univ c Qs (q := dbl i q) fun k _ => by
    fin_cases k
    · exact integrableOn_pv hQV hV'
    · exact integrableOn_pv hMLg hV'
  rw [← hQa, Fin.sum_univ_two] at hlin
  simp only [c, Qs, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
    neg_one_mul] at hlin
  have htr := pv_dup_of_eval_eq D i hQag hQ₂ (q := q) (fun ℓ => by
    rw [hQae, he, hMLe]; ring) hV
  rw [htr] at hlin
  rw [hlin]
  ring

/-- **The Ward–Takahashi derivative of a parametric value along a ray.** -/
theorem hasDerivAt_pv_ray_ward (D : SEData) {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ}
    {d : ℕ} (hpoly : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ)
    (hQ : ∀ p, ∃ Q : LoopQuartic, D.Good Q ∧ Q.quart = 0 ∧ Q.eval = N p)
    (hN3 : ∀ p, RefinedBound D.α D.E 3 (N p)) (w : Fin 4 → ℝ) {t₀ : ℝ}
    (hV : ∀ᶠ t in 𝓝 t₀, D.VPos (D.mom (t • w))) {Qf : ℝ → LoopQuartic}
    (hQf : ∀ᶠ t in 𝓝 t₀, D.Good (Qf t) ∧ (Qf t).eval = N (t • w)) (hQf0 : (Qf t₀).quart = 0)
    {Q₂ : Fin (D.m + 1) → LoopQuartic} (hQ₂ : ∀ i, D.Good (Q₂ i))
    (hder : ∀ ℓ, deriv (fun t => N (t • w) ℓ) t₀ = -∑ i, (Q₂ i).eval ℓ)
    {QV : Fin (D.m + 1) → LoopQuartic} (hQV : ∀ i, (D.dup i).Good (QV i))
    (hQVe : ∀ i ℓ, (QV i).eval ℓ = ((Minkowski.dot (lineMomentum D.α (D.mom (t₀ • w)) i ℓ)
        (lineMomentum D.α (D.mom (t₀ • w)) i ℓ) + D.M i ^ 2 : ℝ) : ℂ) * (Q₂ i).eval ℓ +
      N (t₀ • w) ℓ * (dLineC (D.mom (t₀ • w) i) (D.mom w i) +
        linF (dLineL (D.α i) (D.mom w i)) (loopComp ℓ))) :
    HasDerivAt (fun t => D.pv (Qf t) (D.mom (t • w)))
      (-∑ i, (D.dup i).pv (QV i) (dbl i (D.mom (t₀ • w)))) t₀ := by
  have hV₀ := hV.self_of_nhds
  have hQf₀ := hQf.self_of_nhds
  set Q' := qsum Finset.univ (fun _ => (-1 : ℂ)) Q₂ with hQ'
  have hQ'e : Q'.eval = fun ℓ => deriv (fun t => N (t • w) ℓ) t₀ := by
    funext ℓ
    rw [hQ', eval_qsum, hder, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hQ'g : D.Good Q' := by
    refine ⟨?_, ?_⟩
    · rcases Nat.lt_or_ge D.m 7 with h7 | h7
      · exact Or.inr (quart_qsum _ _ _ fun k _ => ((hQ₂ k).1.resolve_left (by omega)))
      · exact Or.inl h7
    · have e : Q'.eval = fun ℓ => ∑ k, (-1 : ℂ) * (Q₂ k).eval ℓ := funext fun ℓ => eval_qsum _ _ _ ℓ
      rw [e]
      exact RefinedBound.sum _ fun k _ => ((hQ₂ k).2).const_mul _
  have h := hasDerivAt_pv_ray D hpoly hQ hN3 w hV hQf hQf0 hQ'g hQ'e
  have hP3 : RefinedBound D.α D.E 3 (Qf t₀).eval := by rw [hQf₀.2]; exact hN3 _
  have hsplit : ∀ i, (D.dup i).pv (QV i) (dbl i (D.mom (t₀ • w))) =
      D.pv (Q₂ i) (D.mom (t₀ • w)) + (D.dup i).pv (Cubic.mulLin (Qf t₀)
        (dLineC (D.mom (t₀ • w) i) (D.mom w i)) (dLineL (D.α i) (D.mom w i)))
        (dbl i (D.mom (t₀ • w))) := fun i =>
    pv_dup_split D i (hQV i) (hQ₂ i) hQf0 hP3 (D.mom w i) (fun ℓ => by
      rw [hQVe i ℓ, hQf₀.2]) hV₀
  have hpv' : D.pv Q' (D.mom (t₀ • w)) = -∑ i, D.pv (Q₂ i) (D.mom (t₀ • w)) := by
    rw [hQ', pv_qsum _ _ _ fun k _ => integrableOn_pv (hQ₂ k) hV₀, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  convert h using 1
  rw [hpv', Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib]
  ring

end QED.GradedProof.SE2.SEData

end
