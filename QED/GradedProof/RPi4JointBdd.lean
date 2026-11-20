/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Sectors
public import QED.GradedProof.RPi4Unif
public import QED.GradedProof.RPi4LightPiece

/-!
# (R-Π₄) step L6d: uniformly bounded numerator families along a segment of momenta

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), instantiation of the sector
rates. Along the segment `|u| ≤ 1/2` of tilted momenta the numerators of a piece are represented
by the joint quartic `jointQuartic D n Qk u = ∑ₖ λₖ(u) Qₖ` of finitely many node quartics.
The weights `λₖ` are bounded on `[-1/2, 1/2]` (`exists_norm_lam_le`), so the joint quartics
have uniformly bounded coefficients (`lqBdd_jointQuartic`); they inherit the degree bounds along
a loop (`loopDegLe_jointQuartic`) and a vanishing quartic part (`quart_jointQuartic`) from the
nodes.

* `lqBdd_finite`: a finite family of quartics has bounded coefficients;
* `lqBdd_qsum`: combinations with bounded weights of a bounded finite family are bounded;
* `loopDegLe_qsum`, `quart_qsum_eq_zero`;
-/

@[expose] public section

open Complex Set

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZeroLimit

/-- **A finite family of quartics has uniformly bounded coefficients.** -/
theorem lqBdd_finite {κ : Type*} [Finite κ] (Q : κ → LoopQuartic) : ∃ B, LQBdd Q B := by
  obtain ⟨B₀, h₀⟩ := Finite.exists_le fun i => ‖(Q i).const‖
  obtain ⟨B₁, h₁⟩ := Finite.exists_le fun p : κ × LoopIndex => ‖(Q p.1).lin p.2‖
  obtain ⟨B₂, h₂⟩ := Finite.exists_le fun p : κ × LoopIndex × LoopIndex =>
    ‖(Q p.1).quad p.2.1 p.2.2‖
  obtain ⟨B₃, h₃⟩ := Finite.exists_le fun p : κ × LoopIndex × LoopIndex × LoopIndex =>
    ‖(Q p.1).cub p.2.1 p.2.2.1 p.2.2.2‖
  obtain ⟨B₄, h₄⟩ := Finite.exists_le fun p : κ × LoopIndex × LoopIndex × LoopIndex × LoopIndex =>
    ‖(Q p.1).quart p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2‖
  refine ⟨max (max (max B₀ B₁) (max B₂ B₃)) B₄, ⟨fun i => ?_, fun i a => ?_, fun i a b => ?_,
    fun i a b c => ?_, fun i a b c d => ?_⟩⟩
  · exact (h₀ i).trans (by simp)
  · exact (h₁ (i, a)).trans (by simp)
  · exact (h₂ (i, a, b)).trans (by simp)
  · exact (h₃ (i, a, b, c)).trans (by simp)
  · exact (h₄ (i, a, b, c, d)).trans (by simp)

theorem norm_sum_mul_le {κ : Type*} [Fintype κ] {c x : κ → ℂ} {Λ B : ℝ} (hc : ∀ k, ‖c k‖ ≤ Λ)
    (hx : ∀ k, ‖x k‖ ≤ B) : ‖∑ k, c k * x k‖ ≤ Fintype.card κ * (Λ * B) := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖c k * x k‖ ≤ ∑ _k : κ, Λ * B := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]
        exact mul_le_mul (hc k) (hx k) (norm_nonneg _) ((norm_nonneg _).trans (hc k))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Combinations with bounded weights of a bounded finite family are bounded.** -/
theorem lqBdd_qsum {ι κ : Type*} [Fintype κ] {Qk : κ → LoopQuartic} {B : ℝ} (hQ : LQBdd Qk B)
    {c : ι → κ → ℂ} {Λ : ℝ} (hc : ∀ i k, ‖c i k‖ ≤ Λ) :
    LQBdd (fun i => qsum Finset.univ (c i) Qk) (Fintype.card κ * (Λ * B)) :=
  ⟨fun i => norm_sum_mul_le (hc i) fun k => hQ.const k,
    fun i a => norm_sum_mul_le (hc i) fun k => hQ.lin k a,
    fun i a b => norm_sum_mul_le (hc i) fun k => hQ.quad k a b,
    fun i a b d => norm_sum_mul_le (hc i) fun k => hQ.cub k a b d,
    fun i a b d e => norm_sum_mul_le (hc i) fun k => hQ.quart k a b d e⟩

theorem loopDegLe_qsum {κ : Type*} (s : Finset κ) (c : κ → ℂ) {Qk : κ → LoopQuartic}
    {t : Fin 2} {d : ℕ} (h : ∀ k, LoopDegLe t d (Qk k)) : LoopDegLe t d (qsum s c Qk) :=
  ⟨fun a ha => Finset.sum_eq_zero fun k _ => by rw [(h k).lin a ha, mul_zero],
    fun a b ha => Finset.sum_eq_zero fun k _ => by rw [(h k).quad a b ha, mul_zero],
    fun a b d ha => Finset.sum_eq_zero fun k _ => by rw [(h k).cub a b d ha, mul_zero],
    fun a b d e ha => Finset.sum_eq_zero fun k _ => by rw [(h k).quart a b d e ha, mul_zero]⟩

theorem quart_qsum_eq_zero {κ : Type*} (s : Finset κ) (c : κ → ℂ) {Qk : κ → LoopQuartic}
    (h : ∀ k, (Qk k).quart = 0) : (qsum s c Qk).quart = 0 := by
  funext a b d e
  exact Finset.sum_eq_zero fun k _ => by rw [h k]; simp

/-- **The joint quartics along the segment have uniformly bounded coefficients.** -/
theorem lqBdd_jointQuartic (D n : ℕ) (Qk : Fin (D + 1) → LoopQuartic) :
    ∃ B, LQBdd (fun u : {u : ℝ // |u| ≤ 1 / 2} => jointQuartic D n Qk u) B := by
  obtain ⟨B, hB⟩ := lqBdd_finite Qk
  obtain ⟨Λ, hΛ⟩ := exists_norm_lam_le D n
  exact ⟨_, lqBdd_qsum (c := fun u : {u : ℝ // |u| ≤ 1 / 2} => lam D n u) hB
    fun u k => hΛ u u.2 k⟩

theorem loopDegLe_jointQuartic (D n : ℕ) {Qk : Fin (D + 1) → LoopQuartic} {t : Fin 2} {d : ℕ}
    (h : ∀ k, LoopDegLe t d (Qk k)) (u : ℝ) : LoopDegLe t d (jointQuartic D n Qk u) :=
  loopDegLe_qsum _ _ h

theorem quart_jointQuartic (D n : ℕ) {Qk : Fin (D + 1) → LoopQuartic}
    (h : ∀ k, (Qk k).quart = 0) (u : ℝ) : (jointQuartic D n Qk u).quart = 0 :=
  quart_qsum_eq_zero _ _ h

end QED.GradedProof.RPi4

end
