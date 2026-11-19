/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Pauli projection of a covariant family of vertex limits depends only on `q²`

Helper level, Phase 5 Stage 1a, toward obligation O3-9 (the `q² → 0⁺` limit uniformly over the
on-shell pairs). This is the argument of `QED/TwoLoop/PauliZeroKinematics.lean` and
`QED/TwoLoop/PauliZero.lean`, written for an **abstract** family of vertex limits
`Lim p' p V` ("`V` is the limit of the vertex at the pair `(p', p)`") with three properties at a
fixed mass `m > 0`, on on-shell positive-energy pairs with `q² > 0`:

* `CovFamily.exists`: a limit exists;
* `CovFamily.unique`: it is unique;
* `CovFamily.cov`: covariance under every real `L` with a spinor lift `(S, T)`
  (`QED.TwoLoop.LimitCovariance.IsSpinLift`) that keeps positive energies:
  `S W^μ T = L^μ_ν V^ν` for the limits `V` at `(p', p)` and `W` at `(L p', L p)`.

Then:
* `CovFamily.formFactorProj₂_eq_of_dot_sub_eq`: two pairs with the same `q²` have the same Pauli
  projection (two reflections, as in the two-loop case);
* `CovFamily.isLittleGroupCovariant`: every limit is little-group covariant;
* `CovFamily.uniform_of_tendsto`: if the Pauli projection at the canonical pair
  `(boostMomentum m Q, restMomentum m)` tends to `a` as `Q → 0⁺`, the Pauli projection of every
  limit at every pair with `0 < q² < q₀` is within any `η` of `a`.

Nothing here refers to a particular vertex; `QED/ChainProof/HCLinks.lean` applies it to the chain
vertex.
-/

@[expose] public section

open Complex Matrix Filter Topology

namespace QED.ChainProof

open QED.Dirac QED.TwoLoop.LimitCovariance QED.TwoLoop.ReflCovariance QED.TwoLoop.PauliZero

/-- An on-shell positive-energy pair at mass `m` with `q² > 0`. -/
def IsPairQ (m : ℝ) (p' p : Fin 4 → ℝ) : Prop :=
  Minkowski.dot p' p' = -m ^ 2 ∧ Minkowski.dot p p = -m ^ 2 ∧ 0 < p' 0 ∧ 0 < p 0 ∧
    0 < Minkowski.dot (p' - p) (p' - p)

/-- **A covariant family of vertex limits** at mass `m`: on the pairs `IsPairQ m`, limits exist,
are unique, and are covariant under the Lorentz maps with a spinor lift that keep positive
energies. -/
structure CovFamily (m : ℝ) (Lim : (Fin 4 → ℝ) → (Fin 4 → ℝ) → (Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) →
    Prop) : Prop where
  pos : 0 < m
  exists' : ∀ p' p, IsPairQ m p' p → ∃ V, Lim p' p V
  unique : ∀ p' p, IsPairQ m p' p → ∀ V W, Lim p' p V → Lim p' p W → V = W
  cov : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
    ∀ p' p, IsPairQ m p' p → 0 < (L *ᵥ p') 0 → 0 < (L *ᵥ p) 0 →
    ∀ V W, Lim p' p V → Lim (L *ᵥ p') (L *ᵥ p) W → ∀ μ, S * W μ * T = vecAct L V μ

namespace CovFamily

variable {m : ℝ} {Lim : (Fin 4 → ℝ) → (Fin 4 → ℝ) → (Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) → Prop}
  (H : CovFamily m Lim)
include H

/-- **Little-group covariance** of every limit. -/
theorem isLittleGroupCovariant {p' p : Fin 4 → ℝ} (hpq : IsPairQ m p' p) {V}
    (hV : Lim p' p V) : IsLittleGroupCovariant p' p V := by
  intro L S T hST hcov hLp hLp' μ
  have hW : Lim (L *ᵥ p') (L *ᵥ p) V := by rw [hLp, hLp']; exact hV
  have h0 : 0 < (L *ᵥ p') 0 := by rw [hLp']; exact hpq.2.2.1
  have h1 : 0 < (L *ᵥ p) 0 := by rw [hLp]; exact hpq.2.2.2.1
  exact H.cov L S T ⟨hST, hcov⟩ p' p hpq h0 h1 V V hV hW μ

/-- One reflection step: the Pauli projections at `(p', p)` and at its reflection agree. -/
theorem formFactorProj₂_eq_of_reflect {a p' p r' r : Fin 4 → ℝ}
    (ha : Minkowski.dot a a ≠ 0) (hr : reflect a p = r) (hr' : reflect a p' = r')
    (hpq : IsPairQ m p' p) (hr0 : 0 < r 0) (hr0' : 0 < r' 0) {V W}
    (hV : Lim p' p V) (hW : Lim r' r W) (e : ℝ) :
    QED.OneLoop.formFactorProj₂ e m r' r W = QED.OneLoop.formFactorProj₂ e m p' p V := by
  have hLp : reflectMatrix a *ᵥ p = r := by rw [reflectMatrix_mulVec, hr]
  have hLp' : reflectMatrix a *ᵥ p' = r' := by rw [reflectMatrix_mulVec, hr']
  rw [← hLp, ← hLp'] at hW ⊢
  exact formFactorProj₂_map (isSpinLift_reflect ha) e m p' p fun μ =>
    H.cov _ _ _ (isSpinLift_reflect ha) p' p hpq (hLp' ▸ hr0') (hLp ▸ hr0) V W hV hW μ

/-- **The Pauli projection depends on the pair only through `p'·p`.** -/
theorem formFactorProj₂_eq_of_dot_eq {p' p k' k : Fin 4 → ℝ} (hpq : IsPairQ m p' p)
    (hpt : Minkowski.dot k k = -m ^ 2) (hpt' : Minkowski.dot k' k' = -m ^ 2) (hpt0 : 0 < k 0)
    (hpt0' : 0 < k' 0) (hdot : Minkowski.dot k' k = Minkowski.dot p' p) {V W₁}
    (hV : Lim p' p V) (hW₁ : Lim k' k W₁) (e : ℝ) :
    QED.OneLoop.formFactorProj₂ e m k' k W₁ = QED.OneLoop.formFactorProj₂ e m p' p V := by
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hm := H.pos
  have hm2 : Minkowski.dot p p < 0 := by rw [hp]; nlinarith
  have hmt2 : Minkowski.dot k k < 0 := by rw [hpt]; nlinarith
  have hm2' : Minkowski.dot p' p' < 0 := by rw [hp']; nlinarith
  -- Step 1: move `p` to `k`.
  obtain ⟨p'', hp'', hp0'', hdot'', hstep₁⟩ : ∃ p'' : Fin 4 → ℝ,
      Minkowski.dot p'' p'' = -m ^ 2 ∧ 0 < p'' 0 ∧ Minkowski.dot p'' k = Minkowski.dot p' p ∧
      ∀ W, Lim p'' k W →
        QED.OneLoop.formFactorProj₂ e m p'' k W = QED.OneLoop.formFactorProj₂ e m p' p V := by
    by_cases hpp : p = k
    · subst hpp
      exact ⟨p', hp', hp0', rfl, fun W hW => by
        rw [H.unique p' p ⟨hp', hp, hp0', hp0, hq⟩ W V hW hV]⟩
    · set a := p - k with ha_def
      have hk : Minkowski.dot (p + k) (p + k) < 0 := by
        have e1 : Minkowski.dot (p + k) (p + k) =
            Minkowski.dot p p + 2 * Minkowski.dot p k + Minkowski.dot k k := by
          simp only [Minkowski.dot_eq, Pi.add_apply]; ring
        rw [e1]
        have := dot_neg_of_timelike hm2 hmt2 hp0 hpt0
        linarith
      have hak : Minkowski.dot a (p + k) = 0 := by
        have e1 : Minkowski.dot a (p + k) = Minkowski.dot p p - Minkowski.dot k k := by
          simp only [a, Minkowski.dot_eq, Pi.add_apply, Pi.sub_apply]; ring
        rw [e1, hp, hpt, sub_self]
      have ha0 : a ≠ 0 := fun h => hpp (sub_eq_zero.mp h)
      have haa : 0 < Minkowski.dot a a := dot_self_pos_of_dot_eq_zero hk hak ha0
      have hr : reflect a p = k := reflect_sub_self (by rw [hp, hpt]) haa.ne'
      set p'' := reflect a p' with hp''_def
      have hp''2 : Minkowski.dot p'' p'' = -m ^ 2 := by rw [dot_reflect haa.ne', hp']
      have hd : Minkowski.dot p'' k = Minkowski.dot p' p := by
        rw [← hr, dot_reflect haa.ne']
      have hp''0 : 0 < p'' 0 := by
        refine pos_of_dot_neg (by rw [hp''2]; nlinarith) hmt2 hpt0 ?_
        rw [hd]
        exact dot_neg_of_timelike hm2' hm2 hp0' hp0
      exact ⟨p'', hp''2, hp''0, hd, fun W hW =>
        H.formFactorProj₂_eq_of_reflect haa.ne' hr rfl ⟨hp', hp, hp0', hp0, hq⟩ hpt0 hp''0 hV hW
          e⟩
  -- Step 2: move `p''` to `k'`, fixing `k`.
  have hk'' : 0 < Minkowski.dot (p'' - k) (p'' - k) := by
    rw [dot_sub_eq_of_onShell hp'' hpt, hdot'', ← dot_sub_eq_of_onShell hp' hp]
    exact hq
  have hpq'' : IsPairQ m p'' k := ⟨hp'', hpt, hp0'', hpt0, hk''⟩
  obtain ⟨W, hW⟩ := H.exists' p'' k hpq''
  rw [← hstep₁ W hW]
  by_cases hpp : p'' = k'
  · subst hpp
    rw [H.unique p'' k hpq'' W₁ W hW₁ hW]
  · set a := p'' - k' with ha_def
    have hak : Minkowski.dot a k = 0 := by
      have e1 : Minkowski.dot a k = Minkowski.dot p'' k - Minkowski.dot k' k := by
        simp only [a, Minkowski.dot_eq, Pi.sub_apply]; ring
      rw [e1, hdot'', hdot, sub_self]
    have ha0 : a ≠ 0 := fun h => hpp (sub_eq_zero.mp h)
    have haa : 0 < Minkowski.dot a a := dot_self_pos_of_dot_eq_zero hmt2 hak ha0
    exact H.formFactorProj₂_eq_of_reflect haa.ne' (QED.Dirac.reflect_of_dot_eq_zero hak)
      (reflect_sub_self (by rw [hp'', hpt']) haa.ne') hpq'' hpt0 hpt0' hW hW₁ e

/-- **The same with `q²`**: pairs with equal `q²` have equal Pauli projections. -/
theorem formFactorProj₂_eq_of_dot_sub_eq {p' p k' k : Fin 4 → ℝ} (hpq : IsPairQ m p' p)
    (hpt : Minkowski.dot k k = -m ^ 2) (hpt' : Minkowski.dot k' k' = -m ^ 2) (hpt0 : 0 < k 0)
    (hpt0' : 0 < k' 0)
    (hqq : Minkowski.dot (k' - k) (k' - k) = Minkowski.dot (p' - p) (p' - p)) {V W₁}
    (hV : Lim p' p V) (hW₁ : Lim k' k W₁) (e : ℝ) :
    QED.OneLoop.formFactorProj₂ e m k' k W₁ = QED.OneLoop.formFactorProj₂ e m p' p V := by
  refine H.formFactorProj₂_eq_of_dot_eq hpq hpt hpt' hpt0 hpt0' ?_ hV hW₁ e
  rw [dot_sub_eq_of_onShell hpt' hpt, dot_sub_eq_of_onShell hpq.1 hpq.2.1] at hqq
  linarith

/-- The canonical pair with `q² = Q > 0` is admissible. -/
theorem isPairQ_canonical {Q : ℝ} (hQ : 0 < Q) :
    IsPairQ m (boostMomentum m Q) (restMomentum m) :=
  ⟨dot_boostMomentum H.pos hQ.le, dot_restMomentum, boostMomentum_pos H.pos hQ.le,
    restMomentum_pos H.pos, by rw [dot_boostMomentum_sub_restMomentum H.pos hQ.le]; exact hQ⟩

omit H in
/-- The limit at the canonical pair with `q² = Q` (an arbitrary one when there is none). -/
noncomputable def canonicalLimit (Lim : (Fin 4 → ℝ) → (Fin 4 → ℝ) →
    (Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) → Prop) (m Q : ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  by
    classical
    exact if h : ∃ V, Lim (boostMomentum m Q) (restMomentum m) V then h.choose else 0

theorem lim_canonicalLimit {Q : ℝ} (hQ : 0 < Q) :
    Lim (boostMomentum m Q) (restMomentum m) (canonicalLimit Lim m Q) := by
  have h := H.exists' _ _ (H.isPairQ_canonical hQ)
  unfold canonicalLimit
  simp only [h, dite_true]
  exact h.choose_spec

omit H in
/-- **The Pauli projection at the canonical pair with `q² = Q`.** -/
noncomputable def pauliAtCanonical (Lim : (Fin 4 → ℝ) → (Fin 4 → ℝ) →
    (Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) → Prop) (e m Q : ℝ) : ℂ :=
  QED.OneLoop.formFactorProj₂ e m (boostMomentum m Q) (restMomentum m) (canonicalLimit Lim m Q)

/-- **The Pauli projection of every limit is the canonical one at its `q²`.** -/
theorem formFactorProj₂_eq_pauliAtCanonical {p' p : Fin 4 → ℝ} (hpq : IsPairQ m p' p) {V}
    (hV : Lim p' p V) (e : ℝ) :
    QED.OneLoop.formFactorProj₂ e m p' p V =
      pauliAtCanonical Lim e m (Minkowski.dot (p' - p) (p' - p)) := by
  have hQ := hpq.2.2.2.2
  have hc := H.isPairQ_canonical hQ
  exact (H.formFactorProj₂_eq_of_dot_sub_eq hpq hc.2.1 hc.1 hc.2.2.2.1 hc.2.2.1
    (dot_boostMomentum_sub_restMomentum H.pos hQ.le) hV (H.lim_canonicalLimit hQ) e).symm

/-- **O3-9 reduced to one variable.** If the canonical Pauli projection tends to `a` as
`Q → 0⁺`, then for every `η > 0` there is `q₀ > 0` such that every limit at every pair with
`0 < q² < q₀` has `‖P₂ V - a‖ < η`. -/
theorem uniform_of_tendsto (e : ℝ) {a : ℂ}
    (ha : Tendsto (pauliAtCanonical Lim e m) (𝓝[>] 0) (𝓝 a)) :
    ∀ η > 0, ∃ q₀ > 0, ∀ p' p, IsPairQ m p' p → Minkowski.dot (p' - p) (p' - p) < q₀ →
      ∀ V, Lim p' p V → ‖QED.OneLoop.formFactorProj₂ e m p' p V - a‖ < η := by
  intro η hη
  obtain ⟨q₀, hq₀, h⟩ := (tendsto_nhdsWithin_Ioi_iff_uniform.mp ha) η hη
  refine ⟨q₀, hq₀, fun p' p hpq hqq V hV => ?_⟩
  rw [H.formFactorProj₂_eq_pauliAtCanonical hpq hV]
  exact h _ hpq.2.2.2.2 hqq

/-- **Conversely**, the uniform statement gives the one-variable limit. -/
theorem tendsto_of_uniform (e : ℝ) {a : ℂ}
    (h : ∀ η > 0, ∃ q₀ > 0, ∀ p' p, IsPairQ m p' p → Minkowski.dot (p' - p) (p' - p) < q₀ →
      ∀ V, Lim p' p V → ‖QED.OneLoop.formFactorProj₂ e m p' p V - a‖ < η) :
    Tendsto (pauliAtCanonical Lim e m) (𝓝[>] 0) (𝓝 a) := by
  refine tendsto_nhdsWithin_Ioi_iff_uniform.mpr fun η hη => ?_
  obtain ⟨q₀, hq₀, h'⟩ := h η hη
  refine ⟨q₀, hq₀, fun Q hQ hQ₀ => ?_⟩
  have hc := H.isPairQ_canonical hQ
  exact h' _ _ hc (by rw [dot_boostMomentum_sub_restMomentum H.pos hQ.le]; exact hQ₀) _
    (H.lim_canonicalLimit hQ)

end CovFamily

end QED.ChainProof

end
