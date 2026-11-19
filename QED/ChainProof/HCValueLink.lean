/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCValueChain
public import QED.ChainProof.HCClasses
public import QED.TwoLoop.PauliZeroLimitCurve
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `ChainPauliAtLink` from the fixed-`q` nested value, and the counterterm combination (O3-7)

Helper level, Phase 5 Stage 1a. The obligation `QED.ChainProof.ChainPauliAtLink` of
`QED/ChainProof/HCLinks.lean` (the `q² → 0⁺` limit of the Pauli projection of the chain limit at
the canonical pair has the value `e⁶ chainRegMass/(64π⁶)`) is reduced here to a statement at
**fixed** `q² > 0`, the nested form of the chain limit, with the `q² → 0⁺` limit and the value
carried out on the explicit side (`QED/ChainProof/HCValueChain.lean`).

## The conditional statements (not proved here)

* `ChainNestedAtLink` (O3-6 and O3-7 at fixed `q`, at the `ε → 0⁺` level): at admissible
  parameters, for all small `Q > 0`, every `ε → 0⁺` limit `V` of the chain vertex at the canonical
  pair `(boostMomentum m Q, restMomentum m)` has Pauli projection
  `formFactorProj₂ e m p' p V = e² outerAt m Q (chainPhoton P)`: the one-loop Pauli functional of
  the photon function `(Π_loop(k²) - δ₃)² k⁴ D(k²)³` at `q² = Q`, the three-loop analogue of
  `QED.TwoLoop.VPHalf.vpHalfSubAt_iff_outer`.
* `ClassNestedAtLink X R` (O3-6 per class): the same for each class limit of a class decomposition
  `X` (`QED/ChainProof/HCClasses.lean`), with a photon function `R r P` per class.

## Proved

* `chainPauliAtLink_of_nested`: **`ChainExistsLink` and `ChainNestedAtLink` give
  `ChainPauliAtLink`.** The limit is `QED.ChainProof.HCValue.tendsto_outerAt_chainPhoton`
  (O3-9 on the explicit side), the value `outerAt_chainPhoton_zero` (O3-10 with mass scaling).
* `formFactorProj₂_sum`: the Pauli projection is additive over finite sums of vertices.
* `chainNestedAtLink_of_classes` (**the counterterm combination O3-7**): a class decomposition,
  the per-class limit link, the per-class nested values, and photon functions `R r P` that are
  integrable at small `q²` and sum to `chainPhoton P` on `[0, ∞)`, give `ChainNestedAtLink`.
* `chainPauliAtLink_of_classes`: the composite, `ChainPauliAtLink` from the decomposition, the
  per-class limit link and the per-class nested values.

Charge homogeneity is not needed: the statements are at the charge of `P`, and the charge enters
the explicit side through `Π_loop ∝ e²` and `δ₃ = Π_loop(0)` (Z₈).
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real
open QED.WickModel (Params vacuumPolarizationLoop)

namespace QED.ChainProof.HCValue

open QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero QED.ChainProof.CovFamily

/-- **The nested value of the chain limit at fixed `q² = Q`** (O3-6 and O3-7 at fixed `q`; not
proved here): at admissible parameters, for all small `Q > 0`, every limit of the chain vertex at
the canonical pair has Pauli projection `e² outerAt m Q (chainPhoton P)`. -/
def ChainNestedAtLink : Prop :=
  ∀ P : Params, ChainAdmissible P → ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ V,
    chainLim P (boostMomentum P.m Q) (restMomentum P.m) V →
      QED.OneLoop.formFactorProj₂ P.e P.m (boostMomentum P.m Q) (restMomentum P.m) V =
        ((P.e ^ 2 * outerAt P.m Q (chainPhoton P) : ℝ) : ℂ)

/-- The canonical pair with `q² = Q > 0` is an admissible pair. -/
theorem isPairQ_canonical' {m Q : ℝ} (hm : 0 < m) (hQ : 0 < Q) :
    IsPairQ m (boostMomentum m Q) (restMomentum m) :=
  ⟨dot_boostMomentum hm hQ.le, dot_restMomentum, boostMomentum_pos hm hQ.le,
    restMomentum_pos hm, by rw [dot_boostMomentum_sub_restMomentum hm hQ.le]; exact hQ⟩

/-- When a limit exists, the chosen canonical limit is one. -/
theorem lim_canonicalLimit_of_exists {Lim : (Fin 4 → ℝ) → (Fin 4 → ℝ) →
    (Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) → Prop} {m Q : ℝ}
    (h : ∃ V, Lim (boostMomentum m Q) (restMomentum m) V) :
    Lim (boostMomentum m Q) (restMomentum m) (canonicalLimit Lim m Q) := by
  unfold canonicalLimit
  simp only [h, dite_true]
  exact h.choose_spec

/-- **`ChainPauliAtLink` from existence and the fixed-`q` nested value.** -/
theorem chainPauliAtLink_of_nested (hE : ChainExistsLink) (hN : ChainNestedAtLink) :
    ChainPauliAtLink := by
  intro P hA
  have hT := (tendsto_outerAt_chainPhoton hA).const_mul (P.e ^ 2)
  rw [outerAt_chainPhoton_zero hA] at hT
  have hT' := (continuous_ofReal.tendsto _).comp hT
  have hev : (fun Q => ((P.e ^ 2 * outerAt P.m Q (chainPhoton P) : ℝ) : ℂ)) =ᶠ[𝓝[>] 0]
      pauliAtCanonical (chainLim P) P.e P.m := by
    filter_upwards [hN P hA, self_mem_nhdsWithin] with Q hQ (hQ0 : 0 < Q)
    have hex := hE P hA _ _ (isPairQ_canonical' hA.hm hQ0)
    exact (hQ _ (lim_canonicalLimit_of_exists hex)).symm
  refine (hT'.congr' hev).trans (le_of_eq ?_)
  congr 1
  push_cast
  ring

/-! ### Additivity of the Pauli projection -/

/-- **The Pauli projection is additive** over finite sums of vertices. -/
theorem formFactorProj₂_sum {ι : Type*} [Fintype ι] (e m : ℝ) (p' p : Fin 4 → ℝ)
    (Y : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    QED.OneLoop.formFactorProj₂ e m p' p (∑ r, Y r) =
      ∑ r, QED.OneLoop.formFactorProj₂ e m p' p (Y r) := by
  simp only [QED.TwoLoop.PauliZeroLimit.formFactorProj₂_eq_pauliNum,
    QED.TwoLoop.PauliZeroLimit.pauliNum_eq_sum, Finset.sum_apply, Matrix.sum_apply,
    Finset.mul_sum]
  rw [← Finset.sum_div]
  congr 1
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-! ### The counterterm combination (O3-7) -/

section Classes

variable {ι : Type*} [Fintype ι]
  (X : ι → Params → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (R : ι → Params → ℝ → ℝ)

/-- **The nested value of each class limit at fixed `q² = Q`** (O3-6 per class; not proved
here): at admissible parameters, for all small `Q > 0`, every limit of the class vertex `X r` at
the canonical pair has Pauli projection `e² outerAt m Q (R r P)`. -/
def ClassNestedAtLink : Prop :=
  ∀ r P, ChainAdmissible P → ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ Y,
    IsClassLimit X r P (boostMomentum P.m Q) (restMomentum P.m) Y →
      QED.OneLoop.formFactorProj₂ P.e P.m (boostMomentum P.m Q) (restMomentum P.m) Y =
        ((P.e ^ 2 * outerAt P.m Q (R r P) : ℝ) : ℂ)

/-- The class photon functions are integrable at small `q²` and sum to the set (b) photon
function on `[0, ∞)`. -/
structure ClassPhotonData : Prop where
  integrable : ∀ P, ChainAdmissible P → ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ r, IntegrableAt P.m Q (R r P)
  sum : ∀ P, ChainAdmissible P → ∀ s, 0 ≤ s → ∑ r, R r P s = chainPhoton P s

variable {X R}

/-- **The counterterm combination (O3-7)**: the class decomposition, the per-class limits and the
per-class nested values give the nested value of the chain limit. -/
theorem chainNestedAtLink_of_classes (hD : ChainClassDecomposition X) (hL : ClassLimitLink X)
    (hN : ClassNestedAtLink X R) (hR : ClassPhotonData R) : ChainNestedAtLink := by
  intro P hA
  have hall : ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ r, ∀ Y,
      IsClassLimit X r P (boostMomentum P.m Q) (restMomentum P.m) Y →
        QED.OneLoop.formFactorProj₂ P.e P.m (boostMomentum P.m Q) (restMomentum P.m) Y =
          ((P.e ^ 2 * outerAt P.m Q (R r P) : ℝ) : ℂ) :=
    eventually_all.mpr fun r => hN r P hA
  filter_upwards [hall, hR.integrable P hA, self_mem_nhdsWithin] with Q hQ hI (hQ0 : 0 < Q)
  intro V hV
  have hpq := isPairQ_canonical' hA.hm hQ0
  choose Y hY using fun r => hL r P hA _ _ hpq
  rw [chainLim_eq_sum hD hA hpq hY hV, formFactorProj₂_sum,
    Finset.sum_congr rfl fun r _ => hQ r (Y r) (hY r), ← ofReal_sum, ← Finset.mul_sum,
    ← outerAt_sum _ fun r _ => hI r, outerAt_congr hQ0.le (hR.sum P hA)]

/-- **`ChainPauliAtLink` from the class decomposition, the per-class limits and the per-class
nested values.** -/
theorem chainPauliAtLink_of_classes (hD : ChainClassDecomposition X) (hL : ClassLimitLink X)
    (hN : ClassNestedAtLink X R) (hR : ClassPhotonData R) : ChainPauliAtLink :=
  chainPauliAtLink_of_nested (chainExistsLink_of_classes hD hL)
    (chainNestedAtLink_of_classes hD hL hN hR)

end Classes

end QED.ChainProof.HCValue

end
