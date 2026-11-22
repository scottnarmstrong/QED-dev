/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCCovClasses
public import QED.ChainProof.HCValueLink
public import QED.TwoLoop.PauliZeroLimitCt

/-!
# The canonical Pauli limit of set (c) from per-class Pauli limits

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The open input
`QED.ChainProof.SetCPauli.SetCPauliAt P₀ b` of `QED/ChainProof/SetCPauliLink.lean` (as `Q → 0⁺`,
the Pauli projection of every set (c) limit at the canonical pair
`(boostMomentum m Q, restMomentum m)` tends to `b m_γ Λ M₁ M₂`) is reduced here to one statement
per class of the split `QED.ChainProof.SetCPauli.familyVertex_setC_eq_split`
(`QED/ChainProof/SetCCovClasses.lean`):

* `SetCClassPauli V P₀ r β` (open per class): at the set (c) data, as `Q → 0⁺`, the Pauli
  projection of every `ε → 0⁺` limit of the signed class value `V · r` at the canonical pair
  tends to the complex number `β M₁ M₂ c₁ c₂ m_γ Λ D s`. The class values may depend on all the
  data; only their sum enters `SetCPauliAt`.

The set (c) limit is `(1/i) ∑_r Y_r` (`setCLim_eq_sum`) and the Pauli projection is linear
(`QED.ChainProof.HCValue.formFactorProj₂_sum`, `formFactorProj₂_const_smul`), so the per-class
limits add up.

## Main statements

* `formFactorProj₂_const_smul`: `P₂(c • V) = c P₂(V)`;
* **`setCPauliAt_of_all`**: the limit links and per-class Pauli limits of the 56 classes, with
  values `β r` summing to `i b`, give `SetCPauliAt P₀ b`;
* **`setCPauliAt_of_classes`**: the same with the 36 main and the 20 counterterm classes given
  separately (`(1/i)(∑ βᴹ + ∑ βᶜ) = b`).
-/

@[expose] public section

open Complex Matrix Filter Topology
open QED.WickModel (Params)

namespace QED.ChainProof.SetCPauli

open QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-- The type of a per-class Pauli value, a function of the set (c) data
`M₁ M₂ c₁ c₂ m_γ Λ D s`. -/
abbrev ClsPauliVal : Type := ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → RegCt → ℝ × ℝ × ℝ → ℂ

/-- **The canonical Pauli limit of one class** (open per class): at the set (c) data, as
`Q → 0⁺`, the Pauli projection of every `ε → 0⁺` limit of the class value `V · r` at the
canonical pair tends to `β M₁ M₂ c₁ c₂ m_γ Λ D s`. -/
def SetCClassPauli {ι : Type} (V : ClsFam ι) (P₀ : Params) (r : ι) (β : ClsPauliVal) :
    Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ η : ℝ, 0 < η → ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ Y,
      IsClassLimC V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r (boostMomentum P₀.m Q) (restMomentum P₀.m) Y →
      ‖QED.OneLoop.formFactorProj₂ P₀.e P₀.m (boostMomentum P₀.m Q) (restMomentum P₀.m) Y -
        β M₁ M₂ c₁ c₂ mγ Λ D s‖ < η

/-- **The Pauli projection is homogeneous**: `P₂(c • V) = c P₂(V)`. -/
theorem formFactorProj₂_const_smul (e m : ℝ) (p' p : Fin 4 → ℝ) (c : ℂ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    QED.OneLoop.formFactorProj₂ e m p' p (c • V) =
      c * QED.OneLoop.formFactorProj₂ e m p' p V := by
  have h : c • V = fun μ => c • V μ := rfl
  rw [h, QED.TwoLoop.PauliZeroLimit.formFactorProj₂_eq_pauliNum,
    QED.TwoLoop.PauliZeroLimit.formFactorProj₂_eq_pauliNum,
    QED.TwoLoop.PauliZeroLimit.pauliNum_smul, mul_div_assoc, mul_div_assoc]
  ring

variable {P₀ : Params}

/-- The per-class Pauli limits of the 56 classes, from those of the two groups. -/
theorem setCClassPauli_all {βM : MainIdx → ClsPauliVal} {βC : CtIdx → ClsPauliVal}
    (hPM : ∀ r, SetCClassPauli mainFam P₀ r (βM r))
    (hPC : ∀ r, SetCClassPauli ctFam P₀ r (βC r)) :
    ∀ r, SetCClassPauli allFam P₀ r (Sum.elim βM βC r)
  | .inl r => hPM r
  | .inr r => hPC r

/-- **`SetCPauliAt` from the per-class Pauli limits of the 56 classes**, given the limit links
(for the existence of the class limits at the canonical pairs) and class values whose sum, times
`1/i`, is the real number `b m_γ Λ M₁ M₂`. -/
theorem setCPauliAt_of_all {b : ℝ → ℝ → ℝ → ℝ → ℝ} {β : MainIdx ⊕ CtIdx → ClsPauliVal}
    (hm : 0 < P₀.m) (hM : ∀ r, SetCClassLim mainFam P₀ r) (hC : ∀ r, SetCClassLim ctFam P₀ r)
    (hP : ∀ r, SetCClassPauli allFam P₀ r (β r))
    (hsum : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (1 / I) * ∑ r, β r M₁ M₂ c₁ c₂ mγ Λ D s = ((b mγ Λ M₁ M₂ : ℝ) : ℂ)) :
    SetCPauliAt P₀ b := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA η hη
  set N : ℝ := (Fintype.card (MainIdx ⊕ CtIdx) : ℝ) + 1 with hNdef
  have hN : 0 < N := by positivity
  have hall : ∀ᶠ Q in 𝓝[>] (0 : ℝ), ∀ r, ∀ Y,
      IsClassLimC allFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s r (boostMomentum P₀.m Q)
        (restMomentum P₀.m) Y →
      ‖QED.OneLoop.formFactorProj₂ P₀.e P₀.m (boostMomentum P₀.m Q) (restMomentum P₀.m) Y -
        β r M₁ M₂ c₁ c₂ mγ Λ D s‖ < η / N :=
    eventually_all.mpr fun r => hP r M₁ M₂ c₁ c₂ mγ Λ D s hA (η / N) (by positivity)
  filter_upwards [hall, self_mem_nhdsWithin] with Q hQ (hQ0 : 0 < Q)
  intro V hV
  have hpq := QED.ChainProof.HCValue.isPairQ_canonical' hm hQ0
  choose Y hY using fun r => setCClassLim_all hM hC r M₁ M₂ c₁ c₂ mγ Λ D s hA _ _ hpq
  rw [setCLim_eq_sum hY hV, formFactorProj₂_const_smul, QED.ChainProof.HCValue.formFactorProj₂_sum,
    ← hsum M₁ M₂ c₁ c₂ mγ Λ D s hA, ← mul_sub, norm_mul, ← Finset.sum_sub_distrib]
  have h1I : ‖(1 / I : ℂ)‖ = 1 := by simp
  rw [h1I, one_mul]
  calc ‖∑ r, (QED.OneLoop.formFactorProj₂ P₀.e P₀.m (boostMomentum P₀.m Q) (restMomentum P₀.m)
          (Y r) - β r M₁ M₂ c₁ c₂ mγ Λ D s)‖
      ≤ ∑ r, ‖QED.OneLoop.formFactorProj₂ P₀.e P₀.m (boostMomentum P₀.m Q)
          (restMomentum P₀.m) (Y r) - β r M₁ M₂ c₁ c₂ mγ Λ D s‖ := norm_sum_le _ _
    _ ≤ ∑ _r : MainIdx ⊕ CtIdx, η / N := Finset.sum_le_sum fun r _ => (hQ r _ (hY r)).le
    _ = (Fintype.card (MainIdx ⊕ CtIdx) : ℝ) * (η / N) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ < N * (η / N) := by
        have : 0 < η / N := by positivity
        exact mul_lt_mul_of_pos_right (by rw [hNdef]; linarith) this
    _ = η := by field_simp

/-- **`SetCPauliAt` from the per-class Pauli limits**, the 36 main classes and the 20 counterterm
classes given separately: with the limit links and values `βᴹ`, `βᶜ` such that
`(1/i)(∑ βᴹ + ∑ βᶜ) = b`, the canonical Pauli limit of the set (c) limits is `b`. -/
theorem setCPauliAt_of_classes {b : ℝ → ℝ → ℝ → ℝ → ℝ} {βM : MainIdx → ClsPauliVal}
    {βC : CtIdx → ClsPauliVal} (hm : 0 < P₀.m) (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hC : ∀ r, SetCClassLim ctFam P₀ r) (hPM : ∀ r, SetCClassPauli mainFam P₀ r (βM r))
    (hPC : ∀ r, SetCClassPauli ctFam P₀ r (βC r))
    (hsum : ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
      (1 / I) * (∑ r, βM r M₁ M₂ c₁ c₂ mγ Λ D s + ∑ r, βC r M₁ M₂ c₁ c₂ mγ Λ D s) =
        ((b mγ Λ M₁ M₂ : ℝ) : ℂ)) :
    SetCPauliAt P₀ b :=
  setCPauliAt_of_all hm hM hC (setCClassPauli_all hPM hPC) fun M₁ M₂ c₁ c₂ mγ Λ D s hA => by
    rw [Fintype.sum_sum_type]
    exact hsum M₁ M₂ c₁ c₂ mγ Λ D s hA

end QED.ChainProof.SetCPauli

end
