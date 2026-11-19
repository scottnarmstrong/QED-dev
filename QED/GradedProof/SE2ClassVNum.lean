/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ClassVAmp

/-!
# The class `V`: the numerator, even in the loop mass, and its bounds

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), step 2. For the vacuum-polarization graph `repV`:

* `v_amplitude_eq`: the amplitude (T₇) of loop flavour `f` is a constant times
  `(E₀ + M_f² E₂) D_f(u)⁻¹ D_f(v)⁻¹` times the inverse denominators of the open line and the two
  Pauli–Villars photon pairs; `E₀ = seE0`, `E₂ = seE2` do not depend on the flavour, because the
  loop trace is even in the loop mass (`QED.TwoLoop.Bridge.loopTrace_eq`).
* `refinedBound_seE0`, `refinedBound_seE2`, `isLoopPoly_seE0`, `isLoopPoly_seE2`: for any
  parametric data whose lines `e₀, e₁, e₂` carry the open-line momentum and the two bubble
  momenta, `E₀` is bounded by the line weights of `{e₀, e₁, e₂}` with exponent `3` and has degree
  at most `3`; `E₂` is bounded by `{e₀}` with exponent `1` and has degree at most `1`.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat)
open QED.Integration.TwoLoop (lineMomentum RefinedBound)
open Complex

/-- The trace `Tr[γ^σ (M - u̸) γ^τ (M - v̸)]` of the loop of mass `M`. -/
noncomputable def trSE (M : ℝ) (u v : Fin 4 → ℝ) (σ τ : Fin 4) : ℂ :=
  Matrix.trace (Dirac.gamma σ * electronNumerator M u * Dirac.gamma τ * electronNumerator M v)

theorem trSE_eq (M : ℝ) (u v : Fin 4 → ℝ) (σ τ : Fin 4) :
    trSE M u v σ τ =
      trSE 0 u v σ τ + ((M ^ 2 : ℝ) : ℂ) * (Dirac.gamma σ * Dirac.gamma τ).trace := by
  have h := loopTrace_eq M u (v - u) σ τ
  simp only [loopTrace, add_sub_cancel] at h
  exact h

/-- The outer factor: the open-line numerator chain and the two photon numerators. -/
noncomputable def outerSE (P : Params) (ko : Fin 4 → ℝ) (α β l0 l1 l2 l3 : Fin 4) : ℂ :=
  (Dirac.gamma l1 * electronNumerator P.m ko * Dirac.gamma l0) α β *
    ((Minkowski.metric l0 l2 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) *
    ((Minkowski.metric l1 l3 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)

/-- The flavour-independent part `E₀` of the numerator. -/
noncomputable def seE0 (P : Params) (α β : Fin 4) (ko u v : Fin 4 → ℝ) : ℂ :=
  ∑ l0 : Fin 4, ∑ l1 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4,
    outerSE P ko α β l0 l1 l2 l3 * trSE 0 u v l2 l3

/-- The coefficient `E₂` of `M_f²` in the numerator. -/
noncomputable def seE2 (P : Params) (α β : Fin 4) (ko : Fin 4 → ℝ) : ℂ :=
  ∑ l0 : Fin 4, ∑ l1 : Fin 4, ∑ l2 : Fin 4, ∑ l3 : Fin 4,
    outerSE P ko α β l0 l1 l2 l3 * (Dirac.gamma l2 * Dirac.gamma l3).trace

/-- **The amplitude of flavour `f` as numerator times denominators.** -/
theorem v_amplitude_eq (P : Params) (hε : P.ε ≠ 0) (f : Fin 3) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 0 → Fin 4 → ℝ) (k : Line repV → Fin 4 → ℝ) (α β : Fin 4) (μ : Fin 0 → Fin 4) :
    contractionAmplitude₂ P repV (flavSE f) pIn kIn k ![α] ![β] μ =
      (I * P.e) ^ 4 * (1 / I) ^ 5 *
        ((seE0 P α β (k (.inl vf1)) (k (.inl vf2)) (k (.inl vf3)) +
            ((P.mass f ^ 2 : ℝ) : ℂ) * seE2 P α β (k (.inl vf1))) *
          ((propDenom (P.mass f) P.ε (k (.inl vf2)))⁻¹ *
            (propDenom (P.mass f) P.ε (k (.inl vf3)))⁻¹)) *
        ((propDenom P.m P.ε (k (.inl vf1)))⁻¹ *
          ((propDenom P.mγ P.ε (k (.inr vg1)))⁻¹ * (propDenom P.Λ P.ε (k (.inr vg1)))⁻¹) *
          ((propDenom P.mγ P.ε (k (.inr vg2)))⁻¹ * (propDenom P.Λ P.ε (k (.inr vg2)))⁻¹)) := by
  rw [v_amplitude]
  have htr : ∀ l2 l3 : Fin 4, Matrix.trace (Dirac.gamma l2 *
      QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl vf2)) * Dirac.gamma l3 *
        QED.OneLoop.electronPropagator (P.mass f) P.ε (k (.inl vf3))) =
      ((propDenom (P.mass f) P.ε (k (.inl vf2)))⁻¹ *
        (propDenom (P.mass f) P.ε (k (.inl vf3)))⁻¹) *
        (trSE 0 (k (.inl vf2)) (k (.inl vf3)) l2 l3 +
          ((P.mass f ^ 2 : ℝ) : ℂ) * (Dirac.gamma l2 * Dirac.gamma l3).trace) := by
    intro l2 l3
    rw [← trSE_eq, trSE]
    simp only [QED.TwoLoop.Bridge.electronPropagator_eq_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul]
    ring
  have hout : ∀ l0 l1 : Fin 4,
      (Dirac.gamma l1 * QED.OneLoop.electronPropagator P.m P.ε (k (.inl vf1)) *
        Dirac.gamma l0) (![α] 0) (![β] 0) =
      (propDenom P.m P.ε (k (.inl vf1)))⁻¹ *
        (Dirac.gamma l1 * electronNumerator P.m (k (.inl vf1)) * Dirac.gamma l0) α β := by
    intro l0 l1
    simp only [QED.TwoLoop.Bridge.electronPropagator_eq_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
  simp only [htr, hout, photonPropagator_eq_mul _ _ hε, seE0, seE2, outerSE, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib, mul_add]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-! ### Bounds and degrees -/

section Bounds

variable {m : ℕ} (al : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ)

theorem refinedBoundMat_elec (e : Fin (m + 1)) (mass : ℝ) :
    RefinedBoundMat al {e} 1 fun ℓ => electronNumerator mass (lineMomentum al pp e ℓ) :=
  fun i j => QED.TwoLoop.ClassIntegrable.refinedBound_electronNumerator al pp e mass i j

theorem refinedBound_outerSE (P : Params) (e0 : Fin (m + 1)) (α β l0 l1 l2 l3 : Fin 4) :
    RefinedBound al {e0} 1 fun ℓ => outerSE P (lineMomentum al pp e0 ℓ) α β l0 l1 l2 l3 := by
  unfold outerSE
  have h := (((RefinedBoundMat.const (al := al) (Dirac.gamma l1)).mul
    (refinedBoundMat_elec al pp e0 P.m) (Finset.disjoint_empty_left _)).mul
      (RefinedBoundMat.const (Dirac.gamma l0)) (Finset.disjoint_empty_right _)) α β
  have h2 := (h.const_mul ((Minkowski.metric l0 l2 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)).const_mul
    ((Minkowski.metric l1 l3 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)
  simp only [Finset.empty_union, Finset.union_empty, zero_add, add_zero] at h2
  convert h2 using 2 with ℓ
  ring

/-- **The pointwise bound for `E₀`**: by the lines `e₀, e₁, e₂`, exponent `3`. -/
theorem refinedBound_seE0 (P : Params) (α β : Fin 4) {e0 e1 e2 : Fin (m + 1)}
    (h01 : e0 ≠ e1) (h02 : e0 ≠ e2) (h12 : e1 ≠ e2) :
    RefinedBound al {e0, e1, e2} 3 fun ℓ =>
      seE0 P α β (lineMomentum al pp e0 ℓ) (lineMomentum al pp e1 ℓ) (lineMomentum al pp e2 ℓ) := by
  unfold seE0
  refine RefinedBound.sum _ fun l0 _ => RefinedBound.sum _ fun l1 _ =>
    RefinedBound.sum _ fun l2 _ => RefinedBound.sum _ fun l3 _ => ?_
  have hT := ((((RefinedBoundMat.const (al := al) (Dirac.gamma l2)).mul
    (refinedBoundMat_elec al pp e1 0) (Finset.disjoint_empty_left _)).mul
      (RefinedBoundMat.const (Dirac.gamma l3)) (Finset.disjoint_empty_right _)).mul
        (refinedBoundMat_elec al pp e2 0) (by simpa using h12)).trace
  simp only [Finset.empty_union, Finset.union_empty, zero_add, add_zero] at hT
  have h := (refinedBound_outerSE al pp P e0 α β l0 l1 l2 l3).mul hT (by
    rw [Finset.disjoint_singleton_left]
    simp [h01, h02])
  refine h.mono ?_ (by norm_num)
  intro x hx
  simp only [Finset.mem_union, Finset.mem_singleton] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The pointwise bound for `E₂`: by the line `e₀`, exponent `1`. -/
theorem refinedBound_seE2 (P : Params) (α β : Fin 4) (e0 : Fin (m + 1)) :
    RefinedBound al {e0} 1 fun ℓ => seE2 P α β (lineMomentum al pp e0 ℓ) := by
  unfold seE2
  refine RefinedBound.sum _ fun l0 _ => RefinedBound.sum _ fun l1 _ =>
    RefinedBound.sum _ fun l2 _ => RefinedBound.sum _ fun l3 _ => ?_
  have h := (refinedBound_outerSE al pp P e0 α β l0 l1 l2 l3).mul
    (RefinedBound.const (α := al) ((Dirac.gamma l2 * Dirac.gamma l3).trace))
    (Finset.disjoint_empty_right _)
  simpa using h

theorem isLoopPoly_seE0 (P : Params) (α β : Fin 4) {ko u v : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ}
    (hko : IsLoopAffine ko) (hu : IsLoopAffine u) (hv : IsLoopAffine v) :
    IsLoopPoly 2 3 fun ℓ => seE0 P α β (ko ℓ) (u ℓ) (v ℓ) := by
  unfold seE0 outerSE trSE
  refine IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l1 _ =>
    IsLoopPoly.sum _ fun l2 _ => IsLoopPoly.sum _ fun l3 _ => ?_
  have hO := (((IsLoopPolyMat.const (L := 2) (Dirac.gamma l1)).mul
    (hko.isLoopPolyMat_electronNumerator P.m)).mul (IsLoopPolyMat.const (Dirac.gamma l0))) α β
  have hT := ((((IsLoopPolyMat.const (L := 2) (Dirac.gamma l2)).mul
    (hu.isLoopPolyMat_electronNumerator 0)).mul (IsLoopPolyMat.const (Dirac.gamma l3))).mul
      (hv.isLoopPolyMat_electronNumerator 0)).trace
  have h := ((hO.mul (IsLoopPoly.const (n := 0)
    (((Minkowski.metric l0 l2 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)))).mul
    (IsLoopPoly.const (n := 0) (((Minkowski.metric l1 l3 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)))).mul hT
  simpa using h

theorem isLoopPoly_seE2 (P : Params) (α β : Fin 4) {ko : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ}
    (hko : IsLoopAffine ko) : IsLoopPoly 2 1 fun ℓ => seE2 P α β (ko ℓ) := by
  unfold seE2 outerSE
  refine IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l1 _ =>
    IsLoopPoly.sum _ fun l2 _ => IsLoopPoly.sum _ fun l3 _ => ?_
  have hO := (((IsLoopPolyMat.const (L := 2) (Dirac.gamma l1)).mul
    (hko.isLoopPolyMat_electronNumerator P.m)).mul (IsLoopPolyMat.const (Dirac.gamma l0))) α β
  have h := ((hO.mul (IsLoopPoly.const (n := 0)
    (((Minkowski.metric l0 l2 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)))).mul
    (IsLoopPoly.const (n := 0) (((Minkowski.metric l1 l3 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)))).mul
    (IsLoopPoly.const (n := 0) ((Dirac.gamma l2 * Dirac.gamma l3).trace))
  simpa using h

end Bounds

end QED.GradedProof.SE2

end
