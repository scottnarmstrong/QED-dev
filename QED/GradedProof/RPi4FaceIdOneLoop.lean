/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdPadLim

/-!
# (R-Π₄) step L6d3: the one-loop limit behind the class-level face identity

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3.

* `faceId_dBlockD_eq_sum`, `faceId_fLim_eq_sum`: the weighted block is linear in the weight;
* `faceId_lam_const`: `λ · 3e² = (iπ²)⁻¹ · 3e²/(16π²)`;
* **`faceId_oneLoopLim`**: `FaceIdOneLoopLim e` for every `e`;
* **`faceId_faceClassGen`**: hence `FaceClassGen e`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology
open scoped Real
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

section Lin

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

theorem faceId_dBlockD_eq_sum (e : ℝ) (δ : F → ℝ) (ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    dBlockD Φ rep e δ ε k q μ ν =
      ∑ g, (δ g : ℂ) * dBlockD Φ rep e (Pi.single g 1) ε k q μ ν := by
  simp only [dBlockD, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_eq_single (rep f)]
  · simp only [Pi.single_eq_same]
    push_cast
    ring
  · intro g _ hg
    simp only [Pi.single_eq_of_ne (Ne.symm hg)]
    push_cast
    ring
  · simp

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
include hm₀ hmass hrep hPV₁ hPV₂

/-- **The limit of the weighted block is linear in the weight.** -/
theorem faceId_fLim_eq_sum {e : ℝ} (he : e ≠ 0) (δ : F → ℝ) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    fLim Φ rep e δ k μ ν = ∑ g, (δ g : ℂ) * fLim Φ rep e (Pi.single g 1) k μ ν := by
  have h := tendsto_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ (faceIdParams e) he δ hk μ ν
  have hs := tendsto_finsetSum Finset.univ fun g _ =>
    (tendsto_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ (faceIdParams e) he (Pi.single g 1) hk μ
      ν).const_mul (δ g : ℂ)
  refine tendsto_nhds_unique h (hs.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hi := fun g => ((vpf_dBlockD Φ rep hm₀ hmass hrep hPV₁ hPV₂ (faceIdParams e) he
    (Pi.single g 1)).2 ε hε k μ ν).const_mul (δ g : ℂ)
  simp only [← QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  rw [← faceId_efi_sum Finset.univ fun g _ => hi g]
  exact congrArg _ (funext fun q => (faceId_dBlockD_eq_sum Φ rep _ δ ε k q μ ν).symm)

end Lin

theorem faceId_lam_const (e : ℝ) :
    faceIdLam * (3 * (e : ℂ) ^ 2) = (I * (π : ℂ) ^ 2)⁻¹ * ((3 * e ^ 2 / (16 * π ^ 2) : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [faceIdLam, mul_inv, inv_I]
  push_cast
  field_simp
  ring

/-- **The one-loop limit behind the class-level face identity.** -/
theorem faceId_oneLoopLim (e : ℝ) : FaceIdOneLoopLim e := by
  intro F _ _ Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ c s hc hs₁ hs₂
  have hk : -(4 * m₀ ^ 2) < Minkowski.dot (tiltVec c s) (tiltVec c s) := by
    rw [dot_tiltVec hs₂.le]; linarith
  have hpad := (faceId_tendsto_pad_VA Φ hm₀ hmass e hk 2 3).add
    (faceId_tendsto_pad_VC Φ hm₀ hmass e hk 2 3)
  rw [add_zero] at hpad
  set L : ℂ := if e = 0 then 0 else fLim Φ rep e (fun _ => 3 * e ^ 2) (tiltVec c s) 2 3
  have hbub : Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun x =>
        fBubble (faceIdParams e) Φ (faceIdD₀ F) rep true true false ε (tiltVec c s) x 2 3 +
        fBubble (faceIdParams e) Φ (faceIdD₀ F) rep false false true ε (tiltVec c s) x 2 3 +
        2 * gBubble { faceIdParams e with ε := ε } Φ (faceIdD₀ F) rep (tiltVec c s) x 2 3)
      (𝓝[>] 0) (𝓝 L) := by
    by_cases he : e = 0
    · subst he
      simp only [L, ite_true, fBubble, gBubble, kF, faceIdParams, ofReal_zero, mul_zero,
        zero_mul, Finset.sum_const_zero, add_zero, zero_pow two_ne_zero, faceId_efi_zero]
      exact tendsto_const_nhds
    · simp only [L, he, ite_false]
      exact faceId_tendsto_bubbles Φ rep hm₀ hmass hrep hPV₁ hPV₂ he hk 2 3
  have hT := (hbub.const_mul faceIdLam).add hpad
  have hval : faceIdLam * L + 0 = (I * (π : ℂ) ^ 2)⁻¹ * (((3 * e ^ 2 / (16 * π ^ 2) : ℝ) : ℂ) *
      ∑ g, fLim Φ rep e (Pi.single g 1) (tiltVec c s) 2 3) := by
    by_cases he : e = 0
    · subst he
      simp only [L, ite_true, mul_zero, add_zero, zero_pow two_ne_zero, zero_div,
        ofReal_zero, zero_mul]
    · simp only [L, he, ite_false, add_zero]
      rw [faceId_fLim_eq_sum Φ rep hm₀ hmass hrep hPV₁ hPV₂ he _ hk 2 3, ← mul_assoc,
        ← faceId_lam_const, ← Finset.mul_sum]
      push_cast
      ring
  rw [← hval]
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (faceId_classPsi_eq Φ rep hm₀ hmass hrep hPV₁ hPV₂ e (tiltVec c s) hε).symm

/-- **`FaceClassGen e`** for every `e`. -/
theorem faceId_faceClassGen (e : ℝ) : FaceClassGen e :=
  faceId_faceClassGen_of_oneLoop (faceId_oneLoopLim e)

end QED.GradedProof.RPi4

end
