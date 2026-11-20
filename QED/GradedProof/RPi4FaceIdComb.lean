/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdIdent
public import QED.GradedProof.RPi4PairF

/-!
# (R-Π₄) step L6d3: the three classes as the one-loop classes `F0`, `F1`, `G0`, `G1`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. With the
counterterms `faceIdD₀` (`d₁ = d₂ = 1`, `d_m = 4`), the flavour sum of the face integrands of the
three classes is `λ (F0 + F1 + 2 G)`, `λ = -i (2π)⁻⁴`:

* `faceIdParams`, `faceIdD₀`, `faceIdLam`, `faceId_kV_lam`;
* `faceId_insG_smul`: the inserted bubble is linear in `(δ₂, δ_m)`;
* **`faceId_faces_eq_bubbles`**.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

/-- Parameters with charge `e` (the other fields are not used by the one-loop classes). -/
def faceIdParams (e : ℝ) : Params :=
  { e := e, δ₁ := 0, δ₂ := 0, δm := 0, δ₃ := 0, m := 1, mγ := 0, Λ := 1, ε := 0, M₁ := 2,
    M₂ := 3, c₁ := 0, c₂ := 0 }

/-- The counterterms `d₁ = d₂ = 1`, `d_m = 4` of the self-energy insertion `-(ℓ̸ + 4M)`. -/
def faceIdD₀ (F : Type) : Counterterms F :=
  ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 4, fun _ => 0⟩

/-- The constant `λ = -i (2π)⁻⁴`. -/
noncomputable def faceIdLam : ℂ := -I * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹

theorem faceId_kV_lam (e : ℝ) : faceIdKV e 0 1 = -(faceIdLam * kF e * (e : ℂ) ^ 2) := by
  have hI : (1 / I) = -I := by rw [one_div, inv_I]
  simp only [faceIdKV, faceIdLam, kF, hI]
  push_cast
  ring_nf
  rw [show I ^ 9 = -I ^ 7 by rw [show (9 : ℕ) = 7 + 2 from rfl, pow_add, I_sq]; ring]
  ring

theorem faceId_insG_smul (A B : Matrix (Fin 4) (Fin 4) ℂ) (a d₂ dm M ε : ℝ)
    (x y : Fin 4 → ℝ) :
    insG A B (a * d₂) (a * dm) M ε x y = (a : ℂ) * insG A B d₂ dm M ε x y := by
  simp only [insG, insTr, QED.TwoLoop.Insertion.fermionCtMatrix]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  push_cast
  ring

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

omit [DecidableEq F] in
/-- **The faces of the three classes are the one-loop classes** `λ (F0 + F1 + 2 G)` at the
counterterms `faceIdD₀` (pointwise, the loop-`0` face of `VB` translated by `k`). -/
theorem faceId_faces_eq_bubbles (e ε : ℝ) (k x : Fin 4 → ℝ) (μ ν : Fin 4) :
    (∑ f, (Φ.coeff f : ℂ) *
        (vNum e 0 1 aVA baseVA cVA (Φ.mass f) k ![x, (1 / 2 : ℝ) • (x + (0 : ℝ) • k)] μ ν *
          ∏ l, faceIdG (faceIdRB baseVA ![1, 0] l) (faceIdV cVA ε k x l)
            ((Φ.mass f : ℂ) ^ 2))) +
      (∑ f, (Φ.coeff f : ℂ) *
        (vNum e 0 1 aVC baseVC cVC (Φ.mass f) k ![x, (1 / 2 : ℝ) • (x + (1 : ℝ) • k)] μ ν *
          ∏ l, faceIdG (faceIdRB baseVC ![1, 0] l) (faceIdV cVC ε k x l)
            ((Φ.mass f : ℂ) ^ 2))) +
      (∑ f, (Φ.coeff f : ℂ) *
        ((faceIdKV e 0 1 * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 (zk k false x) (zk k true x) +
            (Φ.mass f : ℂ) ^ 2 * (faceIdKV e 0 1 * (Dirac.gamma μ * Dirac.gamma ν).trace)) *
          ∏ l, faceIdG (faceIdRB baseVB ![1, 0] l) (faceIdV cVB ε k x l)
            ((Φ.mass f : ℂ) ^ 2))) +
      (∑ f, (Φ.coeff f : ℂ) *
        ((faceIdKV e 0 1 * bubTr (Dirac.gamma μ) (Dirac.gamma ν) 0 (zk (-k) true (x + k))
            (zk k false (x + k)) +
            (Φ.mass f : ℂ) ^ 2 * (faceIdKV e 0 1 * (Dirac.gamma μ * Dirac.gamma ν).trace)) *
          ∏ l, faceIdG (faceIdRB baseVB ![0, 1] l) (faceIdV cVB ε k (x + k) l)
            ((Φ.mass f : ℂ) ^ 2))) =
    faceIdLam * (fBubble (faceIdParams e) Φ (faceIdD₀ F) rep true true false ε k x μ ν +
      fBubble (faceIdParams e) Φ (faceIdD₀ F) rep false false true ε k x μ ν +
      2 * gBubble { faceIdParams e with ε := ε } Φ (faceIdD₀ F) rep k x μ ν) := by
  simp only [faceId_HA_eq, faceId_HC_eq, faceId_HB1_eq, faceId_HB0_eq]
  simp only [fBubble, gBubble, faceIdD₀, faceIdParams, faceId_insG_smul, faceId_kV_lam,
    Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hT := kF_bubTr_F1 e (Φ.mass f) ε k x μ ν
  push_cast
  linear_combination (-2 * (Φ.coeff f : ℂ) * faceIdLam * (e : ℂ) ^ 2) * hT

end QED.GradedProof.RPi4

end
