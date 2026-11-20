/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdLimD

/-!
# (R-Π₄) step L6d3: the padded defects vanish in the limit

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The padded
defects of `VA` and `VC` are `iε` times a constant times a convergent four-propagator integral of
mass `Y`, so they vanish as `ε → 0⁺`:

* `faceId_trace_gamma00`, `faceId_tendsto_padFour`;
* `faceId_FP_VA_eq`, `faceId_FP_VC_eq`;
* **`faceId_tendsto_pad_VA`**, **`faceId_tendsto_pad_VC`**.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.Bridge

theorem faceId_trace_gamma00 : (Dirac.gamma 0 * Dirac.gamma 0).trace = 4 := by
  have h := congrArg Matrix.trace (QED.Dirac.gamma_anticomm 0 0)
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one] at h
  simp only [Minkowski.metric, Fintype.card_fin] at h
  push_cast at h
  linear_combination h / 2

/-- **`iε` times a four-propagator integral of masses `≥ m₀` vanishes.** -/
theorem faceId_tendsto_padFour {m₀ : ℝ} (hm₀ : 0 < m₀) {Y : ℝ} (hY : m₀ ≤ Y)
    (c0 c1 c2 c3 : Bool) {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * I * QED.OneLoop.energyFirstIntegral fun q =>
        (propDenom Y ε (zk k c0 q))⁻¹ * (propDenom Y ε (zk k c1 q))⁻¹ *
          (propDenom Y ε (zk k c2 q))⁻¹ * (propDenom Y ε (zk k c3 q))⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
  have hV := vpf_four hm₀ Y Y Y Y ⟨hY, hY, hY, hY⟩ c0 c1 c2 c3 (tRc 1)
    (fun p i j => isLoopPoly_tRc 1 p 0 i j) (tcovN_tRc 1)
    (fun q i j => isLoopPoly_tRc (n := 0) 1 0 q i j)
  have hk' : -(m₀ + m₀) ^ 2 < Minkowski.dot k k := by nlinarith
  have h := (faceId_tendsto_eps_vpf hV hk' 0 0).const_mul (4 : ℂ)⁻¹
  rw [mul_zero] at h
  refine h.congr fun ε => ?_
  simp only [tRc, QED.TwoLoop.LimitCovariance.traceT, faceId_trace_gamma00,
    ofReal_one, mul_one, QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  field_simp

theorem faceId_FP_VA_eq (ε : ℝ) (k : Fin 4 → ℝ) (C : ℂ) (Y : ℝ) :
    faceIdFP (faceIdRB baseVA ![1, 0]) cVA ε k (fun _ => C) Y = fun x =>
      C * ((propDenom Y ε (zk k false x))⁻¹ * (propDenom Y ε (zk k false x))⁻¹ *
        (propDenom Y ε (zk k true x))⁻¹ * (propDenom Y ε (zk k false x))⁻¹) := by
  funext x
  simp (config := {decide := true}) only [faceIdFP, Fin.prod_univ_four, faceIdRB,
    faceIdV, faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVA,
    ite_true, ite_false, decide_true, decide_false, faceId_G_false, faceId_W_true,
    faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, zero_smul, one_smul,
    zero_add, zk]

theorem faceId_FP_VC_eq (ε : ℝ) (k : Fin 4 → ℝ) (C : ℂ) (Y : ℝ) :
    faceIdFP (faceIdRB baseVC ![1, 0]) cVC ε k (fun _ => C) Y = fun x =>
      C * ((propDenom Y ε (zk k false x))⁻¹ * (propDenom Y ε (zk k true x))⁻¹ *
        (propDenom Y ε (zk k true x))⁻¹ * (propDenom Y ε (zk k false x))⁻¹) := by
  funext x
  simp (config := {decide := true}) only [faceIdFP, Fin.prod_univ_four, faceIdRB,
    faceIdV, faceId_c_castSucc, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, cVC,
    ite_true, ite_false, decide_true, decide_false, faceId_G_false, faceId_W_true,
    faceId_inv_propDenom_eq_G, Fin.isValue, mul_one, zero_smul, one_smul,
    zero_add, zk]

/-- **The padded defects of `VA` vanish in the limit.** -/
theorem faceId_tendsto_pad_VA {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ}
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => ∑ f, (Φ.coeff f : ℂ) * (ε * I * QED.OneLoop.energyFirstIntegral
        (faceIdFP (faceIdRB baseVA ![1, 0]) cVA ε k (fun _ =>
          ((blockX Φ m₀ : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) *
            (((blockX Φ m₀ + 1 : ℝ) : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) * vNumE4 e 0 1 aVA k μ ν)
          (blockX Φ m₀ + 1))))
      (𝓝[>] 0) (𝓝 0) := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g := Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hY : m₀ ≤ blockX Φ m₀ + 1 := by simp only [blockX]; linarith
  have h := tendsto_finsetSum Finset.univ fun f _ =>
    ((faceId_tendsto_padFour hm₀ hY false false true false hk).const_mul
      (((blockX Φ m₀ : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) *
        (((blockX Φ m₀ + 1 : ℝ) : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) * vNumE4 e 0 1 aVA k μ ν)).const_mul
      (Φ.coeff f : ℂ)
  simp only [mul_zero, Finset.sum_const_zero] at h
  refine h.congr fun ε => Finset.sum_congr rfl fun f _ => ?_
  simp only [faceId_FP_VA_eq, QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  ring

/-- **The padded defects of `VC` vanish in the limit.** -/
theorem faceId_tendsto_pad_VC {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ}
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => ∑ f, (Φ.coeff f : ℂ) * (ε * I * QED.OneLoop.energyFirstIntegral
        (faceIdFP (faceIdRB baseVC ![1, 0]) cVC ε k (fun _ =>
          ((blockX Φ m₀ : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) *
            (((blockX Φ m₀ + 1 : ℝ) : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) * vNumE4 e 0 1 aVC k μ ν)
          (blockX Φ m₀ + 1))))
      (𝓝[>] 0) (𝓝 0) := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g := Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hY : m₀ ≤ blockX Φ m₀ + 1 := by simp only [blockX]; linarith
  have h := tendsto_finsetSum Finset.univ fun f _ =>
    ((faceId_tendsto_padFour hm₀ hY false true true false hk).const_mul
      (((blockX Φ m₀ : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) *
        (((blockX Φ m₀ + 1 : ℝ) : ℂ) ^ 2 - (Φ.mass f : ℂ) ^ 2) * vNumE4 e 0 1 aVC k μ ν)).const_mul
      (Φ.coeff f : ℂ)
  simp only [mul_zero, Finset.sum_const_zero] at h
  refine h.congr fun ε => Finset.sum_congr rfl fun f _ => ?_
  simp only [faceId_FP_VC_eq, QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  ring

end QED.GradedProof.RPi4

end
