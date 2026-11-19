/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideBDOuter

/-!
# Decay and continuity of the outer factors of the bubble–`δ₃` classes

Along `k = (t, w)` at fixed `ε > 0`, the entries of `bdOuter` and `dbOuter` are continuous in `t`
and decay like `(1 + |t|)⁻¹⁰` (in fact `(1 + |t|)⁻¹²`: the open-line chain `2`, the photon
propagator `4`, the `δ₃` insertion `Δ V Δ` `4 + 4 - 2`). These are the hypotheses of
`QED.ChainProof.HCSide.jointEnergyFirstIntegral_nestedF`.
-/

@[expose] public section

open Complex Matrix

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.NestedVPFubiniBound (DecaysLike decaysLike_photonPropagator
  decaysLike_outerChain continuous_photonPropagator continuous_electronPropagator)

/-- The `δ₃` vertex `-(i/2) δ₃ (k² g - k k)` grows like `(1 + |t|)²` along `k = (t, w)`. -/
theorem decaysLike_photonCtFactor (δ₃ : ℝ) (w : Fin 3 → ℝ) (a b : Fin 4) :
    DecaysLike (fun t => photonCtFactor δ₃ (Fin.cons t w) a b) (-2) := by
  refine ⟨|δ₃| * 5 * (1 + ‖w‖) ^ 2, fun t => ?_⟩
  set k : Fin 4 → ℝ := Fin.cons t w
  have hk : ‖k‖ ≤ (1 + |t|) * (1 + ‖w‖) :=
    (QED.Integration.norm_finCons_le t w).trans
      (by nlinarith [abs_nonneg t, norm_nonneg w])
  have hd : |Minkowski.dot k k| ≤ 4 * (‖k‖ * ‖k‖) :=
    QED.WickModel.VacuumPolarizationLimit.abs_dot_le k k
  have hg : |Minkowski.metric a b| ≤ 1 := by
    unfold Minkowski.metric
    split_ifs <;> norm_num
  have ha : |k a| ≤ ‖k‖ := by simpa using norm_le_pi_norm k a
  have hb : |k b| ≤ ‖k‖ := by simpa using norm_le_pi_norm k b
  have hX : |Minkowski.dot k k * Minkowski.metric a b - k a * k b| ≤ 5 * ‖k‖ ^ 2 := by
    calc |Minkowski.dot k k * Minkowski.metric a b - k a * k b|
        ≤ |Minkowski.dot k k| * |Minkowski.metric a b| + |k a| * |k b| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ 4 * (‖k‖ * ‖k‖) * 1 + ‖k‖ * ‖k‖ := by
          gcongr
      _ = 5 * ‖k‖ ^ 2 := by ring
  have hn : ‖photonCtFactor δ₃ k a b‖ =
      1 / 2 * (|δ₃| * |Minkowski.dot k k * Minkowski.metric a b - k a * k b|) := by
    rw [photonCtFactor, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    simp
  have hk2 : ‖k‖ ^ 2 ≤ ((1 + |t|) * (1 + ‖w‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hk 2
  simp only [neg_neg]
  rw [hn, zpow_two]
  have h0 : 0 ≤ |δ₃| := abs_nonneg _
  calc 1 / 2 * (|δ₃| * |Minkowski.dot k k * Minkowski.metric a b - k a * k b|)
      ≤ 1 / 2 * (|δ₃| * (5 * ‖k‖ ^ 2)) := by gcongr
    _ ≤ |δ₃| * 5 * ‖k‖ ^ 2 := by nlinarith [sq_nonneg ‖k‖]
    _ ≤ |δ₃| * 5 * ((1 + |t|) * (1 + ‖w‖)) ^ 2 := by gcongr
    _ = |δ₃| * 5 * (1 + ‖w‖) ^ 2 * ((1 + |t|) * (1 + |t|)) := by ring

theorem continuous_photonCtFactor (δ₃ : ℝ) {q : ℝ → Fin 4 → ℝ} (hq : Continuous q) (a b : Fin 4) :
    Continuous fun t => photonCtFactor δ₃ (q t) a b := by
  unfold photonCtFactor
  refine continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul
    (((QED.OneLoop.VertexLimit.continuous_dot_comp hq hq).mul continuous_const).sub
      (((continuous_apply a).comp hq).mul ((continuous_apply b).comp hq)))))

/-- The `δ₃` insertion `Δ V Δ` decays like `(1 + |t|)⁻⁶` along `k = (t, w)`. -/
theorem decaysLike_photonInsertion (δ₃ mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) (w : Fin 3 → ℝ)
    (ν ρ : Fin 4) :
    DecaysLike (fun t => photonInsertion δ₃ mγ Λ ε (Fin.cons t w) ν ρ) 6 := by
  have hk := decaysLike_photonPropagator mγ Λ hε (fun t => (Fin.cons t w : Fin 4 → ℝ))
    (fun t => by simp) (fun t i => by simp)
  have h := (DecaysLike.const (1 / I)).mul (DecaysLike.sum Finset.univ fun a _ =>
    DecaysLike.sum Finset.univ fun b _ =>
      ((hk ν a).mul (decaysLike_photonCtFactor δ₃ w a b)).mul (hk ρ b))
  exact h.congr fun t => rfl

theorem continuous_photonInsertion (δ₃ mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) {q : ℝ → Fin 4 → ℝ}
    (hq : Continuous q) (ν ρ : Fin 4) :
    Continuous fun t => photonInsertion δ₃ mγ Λ ε (q t) ν ρ := by
  unfold photonInsertion
  exact continuous_const.mul (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    ((continuous_photonPropagator mγ Λ hε hq ν a).mul (continuous_photonCtFactor δ₃ hq a b)).mul
      (continuous_photonPropagator mγ Λ hε hq ρ b))

theorem continuous_outerChain (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) (w : Fin 3 → ℝ)
    (μ l0 l2 α β : Fin 4) :
    Continuous fun t => QED.TwoLoop.NestedVP.outerChain P p kext (Fin.cons t w) μ l0 l2 α β := by
  have hk : Continuous fun t : ℝ => (Fin.cons t w : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_id continuous_const
  refine (continuous_apply β).comp ((continuous_apply α).comp ?_)
  exact ((((continuous_const.matrix_mul (continuous_electronPropagator P.m hε
    (continuous_const.sub hk))).matrix_mul continuous_const).matrix_mul
      (continuous_electronPropagator P.m hε (continuous_const.sub hk))).matrix_mul
        continuous_const)

theorem decaysLike_bdOuter (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) (α β μ : Fin 4)
    (w : Fin 3 → ℝ) (ρ σ : Fin 4) :
    DecaysLike (fun t => bdOuter P p kext α β μ (Fin.cons t w) ρ σ) 10 := by
  have hk := decaysLike_photonPropagator P.mγ P.Λ hε (fun t => (Fin.cons t w : Fin 4 → ℝ))
    (fun t => by simp) (fun t i => by simp)
  have h := (DecaysLike.const (-(((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 3 * (1 / I) ^ 4)).mul
    (DecaysLike.sum Finset.univ fun l0 _ => DecaysLike.sum Finset.univ fun l2 _ =>
      (((decaysLike_outerChain P hε p kext w μ l0 l2).apply α β).mul
        (decaysLike_photonInsertion P.δ₃ P.mγ P.Λ hε w ρ l0)).mul (hk l2 σ))
  exact (h.congr fun t => rfl).mono (by norm_num)

theorem decaysLike_dbOuter (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) (α β μ : Fin 4)
    (w : Fin 3 → ℝ) (ρ σ : Fin 4) :
    DecaysLike (fun t => dbOuter P p kext α β μ (Fin.cons t w) ρ σ) 10 := by
  have hk := decaysLike_photonPropagator P.mγ P.Λ hε (fun t => (Fin.cons t w : Fin 4 → ℝ))
    (fun t => by simp) (fun t i => by simp)
  have h := (DecaysLike.const (-(((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 3 * (1 / I) ^ 4)).mul
    (DecaysLike.sum Finset.univ fun l0 _ => DecaysLike.sum Finset.univ fun l2 _ =>
      (((decaysLike_outerChain P hε p kext w μ l0 l2).apply α β).mul (hk l0 ρ)).mul
        (decaysLike_photonInsertion P.δ₃ P.mγ P.Λ hε w l2 σ))
  exact (h.congr fun t => rfl).mono (by norm_num)

theorem continuous_bdOuter (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) (α β μ : Fin 4)
    (w : Fin 3 → ℝ) (ρ σ : Fin 4) :
    Continuous fun t => bdOuter P p kext α β μ (Fin.cons t w) ρ σ := by
  have hk : Continuous fun t : ℝ => (Fin.cons t w : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_id continuous_const
  unfold bdOuter
  exact continuous_const.mul (continuous_finsetSum _ fun l0 _ => continuous_finsetSum _ fun l2 _ =>
    ((continuous_outerChain P hε p kext w μ l0 l2 α β).mul
      (continuous_photonInsertion P.δ₃ P.mγ P.Λ hε hk ρ l0)).mul
        (continuous_photonPropagator P.mγ P.Λ hε hk l2 σ))

theorem continuous_dbOuter (P : Params) (hε : 0 < P.ε) (p kext : Fin 4 → ℝ) (α β μ : Fin 4)
    (w : Fin 3 → ℝ) (ρ σ : Fin 4) :
    Continuous fun t => dbOuter P p kext α β μ (Fin.cons t w) ρ σ := by
  have hk : Continuous fun t : ℝ => (Fin.cons t w : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_id continuous_const
  unfold dbOuter
  exact continuous_const.mul (continuous_finsetSum _ fun l0 _ => continuous_finsetSum _ fun l2 _ =>
    ((continuous_outerChain P hε p kext w μ l0 l2 α β).mul
      (continuous_photonPropagator P.mγ P.Λ hε hk l0 ρ)).mul
        (continuous_photonInsertion P.δ₃ P.mγ P.Λ hε hk l2 σ))

end QED.ChainProof.HCSide

end
