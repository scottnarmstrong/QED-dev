/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBDecayBub
public import QED.ChainProof.SetCLinkIntDMom
public import QED.TwoLoop.NestedVP
public import QED.TwoLoop.NestedVPFubiniBoundOuter
public import Mathlib.MeasureTheory.Integral.Pi
import QED.Integration.LoopBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (c), the bubble classes: decay lemmas in the two outer energies

Helper level for set (c), the bubble classes `QED.ChainProof.SetCLink.repB i`, at fixed
`ε > 0`: the analytic ingredients of the decay condition
`QED.ChainProof.SetCMainB.OuterDecay'` for the outer factor of the twelve orbits.

* `exists_uniform_bound`: a bound with a constant per index of a finite family gives one constant;
* `exists_norm_electronPropagator_cons_apply_le`, `exists_norm_photonPropagator_cons_le`: at
  fixed spatial momentum the electron propagator is bounded and the regulated photon propagator
  decays like `(1 + |E|)⁻⁴` in the energy `E`, uniformly in the indices;
* `mvReal_cons`: a line momentum of the outer loops at energies `t'` and spatial momenta `v'`
  is `(v₀ t'₀ + v₁ t'₁ + c, w)` with `c`, `w` independent of `t'`;
* **`integrable_shearBound`**: `(1 + |t₀|)⁻² (1 + |t₁ - t₀|)⁻²` is integrable on `ℝ²`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetCMainB

open QED.OneLoop QED.TwoLoop.NestedVPFubiniBound QED.TwoLoop.JointIntegralInvariance
open QED.ChainProof.SetCLink (mvReal)

/-- **One constant for a finite family of bounds.** -/
theorem exists_uniform_bound {ι X : Type*} [Fintype ι] {f : ι → X → ℝ} {g : X → ℝ}
    (hg : ∀ x, 0 ≤ g x) (h : ∀ j, ∃ C, ∀ x, f j x ≤ C * g x) :
    ∃ C, 0 ≤ C ∧ ∀ j x, f j x ≤ C * g x := by
  choose C hC using h
  refine ⟨∑ j, |C j|, by positivity, fun j x => (hC j x).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (hg x)
  exact Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

/-! ### Propagators at fixed spatial momentum -/

/-- **The electron propagator at fixed spatial momentum is bounded** in the energy. -/
theorem exists_norm_electronPropagator_cons_apply_le (m : ℝ) {ε : ℝ} (hε : 0 < ε)
    (w : Fin 3 → ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (a b : Fin 4) (E : ℝ),
      ‖electronPropagator m ε (Fin.cons E w) a b‖ ≤ C * 1 := by
  refine exists_uniform_bound (f := fun (j : Fin 4 × Fin 4) (E : ℝ) =>
      ‖electronPropagator m ε (Fin.cons E w) j.1 j.2‖) (fun _ => zero_le_one)
    (fun j => ?_) |>.imp fun C hC => ⟨hC.1, fun a b E => hC.2 (a, b) E⟩
  obtain ⟨C, hC⟩ := (decaysLike_electronPropagator m hε (fun E => (Fin.cons E w : Fin 4 → ℝ))
    le_rfl (norm_nonneg w) (fun t => by simp) (fun t i => by simp)
    (fun t => QED.Integration.norm_finCons_le t w)).apply j.1 j.2
  refine ⟨|C|, fun E => (hC E).trans ?_⟩
  have h1 : (1 + |E|) ^ (-(1 : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (one_le_one_add_abs E) (by norm_num)
  have h0 : 0 ≤ (1 + |E|) ^ (-(1 : ℤ)) := zpow_nonneg (one_add_abs_pos E).le _
  calc C * (1 + |E|) ^ (-(1 : ℤ)) ≤ |C| * (1 + |E|) ^ (-(1 : ℤ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) h0
    _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)

/-- **The regulated photon propagator at fixed spatial momentum** decays like `(1 + |E|)⁻⁴` in
the energy. -/
theorem exists_norm_photonPropagator_cons_le (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) (w : Fin 3 → ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (a b : Fin 4) (E : ℝ),
      ‖photonPropagator mγ Λ ε (Fin.cons E w) a b‖ ≤ C * ((1 + |E|) ^ 4)⁻¹ := by
  refine exists_uniform_bound (f := fun (j : Fin 4 × Fin 4) (E : ℝ) =>
      ‖photonPropagator mγ Λ ε (Fin.cons E w) j.1 j.2‖) (fun E => by positivity)
    (fun j => ?_) |>.imp fun C hC => ⟨hC.1, fun a b E => hC.2 (a, b) E⟩
  obtain ⟨C, hC⟩ := decaysLike_photonPropagator mγ Λ hε (fun E => (Fin.cons E w : Fin 4 → ℝ))
    (fun t => by simp) (fun t i => by simp) j.1 j.2
  refine ⟨C, fun E => (hC E).trans (le_of_eq ?_)⟩
  rw [zpow_neg]
  norm_cast

/-! ### Line momenta of the outer loops -/

/-- **A line momentum of the outer loops** at energies `t'` and spatial momenta `v'`: its energy
is `v₀ t'₀ + v₁ t'₁ + c` and its spatial part is independent of `t'`. -/
theorem mvReal_cons (t' : Fin 2 → ℝ) (v' : Fin 2 → Fin 3 → ℝ) (p q : Fin 4 → ℝ)
    (v : Fin 4 → ℤ) :
    mvReal (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) p q v =
      Fin.cons ((v 0 : ℝ) * t' 0 + (v 1 : ℝ) * t' 1 + ((v 2 : ℝ) * p 0 + (v 3 : ℝ) * q 0))
        (Fin.tail (mvReal (fun s => (Fin.cons 0 (v' s) : Fin 4 → ℝ)) p q v)) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [mvReal]
    ring
  · simp [mvReal, Fin.tail]

/-! ### Integrability in the two outer energies -/

/-- The bound `(1 + |t₀|)⁻² (1 + |t₁ - t₀|)⁻²` on `ℝ²`. -/
noncomputable def shearBound (t : Fin 2 → ℝ) : ℝ :=
  ((1 + |t 0|) ^ 2)⁻¹ * ((1 + |t 1 - t 0|) ^ 2)⁻¹

theorem shearBound_nonneg (t : Fin 2 → ℝ) : 0 ≤ shearBound t := by
  unfold shearBound; positivity

theorem integrable_inv_one_add_abs_sq : Integrable (fun t : ℝ => ((1 + |t|) ^ 2)⁻¹) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := (2 : ℕ)) (by simp)
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- The shear `(t₀, t₁) ↦ (t₀, t₁ - t₀)`. -/
def shearM2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; -1, 1]

/-- **`(1 + |t₀|)⁻² (1 + |t₁ - t₀|)⁻²` is integrable on `ℝ²`**, by the unimodular shear. -/
theorem integrable_shearBound : Integrable shearBound := by
  have hH : Integrable (fun t : Fin 2 → ℝ => ∏ i, ((1 + |t i|) ^ 2)⁻¹) :=
    Integrable.fintype_prod (μ := fun _ => volume) (f := fun _ t => ((1 + |t|) ^ 2)⁻¹)
      fun _ => integrable_inv_one_add_abs_sq
  have hdet : |LinearMap.det (matrixAct ℝ shearM2)| = 1 := by
    rw [det_matrixAct_real]
    simp [shearM2, Matrix.det_fin_two]
  obtain ⟨hmp, hemb⟩ := QED.TwoLoop.NestedVP.measurePreserving_linear_add volume
    (matrixAct ℝ shearM2) hdet 0
  have := (hmp.integrable_comp_emb hemb).mpr hH
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp [Fin.prod_univ_two, matrixAct_apply, Fin.sum_univ_two, shearM2, shearBound]
  ring_nf

end QED.ChainProof.SetCMainB

end
