/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.TwoPointClassification
public import QED.WickModel.VacuumPolarizationLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The vacuum polarization: well-definedness and transverse form

The proof of the packet-6b theorem goal (Z₂) (decision D-25) for the two-photon 1PI function of
the general Wick model at order `e²`, with the Pauli–Villars flavors of decision D-22.

* Integrability. Every one-loop 1PI contraction of the two-photon function at order `≤ 2` is a
  vacuum polarization loop of two gauge vertices
  (`QED.WickModel.TwoPointClassificationPolarization`);
  its regulated amplitude is `-(2π)⁴` times `vacuumPolarizationIntegrand` at `ℓ` or at `ℓ - k`
  (`IsPolarizationLoop.regulatedAmplitude_eq`). For `ε > 0` the integrand is integrable in both
  stages of M1, for every `k`, under the Pauli–Villars conditions
  (`QED.WickModel.VacuumPolarizationLimit`); the translation `ℓ ↦ ℓ - k` preserves both.
* Existence.
  `(1/i) [i Π^{μν}_ε(k)] = -δ₃ (k² g^{μν} - k^μ k^ν) + (1/i) ∫ vacuumPolarizationIntegrand`
  (`onePIFunction_vacuumPolarization`), and the energy-first integral converges below threshold to
  `i Π_loop(k²) (k² g^{μν} - k^μ k^ν)` (`tendsto_energyFirstIntegral_vacuumPolarizationIntegrand`).
  So `Π(s) = -δ₃ + (e² / 2π²) ∫₀¹ x (1 - x) ∑_f c_f log (M_f² + x (1 - x) s) dx`.
* Uniqueness. For each `s > -4m²` the photon momentum `k = ((1 - s)/2, (1 + s)/2, 0, 0)` has
  `k² = s`, and `k² g^{22} - k² k² = s`, `k² g^{00} - k⁰ k⁰ = -(1 + s)²/4`, not both zero.

## Main statements

* `QED.WickModel.vacuumPolarization_existsUnique_of_twoPoint`: the statement of (Z₂).
-/

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.WickModel

namespace IsPolarizationLoop

variable {C : Contraction 0 2 gauge2} {a b : Fin 2}

/-- **The regulated amplitude of a vacuum polarization loop** is `-(2π)⁴` times the vacuum
polarization integrand of (62.12), at `ℓ` when `A(z₁)` is at vertex `0` and at `ℓ - k`
otherwise. -/
theorem regulatedAmplitude_eq (P : Params) (hC : IsPolarizationLoop C a b)
    (pOut pIn : Fin 0 → Fin 4 → ℝ) (αOut βIn : Fin 0 → Fin 4) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    (ℓ : Fin 4 → ℝ) :
    regulatedAmplitude P C pOut pIn ![k, -k] ℓ αOut βIn ![μ, ν] =
      -(((2 * Real.pi) ^ 4 : ℝ) : ℂ) *
        vacuumPolarizationIntegrand P P.ε k (if a = 0 then ℓ else ℓ - k) μ ν := by
  have hreg : regulatedAmplitude P C pOut pIn ![k, -k] ℓ αOut βIn ![μ, ν] =
      ∑ f : Fin 3, (P.loopCoeff f : ℂ) *
        contractionAmplitude P C (constFlavoring f) pOut pIn ![k, -k] ℓ αOut βIn ![μ, ν] := by
    classical
    rw [regulatedAmplitude, hC.sum_preserves]
    simp only [hC.loopWeight_constFlavoring]
  have h2π : (((2 * Real.pi) ^ 4 : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (pow_ne_zero 4 (by positivity))
  rw [hreg]
  simp only [hC.contractionAmplitude_eq]
  have hab := hC.ne
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
  · rw [vacuumPolarizationIntegrand]
    simp only [ite_true, one_ne_zero, ite_false, Matrix.cons_val_zero, Matrix.cons_val_one,
      add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [trace_mul_mul_mul_rotate (QED.OneLoop.electronPropagator _ _ (ℓ + k)), add_comm ℓ k]
    field_simp
  · rw [vacuumPolarizationIntegrand]
    simp only [ite_true, one_ne_zero, ite_false, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [sub_add_cancel, trace_mul_mul_mul_rotate (Dirac.gamma ν), neg_add_eq_sub]
    field_simp

end IsPolarizationLoop

namespace VacuumPolarizationLimit

/-- `(t, v⃗) - k = (t - k⁰, v⃗ - k⃗)`. -/
theorem cons_sub_eq (t : ℝ) (v : Fin 3 → ℝ) (k : Fin 4 → ℝ) :
    (Fin.cons t v : Fin 4 → ℝ) - k = Fin.cons (t - k 0) (v - Fin.tail k) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

/-- **Integrability in both stages of M1** of the regulated amplitude of a vacuum polarization
loop, for `ε > 0` and every `k`, under the Pauli–Villars conditions. -/
theorem integrable_regulatedAmplitude_of_isPolarizationLoop {P : Params} (hm : 0 < P.m)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {ε : ℝ} (hε : 0 < ε)
    {C : Contraction 0 2 gauge2} {a b : Fin 2} (hC : IsPolarizationLoop C a b) (k : Fin 4 → ℝ)
    (μ ν : Fin 4) :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
      regulatedAmplitude { P with ε := ε } C ![] ![] ![k, -k] (Fin.cons t v) ![] ![] ![μ, ν]) ∧
    Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
      regulatedAmplitude { P with ε := ε } C ![] ![] ![k, -k] (Fin.cons t v) ![] ![] ![μ, ν] := by
  set P' : Params := { P with ε := ε }
  have hI : ∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
      vacuumPolarizationIntegrand P' ε k (Fin.cons t v) μ ν :=
    integrable_vacuumPolarizationIntegrand_time hε P' k μ ν
  have hJ : Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
      vacuumPolarizationIntegrand P' ε k (Fin.cons t v) μ ν :=
    integrable_integral_vacuumPolarizationIntegrand (P := P') hm hM₁ hM₂ hPV₁ hPV₂ hε k μ ν
  have hreg := fun ℓ => hC.regulatedAmplitude_eq P' ![] ![] ![] ![] k μ ν ℓ
  have hε' : P'.ε = ε := rfl
  simp only [hε'] at hreg
  by_cases ha : a = 0
  · simp only [hreg, ha, ite_true]
    refine ⟨fun v => (hI v).const_mul _, ?_⟩
    simp_rw [integral_const_mul]
    exact hJ.const_mul _
  · simp only [hreg, ha, ite_false, cons_sub_eq]
    refine ⟨fun v => ((hI (v - Fin.tail k)).comp_sub_right (k 0)).const_mul _, ?_⟩
    have hrw : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, -(((2 * Real.pi) ^ 4 : ℝ) : ℂ) *
        vacuumPolarizationIntegrand P' ε k (Fin.cons (t - k 0) (v - Fin.tail k)) μ ν
        = -(((2 * Real.pi) ^ 4 : ℝ) : ℂ) *
          ∫ t : ℝ, vacuumPolarizationIntegrand P' ε k (Fin.cons t (v - Fin.tail k)) μ ν := by
      intro v
      rw [integral_const_mul, integral_sub_right_eq_self
        (fun t : ℝ => vacuumPolarizationIntegrand P' ε k (Fin.cons t (v - Fin.tail k)) μ ν) (k 0)]
    simp_rw [hrw]
    exact (hJ.comp_sub_right (Fin.tail k)).const_mul _

/-- Every vertex has order at least `1`. -/
theorem one_le_order (κ : Wick.VertexKind) : 1 ≤ κ.order := by
  cases κ <;> simp [Wick.VertexKind.order]

/-- A vertex sequence of total order at most `2` has at most two vertices. -/
theorem le_two_of_sum_order_le {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (h : ∑ t, (κ t).order ≤ 2) : N ≤ 2 := by
  have : N ≤ ∑ t, (κ t).order := by
    calc N = ∑ _t : Fin N, 1 := by simp
      _ ≤ ∑ t, (κ t).order := Finset.sum_le_sum fun t _ => one_le_order (κ t)
  omega

end VacuumPolarizationLimit

/-- **The packet-6b theorem goal (Z₂): the vacuum polarization, well-definedness and transverse
form** (decision D-25). For `m > 0`, regulator fermions heavier than the electron and the
Pauli–Villars conditions `1 + c₁ + c₂ = 0`, `m² + c₁ M₁² + c₂ M₂² = 0` (decision D-22): first,
for every `ε > 0` the regulated loop integrand of every one-loop 1PI contraction of the
two-photon function at order `e²` is integrable in both stages of M1. Second, there is a unique
`Π` on `s > -4m²` such that `(1/i) [i Π^{μν}_ε(k)] → Π(k²) (k² g^{μν} - k^μ k^ν)` as `ε → 0⁺`.
It is `Π(s) = -δ₃ + vacuumPolarizationLoop P s`. -/
theorem vacuumPolarization_existsUnique_of_twoPoint (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ 2 →
      ∀ C : Contraction 0 2 κ, IsOnePI C → (∃ f : Line C, IsLoopLine f) →
      ∀ (k : Fin 4 → ℝ) (μ ν : Fin 4),
        (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
          regulatedAmplitude { P with ε := ε } C ![] ![] ![k, -k] (Fin.cons t v) ![] ![] ![μ, ν]) ∧
        Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
          regulatedAmplitude { P with ε := ε } C ![] ![] ![k, -k] (Fin.cons t v) ![] ![] ![μ, ν]) ∧
    ∃! Pol : {s : ℝ // -(4 * P.m ^ 2) < s} → ℂ,
      ∀ (k : Fin 4 → ℝ) (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
        Tendsto (fun ε : ℝ => (1 / I) *
            onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν])
          (𝓝[>] 0)
          (𝓝 (Pol ⟨_, hk⟩ *
            ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))) := by
  refine ⟨fun ε hε N κ hκ C hC hloop k μ ν => ?_, ?_⟩
  · obtain rfl | rfl | rfl : N = 0 ∨ N = 1 ∨ N = 2 := by
      have := VacuumPolarizationLimit.le_two_of_sum_order_le hκ
      omega
    · exact absurd hC (not_isOnePI_of_fin_zero_right C)
    · obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = oneVertex k₀ := ⟨κ 0, eq_oneVertex κ⟩
      by_cases hk₀ : k₀ = .photonCt
      · subst hk₀
        obtain ⟨f, -⟩ := hloop
        rcases (isOnePI_iff_polarizationTree C).1 hC with rfl | rfl <;> exact isEmptyElim f
      · exact absurd hC (not_isOnePI_oneVertex_polarization hk₀ C)
    · obtain rfl := eq_gauge2_of_sum_order_le hκ
      obtain ⟨a, b, h⟩ := hC.exists_isPolarizationLoop
      exact VacuumPolarizationLimit.integrable_regulatedAmplitude_of_isPolarizationLoop hm hM₁ hM₂
        hPV₁ hPV₂ hε h k μ ν
  -- existence
  have hPol : ∀ (k : Fin 4 → ℝ) (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
      Tendsto (fun ε : ℝ => (1 / I) *
          onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν])
        (𝓝[>] 0)
        (𝓝 ((-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (Minkowski.dot k k) : ℂ)) *
          ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))) := by
    intro k hk μ ν
    have hlim := tendsto_energyFirstIntegral_vacuumPolarizationIntegrand hm hM₁ hM₂ hPV₁ hPV₂ hk
      μ ν
    have h2 := (hlim.const_add (-I * ((P.δ₃ * (Minkowski.dot k k * Minkowski.metric μ ν
      - k μ * k ν) : ℝ) : ℂ))).const_mul (1 / I)
    have hval : (1 / I) * (-I * ((P.δ₃ * (Minkowski.dot k k * Minkowski.metric μ ν
          - k μ * k ν) : ℝ) : ℂ) + I * (vacuumPolarizationLoop P (Minkowski.dot k k) : ℂ)
            * ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))
        = (-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (Minkowski.dot k k) : ℂ)) *
          ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ) := by
      field_simp
      push_cast
      ring
    rw [hval] at h2
    refine h2.congr fun ε => ?_
    rw [onePIFunction_vacuumPolarization]
    rfl
  refine ⟨fun s => -(P.δ₃ : ℂ) + (vacuumPolarizationLoop P s.1 : ℂ), hPol, fun Pol' hPol' => ?_⟩
  -- uniqueness
  funext ⟨s, hs⟩
  set k : Fin 4 → ℝ := ![(1 - s) / 2, (1 + s) / 2, 0, 0] with hkdef
  have hdot : Minkowski.dot k k = s := by
    simp [Minkowski.dot_eq, hkdef]
    ring
  have hk : -(4 * P.m ^ 2) < Minkowski.dot k k := hdot ▸ hs
  have hsub : (⟨Minkowski.dot k k, hk⟩ : {s : ℝ // -(4 * P.m ^ 2) < s}) = ⟨s, hs⟩ :=
    Subtype.ext hdot
  -- a component of the transverse tensor that does not vanish
  obtain ⟨μ, hT⟩ : ∃ μ : Fin 4,
      ((Minkowski.dot k k * Minkowski.metric μ μ - k μ * k μ : ℝ) : ℂ) ≠ 0 := by
    by_cases hs0 : s = 0
    · refine ⟨0, ?_⟩
      have : Minkowski.dot k k * Minkowski.metric 0 0 - k 0 * k 0 = -(1 / 4) := by
        rw [hdot, hs0]
        simp [hkdef, Minkowski.metric, hs0]
        norm_num
      rw [this]
      norm_num
    · refine ⟨2, ?_⟩
      have : Minkowski.dot k k * Minkowski.metric 2 2 - k 2 * k 2 = s := by
        rw [hdot]
        simp [hkdef, Minkowski.metric]
      rw [this]
      exact_mod_cast hs0
  have h := tendsto_nhds_unique (hPol' k hk μ μ) (hPol k hk μ μ)
  rw [hsub] at h
  have h' := mul_right_cancel₀ hT h
  rw [hdot] at h'
  exact h'

end QED.WickModel

end
