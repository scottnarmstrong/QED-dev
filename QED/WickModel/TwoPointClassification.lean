/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.TwoPointClassificationTree
public import QED.WickModel.TwoPointClassificationSelfEnergy
public import QED.WickModel.TwoPointClassificationPolarization

/-!
# The two-point 1PI functions at one loop

The reduction of the general Wick model's two-point 1PI functions at order `≤ 2` (packet 6a,
decision D-24) to the source's tree terms plus the energy-first integral of the one-loop
integrands of `QED.WickModel.TwoPoint` (decisions D-23, D-25).

The sum over the vertex sequences of total order at most `2` reduces to `[]`, the single vertices
and `[gauge, gauge]`:

* without vertices no contraction is 1PI;
* among the single vertices only `fermionCt` (self-energy) and `photonCt` (vacuum polarization)
  have 1PI contractions, the trees (`QED.WickModel.TwoPointClassificationTree`);
* the 1PI contractions of `[gauge, gauge]` are the two self-energy loops
  (`QED.WickModel.TwoPointClassificationSelfEnergy`), or the two vacuum polarization loops
  (`QED.WickModel.TwoPointClassificationPolarization`); the two labellings have the same signed
  value, so the `1/2!` leaves one copy.

## Main statements

* `onePIFunction_selfEnergy`: `[i Σ(p̸)]_{αβ} = -i (δ₂ p̸ + δ_m m)_{αβ} + ∫ selfEnergyIntegrand`,
  and its matrix form `onePIFunction_selfEnergy_matrix`.
* `onePIFunction_vacuumPolarization`:
  `i Π^{μν}(k) = -i δ₃ (k² g^{μν} - k^μ k^ν) + ∫ vacuumPolarizationIntegrand`.

The self-energy tree is written `-i ((δ₂ p̸ + δ_m m)_{αβ})`, the matrix entry inside the product:
the scalar `-i` times the matrix, then applied to `α β`, does not elaborate (there is no
`HMul ℂ (Matrix _ _ ℂ)` instance), and `(-i • M) α β` is the same number.
-/

@[expose] public section

open Complex

namespace QED.WickModel

open scoped Classical in
/-- **The one-loop electron self-energy from the Wick expansion** (decisions D-23, D-25). For all
parameters, momenta `p` and spinor indices `α`, `β`, the 1PI function with one external fermion
pair of momentum `p` at order `≤ 2`, `[i Σ(p̸)]_{αβ}` of (62.27)–(62.28), is the counterterm tree
`-i (δ₂ p̸ + δ_m m)_{αβ}` plus the energy-first integral of the self-energy integrand
`(ie)² (1/i)² (2π)⁻⁴ γ^ν S̃(p̸ + ℓ̸) γ^μ Δ̃_{μν}(ℓ)`, with the external `Ψ(x)` giving the row `α`
and `Ψ̄(y)` the column `β`. Only the all-electron flavoring contributes: the fermion line is
open. No hypothesis on the parameters is needed. -/
theorem onePIFunction_selfEnergy (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) :
    onePIFunction P 1 0 2 ![p] ![p] ![] ![α] ![β] ![] =
      -I * (((P.δ₂ : ℂ) • Dirac.slash p +
          ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)
        + QED.OneLoop.energyFirstIntegral (fun ℓ => selfEnergyIntegrand P P.ε p ℓ α β) := by
  have h1 : ∀ κ : Fin 1 → Wick.VertexKind, κ ≠ oneVertex .fermionCt →
      ∀ C : Contraction 1 0 κ, ¬ IsOnePI C := by
    intro κ hne C
    obtain ⟨k, rfl⟩ : ∃ k, κ = oneVertex k := ⟨κ 0, eq_oneVertex κ⟩
    exact not_isOnePI_oneVertex_selfEnergy (fun h => hne (congrArg oneVertex h)) C
  rw [onePIFunction]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [Finset.sum_eq_zero fun κ _ => sum_isOnePI_eq_zero not_isOnePI_of_fin_zero_left _,
    Finset.sum_eq_single_of_mem (oneVertex .fermionCt)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩)
      fun κ _ hne => sum_isOnePI_eq_zero (h1 κ hne) _,
    sum_isOnePI_selfEnergyTree,
    Finset.sum_eq_single_of_mem gauge2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩)
      fun κ hκ hne => absurd (eq_gauge2_of_sum_order_le (Finset.mem_filter.mp hκ).2) hne,
    sum_isOnePI_selfEnergyLoop]
  simp only [Matrix.cons_val_zero, Nat.factorial, Nat.cast_one, Nat.cast_mul, inv_one, one_mul,
    mul_zero, zero_add, Nat.succ_eq_add_one]
  ring

open scoped Classical in
/-- **The one-loop vacuum polarization from the Wick expansion** (decisions D-22, D-23, D-25).
For all parameters, momenta `k` and Lorentz indices `μ`, `ν`, the 1PI function with two external
photons of momenta `k` and `-k` at order `≤ 2`, `i Π^{μν}(k)` of (62.4) and (62.12), is the
counterterm tree `-i δ₃ (k² g^{μν} - k^μ k^ν)` plus the energy-first integral of the vacuum
polarization integrand `(-1) (ie)² (1/i)² (2π)⁻⁴ ∑_f c_f Tr[S̃_f(ℓ̸ + k̸) γ^μ S̃_f(ℓ̸) γ^ν]`, the
fermion loop regulated by the Pauli–Villars flavors inside one integrand. No hypothesis on the
parameters is needed; integrability, which needs the Pauli–Villars conditions, is not used. -/
theorem onePIFunction_vacuumPolarization (P : Params) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    onePIFunction P 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν] =
      (-I * ((P.δ₃ * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ) : ℂ))
        + QED.OneLoop.energyFirstIntegral
            (fun ℓ => vacuumPolarizationIntegrand P P.ε k ℓ μ ν) := by
  have h1 : ∀ κ : Fin 1 → Wick.VertexKind, κ ≠ oneVertex .photonCt →
      ∀ C : Contraction 0 2 κ, ¬ IsOnePI C := by
    intro κ hne C
    obtain ⟨k, rfl⟩ : ∃ k, κ = oneVertex k := ⟨κ 0, eq_oneVertex κ⟩
    exact not_isOnePI_oneVertex_polarization (fun h => hne (congrArg oneVertex h)) C
  rw [onePIFunction]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [Finset.sum_eq_zero fun κ _ => sum_isOnePI_eq_zero not_isOnePI_of_fin_zero_right _,
    Finset.sum_eq_single_of_mem (oneVertex .photonCt)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩)
      fun κ _ hne => sum_isOnePI_eq_zero (h1 κ hne) _,
    sum_isOnePI_polarizationTree,
    Finset.sum_eq_single_of_mem gauge2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩)
      fun κ hκ hne => absurd (eq_gauge2_of_sum_order_le (Finset.mem_filter.mp hκ).2) hne,
    sum_isOnePI_polarizationLoop]
  simp only [Nat.factorial, Nat.cast_one, Nat.cast_mul, inv_one, one_mul, mul_zero, zero_add,
    Nat.succ_eq_add_one]
  ring

/-- The self-energy as a matrix: `i Σ(p̸) = -i (δ₂ p̸ + δ_m m) + ∫ selfEnergyIntegrand`, the
matrix form of `onePIFunction_selfEnergy`. -/
theorem onePIFunction_selfEnergy_matrix (P : Params) (p : Fin 4 → ℝ) :
    (Matrix.of fun α β => onePIFunction P 1 0 2 ![p] ![p] ![] ![α] ![β] ![]) =
      -I • ((P.δ₂ : ℂ) • Dirac.slash p +
          ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) +
        Matrix.of fun α β =>
          QED.OneLoop.energyFirstIntegral (fun ℓ => selfEnergyIntegrand P P.ε p ℓ α β) := by
  ext α β
  simp only [Matrix.of_apply, onePIFunction_selfEnergy, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]

end QED.WickModel

end
