/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopParametricAlgebra

/-!
# (X₁) piece D: the Symanzik remainder `V` off the mass shell

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece D. The `ε → 0⁺` limits of the two-loop classes need a lower bound
`V ≥ c > 0` on the simplex. The bounds of `QED/Integration/SymanzikPositivity*.lean` are on
shell; here they are carried to nearby off-shell momenta.

Each remainder `R(q) = ∑ zᵢ qᵢ² - βᵀ A⁻¹ β` is a quadratic form in the column `q`, nonnegative
and at most `∑ zᵢ qᵢ²`. The identity `t R(a + b) + R(t a - b) = (t + t²) R(a) + (1 + t) R(b)`
(`remainder_add_identity`) gives `R(a + b) ≤ (1 + t) R(a) + (1 + 1/t) R(b)` for `t > 0`, and so

`V(p₀ + d) ≥ V(p₀) - t ∑ |p₀|² - (1 + 1/t) ∑ |d|²` (`symanzikV_add_ge`)

on the simplex where `U ≠ 0`. No bound on the loop shifts is needed.

## Main statements

* `QED.GradedProof.X1D.symanzikV_add_ge`: the perturbation bound.
* `QED.GradedProof.X1D.eventually_symanzikV_ge`: if `V ≥ c > 0` at the momenta `mom y₀`, then
  `V ≥ c/2` at `mom y` for `y` near `y₀`, for momenta continuous at `y₀`.
-/

@[expose] public section

open Matrix Filter Topology
open QED.Integration.TwoLoop

namespace QED.GradedProof.X1D

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ)

/-! ### The remainder is a quadratic form -/

theorem coefVec_lin (t : ℝ) (a b : Fin (m + 1) → ℝ) :
    coefVec α z (fun i => t * a i + b i) = t • coefVec α z a + coefVec α z b := by
  funext s
  simp only [coefVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The parallelogram-type identity of the remainder**:
`t R(a + b) + R(t a - b) = (t + t²) R(a) + (1 + t) R(b)`. -/
theorem remainder_add_identity (t : ℝ) (a b : Fin (m + 1) → ℝ) :
    t * remainder α z (fun i => a i + b i) + remainder α z (fun i => t * a i - b i) =
      (t + t ^ 2) * remainder α z a + (1 + t) * remainder α z b := by
  have h1 : coefVec α z (fun i => a i + b i) = coefVec α z a + coefVec α z b := by
    simpa using coefVec_lin α z 1 a b
  have h2 : coefVec α z (fun i => t * a i - b i) = t • coefVec α z a - coefVec α z b := by
    have := coefVec_lin α z t a (fun i => -b i)
    have hb : coefVec α z (fun i => -b i) = -coefVec α z b := by
      funext s
      simp [coefVec]
    simp only [← sub_eq_add_neg] at this
    rw [this, hb, sub_eq_add_neg]
  have hs : t * ∑ i, z i * (a i + b i) ^ 2 + ∑ i, z i * (t * a i - b i) ^ 2 =
      (t + t ^ 2) * ∑ i, z i * a i ^ 2 + (1 + t) * ∑ i, z i * b i ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [remainder, h1, h2, mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add,
    add_dotProduct, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  linear_combination hs

variable {α z}

/-- `R(a + b) ≤ (1 + t) R(a) + (1 + 1/t) R(b)` for `t > 0`. -/
theorem remainder_add_le (hz : ∀ i, 0 ≤ z i) (hU : symanzikU α z ≠ 0) {t : ℝ} (ht : 0 < t)
    (a b : Fin (m + 1) → ℝ) :
    remainder α z (fun i => a i + b i) ≤
      (1 + t) * remainder α z a + (1 + 1 / t) * remainder α z b := by
  have e := remainder_add_identity α z t a b
  have h0 := remainder_nonneg α hz hU (fun i => t * a i - b i)
  have key : t * remainder α z (fun i => a i + b i) ≤
      t * ((1 + t) * remainder α z a + (1 + 1 / t) * remainder α z b) := by
    have : t * ((1 + t) * remainder α z a + (1 + 1 / t) * remainder α z b) =
        (t + t ^ 2) * remainder α z a + (1 + t) * remainder α z b := by
      field_simp
      ring
    linarith
  exact le_of_mul_le_mul_left key ht

theorem sum_mul_sq_le (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (q : Fin (m + 1) → ℝ) :
    ∑ i, z i * q i ^ 2 ≤ ∑ i, q i ^ 2 := by
  have hzle : ∀ i, z i ≤ 1 := fun i => by
    rw [← hz1]
    exact Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i)
  exact Finset.sum_le_sum fun i _ => by nlinarith [hz i, hzle i, sq_nonneg (q i)]

/-! ### The perturbation bound -/

theorem sum_sq_cols (q : Fin (m + 1) → Fin 4 → ℝ) :
    ∑ i, ∑ μ, q i μ ^ 2 = ∑ i, q i 0 ^ 2 + ∑ c : Fin 3, ∑ i, q i c.succ ^ 2 := by
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_succ _

/-- **`V` off the shell**: on the simplex where `U ≠ 0`, for every `t > 0`,
`V(p₀ + d) ≥ V(p₀) - t ∑ |p₀|² - (1 + 1/t) ∑ |d|²`. -/
theorem symanzikV_add_ge (M : Fin (m + 1) → ℝ) (p₀ d : Fin (m + 1) → Fin 4 → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU α z ≠ 0) {t : ℝ} (ht : 0 < t) :
    symanzikV α p₀ M z - t * ∑ i, ∑ μ, p₀ i μ ^ 2 - (1 + 1 / t) * ∑ i, ∑ μ, d i μ ^ 2 ≤
      symanzikV α (p₀ + d) M z := by
  rw [symanzikV_eq, symanzikV_eq, sum_sq_cols p₀, sum_sq_cols d]
  simp only [Pi.add_apply]
  set R := remainder α z
  have hnn := remainder_nonneg α hz hU
  have hle := remainder_le α hz hU
  have hsq := sum_mul_sq_le hz hz1
  have ht1 : 0 < 1 + t := by linarith
  have hit : 0 < 1 / t := by positivity
  -- the energy column: an upper bound
  have h0 : R (fun i => p₀ i 0 + d i 0) ≤ (1 + t) * R (fun i => p₀ i 0) +
      (1 + 1 / t) * R (fun i => d i 0) := remainder_add_le hz hU ht _ _
  have hd0 : R (fun i => d i 0) ≤ ∑ i, d i 0 ^ 2 :=
    (hle (fun i => d i 0)).trans (hsq (fun i => d i 0))
  have hp0 : R (fun i => p₀ i 0) ≤ ∑ i, p₀ i 0 ^ 2 :=
    (hle (fun i => p₀ i 0)).trans (hsq (fun i => p₀ i 0))
  -- the spatial columns: lower bounds
  have hc : ∀ c : Fin 3, R (fun i => p₀ i c.succ) - t * ∑ i, p₀ i c.succ ^ 2 -
      (1 + 1 / t) * ∑ i, d i c.succ ^ 2 ≤ R (fun i => p₀ i c.succ + d i c.succ) := by
    intro c
    have h := remainder_add_le hz hU ht (fun i => p₀ i c.succ + d i c.succ)
      (fun i => -d i c.succ)
    simp only [add_neg_cancel_right] at h
    have hb : R (fun i => -d i c.succ) ≤ ∑ i, d i c.succ ^ 2 := by
      refine (hle _).trans ((hsq _).trans (le_of_eq ?_))
      exact Finset.sum_congr rfl fun i _ => by ring
    have hp : R (fun i => p₀ i c.succ + d i c.succ) ≤ ∑ i, z i * (p₀ i c.succ + d i c.succ) ^ 2 :=
      hle _
    have hpc : R (fun i => p₀ i c.succ) ≤ ∑ i, p₀ i c.succ ^ 2 :=
      (hle _).trans (hsq _)
    have hD : 0 ≤ ∑ i, d i c.succ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hn' := hnn (fun i => p₀ i c.succ)
    have key : R (fun i => p₀ i c.succ) - (1 + 1 / t) * ∑ i, d i c.succ ^ 2 ≤
        (1 + t) * R (fun i => p₀ i c.succ + d i c.succ) := by
      nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 1 + 1 / t)]
    have e1 : (1 + t) * (R (fun i => p₀ i c.succ) - t * ∑ i, p₀ i c.succ ^ 2 -
        (1 + 1 / t) * ∑ i, d i c.succ ^ 2) = (R (fun i => p₀ i c.succ) -
          (1 + 1 / t) * ∑ i, d i c.succ ^ 2) -
        t * ((1 + t) * ∑ i, p₀ i c.succ ^ 2 - R (fun i => p₀ i c.succ)) -
        (t + 1) * ∑ i, d i c.succ ^ 2 := by
      field_simp
      ring
    have e2 : 0 ≤ t * ((1 + t) * ∑ i, p₀ i c.succ ^ 2 - R (fun i => p₀ i c.succ)) := by
      refine mul_nonneg ht.le ?_
      nlinarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (p₀ i c.succ)]
    refine le_of_mul_le_mul_left ?_ ht1
    rw [e1]
    nlinarith [mul_nonneg ht1.le hD]
  simp only [Fin.sum_univ_three] at hc ⊢
  have := hc 0
  have := hc 1
  have := hc 2
  nlinarith [mul_le_mul_of_nonneg_left hp0 ht.le,
    mul_le_mul_of_nonneg_left hd0 (by positivity : (0 : ℝ) ≤ 1 + 1 / t)]

/-! ### `V ≥ c/2` near momenta with `V ≥ c` -/

/-- **`V ≥ c/2` near momenta with `V ≥ c`**: if `V ≥ c > 0` at `mom y₀` at every point of the
simplex with `U ≠ 0`, and `mom` is continuous at `y₀`, then `V ≥ c/2` at `mom y` for `y` near
`y₀`. -/
theorem eventually_symanzikV_ge {Y : Type*} [TopologicalSpace Y] {mom : Y → Fin (m + 1) → Fin 4 → ℝ}
    {y₀ : Y} (hmom : ContinuousAt mom y₀) (M : Fin (m + 1) → ℝ) {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α (mom y₀) M z) :
    ∀ᶠ y in 𝓝 y₀, ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU α z ≠ 0 → c / 2 ≤ symanzikV α (mom y) M z := by
  set K := ∑ i, ∑ μ, mom y₀ i μ ^ 2 with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun μ _ => sq_nonneg _
  set t := c / (4 * (K + 1)) with ht
  have ht0 : 0 < t := by positivity
  set η := c / 4 / (1 + 1 / t) with hη
  have hη0 : 0 < η := by positivity
  have hcont : ContinuousAt (fun y => ∑ i, ∑ μ, (mom y - mom y₀) i μ ^ 2) y₀ := by
    have : Continuous fun q : Fin (m + 1) → Fin 4 → ℝ => ∑ i, ∑ μ, q i μ ^ 2 := by fun_prop
    exact this.continuousAt.comp (hmom.sub continuousAt_const)
  have h0 : (fun y => ∑ i, ∑ μ, (mom y - mom y₀) i μ ^ 2) y₀ = 0 := by simp
  have hev : ∀ᶠ y in 𝓝 y₀, ∑ i, ∑ μ, (mom y - mom y₀) i μ ^ 2 < η :=
    hcont.eventually (Iio_mem_nhds (by rw [h0]; exact hη0))
  filter_upwards [hev] with y hy z hz hz1 hU
  have h := symanzikV_add_ge M (mom y₀) (mom y - mom y₀) hz hz1 hU ht0 (α := α)
  rw [add_sub_cancel] at h
  have hVc := hV z hz hz1 hU
  have htK : t * K ≤ c / 4 := by
    rw [ht, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hdη : (1 + 1 / t) * ∑ i, ∑ μ, (mom y - mom y₀) i μ ^ 2 ≤ c / 4 := by
    have h1 : 0 < 1 + 1 / t := by positivity
    have := mul_le_mul_of_nonneg_left hy.le h1.le
    rw [hη, mul_div_cancel₀ _ h1.ne'] at this
    exact this
  linarith

end QED.GradedProof.X1D

end
