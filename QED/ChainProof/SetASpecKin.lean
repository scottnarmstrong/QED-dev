/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SymanzikPositivity
public import QED.TwoLoop.ClassLimitParametric
public import QED.TwoLoop.VPHalfAtAssemblyPieces

/-!
# Set (a): two-point kinematics of the parametric representation at fixed `ε`

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`
(the two-loop vacuum polarization inserted into the one-loop vertex). The outer vertex is an
energy-first integral over all photon momenta `k ∈ ℝ⁴`, so the inserted two-loop vacuum
polarization is needed at fixed `ε > 0` and at every `k`, in a form the spectral engine
`QED.TwoLoop.VPHalfAtGen.specInt` consumes.

Every two-loop piece of the vacuum polarization has, at fixed `ε`, the parametric representation
`-π⁴ ∫_Δ paramIntegrand`, a sum of powers of `W = V - iε`
(`QED.TwoLoop.ClassLimit.paramIntegrand_eq`). For two-point kinematics, line momenta `pᵢ = cᵢ k`,
this file shows that `W` is a photon-type factor of the set (b) form
`QED.TwoLoop.VPHalfAtAssembly.fDen`:

* `setASpec_symanzikV_twoPoint`: `V(z) = a(z) + w(z) k·k` with `a(z) = ∑ᵢ zᵢ Mᵢ²` (`saMassSq`) and
  `w(z) = remainder α z c`, the minimum of `∑ᵢ zᵢ (αᵢ·y + cᵢ)²` over `y`;
* `setASpec_remainder_le_quarter`, `setASpec_threshold`: a flow certificate `y` (a unit
  `k`-flow with `|αᵢ·y + cᵢ| ≤ 1/2` on every line) gives `w ≤ 1/4`, and with masses
  `Mᵢ ≥ 2 m₀ |αᵢ·y + cᵢ|` also `4 m₀² w ≤ a`: the spectral mass² `a/w` is above the pair
  threshold `4 m₀²`;
* `setASpec_remainder_pos`: `w > 0` at interior points when no `y` annihilates every line;
* `saXi w = (1 - √(1 - 4w))/2`, with `saXi w (1 - saXi w) = w` (`setASpec_saXi_mul`) and
  `saXi w ∈ (0, 1)` for `0 < w ≤ 1/4`;
* **`setASpec_wBase_eq_fDen`**: `W = fDen (√a) ε ξ k = a + ξ(1 - ξ) k² - iε`, `ξ = saXi w`, the
  factor that `specInt` multiplies by, with mass `√a ≥ M_lo` (`setASpec_le_sqrt_saMassSq`).

The identities were checked numerically on the 8-line Pauli–Villars pieces of the classes `VA`,
`VB`, `VC` before the proofs (2000 random points each).
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.VPHalfAtAssembly
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.WickModel (vacuumPolarizationFeynmanMass)

variable {m : ℕ}

/-! ### The mass term and the splitting of `V` -/

/-- The mass term `a(z) = ∑ᵢ zᵢ Mᵢ²` of `V`. -/
def saMassSq (M z : Fin (m + 1) → ℝ) : ℝ := ∑ i, z i * M i ^ 2

theorem saMassSq_nonneg {M z : Fin (m + 1) → ℝ} (hz : ∀ i, 0 ≤ z i) : 0 ≤ saMassSq M z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (sq_nonneg _)

/-- With every mass at least `M_lo ≥ 0`, `M_lo² ≤ a(z)` on the simplex. -/
theorem setASpec_sq_le_saMassSq {M z : Fin (m + 1) → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    {Mlo : ℝ} (hMlo : 0 ≤ Mlo) (hM : ∀ i, Mlo ≤ M i) : Mlo ^ 2 ≤ saMassSq M z := by
  calc Mlo ^ 2 = ∑ i, z i * Mlo ^ 2 := by rw [← Finset.sum_mul, hz1, one_mul]
    _ ≤ saMassSq M z := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMlo (hM i) 2) (hz i)

theorem setASpec_le_sqrt_saMassSq {M z : Fin (m + 1) → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    {Mlo : ℝ} (hMlo : 0 ≤ Mlo) (hM : ∀ i, Mlo ≤ M i) : Mlo ≤ Real.sqrt (saMassSq M z) :=
  Real.le_sqrt_of_sq_le (setASpec_sq_le_saMassSq hz hz1 hMlo hM)

/-- **Two-point kinematics**: for line momenta `cᵢ k`, `V(z) = a(z) + (k·k) w(z)`. -/
theorem setASpec_symanzikV_twoPoint (α : Fin (m + 1) → Fin 2 → ℝ) (M z c : Fin (m + 1) → ℝ)
    (k : Fin 4 → ℝ) :
    symanzikV α (fun i => c i • k) M z = saMassSq M z + Minkowski.dot k k * remainder α z c := by
  have hdot0 : Minkowski.dot k 0 = 0 := by simp [Minkowski.dot_eq]
  have h := symanzikV_smul_add_smul α M z c (fun _ => 0) hdot0
  simp only [smul_zero, add_zero] at h
  have hd00 : Minkowski.dot (0 : Fin 4 → ℝ) 0 = 0 := by simp [Minkowski.dot_eq]
  rw [h, hd00, zero_mul, add_zero]
  rfl

/-! ### Bounds on `w` from a flow certificate -/

/-- **`w ≤ 1/4`** from a flow certificate with `(αᵢ·y + cᵢ)² ≤ 1/4` on every line. -/
theorem setASpec_remainder_le_quarter (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU α z ≠ 0) (c : Fin (m + 1) → ℝ)
    (y : Fin 2 → ℝ) (hy : ∀ i, (∑ s, α i s * y s + c i) ^ 2 ≤ 1 / 4) :
    remainder α z c ≤ 1 / 4 := by
  refine (remainder_le_sum_sq α hz hU c y).trans ?_
  calc ∑ i, z i * (∑ s, α i s * y s + c i) ^ 2 ≤ ∑ i, z i * (1 / 4) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy i) (hz i)
    _ = 1 / 4 := by rw [← Finset.sum_mul, hz1, one_mul]

/-- **The threshold**: with `4 m₀² (αᵢ·y + cᵢ)² ≤ Mᵢ²` on every line, `4 m₀² w ≤ a`. -/
theorem setASpec_threshold (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hU : symanzikU α z ≠ 0) (M c : Fin (m + 1) → ℝ) (y : Fin 2 → ℝ)
    {m₀ : ℝ} (hcap : ∀ i, 4 * m₀ ^ 2 * (∑ s, α i s * y s + c i) ^ 2 ≤ M i ^ 2) :
    4 * m₀ ^ 2 * remainder α z c ≤ saMassSq M z := by
  have h := remainder_le_sum_sq α hz hU c y
  have h4 : 0 ≤ 4 * m₀ ^ 2 := by positivity
  calc 4 * m₀ ^ 2 * remainder α z c
      ≤ 4 * m₀ ^ 2 * ∑ i, z i * (∑ s, α i s * y s + c i) ^ 2 :=
        mul_le_mul_of_nonneg_left h h4
    _ = ∑ i, z i * (4 * m₀ ^ 2 * (∑ s, α i s * y s + c i) ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ saMassSq M z := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcap i) (hz i)

/-- **`w > 0` at interior points** when no `y` makes every line momentum coefficient vanish
(the external momentum must flow through some line). -/
theorem setASpec_remainder_pos (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 < z i) (hU : symanzikU α z ≠ 0) (c : Fin (m + 1) → ℝ)
    (hc : ∀ y : Fin 2 → ℝ, ∃ i, ∑ s, α i s * y s + c i ≠ 0) :
    0 < remainder α z c := by
  set y₀ : Fin 2 → ℝ := -((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z c)
  have h := sum_mul_sq_eq_shift α z hU c y₀
  rw [show y₀ + (symanzikMatrix α z)⁻¹ *ᵥ coefVec α z c = 0 by simp [y₀], zero_dotProduct,
    zero_add] at h
  obtain ⟨i, hi⟩ := hc y₀
  rw [← h]
  have hpos : 0 < z i * (∑ s, α i s * y₀ s + c i) ^ 2 :=
    mul_pos (hz i) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi)))
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun i =>
    z i * (∑ s, α i s * y₀ s + c i) ^ 2) (fun j _ => mul_nonneg (hz j).le (sq_nonneg _))
    (Finset.mem_univ i))

/-! ### The Feynman parameter of a factor -/

/-- The root `ξ = (1 - √(1 - 4w))/2` of `ξ(1 - ξ) = w`. -/
noncomputable def saXi (w : ℝ) : ℝ := (1 - Real.sqrt (1 - 4 * w)) / 2

theorem setASpec_saXi_mul {w : ℝ} (hw : w ≤ 1 / 4) : saXi w * (1 - saXi w) = w := by
  have h := Real.sq_sqrt (show 0 ≤ 1 - 4 * w by linarith)
  unfold saXi
  linear_combination (-1 / 4 : ℝ) * h

theorem setASpec_saXi_le_half (w : ℝ) : saXi w ≤ 1 / 2 := by
  have := Real.sqrt_nonneg (1 - 4 * w)
  unfold saXi
  linarith

theorem setASpec_saXi_pos {w : ℝ} (hw : 0 < w) : 0 < saXi w := by
  have h : Real.sqrt (1 - 4 * w) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  unfold saXi
  linarith

theorem setASpec_saXi_mem_Ioo {w : ℝ} (hw : 0 < w) : saXi w ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨setASpec_saXi_pos hw, (setASpec_saXi_le_half w).trans_lt (by norm_num)⟩

/-! ### `W` is a photon-type factor -/

/-- `V(z)` at two-point kinematics is the inner-loop mass `a + ξ(1 - ξ) k²` of set (b). -/
theorem setASpec_symanzikV_eq_feynmanMass (α : Fin (m + 1) → Fin 2 → ℝ) {M z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (c : Fin (m + 1) → ℝ) (hw : remainder α z c ≤ 1 / 4) (k : Fin 4 → ℝ) :
    symanzikV α (fun i => c i • k) M z =
      vacuumPolarizationFeynmanMass (Real.sqrt (saMassSq M z)) (Minkowski.dot k k)
        (saXi (remainder α z c)) := by
  rw [setASpec_symanzikV_twoPoint, vacuumPolarizationFeynmanMass,
    Real.sq_sqrt (saMassSq_nonneg hz), setASpec_saXi_mul hw]
  ring

/-- **The parametric base `W = V - iε` is the photon-type factor `fDen`** at every simplex point
with `U ≠ 0`, given a flow certificate. -/
theorem setASpec_wBase_eq_fDen (α : Fin (m + 1) → Fin 2 → ℝ) (M c : Fin (m + 1) → ℝ)
    (y : Fin 2 → ℝ) (hy : ∀ i, (∑ s, α i s * y s + c i) ^ 2 ≤ 1 / 4) {x : Fin m → ℝ}
    (hx : x ∈ simplexSet m) (hU : symanzikU α (simplexPoint x) ≠ 0) (ε : ℝ)
    (k : Fin 4 → ℝ) :
    wBase α (fun i => c i • k) M ε x =
      fDen (Real.sqrt (saMassSq M (simplexPoint x))) ε
        (saXi (remainder α (simplexPoint x) c)) k := by
  have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx
  have hw := setASpec_remainder_le_quarter α hz.1 hz.2 hU c y hy
  rw [wBase, fDen, setASpec_symanzikV_eq_feynmanMass α hz.1 c hw]

end QED.ChainProof.SetASpec

end
