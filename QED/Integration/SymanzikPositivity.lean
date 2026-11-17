/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SymanzikIntegrabilityClasses
public import QED.Algebra.Minkowski
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# Positivity of the two-loop Symanzik remainder (no thresholds)

Helper theorems for obligation O2-12 (`docs/TWO-LOOP-DERIVATION.md`, section 4.4): a uniform
positive lower bound for the remainder `V(z) = symanzikV α p M z` of the two-loop parametric
representation on the simplex, for the ladder `L` and the crossed ladder `X` of the order-`e⁵`
vertex, with the loop matrices `class5LoopMatrix .L`, `class5LoopMatrix .X`
(`QED/Integration/SymanzikIntegrabilityClasses.lean`), electron lines of mass `m`, photon lines of
masses `λ₁, λ₂` with `λᵢ² ≥ m_γ²`, and on-shell external momenta `p·p = p'·p' = -m²` with
`q = p' - p` spacelike or zero, `q·q ≥ 0` (mostly-plus metric). No smallness of `q²` and no
positive-energy condition is needed.

## The structure

For line momenta `pᵢ = aᵢ P + bᵢ K` with `P·K = 0` the remainder splits
(`symanzikV_smul_add_smul`):
`V = ∑ᵢ zᵢ Mᵢ² + (P·P) R(a) + (K·K) R(b)`, where `R(c) = ∑ᵢ zᵢ cᵢ² - β(c)ᵀ A⁻¹ β(c)`
(`remainder`) is the residual of the weighted least-squares problem `min_y ∑ᵢ zᵢ (αᵢ·y + cᵢ)²`.
With `P = (p + p')/2`, `K = (p' - p)/2` one has `P·K = 0`, `K·K = q²/4`, `P·P = -m² - q²/4`, so
`V = ∑ᵢ zᵢ Mᵢ² - m² R(a) + (q²/4) (R(b) - R(a))`.

* `R(b) - R(a) ≥ 0`: with `a = x + y`, `b = y - x` (`x`, `y` the lines before and after the
  external photon vertex), `R(b) - R(a) = 4 (β(x)ᵀ A⁻¹ β(y) - ∑ᵢ zᵢ xᵢ yᵢ)`
  (`remainder_sub_sub_remainder_add`), and `U · β(x)ᵀ A⁻¹ β(y)` is a polynomial with nonnegative
  coefficients (the electrical-network form of the maximum principle: the potential of a current
  is largest at its source). So `V` is nondecreasing in `q² ≥ 0` at fixed `z`.
* `m² R(a) ≤ ∑ᵢ zᵢ Mᵢ² - (lower bound)`: `R(a) ≤ ∑ᵢ zᵢ (αᵢ·y + aᵢ)²` for every `y`
  (`remainder_le_sum_sq`); a choice of `y` proportional to the electron-path current gives
  `∑_{electron} zᵢ - R(a) ≥ E²` (`L`) and `≥ E²/4` (`X`), `E = z₀ + z₁ + z₂ + z₃` the electron
  weight. This is the two-loop form of CK-UV (4.3)–(4.7): `∑_{electron} zᵢ - R(a)` is
  `∑_{electron} zᵢ Aᵢ` with `Aᵢ` the current fractions.

The bounds, the two-loop analogues of the one-loop `D ≥ (1 - x₃)² m² + x₃ m_γ²`:

* `L`: `V ≥ m² E² + m_γ² (1 - E)` (`le_symanzikV_classL`);
* `X`: `V ≥ m² E²/4 + m_γ² (1 - E)` (`le_symanzikV_classX`);

hence `V ≥ (3/4) min(m², m_γ²)` and `V ≥ (3/4) min(m²/4, m_γ²)` (`symanzikV_classL_pos`,
`symanzikV_classX_pos`). The hypothesis `U(z) ≠ 0` is necessary: at `U = 0` the Lean inverse is
`0` and `symanzikV` is the junk value `∑ᵢ zᵢ (Mᵢ² + pᵢ·pᵢ)`, which vanishes for instance at a
vertex of the simplex on an electron line. The set `U = 0` is null, and the bound is uniform on
its complement, including near the faces where `U → 0`.

Numerics (`scripts/numerics/two_loop_positivity.py`) show that the infimum over the simplex for
every class is `m_γ² (1 - m_γ²/(4m²))` when `m_γ² ≤ 2m²` (the one-loop value), approached along
edges where `U = 0` (an electron line parallel to a photon line), and that `R(b) ≥ R(a)` for all
nine classes.
-/

@[expose] public section

open Matrix Finset

namespace QED.Integration.TwoLoop

/-! ### General algebra -/

section General

variable {n : ℕ}

theorem dot_smul_add_smul_smul_add_smul (u v u' v' : ℝ) (P K : Fin 4 → ℝ) :
    Minkowski.dot (u • P + v • K) (u' • P + v' • K) =
      u * u' * Minkowski.dot P P + v * v' * Minkowski.dot K K +
        (u * v' + v * u') * Minkowski.dot P K := by
  simp only [Minkowski.dot_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem symanzikVector_smul_add_smul (α : Fin (n + 1) → Fin 2 → ℝ) (a b : Fin (n + 1) → ℝ)
    (P K : Fin 4 → ℝ) (z : Fin (n + 1) → ℝ) (s : Fin 2) :
    symanzikVector α (fun i => a i • P + b i • K) z s =
      coefVec α z a s • P + coefVec α z b s • K := by
  funext μ
  simp only [symanzikVector, coefVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The splitting of `V`.** For line momenta `pᵢ = aᵢ P + bᵢ K` with `P·K = 0`,
`V = ∑ᵢ zᵢ Mᵢ² + (P·P) R(a) + (K·K) R(b)`. Pure algebra (no condition on `U`). -/
theorem symanzikV_smul_add_smul (α : Fin (n + 1) → Fin 2 → ℝ) (M : Fin (n + 1) → ℝ)
    (z : Fin (n + 1) → ℝ) (a b : Fin (n + 1) → ℝ) {P K : Fin 4 → ℝ}
    (hPK : Minkowski.dot P K = 0) :
    symanzikV α (fun i => a i • P + b i • K) M z =
      ∑ i, z i * M i ^ 2 + Minkowski.dot P P * remainder α z a +
        Minkowski.dot K K * remainder α z b := by
  have h1 : ∀ i, Minkowski.dot (a i • P + b i • K) (a i • P + b i • K) =
      a i ^ 2 * Minkowski.dot P P + b i ^ 2 * Minkowski.dot K K := by
    intro i
    rw [dot_smul_add_smul_smul_add_smul, hPK]
    ring
  have hsum : ∑ i, z i * (M i ^ 2 + Minkowski.dot (a i • P + b i • K) (a i • P + b i • K)) =
      ∑ i, z i * M i ^ 2 + Minkowski.dot P P * ∑ i, z i * a i ^ 2 +
        Minkowski.dot K K * ∑ i, z i * b i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1]
    ring
  rw [symanzikV, hsum]
  simp only [symanzikVector_smul_add_smul, dot_smul_add_smul_smul_add_smul, hPK, remainder,
    dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-- `R(q) ≤ ∑ᵢ zᵢ (αᵢ·y + qᵢ)²` for every `y`: the remainder is the minimum. -/
theorem remainder_le_sum_sq (α : Fin (n + 1) → Fin 2 → ℝ) {z : Fin (n + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hdet : symanzikU α z ≠ 0) (q : Fin (n + 1) → ℝ) (y : Fin 2 → ℝ) :
    remainder α z q ≤ ∑ i, z i * (∑ s, α i s * y s + q i) ^ 2 := by
  rw [sum_mul_sq_eq_shift α z hdet q y, dotProduct_symanzikMatrix_mulVec]
  have : 0 ≤ ∑ i, z i * (∑ s, α i s *
      (y + (symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q) s) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (sq_nonneg _)
  linarith

/-- The inverse Symanzik matrix by the adjugate. -/
theorem inv_symanzikMatrix (α : Fin (n + 1) → Fin 2 → ℝ) (z : Fin (n + 1) → ℝ) :
    (symanzikMatrix α z)⁻¹ = (symanzikU α z)⁻¹ •
      !![symanzikMatrix α z 1 1, -symanzikMatrix α z 0 1;
        -symanzikMatrix α z 1 0, symanzikMatrix α z 0 0] := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  rfl

theorem symanzikMatrix_one_zero (α : Fin (n + 1) → Fin 2 → ℝ) (z : Fin (n + 1) → ℝ) :
    symanzikMatrix α z 1 0 = symanzikMatrix α z 0 1 := by
  simp only [symanzikMatrix, of_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `u ⬝ᵥ A⁻¹ w` by the adjugate. -/
theorem dotProduct_inv_symanzikMatrix_mulVec (α : Fin (n + 1) → Fin 2 → ℝ)
    (z : Fin (n + 1) → ℝ) (u w : Fin 2 → ℝ) :
    u ⬝ᵥ (symanzikMatrix α z)⁻¹ *ᵥ w = (symanzikU α z)⁻¹ *
      (symanzikMatrix α z 1 1 * u 0 * w 0 - symanzikMatrix α z 0 1 * (u 0 * w 1 + u 1 * w 0) +
        symanzikMatrix α z 0 0 * u 1 * w 1) := by
  rw [inv_symanzikMatrix]
  simp [dotProduct, mulVec, Fin.sum_univ_two, Matrix.smul_apply, symanzikMatrix_one_zero]
  ring

theorem coefVec_add (α : Fin (n + 1) → Fin 2 → ℝ) (z x y : Fin (n + 1) → ℝ) :
    coefVec α z (fun i => x i + y i) = coefVec α z x + coefVec α z y := by
  funext s
  simp only [coefVec, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem coefVec_sub (α : Fin (n + 1) → Fin 2 → ℝ) (z x y : Fin (n + 1) → ℝ) :
    coefVec α z (fun i => y i - x i) = coefVec α z y - coefVec α z x := by
  funext s
  simp only [coefVec, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `R(y - x) - R(x + y) = 4 (β(x)ᵀ A⁻¹ β(y) - ∑ᵢ zᵢ xᵢ yᵢ)`. -/
theorem remainder_sub_sub_remainder_add (α : Fin (n + 1) → Fin 2 → ℝ) (z x y : Fin (n + 1) → ℝ) :
    remainder α z (fun i => y i - x i) - remainder α z (fun i => x i + y i) =
      4 * (coefVec α z x ⬝ᵥ (symanzikMatrix α z)⁻¹ *ᵥ coefVec α z y - ∑ i, z i * x i * y i) := by
  have hsq : ∑ i, z i * (y i - x i) ^ 2 - ∑ i, z i * (x i + y i) ^ 2 =
      -4 * ∑ i, z i * x i * y i := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : ∀ u w : Fin 2 → ℝ, u ⬝ᵥ (symanzikMatrix α z)⁻¹ *ᵥ w =
      w ⬝ᵥ (symanzikMatrix α z)⁻¹ *ᵥ u := by
    intro u w
    rw [dotProduct_inv_symanzikMatrix_mulVec, dotProduct_inv_symanzikMatrix_mulVec]
    ring
  simp only [remainder, coefVec_add, coefVec_sub]
  simp only [mulVec_add, mulVec_sub, dotProduct_add, dotProduct_sub, add_dotProduct,
    sub_dotProduct]
  rw [key (coefVec α z y) (coefVec α z x)]
  linear_combination hsq

/-- On-shell kinematics: with `P = (p + p')/2`, `K = (p' - p)/2`, `P·K = 0`. -/
theorem dot_half_add_half_sub {mass : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2) :
    Minkowski.dot ((1 / 2 : ℝ) • (p + p')) ((1 / 2 : ℝ) • (p' - p)) = 0 := by
  rw [Minkowski.dot_eq] at hp hp' ⊢
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (1 / 4 : ℝ) * hp' - (1 / 4 : ℝ) * hp

theorem dot_half_add_self {mass : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2) :
    Minkowski.dot ((1 / 2 : ℝ) • (p + p')) ((1 / 2 : ℝ) • (p + p')) =
      -mass ^ 2 - Minkowski.dot ((1 / 2 : ℝ) • (p' - p)) ((1 / 2 : ℝ) • (p' - p)) := by
  rw [Minkowski.dot_eq] at hp hp' ⊢
  rw [Minkowski.dot_eq]
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (1 / 2 : ℝ) * hp' + (1 / 2 : ℝ) * hp

theorem dot_half_sub_self_nonneg {p p' : Fin 4 → ℝ}
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    0 ≤ Minkowski.dot ((1 / 2 : ℝ) • (p' - p)) ((1 / 2 : ℝ) • (p' - p)) := by
  rw [Minkowski.dot_eq] at hq ⊢
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hq ⊢
  nlinarith

end General

/-! ### The ladder and the crossed ladder -/

/-- The loop matrix of the ladder `L` (lines `v₀v₁, v₁v₂, v₂v₃, v₃v₄`, photons `(v₀v₄)`,
`(v₁v₃)`). -/
noncomputable abbrev loopMatrixL : Fin 6 → Fin 2 → ℝ := castLoopMatrix (class5LoopMatrix .L)

/-- The loop matrix of the crossed ladder `X` (lines `v₀v₁, v₁v₂, v₂v₃, v₃v₄`, photons
`(v₀v₃)`, `(v₁v₄)`). -/
noncomputable abbrev loopMatrixX : Fin 6 → Fin 2 → ℝ := castLoopMatrix (class5LoopMatrix .X)

/-- The external momenta of the lines of `L` and `X`, routed along the electron path: `p` enters
at `v₀`, `q = p' - p` at `v₂`, `p'` leaves at `v₄`; the photon lines carry no external
momentum. -/
def classLXMomenta (p p' : Fin 4 → ℝ) : Fin 6 → Fin 4 → ℝ := ![p, p, p', p', 0, 0]

/-- The masses of the lines of `L` and `X`: electrons `m`, photons `λ₁`, `λ₂`. -/
def classLXMasses (mass lam₁ lam₂ : ℝ) : Fin 6 → ℝ := ![mass, mass, mass, mass, lam₁, lam₂]

theorem classLXMomenta_eq (p p' : Fin 4 → ℝ) :
    classLXMomenta p p' = fun i => (![1, 1, 1, 1, 0, 0] : Fin 6 → ℝ) i • ((1 / 2 : ℝ) • (p + p')) +
      (![-1, -1, 1, 1, 0, 0] : Fin 6 → ℝ) i • ((1 / 2 : ℝ) • (p' - p)) := by
  funext i μ
  fin_cases i <;> simp [classLXMomenta] <;> ring

theorem sum_mul_classLXMasses_sq (mass lam₁ lam₂ : ℝ) (z : Fin 6 → ℝ) :
    ∑ i, z i * classLXMasses mass lam₁ lam₂ i ^ 2 =
      mass ^ 2 * (z 0 + z 1 + z 2 + z 3) + lam₁ ^ 2 * z 4 + lam₂ ^ 2 * z 5 := by
  simp [classLXMasses, Fin.sum_univ_six]
  ring

/-- The common reduction for `L` and `X`: with `a = (1,1,1,1,0,0)`, if `R(a)` is at most
`E - B` and `R(b) ≥ R(a)` then `V ≥ m² B + m_γ² (1 - E)`. -/
theorem le_symanzikV_classLX_of {α : Fin 6 → Fin 2 → ℝ} {mass mγ lam₁ lam₂ B : ℝ}
    {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i)
    (hRa : remainder α z ![1, 1, 1, 1, 0, 0] ≤ (z 0 + z 1 + z 2 + z 3) - B)
    (hRb : remainder α z ![1, 1, 1, 1, 0, 0] ≤ remainder α z ![-1, -1, 1, 1, 0, 0]) :
    mass ^ 2 * B + mγ ^ 2 * (z 4 + z 5) ≤
      symanzikV α (classLXMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  rw [classLXMomenta_eq, symanzikV_smul_add_smul _ _ _ _ _ (dot_half_add_half_sub hp hp'),
    dot_half_add_self hp hp', sum_mul_classLXMasses_sq]
  have hK := dot_half_sub_self_nonneg hq
  set k := Minkowski.dot ((1 / 2 : ℝ) • (p' - p)) ((1 / 2 : ℝ) • (p' - p))
  have h1 : 0 ≤ k * (remainder α z ![-1, -1, 1, 1, 0, 0] - remainder α z ![1, 1, 1, 1, 0, 0]) :=
    mul_nonneg hK (by linarith)
  have h2 : mass ^ 2 * remainder α z ![1, 1, 1, 1, 0, 0] ≤
      mass ^ 2 * ((z 0 + z 1 + z 2 + z 3) - B) :=
    mul_le_mul_of_nonneg_left hRa (sq_nonneg _)
  have h3 : mγ ^ 2 * z 4 ≤ lam₁ ^ 2 * z 4 := mul_le_mul_of_nonneg_right hlam₁ (hz 4)
  have h4 : mγ ^ 2 * z 5 ≤ lam₂ ^ 2 * z 5 := mul_le_mul_of_nonneg_right hlam₂ (hz 5)
  nlinarith

/-- From `E - R ≥ B` style bounds: `m² B + μ² s ≥ c ((1 - s)² + s) ≥ (3/4) c`. -/
theorem three_quarters_le {mass mγ c E s : ℝ} (hc : c ≤ mass ^ 2) (hc' : c ≤ mγ ^ 2)
    (hc0 : 0 ≤ c) (hE : E + s = 1) (hs : 0 ≤ s) :
    3 / 4 * c ≤ mass ^ 2 * E ^ 2 + mγ ^ 2 * s := by
  have h1 : c * E ^ 2 ≤ mass ^ 2 * E ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have h2 : c * s ≤ mγ ^ 2 * s := mul_le_mul_of_nonneg_right hc' hs
  nlinarith [sq_nonneg (E - 1 / 2), mul_nonneg hc0 (sq_nonneg (E - 1 / 2))]

/-! #### The ladder -/

/-- `L`: `R(b) - R(a) = 4 β(x)ᵀ A⁻¹ β(y) ≥ 0`. -/
theorem remainder_classL_le {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i) :
    remainder loopMatrixL z ![1, 1, 1, 1, 0, 0] ≤ remainder loopMatrixL z ![-1, -1, 1, 1, 0, 0] := by
  have h := remainder_sub_sub_remainder_add loopMatrixL z ![1, 1, 0, 0, 0, 0] ![0, 0, 1, 1, 0, 0]
  have ha : (fun i => (![1, 1, 0, 0, 0, 0] : Fin 6 → ℝ) i + (![0, 0, 1, 1, 0, 0] : Fin 6 → ℝ) i) =
      ![1, 1, 1, 1, 0, 0] := by
    funext i; fin_cases i <;> simp
  have hb : (fun i => (![0, 0, 1, 1, 0, 0] : Fin 6 → ℝ) i - (![1, 1, 0, 0, 0, 0] : Fin 6 → ℝ) i) =
      ![-1, -1, 1, 1, 0, 0] := by
    funext i; fin_cases i <;> simp
  rw [ha, hb, dotProduct_inv_symanzikMatrix_mulVec] at h
  have hU := symanzikU_nonneg loopMatrixL hz
  simp [coefVec, symanzikMatrix, Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix] at h
  have hpoly : 0 ≤ (symanzikU loopMatrixL z)⁻¹ *
      (z 1 * z 2 * (z 0 + z 3 + z 4 + z 5) + z 1 * z 3 * z 5 + z 0 * z 2 * z 5 +
        z 0 * z 3 * (z 1 + z 2 + z 5)) := by
    have := hz 0; have := hz 1; have := hz 2; have := hz 3; have := hz 4; have := hz 5
    positivity
  nlinarith [h, hpoly]

/-- `L`: `R(a) ≤ E (1 - E)² + z₄ E²`, from `y = -E (1, 1)`. -/
theorem remainder_classL_le_sum {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : symanzikU loopMatrixL z ≠ 0) :
    remainder loopMatrixL z ![1, 1, 1, 1, 0, 0] ≤
      (z 0 + z 1 + z 2 + z 3) * (1 - (z 0 + z 1 + z 2 + z 3)) ^ 2 +
        z 4 * (z 0 + z 1 + z 2 + z 3) ^ 2 := by
  refine (remainder_le_sum_sq loopMatrixL hz hU _
    ![-(z 0 + z 1 + z 2 + z 3), -(z 0 + z 1 + z 2 + z 3)]).trans (le_of_eq ?_)
  simp [Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix]
  ring

/-- **No thresholds for the ladder.** For the ladder `L` with electron mass `m`, photon masses
`λᵢ² ≥ m_γ²`, on-shell `p·p = p'·p' = -m²` and `q = p' - p` with `q·q ≥ 0`, at every point of the
simplex with `U(z) ≠ 0`: `V(z) ≥ m² E² + m_γ² (1 - E)`, `E = z₀ + z₁ + z₂ + z₃`. -/
theorem le_symanzikV_classL {mass mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixL z ≠ 0) :
    mass ^ 2 * (z 0 + z 1 + z 2 + z 3) ^ 2 + mγ ^ 2 * (z 4 + z 5) ≤
      symanzikV loopMatrixL (classLXMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  refine le_symanzikV_classLX_of hp hp' hq hlam₁ hlam₂ hz ?_ (remainder_classL_le hz)
  have h := remainder_classL_le_sum hz hU
  have h1 : z 0 + z 1 + z 2 + z 3 + z 4 + z 5 = 1 := by
    simpa [Fin.sum_univ_six] using hz1
  set E := z 0 + z 1 + z 2 + z 3
  have h4 : z 4 * E ^ 2 ≤ (1 - E) * E ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hz 5]) (sq_nonneg _)
  nlinarith

/-- **No thresholds for the ladder, uniform constant:** `V(z) ≥ (3/4) min(m², m_γ²)`. -/
theorem symanzikV_classL_ge {mass mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixL z ≠ 0) :
    3 / 4 * min (mass ^ 2) (mγ ^ 2) ≤
      symanzikV loopMatrixL (classLXMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  refine le_trans ?_ (le_symanzikV_classL hp hp' hq hlam₁ hlam₂ hz hz1 hU)
  have h1 : z 0 + z 1 + z 2 + z 3 + (z 4 + z 5) = 1 := by
    have := hz1; simp only [Fin.sum_univ_six] at this; linarith
  exact three_quarters_le (min_le_left _ _) (min_le_right _ _)
    (le_min (sq_nonneg _) (sq_nonneg _)) h1 (add_nonneg (hz 4) (hz 5))

theorem symanzikV_classL_pos {mass mγ lam₁ lam₂ : ℝ} (hm : mass ≠ 0) (hmγ : mγ ≠ 0)
    {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixL z ≠ 0) :
    0 < symanzikV loopMatrixL (classLXMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  have h0 : 0 < min (mass ^ 2) (mγ ^ 2) := lt_min (by positivity) (by positivity)
  linarith [symanzikV_classL_ge hp hp' hq hlam₁ hlam₂ hz hz1 hU]

/-! #### The crossed ladder -/

/-- `X`: `R(b) - R(a) = 4 β(x)ᵀ A⁻¹ β(y) ≥ 0`. -/
theorem remainder_classX_le {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i) :
    remainder loopMatrixX z ![1, 1, 1, 1, 0, 0] ≤ remainder loopMatrixX z ![-1, -1, 1, 1, 0, 0] := by
  have h := remainder_sub_sub_remainder_add loopMatrixX z ![1, 1, 0, 0, 0, 0] ![0, 0, 1, 1, 0, 0]
  have ha : (fun i => (![1, 1, 0, 0, 0, 0] : Fin 6 → ℝ) i + (![0, 0, 1, 1, 0, 0] : Fin 6 → ℝ) i) =
      ![1, 1, 1, 1, 0, 0] := by
    funext i; fin_cases i <;> simp
  have hb : (fun i => (![0, 0, 1, 1, 0, 0] : Fin 6 → ℝ) i - (![1, 1, 0, 0, 0, 0] : Fin 6 → ℝ) i) =
      ![-1, -1, 1, 1, 0, 0] := by
    funext i; fin_cases i <;> simp
  rw [ha, hb, dotProduct_inv_symanzikMatrix_mulVec] at h
  have hU := symanzikU_nonneg loopMatrixX hz
  simp [coefVec, symanzikMatrix, Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix] at h
  have hpoly : 0 ≤ (symanzikU loopMatrixX z)⁻¹ *
      (z 0 * z 2 * z 5 + z 1 * z 2 * (z 0 + z 3 + z 4 + z 5) + z 1 * z 3 * z 4) := by
    have := hz 0; have := hz 1; have := hz 2; have := hz 3; have := hz 4; have := hz 5
    positivity
  nlinarith [h, hpoly]

/-- `X`: `R(a) ≤ z₀ + F (1 - F)² + z₅ F²`, `F = z₁ + z₂ + z₃`, from `y = -F (1, 1)`. -/
theorem remainder_classX_le_sum₁ {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : symanzikU loopMatrixX z ≠ 0) :
    remainder loopMatrixX z ![1, 1, 1, 1, 0, 0] ≤
      z 0 + (z 1 + z 2 + z 3) * (1 - (z 1 + z 2 + z 3)) ^ 2 + z 5 * (z 1 + z 2 + z 3) ^ 2 := by
  refine (remainder_le_sum_sq loopMatrixX hz hU _
    ![-(z 1 + z 2 + z 3), -(z 1 + z 2 + z 3)]).trans (le_of_eq ?_)
  simp [Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix]
  ring

/-- `X`: `R(a) ≤ G (1 - G)² + z₃ + z₄ G²`, `G = z₀ + z₁ + z₂`, from `y = -G (1, 0)`. -/
theorem remainder_classX_le_sum₂ {z : Fin 6 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hU : symanzikU loopMatrixX z ≠ 0) :
    remainder loopMatrixX z ![1, 1, 1, 1, 0, 0] ≤
      (z 0 + z 1 + z 2) * (1 - (z 0 + z 1 + z 2)) ^ 2 + z 3 + z 4 * (z 0 + z 1 + z 2) ^ 2 := by
  refine (remainder_le_sum_sq loopMatrixX hz hU _ ![-(z 0 + z 1 + z 2), 0]).trans (le_of_eq ?_)
  simp [Fin.sum_univ_six, castLoopMatrix, class5LoopMatrix]
  ring

/-- **No thresholds for the crossed ladder.** For the crossed ladder `X` with electron mass `m`,
photon masses `λᵢ² ≥ m_γ²`, on-shell `p·p = p'·p' = -m²` and `q = p' - p` with `q·q ≥ 0`, at
every point of the simplex with `U(z) ≠ 0`: `V(z) ≥ m² E²/4 + m_γ² (1 - E)`,
`E = z₀ + z₁ + z₂ + z₃`. -/
theorem le_symanzikV_classX {mass mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixX z ≠ 0) :
    mass ^ 2 * ((z 0 + z 1 + z 2 + z 3) ^ 2 / 4) + mγ ^ 2 * (z 4 + z 5) ≤
      symanzikV loopMatrixX (classLXMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  refine le_symanzikV_classLX_of hp hp' hq hlam₁ hlam₂ hz ?_ (remainder_classX_le hz)
  have r1 := remainder_classX_le_sum₁ hz hU
  have r2 := remainder_classX_le_sum₂ hz hU
  have h1 : z 0 + z 1 + z 2 + z 3 + z 4 + z 5 = 1 := by
    simpa [Fin.sum_univ_six] using hz1
  have hF : z 0 + (z 1 + z 2 + z 3) * (1 - (z 1 + z 2 + z 3)) ^ 2 + z 5 * (z 1 + z 2 + z 3) ^ 2 ≤
      (z 0 + z 1 + z 2 + z 3) - (z 1 + z 2 + z 3) ^ 2 := by
    have : z 5 * (z 1 + z 2 + z 3) ^ 2 ≤ (1 - z 0 - (z 1 + z 2 + z 3)) * (z 1 + z 2 + z 3) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hz 4]) (sq_nonneg _)
    nlinarith [mul_nonneg (hz 0) (sq_nonneg (z 1 + z 2 + z 3))]
  have hG : (z 0 + z 1 + z 2) * (1 - (z 0 + z 1 + z 2)) ^ 2 + z 3 + z 4 * (z 0 + z 1 + z 2) ^ 2 ≤
      (z 0 + z 1 + z 2 + z 3) - (z 0 + z 1 + z 2) ^ 2 := by
    have : z 4 * (z 0 + z 1 + z 2) ^ 2 ≤ (1 - z 3 - (z 0 + z 1 + z 2)) * (z 0 + z 1 + z 2) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hz 5]) (sq_nonneg _)
    nlinarith [mul_nonneg (hz 3) (sq_nonneg (z 0 + z 1 + z 2))]
  have hFG : (z 0 + z 1 + z 2 + z 3) ^ 2 / 4 ≤
      ((z 1 + z 2 + z 3) ^ 2 + (z 0 + z 1 + z 2) ^ 2) / 2 := by
    have hle : z 0 + z 1 + z 2 + z 3 ≤ (z 1 + z 2 + z 3) + (z 0 + z 1 + z 2) := by
      linarith [hz 1, hz 2]
    have h0 : 0 ≤ z 0 + z 1 + z 2 + z 3 := by linarith [hz 0, hz 1, hz 2, hz 3]
    nlinarith [sq_nonneg ((z 1 + z 2 + z 3) - (z 0 + z 1 + z 2)), mul_le_mul hle hle h0
      (by linarith [hz 0, hz 1, hz 2, hz 3])]
  linarith

/-- **No thresholds for the crossed ladder, uniform constant:**
`V(z) ≥ (3/4) min(m²/4, m_γ²)`. -/
theorem symanzikV_classX_ge {mass mγ lam₁ lam₂ : ℝ} {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixX z ≠ 0) :
    3 / 4 * min (mass ^ 2 / 4) (mγ ^ 2) ≤
      symanzikV loopMatrixX (classLXMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  refine le_trans ?_ (le_symanzikV_classX hp hp' hq hlam₁ hlam₂ hz hz1 hU)
  have h1 : z 0 + z 1 + z 2 + z 3 + (z 4 + z 5) = 1 := by
    have := hz1; simp only [Fin.sum_univ_six] at this; linarith
  have hc : min (mass ^ 2 / 4) (mγ ^ 2) ≤ (mass / 2) ^ 2 :=
    (min_le_left _ _).trans_eq (by ring)
  have hc0 : 0 ≤ min (mass ^ 2 / 4) (mγ ^ 2) := le_min (by positivity) (sq_nonneg _)
  have h := three_quarters_le hc (min_le_right _ _) hc0 h1 (add_nonneg (hz 4) (hz 5))
  have : (mass / 2) ^ 2 * (z 0 + z 1 + z 2 + z 3) ^ 2 =
      mass ^ 2 * ((z 0 + z 1 + z 2 + z 3) ^ 2 / 4) := by ring
  linarith

theorem symanzikV_classX_pos {mass mγ lam₁ lam₂ : ℝ} (hm : mass ≠ 0) (hmγ : mγ ≠ 0)
    {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hlam₁ : mγ ^ 2 ≤ lam₁ ^ 2) (hlam₂ : mγ ^ 2 ≤ lam₂ ^ 2) {z : Fin 6 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : symanzikU loopMatrixX z ≠ 0) :
    0 < symanzikV loopMatrixX (classLXMomenta p p') (classLXMasses mass lam₁ lam₂) z := by
  have h0 : 0 < min (mass ^ 2 / 4) (mγ ^ 2) := lt_min (by positivity) (by positivity)
  linarith [symanzikV_classX_ge hp hp' hq hlam₁ hlam₂ hz hz1 hU]

end QED.Integration.TwoLoop

end
