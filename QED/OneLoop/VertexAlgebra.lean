/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexIntegrand
public import QED.Algebra.OnShell
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebra of the one-loop vertex integrand

Algebraic and kinematic facts about the frozen integrand `QED.OneLoop.vertexIntegrand` of the
primary source's (62.40), used to study its limit `ε → 0⁺`. A loop momentum is written
`ℓ = (t, v⃗)`, that is `(Fin.cons t v : Fin 4 → ℝ)`, with `t` the loop energy.

## Main definitions

* `QED.OneLoop.denom`: the scalar denominator `k² + M² - iε`, written as in the frozen
  propagators.
* `QED.OneLoop.vertexNumerator`: the `(i, j)` entry of the Dirac numerator
  `g_{νρ} γ^ρ (m - (p̸' + ℓ̸)) γ^μ (m - (p̸ + ℓ̸)) γ^ν`.
* `QED.OneLoop.feynmanMass`: the mass term left after Feynman combination of the three
  denominators and completion of the square.

## Main statements

* `QED.OneLoop.vertexIntegrand_apply`: entrywise, the integrand is a constant times the
  propagator denominators times the numerator.
* `QED.OneLoop.exists_vertexNumerator_quadratic`: the numerator is quadratic in the loop
  energy, with leading coefficient independent of the spatial loop momentum.
* `QED.OneLoop.exists_norm_vertexNumerator_le`: the numerator grows at most quadratically.
* `QED.OneLoop.feynman_combination`: the Feynman-parameter combination of the denominators
  of one Pauli–Villars term is a single shifted denominator.
* `QED.OneLoop.feynmanMass_ge` and `QED.OneLoop.feynmanMass_pos`: on the mass shell the
  combined mass term is bounded below by a positive constant.
-/

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- A scalar propagator denominator `k² + M² - iε`, written exactly as in the frozen
definitions. -/
noncomputable def denom (M ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot k k + M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I

/-- The `(i, j)` entry of the Dirac numerator of (62.40). -/
noncomputable def vertexNumerator (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ)
    (i j : Fin 4) : ℂ :=
  ∑ ν, ∑ ρ, ((Minkowski.metric ν ρ : ℝ) : ℂ) *
    (Dirac.gamma ρ * ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p' + ℓ)) *
      Dirac.gamma μ * ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p + ℓ)) *
      Dirac.gamma ν) i j

/-- Entrywise factorization of the frozen integrand. -/
theorem vertexIntegrand_apply (e m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 4 → ℝ) (i j : Fin 4) :
    vertexIntegrand e m mγ Λ ε p' p μ ℓ i j =
      ((I * e) ^ 3 * (1 / I) ^ 3 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹) *
        (((denom mγ ε ℓ)⁻¹ - (denom Λ ε ℓ)⁻¹) * (denom m ε (p' + ℓ))⁻¹ *
          (denom m ε (p + ℓ))⁻¹) * vertexNumerator m p' p μ ℓ i j := by
  simp only [vertexIntegrand, photonPropagator, electronPropagator, vertexNumerator, denom,
    Matrix.smul_apply, Matrix.sum_apply, Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
  ring

/-- The imaginary part of a denominator is `-ε`. -/
theorem denom_im (M ε : ℝ) (k : Fin 4 → ℝ) : (denom M ε k).im = -ε := by
  simp only [denom, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
  ring

/-! ### The numerator as a bilinear form -/

/-- The `(i, j)` entry of `g_{νρ} γ^ρ X γ^μ Y γ^ν`. It is bilinear in the matrices `X` and `Y`;
`vertexNumerator` is its value at `X = m - (p̸' + ℓ̸)` and `Y = m - (p̸ + ℓ̸)`. -/
noncomputable def vertexForm (μ : Fin 4) (X Y : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) : ℂ :=
  ∑ ν, ∑ ρ, ((Minkowski.metric ν ρ : ℝ) : ℂ) *
    (Dirac.gamma ρ * X * Dirac.gamma μ * Y * Dirac.gamma ν) i j

theorem vertexNumerator_eq_vertexForm (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 4 → ℝ) (i j : Fin 4) :
    vertexNumerator m p' p μ ℓ i j =
      vertexForm μ ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p' + ℓ))
        ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (p + ℓ)) i j := rfl

theorem vertexForm_sub_left (μ : Fin 4) (X X' Y : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    vertexForm μ (X - X') Y i j = vertexForm μ X Y i j - vertexForm μ X' Y i j := by
  simp only [vertexForm, Matrix.sub_mul, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem vertexForm_sub_right (μ : Fin 4) (X Y Y' : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    vertexForm μ X (Y - Y') i j = vertexForm μ X Y i j - vertexForm μ X Y' i j := by
  simp only [vertexForm, Matrix.sub_mul, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem vertexForm_smul_left (μ : Fin 4) (c : ℂ) (X Y : Matrix (Fin 4) (Fin 4) ℂ)
    (i j : Fin 4) : vertexForm μ (c • X) Y i j = c * vertexForm μ X Y i j := by
  simp only [vertexForm, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => by ring

theorem vertexForm_smul_right (μ : Fin 4) (c : ℂ) (X Y : Matrix (Fin 4) (Fin 4) ℂ)
    (i j : Fin 4) : vertexForm μ X (c • Y) i j = c * vertexForm μ X Y i j := by
  simp only [vertexForm, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => by ring

/-- Expansion of `vertexForm` along the line `t ↦ (X - t E, Y - t E)`. -/
theorem vertexForm_sub_smul_sub_smul (μ : Fin 4) (X Y E : Matrix (Fin 4) (Fin 4) ℂ) (t : ℂ)
    (i j : Fin 4) :
    vertexForm μ (X - t • E) (Y - t • E) i j =
      vertexForm μ E E i j * t ^ 2 + -(vertexForm μ X E i j + vertexForm μ E Y i j) * t
        + vertexForm μ X Y i j := by
  rw [vertexForm_sub_left, vertexForm_sub_right, vertexForm_sub_right, vertexForm_smul_left,
    vertexForm_smul_left, vertexForm_smul_right, vertexForm_smul_right]
  ring

theorem continuous_vertexNumerator (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    Continuous fun ℓ => vertexNumerator m p' p μ ℓ i j := by
  have hslash : Continuous Dirac.slash := by
    unfold Dirac.slash Minkowski.lower
    fun_prop
  have hs : ∀ q : Fin 4 → ℝ, Continuous fun ℓ : Fin 4 → ℝ =>
      (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (q + ℓ) := fun q =>
    continuous_const.sub (hslash.comp (continuous_const.add continuous_id))
  unfold vertexNumerator
  refine continuous_finsetSum _ fun ν _ => continuous_finsetSum _ fun ρ _ =>
    continuous_const.mul ?_
  exact ((((continuous_const.matrix_mul (hs p')).matrix_mul continuous_const).matrix_mul
    (hs p)).matrix_mul continuous_const).matrix_elem i j

/-! ### Dependence on the loop energy -/

/-- Splitting off the loop energy: with `ℓ = (t, v⃗)`,
`(q + ℓ)̸ = (q + (0, v⃗))̸ + t (1, 0⃗)̸`. -/
theorem slash_add_cons (q : Fin 4 → ℝ) (t : ℝ) (v : Fin 3 → ℝ) :
    Dirac.slash (q + (Fin.cons t v : Fin 4 → ℝ)) =
      Dirac.slash (q + (Fin.cons 0 v : Fin 4 → ℝ))
        + (t : ℂ) • Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ) := by
  rw [← Dirac.slash_smul, ← Dirac.slash_add]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k => ?_) k <;> simp

/-- Quadratic in the loop energy, with leading coefficient independent of the spatial part. -/
theorem exists_vertexNumerator_quadratic (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    ∃ α : ℂ, ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      vertexNumerator m p' p μ (Fin.cons t v : Fin 4 → ℝ) i j = α * (t : ℂ) ^ 2 + β * t + γ := by
  -- With `E` the slash of the unit time vector, `X = m - (p' + (0, v⃗))̸` and
  -- `Y = m - (p + (0, v⃗))̸`, the numerator at `ℓ = (t, v⃗)` is `vertexForm μ (X - t E) (Y - t E)`.
  let E := Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ)
  refine ⟨vertexForm μ E E i j, fun v => ?_⟩
  let X := (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
    - Dirac.slash (p' + (Fin.cons 0 v : Fin 4 → ℝ))
  let Y := (m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
    - Dirac.slash (p + (Fin.cons 0 v : Fin 4 → ℝ))
  refine ⟨-(vertexForm μ X E i j + vertexForm μ E Y i j), vertexForm μ X Y i j, fun t => ?_⟩
  rw [vertexNumerator_eq_vertexForm, slash_add_cons p', slash_add_cons p, ← sub_sub, ← sub_sub,
    vertexForm_sub_smul_sub_smul]

/-! ### Growth of the numerator -/

section Growth

/-! The growth bound uses the `ℓ∞` operator norm on matrices, which is submultiplicative. -/

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem norm_apply_le_norm (A : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (f := fun j => ‖A i j‖₊) (fun _ _ => zero_le)
      (Finset.mem_univ j)).trans
        (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i))
  exact_mod_cast h

private theorem norm_lower_le (ℓ : Fin 4 → ℝ) (κ : Fin 4) : ‖Minkowski.lower ℓ κ‖ ≤ ‖ℓ‖ := by
  have h := norm_le_pi_norm ℓ
  rw [Minkowski.lower_eq]
  fin_cases κ
  · simpa using h 0
  · simpa using h 1
  · simpa using h 2
  · simpa using h 3

private theorem norm_slash_le (ℓ : Fin 4 → ℝ) :
    ‖Dirac.slash ℓ‖ ≤ (∑ κ, ‖Dirac.gamma κ‖) * ‖ℓ‖ := by
  rw [Dirac.slash, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)
  rw [norm_smul, Complex.norm_real, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_lower_le ℓ κ) (norm_nonneg _)

private theorem norm_vertexForm_le (μ : Fin 4) (X Y : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    ‖vertexForm μ X Y i j‖ ≤
      (∑ ν, ∑ ρ, ‖((Minkowski.metric ν ρ : ℝ) : ℂ)‖ *
        (‖Dirac.gamma ρ‖ * ‖Dirac.gamma μ‖ * ‖Dirac.gamma ν‖)) * (‖X‖ * ‖Y‖) := by
  rw [vertexForm, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ _ => ?_)
  have hM : ‖(Dirac.gamma ρ * X * Dirac.gamma μ * Y * Dirac.gamma ν) i j‖ ≤
      ‖Dirac.gamma ρ‖ * ‖X‖ * ‖Dirac.gamma μ‖ * ‖Y‖ * ‖Dirac.gamma ν‖ := by
    refine (norm_apply_le_norm _ i j).trans ?_
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact norm_mul_le _ _
  calc ‖((Minkowski.metric ν ρ : ℝ) : ℂ) *
        (Dirac.gamma ρ * X * Dirac.gamma μ * Y * Dirac.gamma ν) i j‖
      ≤ ‖((Minkowski.metric ν ρ : ℝ) : ℂ)‖ *
        (‖Dirac.gamma ρ‖ * ‖X‖ * ‖Dirac.gamma μ‖ * ‖Y‖ * ‖Dirac.gamma ν‖) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hM (norm_nonneg _)
    _ = _ := by ring

private theorem norm_mass_sub_slash_le (m : ℝ) (q ℓ : Fin 4 → ℝ) :
    ‖(m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (q + ℓ)‖ ≤
      (‖(m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash q‖ + ∑ κ, ‖Dirac.gamma κ‖) *
        (1 + ‖ℓ‖) := by
  have h1 := norm_slash_le ℓ
  have h2 : 0 ≤ ‖(m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash q‖ * ‖ℓ‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h3 : 0 ≤ ∑ κ, ‖Dirac.gamma κ‖ := Finset.sum_nonneg fun κ _ => norm_nonneg _
  rw [Dirac.slash_add, ← sub_sub]
  refine (norm_sub_le _ _).trans ?_
  nlinarith

/-- Quadratic growth. -/
theorem exists_norm_vertexNumerator_le (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    ∃ C : ℝ, ∀ ℓ : Fin 4 → ℝ, ‖vertexNumerator m p' p μ ℓ i j‖ ≤ C * (1 + ‖ℓ‖) ^ 2 := by
  set K := ∑ ν, ∑ ρ, ‖((Minkowski.metric ν ρ : ℝ) : ℂ)‖ *
    (‖Dirac.gamma ρ‖ * ‖Dirac.gamma μ‖ * ‖Dirac.gamma ν‖)
  set G := ∑ κ, ‖Dirac.gamma κ‖
  set a' := ‖(m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p'‖
  set a := ‖(m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash p‖
  have hK : 0 ≤ K := Finset.sum_nonneg fun ν _ => Finset.sum_nonneg fun ρ _ =>
    mul_nonneg (norm_nonneg _) (by positivity)
  refine ⟨K * ((a' + G) * (a + G)), fun ℓ => ?_⟩
  rw [vertexNumerator_eq_vertexForm]
  refine (norm_vertexForm_le μ _ _ i j).trans ?_
  rw [mul_assoc, sq, mul_mul_mul_comm]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (norm_mass_sub_slash_le m p' ℓ)
    (norm_mass_sub_slash_le m p ℓ) (norm_nonneg _) (by positivity)) hK

end Growth

/-! ### Feynman parameters -/

/-- The mass term after completing the square. -/
noncomputable def feynmanMass (m M x y : ℝ) (p' p : Fin 4 → ℝ) : ℝ :=
  (1 - y) * M ^ 2
    + y * (x * (Minkowski.dot p' p' + m ^ 2) + (1 - x) * (Minkowski.dot p p + m ^ 2))
    - Minkowski.dot (y • (x • p' + (1 - x) • p)) (y • (x • p' + (1 - x) • p))

/-- Feynman combination of the three denominators of one Pauli–Villars term. -/
theorem feynman_combination (m M ε x y : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    (y : ℂ) * ((x : ℂ) * denom m ε (p' + ℓ) + (1 - x) * denom m ε (p + ℓ))
        + (1 - y) * denom M ε ℓ
      = ((Minkowski.dot (ℓ + y • (x • p' + (1 - x) • p)) (ℓ + y • (x • p' + (1 - x) • p))
          + feynmanMass m M x y p' p : ℝ) : ℂ) - (ε : ℂ) * I := by
  have h : y * (x * (Minkowski.dot (p' + ℓ) (p' + ℓ) + m ^ 2)
        + (1 - x) * (Minkowski.dot (p + ℓ) (p + ℓ) + m ^ 2))
        + (1 - y) * (Minkowski.dot ℓ ℓ + M ^ 2)
      = Minkowski.dot (ℓ + y • (x • p' + (1 - x) • p)) (ℓ + y • (x • p' + (1 - x) • p))
          + feynmanMass m M x y p' p := by
    simp only [feynmanMass, Minkowski.dot_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [← h]
  simp only [denom]
  push_cast
  ring

/-- `(y (x p' + (1 - x) p))² = y² (x² p'² + 2x(1 - x) p'·p + (1 - x)² p²)`. -/
theorem dot_smul_add_smul_self (x y : ℝ) (p' p : Fin 4 → ℝ) :
    Minkowski.dot (y • (x • p' + (1 - x) • p)) (y • (x • p' + (1 - x) • p)) =
      y ^ 2 * (x ^ 2 * Minkowski.dot p' p' + 2 * x * (1 - x) * Minkowski.dot p' p
        + (1 - x) ^ 2 * Minkowski.dot p p) := by
  simp only [Minkowski.dot_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- On the mass shell, `feynmanMass ≥ (1 - y) M² + y² m²`. -/
theorem feynmanMass_ge {m M x y : ℝ} {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (1 - y) * M ^ 2 + y ^ 2 * m ^ 2 ≤ feynmanMass m M x y p' p := by
  -- On shell, `feynmanMass = (1 - y) M² + y² (m² (x² + (1 - x)²) - 2x(1 - x) p'·p)`, and
  -- `p'·p ≤ -m²`.
  have hd := Minkowski.dot_le_neg_sq_of_onShell hp' hp hp0' hp0
  have hprod : 0 ≤ y ^ 2 * (x * (1 - x)) * -(Minkowski.dot p' p + m ^ 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg y) (mul_nonneg hx.1 (sub_nonneg.2 hx.2)))
      (neg_nonneg.2 (by linarith))
  rw [feynmanMass, dot_smul_add_smul_self, hp', hp]
  nlinarith [hprod]

/-- On the mass shell, `feynmanMass ≥ (3/4) min(M², m²)`, since `(1 - y) + y² ≥ 3/4`. -/
theorem feynmanMass_pos {m M x y : ℝ} {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    3 / 4 * min (M ^ 2) (m ^ 2) ≤ feynmanMass m M x y p' p := by
  refine le_trans ?_ (feynmanMass_ge hp' hp hp0' hp0 hx)
  have h1 : min (M ^ 2) (m ^ 2) ≤ M ^ 2 := min_le_left _ _
  have h2 : min (M ^ 2) (m ^ 2) ≤ m ^ 2 := min_le_right _ _
  have h0 : 0 ≤ min (M ^ 2) (m ^ 2) := le_min (sq_nonneg M) (sq_nonneg m)
  nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hy.2),
    mul_le_mul_of_nonneg_left h2 (sq_nonneg y), mul_nonneg h0 (sq_nonneg (y - 1 / 2))]

/-- The shifted square in components: with `ℓ = (t, v⃗)`,
`(ℓ + K)² = -(t + K⁰)² + Σₖ (vₖ + K^{k+1})²`. -/
theorem dot_cons_add (t : ℝ) (v : Fin 3 → ℝ) (K : Fin 4 → ℝ) :
    Minkowski.dot ((Fin.cons t v : Fin 4 → ℝ) + K) ((Fin.cons t v : Fin 4 → ℝ) + K)
      = -(t + K 0) ^ 2 + ∑ k : Fin 3, (v k + K k.succ) ^ 2 := by
  have h2 : (Fin.cons t v : Fin 4 → ℝ) 2 = v 1 := rfl
  have h3 : (Fin.cons t v : Fin 4 → ℝ) 3 = v 2 := rfl
  have h4 : (Fin.succ 2 : Fin 4) = 3 := rfl
  simp only [Minkowski.dot_eq, Fin.sum_univ_three, Pi.add_apply, Fin.cons_zero, Fin.cons_one, h2,
    h3, h4, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

end QED.OneLoop

end
