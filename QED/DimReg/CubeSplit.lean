/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Splitting the unit cube: the generic covering step of sector decomposition

Sector decomposition rewrites an integral over the unit cube `Q = (0, 1]^N` as a sum of
integrals over `Q` with the integrand pulled back by explicit maps. The elementary step
compares two coordinates `i ≠ j`: `Q` is the union of `{yᵢ ≤ yⱼ}` and `{yⱼ ≤ yᵢ}`, which overlap
in a null set, and the substitution `yᵢ ↦ yⱼ yᵢ` (`QED.DimReg.splitMap i j`, Jacobian `yⱼ`) maps
`Q` bijectively onto the first piece. Hence

  `∫_Q g = ∫_Q yⱼ · g(splitMap i j y) dy + ∫_Q yᵢ · g(splitMap j i y) dy`

(`QED.DimReg.integral_unitCube_split`). The covering is proved here once and for all, with no
family data. Iterating it along a binary tree (`QED.DimReg.SplitTree`) gives the decomposition
`∫_Q g = Σ_σ ∫_Q J_σ(y) · g(φ_σ(y)) dy` over the leaves of the tree
(`QED.DimReg.SplitTree.integral_eq_sum`). The maps `φ_σ` are composites of the elementary
substitutions and the Jacobians `J_σ` are monomials. A larger Binoth–Heinrich step (comparing a
set `S` of coordinates at once) is a tree of such pairwise steps, so a sector certificate needs
only the tree.

## Main results

* `QED.DimReg.image_splitMap`, `QED.DimReg.injOn_splitMap`, `QED.DimReg.det_splitDeriv`.
* `QED.DimReg.integral_split`, `QED.DimReg.integrableOn_split_iff`: the change of variables onto
  `{yᵢ ≤ yⱼ}`.
* `QED.DimReg.integral_unitCube_split`: the covering step.
* `QED.DimReg.SplitTree.integral_eq_sum`: the iterated decomposition along a tree.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.DimReg

variable {N : ℕ}

/-- The unit cube `(0, 1]^N`. -/
def unitCube (N : ℕ) : Set (Fin N → ℝ) := univ.pi fun _ => Ioc 0 1

theorem measurableSet_unitCube (N : ℕ) : MeasurableSet (unitCube N) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem mem_unitCube {y : Fin N → ℝ} : y ∈ unitCube N ↔ ∀ i, 0 < y i ∧ y i ≤ 1 := by
  simp [unitCube]

/-- The elementary sector substitution `yᵢ ↦ yⱼ yᵢ`. -/
def splitMap (i j : Fin N) (y : Fin N → ℝ) : Fin N → ℝ := Function.update y i (y j * y i)

/-- The Jacobian matrix of `splitMap i j` at `y`: the identity with row `i` replaced by
`yⱼ eᵢ + yᵢ eⱼ`. -/
def splitMatrix (i j : Fin N) (y : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.updateRow 1 i (y j • (1 : Matrix (Fin N) (Fin N) ℝ) i +
    y i • (1 : Matrix (Fin N) (Fin N) ℝ) j)

/-- The derivative of `splitMap i j` at `y`. -/
noncomputable def splitDeriv (i j : Fin N) (y : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (splitMatrix i j y))

theorem det_splitMatrix {i j : Fin N} (hij : i ≠ j) (y : Fin N → ℝ) :
    (splitMatrix i j y).det = y j := by
  rw [splitMatrix, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, Matrix.det_updateRow_eq_zero hij.symm,
    Matrix.det_one]
  ring

theorem det_splitDeriv {i j : Fin N} (hij : i ≠ j) (y : Fin N → ℝ) :
    (splitDeriv i j y).det = y j := by
  rw [splitDeriv, ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap,
    LinearMap.det_toLin', det_splitMatrix hij]

theorem splitDeriv_apply_self (i j : Fin N) (y v : Fin N → ℝ) :
    splitDeriv i j y v i = y j * v i + y i * v j := by
  simp [splitDeriv, splitMatrix, Matrix.mulVec, dotProduct, Matrix.one_apply, add_mul,
    Finset.sum_add_distrib, ite_mul]

theorem splitDeriv_apply_ne {i j k : Fin N} (hk : k ≠ i) (y v : Fin N → ℝ) :
    splitDeriv i j y v k = v k := by
  simp [splitDeriv, splitMatrix, Matrix.mulVec, dotProduct, Matrix.updateRow_ne hk,
    Matrix.one_apply]

theorem hasFDerivAt_splitMap (i j : Fin N) (y : Fin N → ℝ) :
    HasFDerivAt (splitMap i j) (splitDeriv i j y) y := by
  rw [hasFDerivAt_pi']
  intro k
  by_cases hk : k = i
  · subst hk
    have h := (hasFDerivAt_apply (𝕜 := ℝ) j y).mul (hasFDerivAt_apply (𝕜 := ℝ) k y)
    convert h using 1
    · funext x; simp [splitMap]
    · ext v; simp [splitDeriv_apply_self]
  · have h := hasFDerivAt_apply (𝕜 := ℝ) k y
    convert h using 1
    · funext x; simp [splitMap, Function.update_of_ne hk]
    · ext v; simp [splitDeriv_apply_ne hk]

theorem injOn_splitMap {i j : Fin N} (hij : i ≠ j) : InjOn (splitMap i j) (unitCube N) := by
  intro y hy y' hy' h
  have hj : y j = y' j := by
    simpa [splitMap, Function.update_of_ne hij.symm] using congrFun h j
  funext k
  by_cases hk : k = i
  · subst hk
    have h1 : y j * y k = y' j * y' k := by simpa [splitMap] using congrFun h k
    rw [hj] at h1
    exact mul_left_cancel₀ (mem_unitCube.mp hy' j).1.ne' h1
  · simpa [splitMap, Function.update_of_ne hk] using congrFun h k

theorem image_splitMap {i j : Fin N} (hij : i ≠ j) :
    splitMap i j '' unitCube N = {y ∈ unitCube N | y i ≤ y j} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := mem_unitCube.mp hy
    refine ⟨mem_unitCube.mpr fun k => ?_, ?_⟩
    · by_cases hk : k = i
      · subst hk
        simp only [splitMap, Function.update_self]
        exact ⟨mul_pos (hy' j).1 (hy' k).1,
          (mul_le_of_le_one_right (hy' j).1.le (hy' k).2).trans (hy' j).2⟩
      · simpa [splitMap, Function.update_of_ne hk] using hy' k
    · simp only [splitMap, Function.update_self, Function.update_of_ne hij.symm]
      exact mul_le_of_le_one_right (hy' j).1.le (hy' i).2
  · rintro ⟨hz, hle⟩
    have hz' := mem_unitCube.mp hz
    refine ⟨Function.update z i (z i / z j), mem_unitCube.mpr fun k => ?_, ?_⟩
    · by_cases hk : k = i
      · subst hk
        simp only [Function.update_self]
        exact ⟨div_pos (hz' k).1 (hz' j).1, (div_le_one (hz' j).1).mpr hle⟩
      · simpa [Function.update_of_ne hk] using hz' k
    · funext k
      by_cases hk : k = i
      · subst hk
        simp only [splitMap, Function.update_self, Function.update_of_ne hij.symm]
        field_simp [(hz' j).1.ne']
      · simp [splitMap, Function.update_of_ne hk]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem abs_det_splitDeriv_smul {i j : Fin N} (hij : i ≠ j) (g : (Fin N → ℝ) → E) :
    EqOn (fun y => |(splitDeriv i j y).det| • g (splitMap i j y))
      (fun y => y j • g (splitMap i j y)) (unitCube N) := by
  intro y hy
  simp only [det_splitDeriv hij, abs_of_pos (mem_unitCube.mp hy j).1]

/-- **The change of variables onto `{yᵢ ≤ yⱼ}`.** -/
theorem integral_split {i j : Fin N} (hij : i ≠ j) (g : (Fin N → ℝ) → E) :
    ∫ y in {y ∈ unitCube N | y i ≤ y j}, g y =
      ∫ y in unitCube N, y j • g (splitMap i j y) := by
  rw [← image_splitMap hij, integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_unitCube N) (fun y _ => (hasFDerivAt_splitMap i j y).hasFDerivWithinAt)
    (injOn_splitMap hij) g]
  exact setIntegral_congr_fun (measurableSet_unitCube N) (abs_det_splitDeriv_smul hij g)

theorem integrableOn_split_iff {i j : Fin N} (hij : i ≠ j) (g : (Fin N → ℝ) → E) :
    IntegrableOn g {y ∈ unitCube N | y i ≤ y j} ↔
      IntegrableOn (fun y => y j • g (splitMap i j y)) (unitCube N) := by
  rw [← image_splitMap hij, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (measurableSet_unitCube N) (fun y _ => (hasFDerivAt_splitMap i j y).hasFDerivWithinAt)
    (injOn_splitMap hij) g]
  exact integrableOn_congr_fun (abs_det_splitDeriv_smul hij g) (measurableSet_unitCube N)

/-- The diagonal `{yᵢ = yⱼ}` (`i ≠ j`) is Lebesgue-null. -/
theorem volume_diag_eq_zero {i j : Fin N} (hij : i ≠ j) :
    volume {y : Fin N → ℝ | y i = y j} = 0 := by
  let L : (Fin N → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin N → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have : (Pi.single i (1 : ℝ) : Fin N → ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    simp [L, hij.symm] at this
  have hset : {y : Fin N → ℝ | y i = y j} = (LinearMap.ker L : Set (Fin N → ℝ)) := by
    ext y
    simp [L, sub_eq_zero]
  rw [hset]
  exact Measure.addHaar_submodule volume _ hne

/-- **The covering step.** For `i ≠ j` and `g` integrable on the cube,
`∫_Q g = ∫_Q yⱼ g(splitMap i j y) + ∫_Q yᵢ g(splitMap j i y)`, both integrands integrable. -/
theorem integral_unitCube_split {i j : Fin N} (hij : i ≠ j) {g : (Fin N → ℝ) → E}
    (hg : IntegrableOn g (unitCube N)) :
    IntegrableOn (fun y => y j • g (splitMap i j y)) (unitCube N) ∧
      IntegrableOn (fun y => y i • g (splitMap j i y)) (unitCube N) ∧
      ∫ y in unitCube N, g y = (∫ y in unitCube N, y j • g (splitMap i j y)) +
        ∫ y in unitCube N, y i • g (splitMap j i y) := by
  set A := {y ∈ unitCube N | y i ≤ y j}
  set B := {y ∈ unitCube N | y j ≤ y i}
  set B' := {y ∈ unitCube N | y j < y i}
  have hA : IntegrableOn g A := hg.mono_set fun y hy => hy.1
  have hB : IntegrableOn g B := hg.mono_set fun y hy => hy.1
  have hB'm : MeasurableSet B' :=
    (measurableSet_unitCube N).inter (measurableSet_lt (measurable_pi_apply j)
      (measurable_pi_apply i))
  have hQ : unitCube N = A ∪ B' := by
    ext y
    simp only [A, B', mem_union, mem_ofPred_eq]
    constructor
    · intro hy
      rcases le_or_gt (y i) (y j) with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (h | h) <;> exact h.1
  have hdisj : Disjoint A B' := by
    rw [Set.disjoint_left]
    rintro y ⟨_, h1⟩ ⟨_, h2⟩
    linarith
  have hBB' : B' =ᵐ[volume] B := by
    refine ae_eq_set.mpr ⟨?_, ?_⟩
    · exact measure_mono_null (fun y hy => (hy.2 ⟨hy.1.1, hy.1.2.le⟩).elim) measure_empty
    · refine measure_mono_null (fun y hy => ?_) (volume_diag_eq_zero hij)
      simp only [B, B', mem_sdiff, mem_ofPred_eq, not_and, not_lt] at hy
      exact le_antisymm (hy.2 hy.1.1) hy.1.2
  have hsplit : ∫ y in unitCube N, g y = (∫ y in A, g y) + ∫ y in B, g y := by
    rw [hQ, setIntegral_union hdisj hB'm hA (hB.mono_set fun y hy => ⟨hy.1, hy.2.le⟩),
      setIntegral_congr_set hBB']
  refine ⟨(integrableOn_split_iff hij g).mp hA, (integrableOn_split_iff hij.symm g).mp hB, ?_⟩
  rw [hsplit, integral_split hij, integral_split hij.symm]

/-! ### Iterated splitting along a tree -/

/-- A binary tree of elementary splitting steps. At `node i j l r` the left subtree refines the
piece `{yᵢ ≤ yⱼ}` (after `yᵢ ↦ yⱼ yᵢ`) and the right subtree the piece `{yⱼ ≤ yᵢ}`. -/
inductive SplitTree (N : ℕ) where
  | leaf : SplitTree N
  | node (i j : Fin N) (l r : SplitTree N) : SplitTree N

/-- The composite substitution of a leaf, given its path from the root as the list of steps
`(i, j)` taken (`yᵢ ↦ yⱼ yᵢ`). The root step acts last. -/
def leafMap : List (Fin N × Fin N) → (Fin N → ℝ) → (Fin N → ℝ)
  | [], y => y
  | p :: ps, y => splitMap p.1 p.2 (leafMap ps y)

/-- The Jacobian of a leaf. -/
def leafJac : List (Fin N × Fin N) → (Fin N → ℝ) → ℝ
  | [], _ => 1
  | p :: ps, y => leafJac ps y * leafMap ps y p.2

/-- The pulled-back integrand of a leaf, `J_σ(y) · g(φ_σ(y))`. -/
def leafIntegrand (g : (Fin N → ℝ) → E) (ps : List (Fin N × Fin N)) (y : Fin N → ℝ) : E :=
  leafJac ps y • g (leafMap ps y)

theorem leafIntegrand_cons (g : (Fin N → ℝ) → E) (i j : Fin N) (ps : List (Fin N × Fin N)) :
    leafIntegrand (fun y => y j • g (splitMap i j y)) ps = leafIntegrand g ((i, j) :: ps) := by
  funext y
  simp [leafIntegrand, leafJac, leafMap, mul_smul]

namespace SplitTree

/-- The paths from the root to the leaves. -/
def paths : SplitTree N → List (List (Fin N × Fin N))
  | leaf => [[]]
  | node i j l r => (l.paths.map ((i, j) :: ·)) ++ (r.paths.map ((j, i) :: ·))

/-- Every step compares two distinct coordinates. -/
def Valid : SplitTree N → Prop
  | leaf => True
  | node i j l r => i ≠ j ∧ l.Valid ∧ r.Valid

/-- **Iterated sector decomposition.** Along a valid tree, an integrable `g` satisfies
`∫_Q g = Σ_σ ∫_Q J_σ · g ∘ φ_σ`, every leaf integrand being integrable. -/
theorem integral_eq_sum : ∀ (T : SplitTree N), T.Valid → ∀ {g : (Fin N → ℝ) → E},
    IntegrableOn g (unitCube N) →
      (∀ ps ∈ T.paths, IntegrableOn (leafIntegrand g ps) (unitCube N)) ∧
      ∫ y in unitCube N, g y =
        (T.paths.map fun ps => ∫ y in unitCube N, leafIntegrand g ps y).sum
  | leaf, _, g, hg => by
    refine ⟨fun ps hps => ?_, ?_⟩
    · simp only [paths, List.mem_singleton] at hps
      subst hps
      have e : leafIntegrand g [] = g := funext fun y => by simp [leafIntegrand, leafJac, leafMap]
      rwa [e]
    · simp [paths, leafIntegrand, leafJac, leafMap]
  | node i j l r, ⟨hij, hl, hr⟩, g, hg => by
    obtain ⟨h1, h2, h3⟩ := integral_unitCube_split hij hg
    obtain ⟨il, el⟩ := integral_eq_sum l hl h1
    obtain ⟨ir, er⟩ := integral_eq_sum r hr h2
    refine ⟨fun ps hps => ?_, ?_⟩
    · simp only [paths, List.mem_append, List.mem_map] at hps
      rcases hps with ⟨qs, hqs, rfl⟩ | ⟨qs, hqs, rfl⟩
      · rw [← leafIntegrand_cons]; exact il qs hqs
      · rw [← leafIntegrand_cons]; exact ir qs hqs
    · rw [h3, el, er]
      simp only [paths, List.map_append, List.map_map, List.sum_append]
      congr 2
      · exact List.map_congr_left fun qs _ => by simp only [Function.comp, leafIntegrand_cons]
      · exact List.map_congr_left fun qs _ => by simp only [Function.comp, leafIntegrand_cons]

end SplitTree

end QED.DimReg
