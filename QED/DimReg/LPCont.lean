/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.LeafForm
public import QED.DimReg.PowerFamily
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Certified sector decomposition ⇒ meromorphic continuation of a Lee–Pomeransky integral

Let `G` be a polynomial with natural coefficients and partial degrees at most `D`, and suppose
that for every box `T ⊆ Fin N` a splitting tree passes the sector checker on the box polynomial
`P_T` (`QED.DimReg.LPSectorData`). Along a holomorphic curve `λ ↦ (ν(λ), d(λ))` in parameter space,
the Lee–Pomeransky integral `∫_{(0,∞)^N} x ^ (ν - 1) G ^ (-d / 2)` is the sum over boxes and
leaves of cube Mellin integrals

  `∫_Q ∏ₖ yₖ ^ (ℓₖ(λ) - 1) · P̃(y) ^ (-d(λ) / 2) dy`

(`QED.DimReg.BoxInversion`, `QED.DimReg.SplitTree.integral_eq_sum`,
`QED.DimReg.Sector.leafIntegrand_lp`).
Replacing each by its `K`-fold continuation `QED.DimReg.cubeMellinCont` gives
`QED.DimReg.LPSectorData.lpCont`:

* where all leaf exponents have `re ℓₖ > 0`, the integral converges absolutely and equals
  `lpCont` (`QED.DimReg.LPSectorData.lpConvergent_of_re`,
  `QED.DimReg.LPSectorData.lpIntegral_eq_lpCont`);
* `lpCont` is meromorphic where all `re ℓₖ > -K` (`QED.DimReg.LPSectorData.meromorphicAt_lpCont`),
  and analytic where moreover no `ℓₖ` lies in `{0, -1, …}`
  (`QED.DimReg.LPSectorData.analyticAt_lpCont`).

The leaf exponents are affine in `(ν, d / 2)` (`QED.DimReg.Sector.leafExp`), so these regions are
explicit polyhedra.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.DimReg

variable {N : ℕ}

/-! ### Integrability from the leaves -/

namespace SplitTree

/-- The converse of `QED.DimReg.SplitTree.integral_eq_sum` for integrability: if every leaf
integrand is integrable on the cube, so is `g`. -/
theorem integrableOn_of_leaves {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ (T : SplitTree N), T.Valid → ∀ {g : (Fin N → ℝ) → E},
      (∀ ps ∈ T.paths, IntegrableOn (leafIntegrand g ps) (unitCube N)) →
      IntegrableOn g (unitCube N)
  | leaf, _, g, h => by
    have e : leafIntegrand g [] = g := funext fun y => by simp [leafIntegrand, leafJac, leafMap]
    simpa [paths, e] using h [] (by simp [paths])
  | node i j l r, ⟨hij, hl, hr⟩, g, h => by
    have h1 := integrableOn_of_leaves l hl (g := fun y => y j • g (splitMap i j y)) fun ps hps => by
      rw [leafIntegrand_cons]
      exact h _ (by simp only [paths, List.mem_append, List.mem_map]; exact Or.inl ⟨ps, hps, rfl⟩)
    have h2 := integrableOn_of_leaves r hr (g := fun y => y i • g (splitMap j i y)) fun ps hps => by
      rw [leafIntegrand_cons]
      exact h _ (by simp only [paths, List.mem_append, List.mem_map]; exact Or.inr ⟨ps, hps, rfl⟩)
    have hA := (integrableOn_split_iff hij g).mpr h1
    have hB := (integrableOn_split_iff hij.symm g).mpr h2
    refine (hA.union hB).mono_set fun y hy => ?_
    rcases le_total (y i) (y j) with h | h
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, h⟩

end SplitTree

namespace Sector

/-! ### Sparse polynomials as `MvPolynomial`s -/

/-- A sparse natural polynomial as an `MvPolynomial`. -/
noncomputable def NPoly.toMv (P : NPoly) : MvPolynomial (Fin N) ℝ :=
  (P.map fun t => MvPolynomial.C (t.2 : ℝ) * ∏ k : Fin N, MvPolynomial.X k ^ t.1.getD k 0).sum

theorem NPoly.eval_toMv (P : NPoly) (y : Fin N → ℝ) :
    MvPolynomial.eval y (NPoly.toMv P) = P.eval y := by
  simp only [NPoly.toMv, NPoly.eval, map_list_sum, List.map_map, Function.comp_def, map_mul,
    MvPolynomial.eval_C, map_prod, map_pow, MvPolynomial.eval_X, mono]

end Sector

open Sector

/-! ### The data and the continuation -/

/-- Certified sector data for the Lee–Pomeransky polynomial `G`: partial degrees bounded by `D`,
and for every box `T` a splitting tree passing the checker on the box polynomial. -/
structure LPSectorData (N : ℕ) where
  /-- The Lee–Pomeransky polynomial `G = U + F`. -/
  G : NPoly
  /-- Bounds for the partial degrees. -/
  D : List ℕ
  /-- The splitting tree of each box. -/
  tree : Finset (Fin N) → SplitTree N
  deg : ∀ t ∈ G, ∀ i : Fin N, t.1.getD i 0 ≤ D.getD i 0
  check : ∀ T, (⟨tree T, [boxPolyF T D G]⟩ : SDCert N).check = true

namespace LPSectorData

variable (S : LPSectorData N)

/-- The minimal exponent `m` of `P_T ∘ φ_σ` on the leaf `ps`. -/
def leafMin (T : Finset (Fin N)) (ps : List (Fin N × Fin N)) : List ℕ :=
  NPoly.minE ((boxPolyF T S.D S.G).pull ps)

/-- The cofactor `P̃ = P_T ∘ φ_σ / y ^ m` on the leaf `ps`. -/
def leafPoly (T : Finset (Fin N)) (ps : List (Fin N × Fin N)) : NPoly :=
  ((boxPolyF T S.D S.G).pull ps).shift (S.leafMin T ps)

/-- The cofactor as an `MvPolynomial`. -/
noncomputable def leafMv (T : Finset (Fin N)) (ps : List (Fin N × Fin N)) :
    MvPolynomial (Fin N) ℝ :=
  NPoly.toMv (S.leafPoly T ps)

/-- The leaf exponents along a curve `λ ↦ (ν(λ), d(λ))`. -/
noncomputable def leafS (T : Finset (Fin N)) (ps : List (Fin N × Fin N)) (ν : ℂ → Fin N → ℂ)
    (d : ℂ → ℂ) (l : ℂ) (k : Fin N) : ℂ :=
  leafExp S.D T ps (S.leafMin T ps) (ν l) (d l) k

/-- The continued leaf integral. -/
noncomputable def leafCont (K : ℕ) (T : Finset (Fin N)) (ps : List (Fin N × Fin N))
    (ν : ℂ → Fin N → ℂ) (d : ℂ → ℂ) (l : ℂ) : ℂ :=
  cubeMellinCont K (powFamily (S.leafMv T ps) fun l => d l / 2)
    (S.leafS T ps ν d) l

/-- **The continued Lee–Pomeransky integral** along `λ ↦ (ν(λ), d(λ))`: the sum of the `K`-fold
continuations of all leaf integrals. -/
noncomputable def lpCont (K : ℕ) (ν : ℂ → Fin N → ℂ) (d : ℂ → ℂ) (l : ℂ) : ℂ :=
  ∑ T : Finset (Fin N), ((S.tree T).paths.map fun ps => S.leafCont K T ps ν d l).sum

/-- All leaf exponents at `λ` have real part `> c`. -/
def ReGt (ν : ℂ → Fin N → ℂ) (d : ℂ → ℂ) (c : ℝ) (l : ℂ) : Prop :=
  ∀ T, ∀ ps ∈ (S.tree T).paths, ∀ k, c < (S.leafS T ps ν d l k).re

theorem leafOk_of_mem {T : Finset (Fin N)} {ps : List (Fin N × Fin N)}
    (hps : ps ∈ (S.tree T).paths) :
    leafOk (S.leafMin T ps) ((boxPolyF T S.D S.G).pull ps) = true := by
  have h := S.check T
  simp only [SDCert.check, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 ps hps _ (List.mem_singleton_self _)

theorem valid (T : Finset (Fin N)) : (S.tree T).Valid := by
  have h := S.check T
  simp only [SDCert.check, Bool.and_eq_true] at h
  exact SplitTree.valid_of_validB _ h.1

theorem leafPoly_pos {T : Finset (Fin N)} {ps : List (Fin N × Fin N)}
    (hps : ps ∈ (S.tree T).paths) {y : Fin N → ℝ} (hy : ∀ k, 0 ≤ y k) :
    0 < (S.leafPoly T ps).eval y :=
  zero_lt_one.trans_le (one_le_eval_shift (S.leafOk_of_mem hps) hy)

theorem leafFac {T : Finset (Fin N)} {ps : List (Fin N × Fin N)}
    (hps : ps ∈ (S.tree T).paths) (y : Fin N → ℝ) :
    (boxPolyF T S.D S.G).eval (leafMap ps y) =
      mono (S.leafMin T ps) y * (S.leafPoly T ps).eval y := by
  rw [← NPoly.eval_pull, leafPoly, eval_eq_mono_mul_of_leafOk (S.leafOk_of_mem hps)]

/-- The pulled-back integrand on the box `T`. -/
noncomputable def boxIntegrand (ν : Fin N → ℂ) (d : ℂ) (T : Finset (Fin N)) (y : Fin N → ℝ) :
    ℂ :=
  boxJac T y • lpIntegrand (fun x => S.G.eval x) ν d (boxInv T y)

theorem leafIntegrand_eq {T : Finset (Fin N)} {ps : List (Fin N × Fin N)}
    (hps : ps ∈ (S.tree T).paths) (ν : ℂ → Fin N → ℂ) (d : ℂ → ℂ) (l : ℂ) {y : Fin N → ℝ}
    (hy : y ∈ unitCube N) :
    leafIntegrand (S.boxIntegrand (ν l) (d l) T) ps y =
      cubeWeight (S.leafS T ps ν d l) y *
        powFamily (S.leafMv T ps) (fun l => d l / 2) [] l y := by
  rw [powFamily_nil, leafMv, NPoly.eval_toMv]
  exact leafIntegrand_lp (fun t ht i _ => S.deg t ht i)
    (SplitTree.paths_ne _ (S.valid T) ps hps) (S.leafFac hps) (ν l) (d l) hy
    (S.leafPoly_pos hps fun k => ((mem_unitCube.mp hy) k).1.le)

theorem cubeDerivFamily_leaf {T : Finset (Fin N)} {ps : List (Fin N × Fin N)}
    (hps : ps ∈ (S.tree T).paths) {d : ℂ → ℂ} (hd : Differentiable ℂ d) (U : Set ℂ) :
    CubeDerivFamily (powFamily (S.leafMv T ps) fun l => d l / 2) U :=
  cubeDerivFamily_powFamily (hd.div_const 2) (fun y hy => by
    rw [leafMv, NPoly.eval_toMv]
    exact S.leafPoly_pos hps fun k => ((mem_closedCube.mp hy) k).1) U

theorem differentiable_leafS (T : Finset (Fin N)) (ps : List (Fin N × Fin N))
    {ν : ℂ → Fin N → ℂ} {d : ℂ → ℂ} (hν : ∀ i, Differentiable ℂ fun l => ν l i)
    (hd : Differentiable ℂ d) (k : Fin N) : Differentiable ℂ fun l => S.leafS T ps ν d l k := by
  unfold leafS leafExp boxE
  refine ((differentiable_const _).add (Differentiable.fun_sum fun i _ => ?_)).sub
    ((hd.div_const 2).mul (differentiable_const _))
  split_ifs
  · exact ((((hν i).neg).sub (differentiable_const _)).add
      ((differentiable_const _).mul (hd.div_const 2))).mul (differentiable_const _)
  · exact ((hν i).sub (differentiable_const _)).mul (differentiable_const _)

/-! ### Convergence and the value -/

theorem integrableOn_leaf {T : Finset (Fin N)} {ps : List (Fin N × Fin N)}
    (hps : ps ∈ (S.tree T).paths) {ν : ℂ → Fin N → ℂ} {d : ℂ → ℂ} (hd : Differentiable ℂ d)
    {l : ℂ} (hre : ∀ k, 0 < (S.leafS T ps ν d l k).re) :
    IntegrableOn (leafIntegrand (S.boxIntegrand (ν l) (d l) T) ps) (unitCube N) := by
  have hc' : ContinuousOn (powFamily (S.leafMv T ps) (fun l => d l / 2) [] l) (closedCube N) :=
    continuousOn_powFamily_slice (hd.div_const 2) (fun y hy => by
      rw [leafMv, NPoly.eval_toMv]
      exact S.leafPoly_pos hps fun k => ((mem_closedCube.mp hy) k).1) [] l
  refine (integrableOn_cubeMellin hc' hre).congr_fun (fun y hy => ?_) (measurableSet_unitCube N)
  exact (S.leafIntegrand_eq hps ν d l hy).symm

/-- **Convergence.** Where all leaf exponents have positive real part, the Lee–Pomeransky integral
converges absolutely. -/
theorem lpConvergent_of_re {ν : ℂ → Fin N → ℂ} {d : ℂ → ℂ} (hd : Differentiable ℂ d) {l : ℂ}
    (hre : S.ReGt ν d 0 l) : LPConvergent (fun x => S.G.eval x) (ν l) (d l) := by
  refine (integrableOn_posOrthant_iff_box _).mpr fun T => ?_
  exact SplitTree.integrableOn_of_leaves _ (S.valid T) fun ps hps =>
    S.integrableOn_leaf hps hd (hre T ps hps)

/-- **The integral is the continuation** where all leaf exponents have positive real part. -/
theorem lpIntegral_eq_lpCont (K : ℕ) {ν : ℂ → Fin N → ℂ} {d : ℂ → ℂ}
    (hd : Differentiable ℂ d) {l : ℂ} (hre : S.ReGt ν d 0 l) :
    lpIntegral (fun x => S.G.eval x) (ν l) (d l) = S.lpCont K ν d l := by
  rw [lpIntegral, integral_posOrthant_eq_sum_box (S.lpConvergent_of_re hd hre), lpCont]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hg : IntegrableOn (S.boxIntegrand (ν l) (d l) T) (unitCube N) :=
    SplitTree.integrableOn_of_leaves _ (S.valid T) fun ps hps =>
      S.integrableOn_leaf hps hd (hre T ps hps)
  rw [show (fun y => boxJac T y • lpIntegrand (fun x => S.G.eval x) (ν l) (d l) (boxInv T y)) =
    S.boxIntegrand (ν l) (d l) T from rfl, (SplitTree.integral_eq_sum _ (S.valid T) hg).2]
  congr 1
  refine List.map_congr_left fun ps hps => ?_
  rw [leafCont, cubeMellinCont_eq K (S.cubeDerivFamily_leaf hps hd univ) (mem_univ l)
    (hre T ps hps)]
  exact setIntegral_congr_fun (measurableSet_unitCube N) fun y hy =>
    S.leafIntegrand_eq hps ν d l hy

/-! ### Meromorphy and analyticity -/

theorem meromorphicAt_list_sum {ι : Type*} (L : List ι) {f : ι → ℂ → ℂ} {z : ℂ}
    (h : ∀ i ∈ L, MeromorphicAt (f i) z) :
    MeromorphicAt (fun x => (L.map fun i => f i x).sum) z := by
  induction L with
  | nil => simp [MeromorphicAt.const]
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun i hi => h i (List.mem_cons_of_mem a hi))

theorem analyticAt_list_sum {ι : Type*} (L : List ι) {f : ι → ℂ → ℂ} {z : ℂ}
    (h : ∀ i ∈ L, AnalyticAt ℂ (f i) z) : AnalyticAt ℂ (fun x => (L.map fun i => f i x).sum) z := by
  induction L with
  | nil => simpa using analyticAt_const
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun i hi => h i (List.mem_cons_of_mem a hi))

/-- **Meromorphy** where all leaf exponents have real part `> -K`. -/
theorem meromorphicAt_lpCont (K : ℕ) {ν : ℂ → Fin N → ℂ} {d : ℂ → ℂ}
    (hν : ∀ i, Differentiable ℂ fun l => ν l i) (hd : Differentiable ℂ d) {l₀ : ℂ}
    (hre : S.ReGt ν d (-K) l₀) : MeromorphicAt (S.lpCont K ν d) l₀ := by
  have : S.lpCont K ν d = fun l => ∑ T : Finset (Fin N),
      ((S.tree T).paths.map fun ps => S.leafCont K T ps ν d l).sum := rfl
  rw [this]
  refine MeromorphicAt.fun_sum fun T _ => meromorphicAt_list_sum _ fun ps hps => ?_
  exact meromorphicAt_cubeMellinCont K isOpen_univ (S.cubeDerivFamily_leaf hps hd univ)
    (fun k => (S.differentiable_leafS T ps hν hd k).differentiableOn) (mem_univ l₀)
    (hre T ps hps)

/-- **Analyticity** where all leaf exponents have real part `> -K` and none lies in
`{0, -1, -2, …}`. -/
theorem analyticAt_lpCont (K : ℕ) {ν : ℂ → Fin N → ℂ} {d : ℂ → ℂ}
    (hν : ∀ i, Differentiable ℂ fun l => ν l i) (hd : Differentiable ℂ d) {l₀ : ℂ}
    (hre : S.ReGt ν d (-K) l₀)
    (hpole : ∀ T, ∀ ps ∈ (S.tree T).paths, ∀ k, ∀ j : ℕ, S.leafS T ps ν d l₀ k + j ≠ 0) :
    AnalyticAt ℂ (S.lpCont K ν d) l₀ := by
  have : S.lpCont K ν d = fun l => ∑ T : Finset (Fin N),
      ((S.tree T).paths.map fun ps => S.leafCont K T ps ν d l).sum := rfl
  rw [this]
  refine Finset.analyticAt_fun_sum _ fun T _ => analyticAt_list_sum _ fun ps hps => ?_
  exact analyticAt_cubeMellinCont K isOpen_univ (S.cubeDerivFamily_leaf hps hd univ)
    (fun k => (S.differentiable_leafS T ps hν hd k).differentiableOn) (mem_univ l₀)
    (hre T ps hps) (hpole T ps hps)

end LPSectorData

end QED.DimReg
