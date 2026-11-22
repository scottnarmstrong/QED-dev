/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecPieceJ
public import QED.ChainProof.SetASpecAux
public import QED.GradedProof.VP2Kinds
public import QED.Integration.SimplexMerge

/-!
# Set (a): one-loop pieces have the spectral tensor form

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
The one-loop analogue of `QED.ChainProof.SetASpec.saj_piece`, for the inserted bubbles `F0`, `F1`.

* `SAJ1 M_lo F`: at every `ε > 0` the one-loop family `F ε k q μ ν` is integrable in both stages
  (`QED.GradedProof.VP2.EF`) and its energy-first integral is `SAForm M_lo ε`; closed under sums,
  multiplication by functions of `ε` and pointwise equality.
* `SAPolyK1 d N`: `k ↦ N_k(λ k + δ)` has degree at most `d`.
* **`saj1_five`**: a covariant numerator of degree four over five lines at `q` or `k + q`, with
  both momenta present, is `SAJ1`. At fixed `ε` the integrand times the auxiliary loop
  `(ℓ₁² + M_a² - iε)⁻³`, `M_a = M_lo + 1 + ε`, is a two-loop piece with eight lines
  (`saj_piece`), whose joint integral is the product of the two one-loop integrals; the
  auxiliary loop is not zero (`setASpec_aux_ne_zero`, `2 ε ≤ M_a²`).
* **`saj1_four`**: four lines, padded to five (`D = D⁰ - iε`).
* **`saForm_const`**: a covariant polynomial tensor `C(k)` times a constant is `SAForm`
  (spectral terms with `r = 0` over the simplex of dimension one, `saIntegral_simplexOne`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.VP2
open QED.Integration.Feynman (simplexSet)
open QED.GradedProof.RPi4 (gkTensor)

/-! ### One-loop families -/

/-- **One-loop families with the spectral tensor form at every `ε > 0`.** -/
def SAJ1 (Mlo : ℝ) (F : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → (∀ k i j, EF fun q => F ε k q i j) ∧
    SAForm Mlo ε fun k i j => QED.OneLoop.energyFirstIntegral fun q => F ε k q i j

namespace SAJ1

variable {Mlo : ℝ} {F G : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hF : SAJ1 Mlo F) (hG : SAJ1 Mlo G) :
    SAJ1 Mlo fun ε k q i j => F ε k q i j + G ε k q i j := by
  intro ε hε
  obtain ⟨hFi, hFf⟩ := hF ε hε
  obtain ⟨hGi, hGf⟩ := hG ε hε
  refine ⟨fun k i j => (hFi k i j).add (hGi k i j), (hFf.add hGf).congr fun k i j => ?_⟩
  rw [efi_add (hFi k i j) (hGi k i j)]

theorem mul (hF : SAJ1 Mlo F) (c : ℝ → ℂ) : SAJ1 Mlo fun ε k q i j => c ε * F ε k q i j := by
  intro ε hε
  obtain ⟨hFi, hFf⟩ := hF ε hε
  refine ⟨fun k i j => (hFi k i j).const_mul (c ε), (hFf.const_mul (c ε)).congr
    fun k i j => ?_⟩
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]

theorem const_mul (hF : SAJ1 Mlo F) (c : ℂ) : SAJ1 Mlo fun ε k q i j => c * F ε k q i j :=
  hF.mul fun _ => c

theorem congr (hF : SAJ1 Mlo F) (e : ∀ ε : ℝ, 0 < ε → ∀ k q i j, F ε k q i j = G ε k q i j) :
    SAJ1 Mlo G := by
  intro ε hε
  obtain ⟨hFi, hFf⟩ := hF ε hε
  refine ⟨fun k i j => (hFi k i j).congr (e ε hε k · i j), hFf.congr fun k i j => ?_⟩
  rw [show (fun q => F ε k q i j) = fun q => G ε k q i j from funext (e ε hε k · i j)]

theorem zero : SAJ1 Mlo fun _ _ _ _ _ => 0 := by
  intro ε _
  refine ⟨fun _ _ _ => EF.zero, SAForm.zero.congr fun k i j => ?_⟩
  simp [QED.OneLoop.energyFirstIntegral]

theorem sum {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hF : ∀ a ∈ s, SAJ1 Mlo (F a)) : SAJ1 Mlo fun ε k q i j => ∑ a ∈ s, F a ε k q i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : SAJ1 Mlo fun _ _ _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

end SAJ1

/-- **Polynomial along affine loop momenta (one loop)**: `k ↦ N_k(λ k + δ)` has degree `≤ d`. -/
def SAPolyK1 (d : ℕ) (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ (lam : ℝ) (δ : Fin 4 → ℝ) (μ ν : Fin 4),
    IsLoopPoly 1 d fun y => N (y 0) (lam • y 0 + δ) μ ν

theorem SAPolyK1.mono {d d' : ℕ} {N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : SAPolyK1 d N) (hd : d ≤ d') : SAPolyK1 d' N :=
  fun lam δ μ ν => (h lam δ μ ν).mono hd

/-- `y ↦ zk y c (λ y + δ)` is affine. -/
theorem saAffine_zk (c : Bool) (lam : ℝ) (δ : Fin 4 → ℝ) :
    IsLoopAffine fun y : Fin 1 → Fin 4 → ℝ => zk (y 0) c (lam • y 0 + δ) := by
  refine ⟨![if c then 1 + lam else lam], δ, fun y => ?_⟩
  cases c <;> funext μ <;> simp [zk]; ring

theorem SAPolyK1.mul_propDenom {d : ℕ} {N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : SAPolyK1 d N) (M ε : ℝ) (c : Bool) :
    SAPolyK1 (d + 2) fun k q i j => N k q i j * propDenom M ε (zk k c q) :=
  fun lam δ μ ν => (h lam δ μ ν).mul ((saAffine_zk c lam δ).isLoopPoly_propDenom M ε)

/-! ### The eight-line data of a five-line piece -/

/-- The rows: `q` (`0`), `k + q` (`1`), the auxiliary loop (`2`), unused (`3`, `4`). -/
def saBase5 : Fin 5 → Fin 2 → ℤ := ![![1, 0], ![1, 0], ![0, 1], ![1, 0], ![0, 0]]

/-- The external coefficients of the rows. -/
def saC5 : Fin 5 → ℝ := ![0, 1, 0, 0, 0]

/-- The row of a line at `zk k c q`. -/
def saRow (c : Bool) : Fin 5 := if c then 1 else 0

/-- The shape: five lines at `q` or `k + q`, three auxiliary lines. -/
def saSh5 (b : Fin 5 → Bool) : Fin 8 → Fin 5 :=
  ![saRow (b 0), saRow (b 1), saRow (b 2), saRow (b 3), saRow (b 4), 2, 2, 2]

theorem saFlow5 (j : Fin 5) :
    |∑ s, (saBase5 j s : ℝ) * (![-1 / 2, 0] : Fin 2 → ℝ) s + saC5 j| +
      |∑ s, (saBase5 j s : ℝ) * (![-1 / 2, 0] : Fin 2 → ℝ) s + saC5 j| ≤
      if j = 4 then 0 else 1 := by
  fin_cases j <;> norm_num [saBase5, saC5, Fin.sum_univ_two, abs_of_neg, abs_of_pos]

theorem saCrit5 : ∀ b : Fin 5 → Bool,
    IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => saBase5 (saSh5 b i) := by
  decide

theorem saBase5_row (c : Bool) : saBase5 (saRow c) = ![1, 0] := by
  cases c <;> rfl

theorem saLin5 (c : Bool) (y : Fin 2 → ℝ) :
    ∑ s, (saBase5 (saRow c) s : ℝ) * y s + saC5 (saRow c) = y 0 + if c then 1 else 0 := by
  cases c <;> simp [saBase5, saRow, saC5, Fin.sum_univ_two]

theorem saLm5 (c : Bool) (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (castLoopMatrix saBase5) (fun r => saC5 r • k) (saRow c) ℓ = zk k c (ℓ 0) := by
  cases c <;> funext μ <;>
    simp [lineMomentum, castLoopMatrix, saBase5, saRow, saC5, zk, Fin.sum_univ_two]; ring

theorem saLmAux (k : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (castLoopMatrix saBase5) (fun r => saC5 r • k) 2 ℓ = ℓ 1 := by
  funext μ
  simp [lineMomentum, castLoopMatrix, saBase5, saC5, Fin.sum_univ_two]

theorem saSh5_cast (b : Fin 5 → Bool) (l : Fin 5) :
    saSh5 b ⟨l.val, by omega⟩ = saRow (b l) := by
  fin_cases l <;> rfl

/-! ### Five and four lines -/

section Pieces

variable {Mlo : ℝ} (hMlo0 : 0 ≤ Mlo)
include hMlo0

/-- **Five lines at `q` or `k + q`**, both present, with a covariant numerator of degree four. -/
theorem saj1_five (Ms : Fin 5 → ℝ) (hMs : ∀ i, Mlo ≤ Ms i) (b : Fin 5 → Bool)
    (hb : ∃ l l', b l ≠ b l') (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    (hK : SAPolyK1 4 N) :
    SAJ1 Mlo fun ε k q i j => N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹ := by
  intro ε hε
  set Ma : ℝ := Mlo + 1 + ε with hMa
  have hMa0 : 0 < Ma := by positivity
  have hMa2 : 2 * ε ≤ Ma ^ 2 := by nlinarith
  set Ms8 : Fin 8 → ℝ := ![Ms 0, Ms 1, Ms 2, Ms 3, Ms 4, Ma, Ma, Ma] with hMs8
  have hα : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin 8)),
      castLoopMatrix (fun i => saBase5 (saSh5 b i)) e = ![1, 0] := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> funext s <;> fin_cases s <;>
      simp [castLoopMatrix, saSh5, saBase5_row]
  have hB : ∀ k i j, RefinedBound (castLoopMatrix fun i => saBase5 (saSh5 b i)) {0, 1, 2, 3} 4
      fun ℓ => N k (ℓ 0) i j := fun k i j => by
    obtain ⟨Q, hQ⟩ := (hN k i j).exists_loopQuartic
    have h := refinedBound_of_dependsOnZero _ (by decide) hα Q fun ℓ => by
      simp only [hQ, Matrix.cons_val_zero]
    rwa [hQ] at h
  have hc : ∀ y : Fin 2 → ℝ, ∃ i : Fin 8,
      ∑ s, (saBase5 (saSh5 b i) s : ℝ) * y s + saC5 (saSh5 b i) ≠ 0 := by
    intro y
    obtain ⟨l, l', hl⟩ := hb
    have ex : ∀ c : Bool, ∃ m, b m = c := fun c => by
      cases h : b l <;> cases h' : b l' <;> cases c <;> simp_all <;> first
        | exact ⟨l, h⟩ | exact ⟨l', h'⟩
    by_cases hy : y 0 = 0
    · obtain ⟨m, hm⟩ := ex true
      exact ⟨⟨m.val, by omega⟩, by rw [saSh5_cast, saLin5, hm, hy]; norm_num⟩
    · obtain ⟨m, hm⟩ := ex false
      exact ⟨⟨m.val, by omega⟩, by rw [saSh5_cast, saLin5, hm]; simpa using hy⟩
  have hMlo8 : ∀ i, Mlo ≤ Ms8 i := fun i => by
    fin_cases i <;> simp [hMs8, hMs] <;> linarith
  have h := saj_piece saBase5 saC5 ![-1 / 2, 0] ![-1 / 2, 0] saFlow5 (Or.inr rfl) (saSh5 b) Ms8
    (saCrit5 b) (fun k ℓ i j => N k (ℓ 0) i j) hN hB (fun L S S' hL k ℓ => hcov L S S' hL k (ℓ 0))
    (fun lam δ μ ν => hK (lam 0) (δ 0) μ ν) hc hMlo0 hMlo8
  obtain ⟨-, hform⟩ := h ε hε
  have hfac : ∀ k (ℓ : Fin 2 → Fin 4 → ℝ) i j, N k (ℓ 0) i j * ∏ l : Fin 8, (propDenom (Ms8 l) ε
      (lineMomentum (castLoopMatrix saBase5) (fun r => saC5 r • k) (saSh5 b l) ℓ))⁻¹ =
      (N k (ℓ 0) i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) (ℓ 0)))⁻¹) *
        ((propDenom Ma ε (ℓ 1))⁻¹) ^ 3 := fun k ℓ i j => by
    rw [Fin.prod_univ_eight, Fin.prod_univ_five]
    simp only [saSh5, hMs8, Matrix.cons_val, saLm5, saLmAux]
    ring
  have hA := setASpec_aux_ne_zero hMa0 hε hMa2
  refine ⟨fun k i j => ef_piece5 b Ms hε k _ (hN k i j), (hform.const_mul
    (QED.OneLoop.energyFirstIntegral fun q => ((propDenom Ma ε q)⁻¹) ^ 3)⁻¹).congr
      fun k i j => ?_⟩
  simp only [hfac]
  rw [jointEnergyFirstIntegral_two_mul
    (fun q => N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹)
    (fun q => ((propDenom Ma ε q)⁻¹) ^ 3)]
  generalize (QED.OneLoop.energyFirstIntegral fun q => ((propDenom Ma ε q)⁻¹) ^ 3) = A at hA ⊢
  generalize (QED.OneLoop.energyFirstIntegral fun q =>
    N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹) = X
  field_simp

/-- **Four lines**, padded to five with a numerator of degree two. -/
theorem saj1_four (Ms : Fin 4 → ℝ) (hMs : ∀ i, Mlo ≤ Ms i) (b : Fin 4 → Bool)
    (hb : ∃ l l', b l ≠ b l') (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 2 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    (hK : SAPolyK1 2 N) :
    SAJ1 Mlo fun ε k q i j => N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹ := by
  set Ms' : Fin 5 → ℝ := Fin.cons (Ms 0) Ms with hMs'
  set b' : Fin 5 → Bool := Fin.cons (b 0) b with hb'
  have hMs1 : ∀ i, Mlo ≤ Ms' i := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hMs 0
    · simp only [hMs', Fin.cons_succ]; exact hMs j
  have hb1 : ∃ l l', b' l ≠ b' l' := by
    obtain ⟨l, l', h⟩ := hb
    exact ⟨l.succ, l'.succ, by simpa [hb'] using h⟩
  set N' : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
    fun k q i j => N k q i j * propDenom (Ms 0) 0 (zk k (b 0) q) with hN'
  have hN1 : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N' p (ℓ 0) i j := fun p i j =>
    (hN p i j).mul ((isLoopAffine_zk p (b 0)).isLoopPoly_propDenom (Ms 0) 0)
  have hN4 : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j := fun p i j =>
    (hN p i j).mono (by norm_num)
  have A := saj1_five hMlo0 Ms' hMs1 b' hb1 N' hN1 (hcov.mul_propDenom _ _ _)
    (hK.mul_propDenom _ _ _)
  have B := (saj1_five hMlo0 Ms' hMs1 b' hb1 N hN4 hcov (hK.mono (by norm_num))).mul
    fun ε => -(ε : ℂ) * I
  refine (A.add B).congr fun ε hε k q i j => ?_
  have hd := propDenom_ne_zero (M := Ms 0) hε.ne' (zk k (b 0) q)
  have h0 : propDenom (Ms 0) 0 (zk k (b 0) q) = propDenom (Ms 0) ε (zk k (b 0) q) + ε * I := by
    simp only [propDenom]; push_cast; ring
  simp only [hMs', hb', prod_five_cons, hN', h0]
  field_simp
  ring

end Pieces

/-! ### Constant pieces -/

/-- The simplex of dimension one is the unit interval. -/
theorem saSimplexOne :
    simplexSet 1 = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Icc (0 : ℝ) 1 := by
  ext x
  rw [QED.Integration.SimplexMerge.mem_simplexSet_iff_le one_pos]
  simp [MeasurableEquiv.funUnique]

/-- **An integral over the simplex of dimension one** is an interval integral. -/
theorem saIntegral_simplexOne (h : ℝ → ℂ) :
    ∫ x in simplexSet 1, h (x 0) = ∫ t in (0 : ℝ)..1, h t := by
  rw [saSimplexOne, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding h _

/-- The integral of a constant over the simplex of dimension one. -/
theorem saIntegral_simplexOne_const (c : ℂ) : ∫ _ in simplexSet 1, c = c := by
  rw [saIntegral_simplexOne (fun _ => c), intervalIntegral.integral_const]
  simp

theorem SACov.mul_const {C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (h : SACov C) (G : ℂ) :
    SACov fun k μ ν => C k μ ν * G := fun a ha k => by
  funext μ ν
  show C (QED.Dirac.reflect a k) μ ν * G = _
  rw [h a ha k]
  simp only [QED.GradedProof.VP2.rAct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **A covariant polynomial tensor times a constant** is `SAForm`. -/
theorem saForm_const {C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (hcov : SACov C)
    (hpoly : ∀ μ ν, IsLoopPoly 1 4 fun y => C (y 0) μ ν) (G : ℂ) {ε : ℝ} (hε : 0 < ε)
    (Mlo : ℝ) : SAForm Mlo ε fun k μ ν => C k μ ν * G := by
  set Cf : (Fin 1 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ := fun _ k μ ν => C k μ ν * G
  have hvol : volume (simplexSet 1) < ⊤ :=
    (QED.Integration.Feynman.isCompact_simplexSet 1).measure_lt_top
  have hI : ∀ k μ ν, IntegrableOn (fun x => Cf x k μ ν) (simplexSet 1) :=
    fun k μ ν => integrableOn_const hvol.ne
  have hC : ∀ x k μ ν, Cf x k μ ν = gkTensor (saXq (Cf x) (Minkowski.dot k k))
      (saYq (Cf x) (Minkowski.dot k k)) k μ ν := fun x k μ ν =>
    (hcov.mul_const G).eq_gk (fun μ ν => (hpoly μ ν).mul (IsLoopPoly.const (n := 0) G)) k μ ν
  refine ⟨saTerms5 Cf 0 (fun _ => Mlo) (fun _ => 1 / 2),
    saTerms5_good _ _ _ measurable_const measurable_const hI
      (Eventually.of_forall fun _ => ⟨le_rfl, by norm_num, by norm_num⟩), fun k μ ν => ?_⟩
  rw [← saTerms5_integral rfl hε 0 _ _ measurable_const measurable_const hI hC k μ ν]
  simp only [pow_zero, inv_one, mul_one, Cf]
  exact (saIntegral_simplexOne_const _).symm

end QED.ChainProof.SetASpec

end
