/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecUForm
public import QED.ChainProof.SetASpecOne

/-!
# Set (a): one-loop pieces have the uniform spectral tensor form

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
The `ε`-uniform copy of `QED.ChainProof.SetASpec.SAJ1`, `saj1_five` and `saj1_four`.

* `saUCoef_auxInv`: for an auxiliary mass `M_a > 0` with `M_a² ≥ 2` the inverse auxiliary loop
  `1 / EFI((ℓ² + M_a² - iε)⁻³)` is a uniform coefficient: `ε ↦ ∫ auxSpatial M_a ε` is continuous
  on `[0, 1]` (dominated convergence), and it does not vanish there (`setASpec_aux_ne_zero`,
  `auxLimit_ne_zero`).
* `SAUJ1 M_lo F`: one-loop families integrable at every `ε > 0` whose energy-first integrals are
  `SAUForm M_lo`.
* **`saUj1_five`**: five lines at `q` or `k + q`, both present; the auxiliary mass is frozen at
  `M_a = M_lo + 2` (independent of `ε`, `2 ε ≤ M_a²` for `ε ≤ 1`).
* **`saUj1_four`**: four lines, padded to five.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.VP2
open QED.Integration.Feynman (simplexSet)

/-! ### The inverse auxiliary loop -/

theorem saU_continuousOn_auxSpatial {M : ℝ} (hM : 0 < M) (v : Fin 3 → ℝ) :
    ContinuousOn (fun ε => auxSpatial M ε v) (Icc 0 1) := by
  intro ε hε
  rcases eq_or_lt_of_le hε.1 with h0 | h0
  · subst h0
    have h := (tendsto_auxSpatial hM v : ContinuousWithinAt (fun ε => auxSpatial M ε v) (Ioi 0) 0)
    exact (continuousWithinAt_Ioi_iff_Ici.mp h).mono Icc_subset_Ici_self
  · refine ContinuousAt.continuousWithinAt ?_
    unfold auxSpatial
    exact ((ContinuousAt.cpow (f := fun ε : ℝ =>
      -((((∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - (ε : ℂ) * I)) (by fun_prop) continuousAt_const
      (neg_aux_mem_slitPlane h0 v)).const_mul _).neg

theorem saU_efi_aux_eq (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    QED.OneLoop.energyFirstIntegral (fun k => ((propDenom M ε k)⁻¹) ^ 3) =
      ∫ v, auxSpatial M ε v := by
  unfold QED.OneLoop.energyFirstIntegral
  exact integral_congr_ae (Eventually.of_forall fun v => integral_aux_time M hε v)

/-- **The inverse auxiliary loop is a uniform coefficient** when `M_a² ≥ 2`. -/
theorem saUCoef_auxInv {M : ℝ} (hM : 0 < M) (h2 : 2 ≤ M ^ 2) :
    SAUCoef fun ε => (QED.OneLoop.energyFirstIntegral fun k => ((propDenom M ε k)⁻¹) ^ 3)⁻¹ := by
  have hbnd : Integrable fun v : Fin 3 → ℝ =>
      3 * π / 8 * (∑ k, v k ^ 2 + M ^ 2) ^ (-(5 / 2 : ℝ)) :=
    (QED.Integration.integrable_sum_sq_add_rpow (by positivity) (by norm_num)).const_mul _
  have hG : ContinuousOn (fun ε => ∫ v, auxSpatial M ε v) (Icc 0 1) :=
    continuousOn_of_dominated
      (fun ε _ => (by unfold auxSpatial; fun_prop :
        Measurable (auxSpatial M ε)).aestronglyMeasurable)
      (fun ε _ => Eventually.of_forall fun v => norm_auxSpatial_le hM ε v) hbnd
      (Eventually.of_forall fun v => saU_continuousOn_auxSpatial hM v)
  have hne : ∀ ε ∈ Icc (0 : ℝ) 1, (∫ v, auxSpatial M ε v) ≠ 0 := by
    intro ε hε
    rcases eq_or_lt_of_le hε.1 with h0 | h0
    · subst h0
      exact auxLimit_ne_zero hM
    · rw [← saU_efi_aux_eq M h0]
      exact setASpec_aux_ne_zero hM h0 (by nlinarith [hε.2])
  exact SAUCoef.of_continuousOn (hG.inv₀ hne) fun ε h0 _ => by rw [saU_efi_aux_eq M h0]; rfl

/-! ### One-loop families -/

/-- **One-loop families with the uniform spectral tensor form.** -/
def SAUJ1 (Mlo : ℝ) (F : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∀ k i j, EF fun q => F ε k q i j) ∧
    SAUForm Mlo fun ε k i j => QED.OneLoop.energyFirstIntegral fun q => F ε k q i j

namespace SAUJ1

variable {Mlo : ℝ} {F G : ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hF : SAUJ1 Mlo F) (hG : SAUJ1 Mlo G) :
    SAUJ1 Mlo fun ε k q i j => F ε k q i j + G ε k q i j := by
  refine ⟨fun ε hε k i j => (hF.1 ε hε k i j).add (hG.1 ε hε k i j),
    (hF.2.add hG.2).congr fun ε hε _ k i j => ?_⟩
  rw [efi_add (hF.1 ε hε k i j) (hG.1 ε hε k i j)]

theorem mul (hF : SAUJ1 Mlo F) {c : ℝ → ℂ} (hc : SAUCoef c) :
    SAUJ1 Mlo fun ε k q i j => c ε * F ε k q i j := by
  refine ⟨fun ε hε k i j => (hF.1 ε hε k i j).const_mul (c ε), (hF.2.mul hc).congr
    fun ε _ _ k i j => ?_⟩
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]

theorem const_mul (hF : SAUJ1 Mlo F) (c : ℂ) : SAUJ1 Mlo fun ε k q i j => c * F ε k q i j :=
  hF.mul (SAUCoef.const c)

theorem congr (hF : SAUJ1 Mlo F) (e : ∀ ε : ℝ, 0 < ε → ∀ k q i j, F ε k q i j = G ε k q i j) :
    SAUJ1 Mlo G := by
  refine ⟨fun ε hε k i j => (hF.1 ε hε k i j).congr (e ε hε k · i j),
    hF.2.congr fun ε hε _ k i j => ?_⟩
  rw [show (fun q => F ε k q i j) = fun q => G ε k q i j from funext (e ε hε k · i j)]

theorem zero : SAUJ1 Mlo fun _ _ _ _ _ => 0 := by
  refine ⟨fun _ _ _ _ _ => EF.zero, SAUForm.zero.congr fun ε _ _ k i j => ?_⟩
  simp [QED.OneLoop.energyFirstIntegral]

theorem sum {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hF : ∀ a ∈ s, SAUJ1 Mlo (F a)) : SAUJ1 Mlo fun ε k q i j => ∑ a ∈ s, F a ε k q i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : SAUJ1 Mlo fun _ _ _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

end SAUJ1

/-! ### Five and four lines -/

section Pieces

variable {Mlo : ℝ} (hMlo0 : 0 ≤ Mlo)
include hMlo0

/-- **Five lines at `q` or `k + q`**, both present, with a covariant numerator of degree four;
the auxiliary mass is `M_lo + 2`. -/
theorem saUj1_five (Ms : Fin 5 → ℝ) (hMs : ∀ i, Mlo ≤ Ms i) (b : Fin 5 → Bool)
    (hb : ∃ l l', b l ≠ b l') (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 4 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    (hK : SAPolyK1 4 N) :
    SAUJ1 Mlo fun ε k q i j => N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹ := by
  set Ma : ℝ := Mlo + 2 with hMa
  have hMa0 : 0 < Ma := by positivity
  have hMa2 : 2 ≤ Ma ^ 2 := by nlinarith
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
  have h := saUj_piece saBase5 saC5 ![-1 / 2, 0] ![-1 / 2, 0] saFlow5 (Or.inr rfl) (saSh5 b) Ms8
    (saCrit5 b) (fun k ℓ i j => N k (ℓ 0) i j) hN hB (fun L S S' hL k ℓ => hcov L S S' hL k (ℓ 0))
    (fun lam δ μ ν => hK (lam 0) (δ 0) μ ν) hc hMlo0 hMlo8
  have hfac : ∀ ε k (ℓ : Fin 2 → Fin 4 → ℝ) i j, N k (ℓ 0) i j * ∏ l : Fin 8,
      (propDenom (Ms8 l) ε
        (lineMomentum (castLoopMatrix saBase5) (fun r => saC5 r • k) (saSh5 b l) ℓ))⁻¹ =
      (N k (ℓ 0) i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) (ℓ 0)))⁻¹) *
        ((propDenom Ma ε (ℓ 1))⁻¹) ^ 3 := fun ε k ℓ i j => by
    rw [Fin.prod_univ_eight, Fin.prod_univ_five]
    simp only [saSh5, hMs8, Matrix.cons_val, saLm5, saLmAux]
    ring
  refine ⟨fun ε hε k i j => ef_piece5 b Ms hε k _ (hN k i j),
    (h.2.mul (saUCoef_auxInv hMa0 hMa2)).congr fun ε hε hε1 k i j => ?_⟩
  have hA := setASpec_aux_ne_zero hMa0 hε (by nlinarith)
  simp only [hfac]
  rw [jointEnergyFirstIntegral_two_mul
    (fun q => N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹)
    (fun q => ((propDenom Ma ε q)⁻¹) ^ 3)]
  generalize (QED.OneLoop.energyFirstIntegral fun q => ((propDenom Ma ε q)⁻¹) ^ 3) = A at hA ⊢
  generalize (QED.OneLoop.energyFirstIntegral fun q =>
    N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹) = X
  field_simp

/-- **Four lines**, padded to five with a numerator of degree two. -/
theorem saUj1_four (Ms : Fin 4 → ℝ) (hMs : ∀ i, Mlo ≤ Ms i) (b : Fin 4 → Bool)
    (hb : ∃ l l', b l ≠ b l') (N : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hN : ∀ p i j, IsLoopPoly 2 2 fun ℓ => N p (ℓ 0) i j) (hcov : TCovN N)
    (hK : SAPolyK1 2 N) :
    SAUJ1 Mlo fun ε k q i j => N k q i j * ∏ l, (propDenom (Ms l) ε (zk k (b l) q))⁻¹ := by
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
  have A := saUj1_five hMlo0 Ms' hMs1 b' hb1 N' hN1 (hcov.mul_propDenom _ _ _)
    (hK.mul_propDenom _ _ _)
  have B := (saUj1_five hMlo0 Ms' hMs1 b' hb1 N hN4 hcov (hK.mono (by norm_num))).mul
    (SAUCoef.of_continuous (c := fun ε : ℝ => -(ε : ℂ) * I) (by fun_prop))
  refine (A.add B).congr fun ε hε k q i j => ?_
  have hd := propDenom_ne_zero (M := Ms 0) hε.ne' (zk k (b 0) q)
  have h0 : propDenom (Ms 0) 0 (zk k (b 0) q) = propDenom (Ms 0) ε (zk k (b 0) q) + ε * I := by
    simp only [propDenom]; push_cast; ring
  simp only [hMs', hb', prod_five_cons, hN', h0]
  field_simp
  ring

end Pieces

end QED.ChainProof.SetASpec

end
