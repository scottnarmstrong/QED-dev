/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecCoeff
public import QED.ChainProof.SetASpecPiece

/-!
# Set (a): the spectral tensor form `T★` at fixed `ε`

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
The form in which the fixed-`ε` two-loop vacuum polarization enters the outer vertex integral: a
finite sum of **spectral terms** (`SATerm`)

`t(k)^{μν} (k²)ʲ ∫_Δ w(x) fDen(M(x), ε, ξ(x), k)^{-r}`,

`t = g` or `k k` (`saTens`), with an integrable weight `w`, a mass `M ≥ M_lo`, a Feynman parameter
`ξ ∈ (0, 1)` almost everywhere, and `j + [t = k k] ≤ 2` (`SATerm.Good`). Each term is, after the
outer contraction, the integrand `QED.TwoLoop.VPHalfAtGen.specInt` of the spectral engine
`QED.ChainProof.SetASpec.setASpec_exists_good_specPow` with `Msp = M(x)`, `ξ = ξ(x)` and `j`
(resp. `j + 1` for `k k`, which contracts to one more `k²`), `j ≤ 2`, `r` unrestricted.

* `SAForm M_lo ε W`: `W` is such a finite sum, for every `k, μ, ν`; closed under sums and
  constant multiples.
* `SAJ M_lo F`: at every `ε > 0` the two-loop family `F ε k ℓ μ ν` is integrable in both stages
  and its joint integral is `SAForm`; closed under sums, multiplication by functions of `ε` and
  pointwise equality (the fixed-`ε` analogue of `QED.GradedProof.VP2.VPJ`).
* `saTerms5`: a covariant coefficient family `X(k²) g + Y(k²) k k` against `fDen^{-r}` is five
  terms (`saTerms5_integral`).
* **`setASpec_pieceSpec_form`**: the spectral form `-π⁴ ∫ saPieceSpec` of one piece with a
  covariant numerator, polynomial along affine loop momenta, is `SAForm`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.VPHalfAtAssembly
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.GradedProof.RPi4 (gkTensor)
open QED.GradedProof.VP2 (TCov2)

/-- The two tensor structures: `g^{μν}` (`false`) and `k^μ k^ν` (`true`). -/
noncomputable def saTens : Bool → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ
  | false, _, μ, ν => ((Minkowski.metric μ ν : ℝ) : ℂ)
  | true, k, μ, ν => ((k μ * k ν : ℝ) : ℂ)

/-- **A spectral term** `t(k) (k²)ʲ ∫_Δ w fDen(M, ε, ξ, k)^{-r}` over the simplex of dimension
`m`. -/
structure SATerm where
  /-- The simplex dimension. -/
  m : ℕ
  /-- The power of `k²`. -/
  j : ℕ
  /-- The power of the photon-type factor. -/
  r : ℕ
  /-- The tensor structure. -/
  t : Bool
  /-- The weight. -/
  w : (Fin m → ℝ) → ℂ
  /-- The mass of the factor. -/
  mass : (Fin m → ℝ) → ℝ
  /-- The Feynman parameter of the factor. -/
  xi : (Fin m → ℝ) → ℝ

namespace SATerm

/-- The value of a term at `ε`, `k`, `(μ, ν)`. -/
noncomputable def val (τ : SATerm) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  saTens τ.t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ τ.j *
    ∫ x in simplexSet τ.m, τ.w x * (fDen (τ.mass x) ε (τ.xi x) k ^ τ.r)⁻¹

/-- The hypotheses of the spectral engine on a term. -/
def Good (Mlo : ℝ) (τ : SATerm) : Prop :=
  IntegrableOn τ.w (simplexSet τ.m) ∧ Measurable τ.mass ∧ Measurable τ.xi ∧
    (∀ᵐ x ∂(volume.restrict (simplexSet τ.m)), Mlo ≤ τ.mass x ∧ τ.xi x ∈ Ioo (0 : ℝ) 1) ∧
    τ.j + (if τ.t then 1 else 0) ≤ 2

/-- A constant multiple of the weight. -/
noncomputable def smul (c : ℂ) (τ : SATerm) : SATerm :=
  { τ with w := fun x => c * τ.w x }

theorem val_smul (c : ℂ) (τ : SATerm) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    (τ.smul c).val ε k μ ν = c * τ.val ε k μ ν := by
  obtain ⟨m, j, r, t, w, mass, xi⟩ := τ
  simp only [val, smul]
  have h : ∀ (f g : (Fin m → ℝ) → ℂ), ∫ x in simplexSet m, c * f x * g x =
      c * ∫ x in simplexSet m, f x * g x := fun f g => by
    rw [← integral_const_mul]
    simp only [mul_assoc]
  show saTens t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j *
      ∫ x in simplexSet m, c * w x * (fDen (mass x) ε (xi x) k ^ r)⁻¹ =
    c * (saTens t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j *
      ∫ x in simplexSet m, w x * (fDen (mass x) ε (xi x) k ^ r)⁻¹)
  rw [h]
  ring

theorem Good.smul {Mlo : ℝ} {τ : SATerm} (h : τ.Good Mlo) (c : ℂ) : (τ.smul c).Good Mlo :=
  ⟨h.1.const_mul c, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end SATerm

/-- **The spectral tensor form at `ε`**: `W` is a finite sum of good spectral terms. -/
def SAForm (Mlo ε : ℝ) (W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∃ l : List SATerm, (∀ τ ∈ l, τ.Good Mlo) ∧
    ∀ k μ ν, W k μ ν = (l.map fun τ => τ.val ε k μ ν).sum

namespace SAForm

variable {Mlo ε : ℝ} {W V : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem zero : SAForm Mlo ε fun _ _ _ => 0 := ⟨[], by simp, by simp⟩

theorem add (hW : SAForm Mlo ε W) (hV : SAForm Mlo ε V) :
    SAForm Mlo ε fun k μ ν => W k μ ν + V k μ ν := by
  obtain ⟨l, hl, hW⟩ := hW
  obtain ⟨l', hl', hV⟩ := hV
  refine ⟨l ++ l', fun τ hτ => ?_, fun k μ ν => by simp [hW, hV]⟩
  rcases List.mem_append.mp hτ with h | h
  exacts [hl τ h, hl' τ h]

theorem const_mul (c : ℂ) (hW : SAForm Mlo ε W) : SAForm Mlo ε fun k μ ν => c * W k μ ν := by
  obtain ⟨l, hl, hW⟩ := hW
  refine ⟨l.map (SATerm.smul c), fun τ hτ => ?_, fun k μ ν => ?_⟩
  · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ
    exact (hl σ hσ).smul c
  · show c * W k μ ν = _
    rw [hW, List.map_map, ← List.sum_map_mul_left]
    congr 1
    exact List.map_congr_left fun τ _ => (SATerm.val_smul c τ ε k μ ν).symm

theorem congr (hW : SAForm Mlo ε W) (h : ∀ k μ ν, W k μ ν = V k μ ν) : SAForm Mlo ε V := by
  obtain ⟨l, hl, hW⟩ := hW
  exact ⟨l, hl, fun k μ ν => by rw [← h, hW]⟩

theorem sum {ι : Type*} (s : Finset ι) {W : ι → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : ∀ i ∈ s, SAForm Mlo ε (W i)) : SAForm Mlo ε fun k μ ν => ∑ i ∈ s, W i k μ ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : SAForm Mlo ε _)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end SAForm

/-! ### Two-loop families -/

open QED.GradedProof.VP2 in
/-- **Two-loop families with the spectral tensor form at every `ε > 0`**: integrable in both
stages, with joint integrals of the form `SAForm M_lo ε`. -/
def SAJ (Mlo : ℝ) (F : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → (∀ k i j, QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => F ε k ℓ i j) ∧
    SAForm Mlo ε fun k i j => QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ => F ε k ℓ i j

namespace SAJ

open QED.GradedProof.VP2

variable {Mlo : ℝ} {F G : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hF : SAJ Mlo F) (hG : SAJ Mlo G) :
    SAJ Mlo fun ε k ℓ i j => F ε k ℓ i j + G ε k ℓ i j := by
  intro ε hε
  obtain ⟨hFi, hFf⟩ := hF ε hε
  obtain ⟨hGi, hGf⟩ := hG ε hε
  refine ⟨fun k i j => QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add (hFi k i j)
    (hGi k i j), (hFf.add hGf).congr fun k i j => ?_⟩
  rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add (hFi k i j) (hGi k i j)]

theorem mul (hF : SAJ Mlo F) (c : ℝ → ℂ) : SAJ Mlo fun ε k ℓ i j => c ε * F ε k ℓ i j := by
  intro ε hε
  obtain ⟨hFi, hFf⟩ := hF ε hε
  refine ⟨fun k i j => JEF.const_mul (hFi k i j) (c ε), (hFf.const_mul (c ε)).congr
    fun k i j => ?_⟩
  rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]

theorem const_mul (hF : SAJ Mlo F) (c : ℂ) : SAJ Mlo fun ε k ℓ i j => c * F ε k ℓ i j :=
  hF.mul fun _ => c

theorem congr (hF : SAJ Mlo F) (e : ∀ ε : ℝ, 0 < ε → ∀ k ℓ i j, F ε k ℓ i j = G ε k ℓ i j) :
    SAJ Mlo G := by
  intro ε hε
  obtain ⟨hFi, hFf⟩ := hF ε hε
  refine ⟨fun k i j => JEF.congr (hFi k i j) (e ε hε k · i j), hFf.congr fun k i j => ?_⟩
  rw [show (fun ℓ => F ε k ℓ i j) = fun ℓ => G ε k ℓ i j from funext (e ε hε k · i j)]

theorem zero : SAJ Mlo fun _ _ _ _ _ => 0 := by
  intro ε _
  refine ⟨fun _ _ _ => JEF.zero, SAForm.zero.congr fun k i j => ?_⟩
  simp [QED.TwoLoop.jointEnergyFirstIntegral]

theorem sum {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hF : ∀ a ∈ s, SAJ Mlo (F a)) : SAJ Mlo fun ε k ℓ i j => ∑ a ∈ s, F a ε k ℓ i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : SAJ Mlo fun _ _ _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

end SAJ

/-! ### Five terms from one covariant coefficient family -/

section Terms

variable {m : ℕ}

/-- The five terms `sʲ g ∫ Xⱼ fDen^{-r}` (`j ≤ 2`) and `sʲ k k ∫ Yⱼ fDen^{-r}` (`j ≤ 1`) of a
coefficient family `Cf x`. -/
noncomputable def saTerms5 (Cf : (Fin m → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (r : ℕ)
    (mass xi : (Fin m → ℝ) → ℝ) : List SATerm :=
  [⟨m, 0, r, false, fun x => saX (Cf x) 0, mass, xi⟩,
    ⟨m, 1, r, false, fun x => saX (Cf x) 1, mass, xi⟩,
    ⟨m, 2, r, false, fun x => saX (Cf x) 2, mass, xi⟩,
    ⟨m, 0, r, true, fun x => saY (Cf x) 0, mass, xi⟩,
    ⟨m, 1, r, true, fun x => saY (Cf x) 1, mass, xi⟩]

variable {Cf : (Fin m → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem integrableOn_saAv {S : Set (Fin m → ℝ)}
    (hI : ∀ k μ ν, IntegrableOn (fun x => Cf x k μ ν) S) (j : ℝ) :
    IntegrableOn (fun x => saAv (Cf x) j) S :=
  hI _ 2 2

theorem integrableOn_saBv {S : Set (Fin m → ℝ)}
    (hI : ∀ k μ ν, IntegrableOn (fun x => Cf x k μ ν) S) (j : ℝ) :
    IntegrableOn (fun x => saBv (Cf x) j) S := by
  simp only [saBv, div_eq_mul_inv]
  exact (hI _ 0 1).mul_const _

theorem integrableOn_saX {S : Set (Fin m → ℝ)}
    (hI : ∀ k μ ν, IntegrableOn (fun x => Cf x k μ ν) S) (j : Fin 3) :
    IntegrableOn (fun x => saX (Cf x) j) S := by
  have h := integrableOn_saAv hI
  fin_cases j <;> simp only [saX]
  · exact (((h 1).const_mul 3).sub ((h 2).const_mul 3)).add (h 3)
  · exact (((h 1).const_mul _).add ((h 2).const_mul 4)).sub ((h 3).const_mul _)
  · simp only [div_eq_mul_inv]
    exact (((h 1).mul_const _).sub (h 2)).add ((h 3).mul_const _)

theorem integrableOn_saY {S : Set (Fin m → ℝ)}
    (hI : ∀ k μ ν, IntegrableOn (fun x => Cf x k μ ν) S) (j : Fin 2) :
    IntegrableOn (fun x => saY (Cf x) j) S := by
  have h := integrableOn_saBv hI
  fin_cases j <;> simp only [saY]
  · exact ((h 1).const_mul 2).sub (h 2)
  · exact (h 2).sub (h 1)

theorem norm_fDen_inv_pow_le {ε : ℝ} (hε : 0 < ε) (M x : ℝ) (k : Fin 4 → ℝ) (r : ℕ) :
    ‖(fDen M ε x k ^ r)⁻¹‖ ≤ (ε ^ r)⁻¹ := by
  have h : ε ≤ ‖fDen M ε x k‖ := by
    have := Complex.abs_im_le_norm (fDen M ε x k)
    simp only [fDen, sub_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
      add_zero, zero_sub, abs_neg] at this
    rwa [abs_of_pos hε] at this
  rw [norm_inv, norm_pow]
  exact inv_anti₀ (pow_pos hε r) (pow_le_pow_left₀ hε.le h r)

theorem measurable_fDen (mass xi : (Fin m → ℝ) → ℝ) (hmass : Measurable mass)
    (hxi : Measurable xi) (ε : ℝ) (k : Fin 4 → ℝ) :
    Measurable fun x => fDen (mass x) ε (xi x) k := by
  simp only [fDen, QED.WickModel.vacuumPolarizationFeynmanMass]
  fun_prop

/-- **The integral of one coefficient family against `fDen^{-r}` is five terms.** -/
theorem saTerms5_integral {S : Set (Fin m → ℝ)} (hS : S = simplexSet m) {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) (mass xi : (Fin m → ℝ) → ℝ) (hmass : Measurable mass) (hxi : Measurable xi)
    (hI : ∀ k μ ν, IntegrableOn (fun x => Cf x k μ ν) S)
    (hC : ∀ x k μ ν, Cf x k μ ν =
      gkTensor (saXq (Cf x) (Minkowski.dot k k)) (saYq (Cf x) (Minkowski.dot k k)) k μ ν)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    ∫ x in S, Cf x k μ ν * (fDen (mass x) ε (xi x) k ^ r)⁻¹ =
      ((saTerms5 Cf r mass xi).map fun τ => τ.val ε k μ ν).sum := by
  subst hS
  set D : (Fin m → ℝ) → ℂ := fun x => (fDen (mass x) ε (xi x) k ^ r)⁻¹ with hD
  have hDm : AEStronglyMeasurable D (volume.restrict (simplexSet m)) :=
    (((measurable_fDen mass xi hmass hxi ε k).pow_const r).inv).aestronglyMeasurable
  have hDb : ∀ᵐ x ∂(volume.restrict (simplexSet m)), ‖D x‖ ≤ (ε ^ r)⁻¹ :=
    Eventually.of_forall fun x => norm_fDen_inv_pow_le hε _ _ k r
  have iX : ∀ j, Integrable (fun x => saX (Cf x) j * D x) (volume.restrict (simplexSet m)) :=
    fun j => (integrableOn_saX hI j).mul_bdd hDm hDb
  have iY : ∀ j, Integrable (fun x => saY (Cf x) j * D x) (volume.restrict (simplexSet m)) :=
    fun j => (integrableOn_saY hI j).mul_bdd hDm hDb
  set cst : Fin 5 → ℂ := ![saTens false k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ 0,
    saTens false k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ 1,
    saTens false k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ 2,
    saTens true k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ 0,
    saTens true k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ 1] with hcst
  set wt : Fin 5 → (Fin m → ℝ) → ℂ := ![fun x => saX (Cf x) 0, fun x => saX (Cf x) 1,
    fun x => saX (Cf x) 2, fun x => saY (Cf x) 0, fun x => saY (Cf x) 1] with hwt
  have hw : ∀ i, Integrable (fun x => cst i * (wt i x * D x)) (volume.restrict (simplexSet m)) :=
    fun i => by
      refine Integrable.const_mul ?_ _
      fin_cases i
      exacts [iX 0, iX 1, iX 2, iY 0, iY 1]
  have e : ∀ x, Cf x k μ ν * D x = ∑ i : Fin 5, cst i * (wt i x * D x) := fun x => by
    rw [hC, gkTensor, saXq_eq_sum, saYq_eq_sum]
    simp only [Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_five, saTens, hcst, hwt,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    ring
  rw [integral_congr_ae (Eventually.of_forall e), integral_finsetSum _ fun i _ => hw i]
  simp only [integral_const_mul, Fin.sum_univ_five, hcst, hwt, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, saTerms5, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, SATerm.val, hD]
  ring

theorem saTerms5_good {Mlo : ℝ} (r : ℕ) (mass xi : (Fin m → ℝ) → ℝ) (hmass : Measurable mass)
    (hxi : Measurable xi) (hI : ∀ k μ ν, IntegrableOn (fun x => Cf x k μ ν) (simplexSet m))
    (hae : ∀ᵐ x ∂(volume.restrict (simplexSet m)), Mlo ≤ mass x ∧ xi x ∈ Ioo (0 : ℝ) 1) :
    ∀ τ ∈ saTerms5 Cf r mass xi, τ.Good Mlo := by
  intro τ hτ
  simp only [saTerms5, List.mem_cons, List.not_mem_nil, or_false] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact ⟨integrableOn_saX hI 0, hmass, hxi, hae, by simp⟩
  · exact ⟨integrableOn_saX hI 1, hmass, hxi, hae, by simp⟩
  · exact ⟨integrableOn_saX hI 2, hmass, hxi, hae, by simp⟩
  · exact ⟨integrableOn_saY hI 0, hmass, hxi, hae, by simp⟩
  · exact ⟨integrableOn_saY hI 1, hmass, hxi, hae, by simp⟩

end Terms

end QED.ChainProof.SetASpec

end
