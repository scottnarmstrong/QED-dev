/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecPieceJ

/-!
# Set (a): the `ε`-uniform spectral tensor form

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
The fixed-`ε` spectral form `QED.ChainProof.SetASpec.SAForm` chooses its terms separately at each
`ε`. The limit `ε → 0⁺` (`QED.ChainProof.SetASpec.saLim_tendsto_term`) needs **one** family of
terms for all `ε ∈ (0, 1]`: fixed simplex dimension, powers, tensor, mass and Feynman parameter,
and weights `w_ε` converging almost everywhere to `w₀` with one integrable majorant.

* `SAUCoef c`: a coefficient `c(ε)` converging as `ε → 0⁺` and bounded on `(0, 1]`
  (`SAUCoef.of_continuousOn`: continuous on `[0, 1]`);
* `SAUTerm`, `SAUTerm.Good`: a uniform spectral term and the hypotheses on it;
* `SAUForm M_lo W`: for every `ε ∈ (0, 1]`, `W ε` is the sum of one list of good uniform terms;
  closed under sums, `SAUCoef` multiples and pointwise equality; lists of `ε`-independent terms
  lift (`SAUForm.of_list`);
* `SAUJ M_lo F`: the two-loop families integrable at every `ε > 0` whose joint integrals are
  `SAUForm`;
* **`saUForm_pieceSpec`**, **`saUj_piece`**: the uniform versions of
  `QED.ChainProof.SetASpec.setASpec_pieceSpec_form` and `saj_piece` (the terms of a piece do not
  depend on `ε`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.VPHalfAtAssembly
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly propDenom)
open QED.GradedProof.VP2 (TCov2 good_of_poly)

/-! ### Coefficients -/

/-- **A uniform coefficient**: `c(ε)` converges as `ε → 0⁺` and is bounded on `(0, 1]`. -/
def SAUCoef (c : ℝ → ℂ) : Prop :=
  (∃ c₀ : ℂ, Tendsto c (𝓝[>] 0) (𝓝 c₀)) ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖c ε‖ ≤ C

namespace SAUCoef

theorem const (a : ℂ) : SAUCoef fun _ => a :=
  ⟨⟨a, tendsto_const_nhds⟩, ‖a‖, fun _ _ _ => le_rfl⟩

theorem mul {c d : ℝ → ℂ} (hc : SAUCoef c) (hd : SAUCoef d) : SAUCoef fun ε => c ε * d ε := by
  obtain ⟨⟨c₀, hc0⟩, C, hC⟩ := hc
  obtain ⟨⟨d₀, hd0⟩, E, hE⟩ := hd
  refine ⟨⟨c₀ * d₀, hc0.mul hd0⟩, C * E, fun ε h0 h1 => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC ε h0 h1) (hE ε h0 h1) (norm_nonneg _) ((norm_nonneg _).trans (hC ε h0 h1))

/-- A coefficient agreeing on `(0, 1]` with a function continuous on `[0, 1]` is uniform. -/
theorem of_continuousOn {c g : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 1))
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → c ε = g ε) : SAUCoef c := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  refine ⟨⟨g 0, ?_⟩, C, fun ε h0 h1 => by rw [h ε h0 h1]; exact hC ε ⟨h0.le, h1⟩⟩
  have hmem : Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT zero_lt_one
  have hg0 : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
    ((hg 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
      (mem_of_superset hmem Ioc_subset_Icc_self)).tendsto
  refine hg0.congr' ?_
  filter_upwards [hmem] with ε hε
  exact (h ε hε.1 hε.2).symm

/-- A polynomial-type coefficient continuous on `ℝ` is uniform. -/
theorem of_continuous {c : ℝ → ℂ} (hc : Continuous c) : SAUCoef c :=
  of_continuousOn hc.continuousOn fun _ _ _ => rfl

end SAUCoef

/-! ### Uniform terms -/

/-- **A uniform spectral term** `t(k) (k²)ʲ ∫_Δ w_ε(x) fDen(M(x), ε, ξ(x), k)^{-r}` over the
simplex of dimension `m`, with limit weight `w₀`. -/
structure SAUTerm where
  /-- The simplex dimension. -/
  m : ℕ
  /-- The power of `k²`. -/
  j : ℕ
  /-- The power of the photon-type factor. -/
  r : ℕ
  /-- The tensor structure. -/
  t : Bool
  /-- The weight at `ε`. -/
  w : ℝ → (Fin m → ℝ) → ℂ
  /-- The limit weight. -/
  w₀ : (Fin m → ℝ) → ℂ
  /-- The mass of the factor. -/
  mass : (Fin m → ℝ) → ℝ
  /-- The Feynman parameter of the factor. -/
  xi : (Fin m → ℝ) → ℝ

namespace SAUTerm

/-- The value of a term at `ε`, `k`, `(μ, ν)`. -/
noncomputable def val (τ : SAUTerm) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  saTens τ.t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ τ.j *
    ∫ x in simplexSet τ.m, τ.w ε x * (fDen (τ.mass x) ε (τ.xi x) k ^ τ.r)⁻¹

/-- The hypotheses of the limit engine on a term: one integrable majorant of the weights on
`ε ∈ (0, 1]`, convergence of the weights almost everywhere, and the hypotheses of `SATerm.Good`
on the mass, the parameter and the powers. -/
def Good (Mlo : ℝ) (τ : SAUTerm) : Prop :=
  (∃ h : (Fin τ.m → ℝ) → ℝ, IntegrableOn h (simplexSet τ.m) ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      AEStronglyMeasurable (τ.w ε) (volume.restrict (simplexSet τ.m)) ∧
      ∀ᵐ x ∂(volume.restrict (simplexSet τ.m)), ‖τ.w ε x‖ ≤ h x) ∧
    (∀ᵐ x ∂(volume.restrict (simplexSet τ.m)),
      Tendsto (fun ε => τ.w ε x) (𝓝[>] 0) (𝓝 (τ.w₀ x))) ∧
    Measurable τ.mass ∧ Measurable τ.xi ∧
    (∀ᵐ x ∂(volume.restrict (simplexSet τ.m)), Mlo ≤ τ.mass x ∧ τ.xi x ∈ Ioo (0 : ℝ) 1) ∧
    τ.j + (if τ.t then 1 else 0) ≤ 2

/-- An `ε`-independent term. -/
noncomputable def ofConst (τ : SATerm) : SAUTerm :=
  ⟨τ.m, τ.j, τ.r, τ.t, fun _ => τ.w, τ.w, τ.mass, τ.xi⟩

theorem val_ofConst (τ : SATerm) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    (ofConst τ).val ε k μ ν = τ.val ε k μ ν := rfl

theorem good_ofConst {Mlo : ℝ} {τ : SATerm} (h : τ.Good Mlo) : (ofConst τ).Good Mlo :=
  ⟨⟨fun x => ‖τ.w x‖, h.1.norm, fun _ _ _ =>
      ⟨h.1.aestronglyMeasurable, Eventually.of_forall fun _ => le_rfl⟩⟩,
    Eventually.of_forall fun _ => tendsto_const_nhds, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- A multiple of the weight by a coefficient `c(ε)` with limit `c₀`. -/
noncomputable def smul (c : ℝ → ℂ) (c₀ : ℂ) (τ : SAUTerm) : SAUTerm :=
  { τ with w := fun ε x => c ε * τ.w ε x, w₀ := fun x => c₀ * τ.w₀ x }

theorem val_smul (c : ℝ → ℂ) (c₀ : ℂ) (τ : SAUTerm) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    (τ.smul c c₀).val ε k μ ν = c ε * τ.val ε k μ ν := by
  obtain ⟨m, j, r, t, w, w₀, mass, xi⟩ := τ
  simp only [val, smul]
  have h : ∀ (f g : (Fin m → ℝ) → ℂ), ∫ x in simplexSet m, c ε * f x * g x =
      c ε * ∫ x in simplexSet m, f x * g x := fun f g => by
    rw [← integral_const_mul]
    simp only [mul_assoc]
  show saTens t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j *
      ∫ x in simplexSet m, c ε * w ε x * (fDen (mass x) ε (xi x) k ^ r)⁻¹ =
    c ε * (saTens t k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j *
      ∫ x in simplexSet m, w ε x * (fDen (mass x) ε (xi x) k ^ r)⁻¹)
  rw [h]
  ring

theorem Good.smul {Mlo : ℝ} {τ : SAUTerm} (h : τ.Good Mlo) {c : ℝ → ℂ} {c₀ : ℂ}
    (hc0 : Tendsto c (𝓝[>] 0) (𝓝 c₀)) {C : ℝ} (hC : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖c ε‖ ≤ C) :
    (τ.smul c c₀).Good Mlo := by
  obtain ⟨⟨g, hg, hw⟩, hl, h3⟩ := h
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 one_pos le_rfl)
  refine ⟨⟨fun x => C * g x, hg.const_mul C, fun ε h0 h1 => ⟨?_, ?_⟩⟩, ?_, h3⟩
  · exact aestronglyMeasurable_const.mul (hw ε h0 h1).1
  · filter_upwards [(hw ε h0 h1).2] with x hx
    show ‖c ε * τ.w ε x‖ ≤ C * g x
    rw [norm_mul]
    exact mul_le_mul (hC ε h0 h1) hx (norm_nonneg _) hC0
  · filter_upwards [hl] with x hx
    exact hc0.mul hx

end SAUTerm

/-! ### The uniform form -/

/-- **The `ε`-uniform spectral tensor form**: for every `ε ∈ (0, 1]`, `W ε` is the sum of one
list of good uniform terms. -/
def SAUForm (Mlo : ℝ) (W : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∃ l : List SAUTerm, (∀ τ ∈ l, τ.Good Mlo) ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k μ ν, W ε k μ ν = (l.map fun τ => τ.val ε k μ ν).sum

namespace SAUForm

variable {Mlo : ℝ} {W V : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem zero : SAUForm Mlo fun _ _ _ _ => 0 := ⟨[], by simp, by simp⟩

theorem add (hW : SAUForm Mlo W) (hV : SAUForm Mlo V) :
    SAUForm Mlo fun ε k μ ν => W ε k μ ν + V ε k μ ν := by
  obtain ⟨l, hl, hW⟩ := hW
  obtain ⟨l', hl', hV⟩ := hV
  refine ⟨l ++ l', fun τ hτ => ?_, fun ε h0 h1 k μ ν => by simp [hW ε h0 h1, hV ε h0 h1]⟩
  rcases List.mem_append.mp hτ with h | h
  exacts [hl τ h, hl' τ h]

theorem mul {c : ℝ → ℂ} (hc : SAUCoef c) (hW : SAUForm Mlo W) :
    SAUForm Mlo fun ε k μ ν => c ε * W ε k μ ν := by
  obtain ⟨⟨c₀, hc0⟩, C, hC⟩ := hc
  obtain ⟨l, hl, hW⟩ := hW
  refine ⟨l.map (SAUTerm.smul c c₀), fun τ hτ => ?_, fun ε h0 h1 k μ ν => ?_⟩
  · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ
    exact (hl σ hσ).smul hc0 hC
  · show c ε * W ε k μ ν = _
    rw [hW ε h0 h1, List.map_map, ← List.sum_map_mul_left]
    congr 1
    exact List.map_congr_left fun τ _ => (SAUTerm.val_smul c c₀ τ ε k μ ν).symm

theorem const_mul (c : ℂ) (hW : SAUForm Mlo W) : SAUForm Mlo fun ε k μ ν => c * W ε k μ ν :=
  hW.mul (SAUCoef.const c)

theorem congr (hW : SAUForm Mlo W) (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k μ ν, W ε k μ ν = V ε k μ ν) :
    SAUForm Mlo V := by
  obtain ⟨l, hl, hW⟩ := hW
  exact ⟨l, hl, fun ε h0 h1 k μ ν => by rw [← h ε h0 h1, hW ε h0 h1]⟩

theorem sum {ι : Type*} (s : Finset ι) {W : ι → ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : ∀ i ∈ s, SAUForm Mlo (W i)) : SAUForm Mlo fun ε k μ ν => ∑ i ∈ s, W i ε k μ ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : SAUForm Mlo _)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **A list of `ε`-independent good terms** giving `W ε` for every `ε ∈ (0, 1]`. -/
theorem of_list (l : List SATerm) (hl : ∀ τ ∈ l, τ.Good Mlo)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k μ ν, W ε k μ ν = (l.map fun τ => τ.val ε k μ ν).sum) :
    SAUForm Mlo W := by
  refine ⟨l.map SAUTerm.ofConst, fun τ hτ => ?_, fun ε h0 h1 k μ ν => ?_⟩
  · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ
    exact SAUTerm.good_ofConst (hl σ hσ)
  · rw [h ε h0 h1, List.map_map]
    rfl

end SAUForm

/-! ### Two-loop families -/

open QED.GradedProof.VP2 in
/-- **Two-loop families with the uniform spectral tensor form**: integrable in both stages at
every `ε > 0`, with joint integrals of the form `SAUForm M_lo`. -/
def SAUJ (Mlo : ℝ) (F : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∀ k i j, QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => F ε k ℓ i j) ∧
    SAUForm Mlo fun ε k i j => QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ => F ε k ℓ i j

namespace SAUJ

open QED.GradedProof.VP2

variable {Mlo : ℝ} {F G : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hF : SAUJ Mlo F) (hG : SAUJ Mlo G) :
    SAUJ Mlo fun ε k ℓ i j => F ε k ℓ i j + G ε k ℓ i j := by
  refine ⟨fun ε hε k i j => QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add
    (hF.1 ε hε k i j) (hG.1 ε hε k i j), (hF.2.add hG.2).congr fun ε h0 _ k i j => ?_⟩
  rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_add (hF.1 ε h0 k i j) (hG.1 ε h0 k i j)]

theorem mul (hF : SAUJ Mlo F) {c : ℝ → ℂ} (hc : SAUCoef c) :
    SAUJ Mlo fun ε k ℓ i j => c ε * F ε k ℓ i j := by
  refine ⟨fun ε hε k i j => JEF.const_mul (hF.1 ε hε k i j) (c ε), (hF.2.mul hc).congr
    fun ε _ _ k i j => ?_⟩
  rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]

theorem const_mul (hF : SAUJ Mlo F) (c : ℂ) : SAUJ Mlo fun ε k ℓ i j => c * F ε k ℓ i j :=
  hF.mul (SAUCoef.const c)

theorem congr (hF : SAUJ Mlo F) (e : ∀ ε : ℝ, 0 < ε → ∀ k ℓ i j, F ε k ℓ i j = G ε k ℓ i j) :
    SAUJ Mlo G := by
  refine ⟨fun ε hε k i j => JEF.congr (hF.1 ε hε k i j) (e ε hε k · i j),
    hF.2.congr fun ε hε _ k i j => ?_⟩
  rw [show (fun ℓ => F ε k ℓ i j) = fun ℓ => G ε k ℓ i j from funext (e ε hε k · i j)]

theorem zero : SAUJ Mlo fun _ _ _ _ _ => 0 := by
  refine ⟨fun _ _ _ _ _ => JEF.zero, SAUForm.zero.congr fun ε _ _ k i j => ?_⟩
  simp [QED.TwoLoop.jointEnergyFirstIntegral]

theorem sum {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hF : ∀ a ∈ s, SAUJ Mlo (F a)) : SAUJ Mlo fun ε k ℓ i j => ∑ a ∈ s, F a ε k ℓ i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : SAUJ Mlo fun _ _ _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

end SAUJ

/-! ### The piece -/

variable {m : ℕ}

/-- **The uniform spectral form of the joint integral of a piece** with a covariant numerator:
the terms (`saTerms5` of the three coefficient families) do not depend on `ε`. -/
theorem saUForm_pieceSpec {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hQ : ∀ k μ ν, ∃ Q : LoopQuartic, Q.eval = fun ℓ => N k ℓ μ ν) (hcov : TCov2 N)
    (hK : SAPolyK 4 N) (α : Fin (m + 1) → Fin 2 → ℝ) (c M : Fin (m + 1) → ℝ)
    (hI : ∀ k μ ν, IntegrableOn (fun x => saT1 N α c x k μ ν) (simplexSet m) ∧
      IntegrableOn (fun x => saT2 N α c x k μ ν) (simplexSet m) ∧
      IntegrableOn (fun x => saT3 N α x k μ ν) (simplexSet m))
    {Mlo : ℝ} (hae : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      Mlo ≤ saMass M x ∧ saXiAt α c x ∈ Ioo (0 : ℝ) 1) :
    SAUForm Mlo fun ε k μ ν =>
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m, saPieceSpec (saQ N k μ ν) α c M ε k x := by
  have hmass := measurable_saMass (m := m) M
  have hxi := measurable_saXiAt (m := m) α c
  have F1 : SAUForm Mlo fun ε k μ ν => ∫ x in simplexSet m, saT1 N α c x k μ ν *
      (fDen (saMass M x) ε (saXiAt α c x) k ^ (m - 3))⁻¹ :=
    SAUForm.of_list (saTerms5 (fun x => saT1 N α c x) (m - 3) (saMass M) (saXiAt α c))
      (saTerms5_good _ _ _ hmass hxi (fun k μ ν => (hI k μ ν).1) hae)
      fun ε hε _ k μ ν => saTerms5_integral rfl hε _ _ _ hmass hxi (fun k μ ν => (hI k μ ν).1)
        (fun x => (saT1_cov α c hQ hcov x).eq_gk (saT1_poly α c hQ hK x)) k μ ν
  have F2 : SAUForm Mlo fun ε k μ ν => ∫ x in simplexSet m, saT2 N α c x k μ ν *
      (fDen (saMass M x) ε (saXiAt α c x) k ^ (m - 4))⁻¹ :=
    SAUForm.of_list (saTerms5 (fun x => saT2 N α c x) (m - 4) (saMass M) (saXiAt α c))
      (saTerms5_good _ _ _ hmass hxi (fun k μ ν => (hI k μ ν).2.1) hae)
      fun ε hε _ k μ ν => saTerms5_integral rfl hε _ _ _ hmass hxi
        (fun k μ ν => (hI k μ ν).2.1)
        (fun x => (saT2_cov α c hQ hcov x).eq_gk (saT2_poly α c hQ hK x)) k μ ν
  have F3 : SAUForm Mlo fun ε k μ ν => ∫ x in simplexSet m, saT3 N α x k μ ν *
      (fDen (saMass M x) ε (saXiAt α c x) k ^ (m - 5))⁻¹ :=
    SAUForm.of_list (saTerms5 (fun x => saT3 N α x) (m - 5) (saMass M) (saXiAt α c))
      (saTerms5_good _ _ _ hmass hxi (fun k μ ν => (hI k μ ν).2.2) hae)
      fun ε hε _ k μ ν => saTerms5_integral rfl hε _ _ _ hmass hxi
        (fun k μ ν => (hI k μ ν).2.2)
        (fun x => (saT3_cov α hQ hcov x).eq_gk (saT3_poly α hQ hK x)) k μ ν
  refine ((F1.add F2).add F3).const_mul (-((π : ℂ) ^ 4)) |>.congr fun ε hε _ k μ ν => ?_
  have hD : ∀ (r : ℕ), AEStronglyMeasurable
      (fun x => (fDen (saMass M x) ε (saXiAt α c x) k ^ r)⁻¹) (volume.restrict (simplexSet m)) :=
    fun r => (((measurable_fDen _ _ hmass hxi ε k).pow_const r).inv).aestronglyMeasurable
  have hDb : ∀ (r : ℕ), ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      ‖(fDen (saMass M x) ε (saXiAt α c x) k ^ r)⁻¹‖ ≤ (ε ^ r)⁻¹ :=
    fun r => Eventually.of_forall fun x => norm_fDen_inv_pow_le hε _ _ k r
  congr 1
  have i1 := ((hI k μ ν).1.mul_bdd (hD _) (hDb (m - 3)))
  have i2 := ((hI k μ ν).2.1.mul_bdd (hD _) (hDb (m - 4)))
  have i3 := ((hI k μ ν).2.2.mul_bdd (hD _) (hDb (m - 5)))
  have h3 := integral_add (i1.add i2) i3
  simp only [Pi.add_apply] at h3
  rw [← integral_add i1 i2, ← h3]
  rfl

/-- **A piece over a shape of a vacuum-polarization routing has the uniform spectral form**
(`SAUJ`). -/
theorem saUj_piece (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
    (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
      |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
    {n : ℕ} (hn : n = 6 ∨ n = 7) (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ)
    {E : Finset (Fin (n + 1))} (hcrit : IntNoSubdivergenceRefined 2 E fun i => base (sh i))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hpoly : ∀ k i j, IsLoopPoly 2 (n - 3) fun ℓ => N k ℓ i j)
    (hB : ∀ k i j, RefinedBound (castLoopMatrix fun i => base (sh i)) E 4 fun ℓ => N k ℓ i j)
    (hcov : TCov2 N) (hK : SAPolyK 4 N)
    (hc : ∀ y : Fin 2 → ℝ, ∃ i, ∑ s, (base (sh i) s : ℝ) * y s + c (sh i) ≠ 0)
    {Mlo : ℝ} (hMlo0 : 0 ≤ Mlo) (hMlo : ∀ i, Mlo ≤ Ms i) :
    SAUJ Mlo fun ε k ℓ i j => N k ℓ i j * ∏ l,
      (propDenom (Ms l) ε (lineMomentum (castLoopMatrix base) (fun r => c r • k) (sh l) ℓ))⁻¹ := by
  have hcrit' := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit
  have h6 : 6 ≤ n := by omega
  set α : Fin (n + 1) → Fin 2 → ℝ := castLoopMatrix fun i => base (sh i) with hα
  set c' : Fin (n + 1) → ℝ := fun i => c (sh i) with hc'
  have hgood := fun k i j => good_of_poly hn (hpoly k i j) (hB k i j)
  choose Q hq hb he using hgood
  have hQ : ∀ k μ ν, ∃ Q : LoopQuartic, Q.eval = fun ℓ => N k ℓ μ ν :=
    fun k μ ν => ⟨Q k μ ν, he k μ ν⟩
  have hQs : ∀ k μ ν, (saQ N k μ ν).eval = (Q k μ ν).eval := fun k μ ν =>
    (saQ_eval hQ k μ ν).trans (he k μ ν).symm
  have hy : ∀ i, (∑ s, α i s * ((1 / 2 : ℝ) • (y₁ + y₂)) s + c' i) ^ 2 ≤ 1 / 4 := by
    intro i
    have h := hflow (sh i)
    refine saFlow_sq_le (a := fun s => (base (sh i) s : ℝ)) (b := c (sh i)) (h.trans ?_)
    split_ifs <;> norm_num
  have hI : ∀ k μ ν, IntegrableOn (fun x => saT1 N α c' x k μ ν) (simplexSet n) ∧
      IntegrableOn (fun x => saT2 N α c' x k μ ν) (simplexSet n) ∧
      IntegrableOn (fun x => saT3 N α x k μ ν) (simplexSet n) := by
    intro k μ ν
    have e1 : (fun x => saT1 N α c' x k μ ν) = coeffOne (Q k μ ν) α (fun i => c' i • k) :=
      coeffOne_congr (hQs k μ ν) α _
    have e2 : (fun x => saT2 N α c' x k μ ν) = coeffTwo (Q k μ ν) α (fun i => c' i • k) :=
      coeffTwo_congr (hQs k μ ν) α _
    have e3 : (fun x => saT3 N α x k μ ν) = coeffThree (Q k μ ν) α :=
      coeffThree_congr (hQs k μ ν) α
    rw [e1, e2, e3]
    rcases hq k μ ν with h7 | hq0
    · exact integrableOn_coeff (Q k μ ν) α _ h7 hcrit' (hb k μ ν)
    · exact integrableOn_coeff_cubic (Q k μ ν) α _ hq0 h6 hcrit' (hb k μ ν)
  have hae : ∀ᵐ x ∂(volume.restrict (simplexSet n)),
      Mlo ≤ saMass Ms x ∧ saXiAt α c' x ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [setASpec_ae_mass_ge Ms hMlo0 hMlo,
      setASpec_ae_saXi_mem_Ioo (by omega) (setASpec_hspan hcrit') hc] with x h1 h2
    exact ⟨h1, h2⟩
  have hint : ∀ ε : ℝ, 0 < ε → ∀ k i j, QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      N k ℓ i j * ∏ l, (propDenom (Ms l) ε (lineMomentum (castLoopMatrix base)
        (fun r => c r • k) (sh l) ℓ))⁻¹ := by
    intro ε hε k i j
    have h := (show QED.TwoLoop.jointEnergyFirstIntegrable 2
        (fun ℓ => (Q k i j).eval ℓ * ∏ l, (lineDenom α (fun l => c' l • k) Ms ε l ℓ)⁻¹) from by
      rcases hq k i j with h7 | hq0
      · exact jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined _ _ _ _
          h7 hε hcrit' (hb k i j)
      · exact jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic _ _ _ _
          hq0 h6 hε hcrit' (hb k i j))
    rw [he] at h
    exact h
  refine ⟨hint, (saUForm_pieceSpec hQ hcov hK α c' Ms hI hae).congr fun ε hε _ k i j => ?_⟩
  have hJ : (QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ => N k ℓ i j * ∏ l,
      (propDenom (Ms l) ε (lineMomentum (castLoopMatrix base) (fun r => c r • k) (sh l)
        ℓ))⁻¹) = QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => (Q k i j).eval ℓ * ∏ l, (lineDenom α (fun l => c' l • k) Ms ε l ℓ)⁻¹) := by
    rw [he]
    rfl
  rw [hJ, saPieceSpec_congr (hQs k i j)]
  rcases hq k i j with h7 | hq0
  · rw [setASpec_piece_eq_spectral (Q k i j) Ms h7 hε hcrit' (hb k i j) _ hy k]
  · rw [setASpec_piece_eq_spectral_cubic (Q k i j) Ms hq0 h6 hε hcrit' (hb k i j) _ hy k]

end QED.ChainProof.SetASpec

end
