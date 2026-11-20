/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceAsm
public import QED.GradedProof.RPi4FaceLip

/-!
# (R-Π₄) step L6d2: the rescaled data of a face shape are uniformly Lipschitz

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2. Over the
barycentric points of `Δ_p × Δ_q` (`FaceIdx`), the rescaled data of a `FaceShape` satisfy the
uniform bounds `FaceData` (with `Û ≥ 1 - ρ₀`), so every coefficient of the face brackets is
`UnifLip`. The rescaled second Symanzik function `vHat` is `UnifLip` too, and a lower bound
`V₀ ≥ c₁` of the raw function for `ρ > 0` passes to `vHat` on `[0, ρ₀]`, including `ρ = 0`
where the raw function is not defined by the formula (`U = 0`).

* `FaceIdx`, `abs_sum_mul_le`, **`FaceShape.faceData`**, **`faceDataFam`** (a family of shapes with
  uniformly bounded data), `UnifLip.dot`, **`FaceShape.unifLip_vHat`** (uniform over the family),
  `le_of_lip`, **`FaceShape.vHat_ge`**.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex)

/-- The barycentric points of `Δ_p × Δ_q`. -/
abbrev FaceIdx (p q : ℕ) : Type :=
  {x : (Fin p → ℝ) × (Fin q → ℝ) // x ∈ simplexSet p ×ˢ simplexSet q}

/-- `|∑ Wᵢ yᵢ| ≤ ∑ |yᵢ|` for weights in `[0, 1]`. -/
theorem abs_sum_mul_le {n : ℕ} {W y : Fin n → ℝ} (h0 : ∀ i, 0 ≤ W i) (h1 : ∀ i, W i ≤ 1) :
    |∑ i, W i * y i| ≤ ∑ i, |y i| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (h0 i)]
  exact mul_le_of_le_one_left (abs_nonneg _) (h1 i)

theorem bary_le_one {n : ℕ} {W : Fin n → ℝ} (h0 : ∀ i, 0 ≤ W i) (h1 : ∑ i, W i = 1) (i : Fin n) :
    W i ≤ 1 :=
  h1 ▸ Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

namespace FaceShape

variable {p q : ℕ} (S : FaceShape p q)

/-- The face-block point of an index. -/
noncomputable abbrev Wi (i : FaceIdx p q) : Fin (p + 1) → ℝ := simplexPoint i.1.1

/-- The rest point of an index. -/
noncomputable abbrev Vi (i : FaceIdx p q) : Fin (q + 1) → ℝ := simplexPoint i.1.2

theorem Wi_nonneg (i : FaceIdx p q) (j : Fin (p + 1)) : 0 ≤ Wi i j :=
  (simplexPoint_mem_stdSimplex i.2.1).1 j

theorem Vi_nonneg (i : FaceIdx p q) (j : Fin (q + 1)) : 0 ≤ Vi i j :=
  (simplexPoint_mem_stdSimplex i.2.2).1 j

theorem Wi_le_one (i : FaceIdx p q) (j : Fin (p + 1)) : Wi i j ≤ 1 :=
  bary_le_one (Wi_nonneg i) (sum_simplexPoint _) j

theorem Vi_le_one (i : FaceIdx p q) (j : Fin (q + 1)) : Vi i j ≤ 1 :=
  bary_le_one (Vi_nonneg i) (sum_simplexPoint _) j

/-- The bound of the momentum data. -/
noncomputable def kP : ℝ :=
  ∑ μ : Fin 4, ((∑ j, |S.pR j μ|) + (∑ i, |S.αF i 0 * S.pF i μ|) + ∑ i, |S.αF i 1 * S.pF i μ|)

/-- The uniform bound `K` of the rescaled data. -/
noncomputable def kF : ℝ :=
  1 + (∑ i, |S.αF i 0 * S.αF i 0|) + (∑ i, |S.αF i 0 * S.αF i 1|) +
    (∑ i, |S.αF i 1 * S.αF i 1|) + S.kP

theorem kP_ge (μ : Fin 4) :
    (∑ j, |S.pR j μ|) + (∑ i, |S.αF i 0 * S.pF i μ|) + ∑ i, |S.αF i 1 * S.pF i μ| ≤ S.kP :=
  Finset.single_le_sum (f := fun μ => (∑ j, |S.pR j μ|) + (∑ i, |S.αF i 0 * S.pF i μ|) +
    ∑ i, |S.αF i 1 * S.pF i μ|) (fun _ _ => by positivity) (Finset.mem_univ μ)

theorem kP_nonneg : 0 ≤ S.kP := Finset.sum_nonneg fun _ _ => by positivity

/-- **The rescaled data of a face shape satisfy the uniform bounds**, with `Û ≥ 1 - ρ₀`. -/
theorem faceData {ρ₀ : ℝ} (hρ₁ : ρ₀ < 1) :
    FaceData ρ₀ (fun i : FaceIdx p q => a0 (Vi i)) (fun i => S.a1 (Wi i) (Vi i))
      (fun i => S.b (Wi i)) (fun i => S.c (Wi i)) (fun i => S.P0 (Vi i))
      (fun i => S.P1 (Wi i) (Vi i)) (fun i => S.b₁ (Wi i)) S.kF (1 - ρ₀) := by
  have hP := S.kP_nonneg
  have h1 : 0 ≤ ∑ i, |S.αF i 0 * S.αF i 0| := by positivity
  have h2 : 0 ≤ ∑ i, |S.αF i 0 * S.αF i 1| := by positivity
  have h3 : 0 ≤ ∑ i, |S.αF i 1 * S.αF i 1| := by positivity
  have hW : ∀ (i : FaceIdx p q) (y : Fin (p + 1) → ℝ), |∑ j, Wi i j * y j| ≤ ∑ j, |y j| :=
    fun i _ => abs_sum_mul_le (Wi_nonneg i) (Wi_le_one i)
  have hV : ∀ (i : FaceIdx p q) (y : Fin (q + 1) → ℝ), |∑ j, Vi i j * y j| ≤ ∑ j, |y j| :=
    fun i _ => abs_sum_mul_le (Vi_nonneg i) (Vi_le_one i)
  have hV1 : ∀ i : FaceIdx p q, ∑ j, Vi i j = 1 := fun i => sum_simplexPoint _
  refine ⟨by linarith, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i μ => ?_,
    fun i μ => ?_, fun i μ => ?_, fun i ρ hρ hρ' => ?_⟩
  · simp only [a0, hV1, abs_one, kF]; linarith
  · simp only [a1, hV1]
    have := hW i (fun j => S.αF j 0 * S.αF j 0)
    simp only [← mul_assoc] at this
    calc _ ≤ |∑ j, Wi i j * S.αF j 0 * S.αF j 0| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ _ := by simp only [kF, abs_one]; linarith
  · have := hW i (fun j => S.αF j 0 * S.αF j 1)
    simp only [← mul_assoc] at this
    simp only [b, kF]; linarith
  · have := hW i (fun j => S.αF j 1 * S.αF j 1)
    simp only [← mul_assoc] at this
    simp only [c, kF]; linarith
  · have := hV i (fun j => S.pR j μ)
    have hk := S.kP_ge μ
    have : 0 ≤ ∑ j, |S.αF j 0 * S.pF j μ| := by positivity
    have : 0 ≤ ∑ j, |S.αF j 1 * S.pF j μ| := by positivity
    simp only [P0, kF]; linarith
  · have hA := hW i (fun j => S.αF j 0 * S.pF j μ)
    have hB := hV i (fun j => S.pR j μ)
    simp only [← mul_assoc] at hA
    have hk := S.kP_ge μ
    have : 0 ≤ ∑ j, |S.αF j 1 * S.pF j μ| := by positivity
    simp only [P1, kF]
    linarith [abs_sub (∑ j, Wi i j * S.αF j 0 * S.pF j μ) (∑ j, Vi i j * S.pR j μ)]
  · have hA := hW i (fun j => S.αF j 1 * S.pF j μ)
    simp only [← mul_assoc] at hA
    have hk := S.kP_ge μ
    have : 0 ≤ ∑ j, |S.αF j 0 * S.pF j μ| := by positivity
    have : 0 ≤ ∑ j, |S.pR j μ| := by positivity
    simp only [b₁, kF]; linarith
  · have := S.uJ_ge ρ (Wi i) (Vi i) (Wi_nonneg i) (sum_simplexPoint _) (hV1 i) hρ
    simp only [uJ, aJ] at this
    linarith

end FaceShape

/-- **The Minkowski product of `UnifLip` vectors.** -/
theorem UnifLip.dot {ι : Type*} {ρ₀ : ℝ} {x y : ι → ℝ → Fin 4 → ℝ}
    (hx : ∀ μ, UnifLip ρ₀ fun i ρ => ((x i ρ μ : ℝ) : ℂ))
    (hy : ∀ μ, UnifLip ρ₀ fun i ρ => ((y i ρ μ : ℝ) : ℂ)) :
    UnifLip ρ₀ fun i ρ => ((Minkowski.dot (x i ρ) (y i ρ) : ℝ) : ℂ) := by
  simp only [Minkowski.dot]
  push_cast
  exact UnifLip.sum _ fun μ _ => UnifLip.sum _ fun ν _ =>
    ((UnifLip.const _).mul (hx μ)).mul (hy ν)

/-- **The rescaled data of a family of face shapes satisfy uniform bounds**, indexed by the
shape and the barycentric point. -/
theorem faceDataFam {ι : Type*} {p q : ℕ} (S : ι → FaceShape p q) {K ρ₀ : ℝ}
    (hK : ∀ s, (S s).kF ≤ K) (hρ₁ : ρ₀ < 1) :
    FaceData ρ₀ (fun i : ι × FaceIdx p q => FaceShape.a0 (FaceShape.Vi i.2))
      (fun i => (S i.1).a1 (FaceShape.Wi i.2) (FaceShape.Vi i.2))
      (fun i => (S i.1).b (FaceShape.Wi i.2)) (fun i => (S i.1).c (FaceShape.Wi i.2))
      (fun i => (S i.1).P0 (FaceShape.Vi i.2))
      (fun i => (S i.1).P1 (FaceShape.Wi i.2) (FaceShape.Vi i.2))
      (fun i => (S i.1).b₁ (FaceShape.Wi i.2)) K (1 - ρ₀) :=
  have h := fun s => (S s).faceData hρ₁
  ⟨by linarith, fun i => ((h i.1).ha₀ i.2).trans (hK i.1),
    fun i => ((h i.1).ha₁ i.2).trans (hK i.1), fun i => ((h i.1).hb i.2).trans (hK i.1),
    fun i => ((h i.1).hc i.2).trans (hK i.1), fun i μ => ((h i.1).hP₀ i.2 μ).trans (hK i.1),
    fun i μ => ((h i.1).hP₁ i.2 μ).trans (hK i.1), fun i μ => ((h i.1).hb₁ i.2 μ).trans (hK i.1),
    fun i ρ hρ hρ' => (h i.1).hU i.2 ρ hρ hρ'⟩

namespace FaceShape

/-- The bound of the mass terms. -/
noncomputable def kM {p q : ℕ} (S : FaceShape p q) : ℝ :=
  (∑ i, |S.MF i ^ 2 + Minkowski.dot (S.pF i) (S.pF i)|) +
    ∑ j, |S.MR j ^ 2 + Minkowski.dot (S.pR j) (S.pR j)|

variable {ι : Type*} {p q : ℕ} (S : ι → FaceShape p q) {K KM ρ₀ : ℝ}
  (hK : ∀ s, (S s).kF ≤ K) (hρ₁ : ρ₀ < 1)
include hK hρ₁

theorem unifLip_PJ (μ : Fin 4) :
    UnifLip ρ₀ fun (i : ι × FaceIdx p q) ρ => (((S i.1).PJ ρ (Wi i.2) (Vi i.2) μ : ℝ) : ℂ) := by
  have h := faceDataFam S hK hρ₁
  simp only [PJ]
  push_cast
  exact unifLip_aff _ _ (fun i => h.hP₀ i μ) (fun i => h.hP₁ i μ)

theorem unifLip_b₁ (μ : Fin 4) :
    UnifLip ρ₀ fun (i : ι × FaceIdx p q) (_ : ℝ) => (((S i.1).b₁ (Wi i.2) μ : ℝ) : ℂ) :=
  unifLip_ofReal_bdd (fun i : ι × FaceIdx p q => (S i.1).b₁ (Wi i.2) μ) fun i =>
    (faceDataFam S hK hρ₁).hb₁ i μ

/-- **The rescaled second Symanzik function is uniformly Lipschitz in `ρ`**, uniformly over the
family. -/
theorem unifLip_vHat (hKM : ∀ s, (S s).kM ≤ KM) :
    UnifLip ρ₀ fun (i : ι × FaceIdx p q) ρ => (((S i.1).vHat ρ (Wi i.2) (Vi i.2) : ℝ) : ℂ) := by
  have h := faceDataFam S hK hρ₁
  have hF : ∀ i : ι × FaceIdx p q, |(S i.1).mF (Wi i.2)| ≤ KM := fun i => by
    have := abs_sum_mul_le (Wi_nonneg i.2) (Wi_le_one i.2)
      (y := fun j => (S i.1).MF j ^ 2 + Minkowski.dot ((S i.1).pF j) ((S i.1).pF j))
    have : 0 ≤ ∑ j, |(S i.1).MR j ^ 2 + Minkowski.dot ((S i.1).pR j) ((S i.1).pR j)| := by
      positivity
    have := hKM i.1
    simp only [mF, kM] at *; linarith
  have hR : ∀ i : ι × FaceIdx p q, |(S i.1).mR (Vi i.2)| ≤ KM := fun i => by
    have := abs_sum_mul_le (Vi_nonneg i.2) (Vi_le_one i.2)
      (y := fun j => (S i.1).MR j ^ 2 + Minkowski.dot ((S i.1).pR j) ((S i.1).pR j))
    have : 0 ≤ ∑ j, |(S i.1).MF j ^ 2 + Minkowski.dot ((S i.1).pF j) ((S i.1).pF j)| := by
      positivity
    have := hKM i.1
    simp only [mR, kM] at *; linarith
  have hmF := unifLip_ofReal_bdd (ρ₀ := ρ₀) _ hF
  have hmR := unifLip_ofReal_bdd (ρ₀ := ρ₀) _ hR
  have hb := unifLip_ofReal_bdd (ρ₀ := ρ₀) _ h.hb
  have hc := unifLip_ofReal_bdd (ρ₀ := ρ₀) _ h.hc
  have hPP := UnifLip.dot (unifLip_PJ S hK hρ₁) (unifLip_PJ S hK hρ₁)
  have hPb := UnifLip.dot (unifLip_PJ S hK hρ₁) (unifLip_b₁ S hK hρ₁)
  have hbb := UnifLip.dot (x := fun (i : ι × FaceIdx p q) (_ : ℝ) => (S i.1).b₁ (Wi i.2))
    (unifLip_b₁ S hK hρ₁) (unifLip_b₁ S hK hρ₁)
  have hU := h.unifLip_uHat_inv
  have ha := h.unifLip_a
  simp only [vHat, uJ, aJ, div_eq_mul_inv]
  push_cast
  exact (hmR.add (UnifLip.id.mul (hmF.sub hmR))).sub
    ((((hc.mul hPP).sub ((((UnifLip.const 2).mul UnifLip.id).mul hb).mul hPb)).add
      ((UnifLip.id.mul ha).mul hbb)).mul hU)

end FaceShape

/-- A lower bound for `ρ > 0` passes to `ρ = 0` through a Lipschitz bound at `0`. -/
theorem le_of_lip {f : ℝ → ℝ} {c L ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hc : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → c ≤ f ρ) (hL : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → |f ρ - f 0| ≤ L * ρ) :
    c ≤ f 0 := by
  have ht : Tendsto (fun ρ : ℝ => f 0 + L * ρ) (𝓝[>] 0) (𝓝 (f 0 + L * 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_const.add (continuous_const.mul continuous_id)).tendsto 0)
  rw [mul_zero, add_zero] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT hρ₀] with ρ hρ
  have h1 := hc ρ hρ.1 hρ.2.le
  have h2 := hL ρ hρ.1 hρ.2.le
  linarith [le_abs_self (f ρ - f 0)]

namespace FaceShape

variable {p q : ℕ} (S : FaceShape p q)

/-- **The lower bound of `vHat` on `[0, ρ₀]`**, from a lower bound of the raw `V₀` for `ρ > 0`. -/
theorem vHat_ge {ρ₀ c₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1)
    (hV : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet p ×ˢ simplexSet q,
      c₁ ≤ symanzikV S.α S.pp S.M (joinZ ρ (simplexPoint x.1) (simplexPoint x.2)))
    (i : FaceIdx p q) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ ρ₀) : c₁ ≤ S.vHat ρ (Wi i) (Vi i) := by
  have hpos : ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → c₁ ≤ S.vHat ρ (Wi i) (Vi i) := fun ρ h0 h1 => by
    have hu := S.uJ_ge ρ (Wi i) (Vi i) (Wi_nonneg i) (sum_simplexPoint _) (sum_simplexPoint _)
      h0.le
    rw [← S.symanzikV_join_eq ρ _ _ h0.ne' (by linarith)]
    exact hV ρ h0 h1 i.1 i.2
  rcases hρ.lt_or_eq with h0 | rfl
  · exact hpos ρ h0 hρ'
  · obtain ⟨B, L, hBL⟩ := unifLip_vHat (fun _ : Unit => S) (fun _ => le_rfl) hρ₁
      (fun _ => le_rfl)
    refine le_of_lip (f := fun ρ => S.vHat ρ (Wi i) (Vi i)) (L := L) hρ₀ hpos fun ρ h0 h1 => ?_
    have := (hBL ((), i) ρ h0.le h1).2
    rwa [← ofReal_sub, norm_real, Real.norm_eq_abs] at this

end FaceShape

end QED.GradedProof.RPi4

end
