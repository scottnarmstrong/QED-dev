/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitLimit

/-!
# Multi-denominator two-loop vertex units: repeated and rescaled lines

Helper level for set (c) (stage L2). The element photon line of the classes `repB`, `repD` is,
at fixed regulators, a product of several denominators with the momentum `k` of one photon line of
the two-loop vertex: the four photon-type denominators of `D(k) · D(k)` and, for `repB`, one
spectral denominator of the dispersion of `Π_ε(k)`. This file gives the line-level facts needed to
run the parametric engine on such a product.

**Repeated, rescaled lines.** A graph `α'ᵢ = κᵢ α_{σ i}`, `p'ᵢ = κᵢ p_{σ i}` (line `σ i` repeated,
its momentum scaled by `κᵢ ≠ 0`) has the line denominator `κᵢ² k² + M'ᵢ² - iε`. With
`κ = √(x(1-x))` this is the spectral factor `M² + x(1-x) k² - iε` of the one-loop vacuum
polarization (the `fDen` of set (a)), so the *mixed prescription*
`(k² + μ² - iε/w)⁻¹ = w (w k² + w μ² - iε)⁻¹`, `w = x(1-x)`, is a line of the engine with the
single prescription `ε` (`inv_spectral_eq`): no per-line `ε` scaling is needed.

* `noSubdivergenceRefined_scale_comp`: the numerator-aware criterion survives repeating lines
  (the counts of non-parallel lines only grow; parallelism is unchanged by `κᵢ ≠ 0`);
* `refinedBound_map`: the pointwise numerator bound only sees the numerator lines `E`;
* `symanzikV_scale`: `V` of the rescaled graph is `∑ᵢ zᵢ (M'ᵢ² - κᵢ² Mᵢ²) + S · V(y)`, with
  `S = ∑ᵢ κᵢ² zᵢ` and `yᵢ = κᵢ² zᵢ / S` on the simplex;
* **`le_symanzikV_scale_comp_of`**: a lower bound `c` for the original graph holds for the
  repeated, rescaled graph whenever `κᵢ² M_{σ i}² + (1 - κᵢ²) c ≤ M'ᵢ²`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.Integration.TwoLoop (symanzikU symanzikV symanzikMatrix symanzikVector pairDet
  NoSubdivergenceRefined RefinedBound lineWeight lineDenom lineMomentum mergeWeights)

/-! ### The numerator-aware criterion and the numerator bound -/

section Transfer

variable {n q : ℕ}

theorem pairDet_scale_comp (κ : Fin (q + 1) → ℝ) (α : Fin (n + 1) → Fin 2 → ℝ)
    (ρ : Fin (q + 1) → Fin (n + 1)) (i j : Fin (q + 1)) :
    pairDet (fun i => κ i • α (ρ i)) i j = κ i * κ j * pairDet α (ρ i) (ρ j) := by
  simp only [pairDet, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Repeating rescaled lines preserves the numerator-aware criterion.** If `ρ ∘ ι = id`, the
rows on the image of `ι` are the original rows and every scale is nonzero, the criterion for
`(E, α)` gives the criterion for `(ι E, κ α ∘ ρ)`. -/
theorem noSubdivergenceRefined_scale_comp {k : ℕ} {E : Finset (Fin (n + 1))}
    {α : Fin (n + 1) → Fin 2 → ℝ} (h : NoSubdivergenceRefined k E α)
    (ρ : Fin (q + 1) → Fin (n + 1)) (ι : Fin (n + 1) ↪ Fin (q + 1)) (hρι : ∀ j, ρ (ι j) = j)
    (κ : Fin (q + 1) → ℝ) (hκ : ∀ i, κ i ≠ 0) :
    NoSubdivergenceRefined k (E.map ι) (fun i => κ i • α (ρ i)) := by
  intro i
  have hd : ∀ j, pairDet (fun i => κ i • α (ρ i)) i j ≠ 0 ↔ pairDet α (ρ i) (ρ j) ≠ 0 :=
    fun j => by
      rw [pairDet_scale_comp]
      exact ⟨fun h' h0 => h' (by rw [h0, mul_zero]), fun h' => mul_ne_zero
        (mul_ne_zero (hκ i) (hκ j)) h'⟩
  have hE : ((E.map ι).filter fun e => pairDet (fun i => κ i • α (ρ i)) i e ≠ 0).card =
      (E.filter fun e => pairDet α (ρ i) e ≠ 0).card := by
    rw [Finset.filter_map, Finset.card_map]
    congr 1
    refine Finset.filter_congr fun e _ => ?_
    simp only [Function.comp_apply, hd, hρι]
  have hU : (Finset.univ.filter fun j => pairDet α (ρ i) j ≠ 0).card ≤
      (Finset.univ.filter fun j => pairDet (fun i => κ i • α (ρ i)) i j ≠ 0).card := by
    rw [← Finset.card_map ι]
    refine Finset.card_le_card fun j hj => ?_
    obtain ⟨j₀, hj₀, rfl⟩ := Finset.mem_map.mp hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀ ⊢
    rw [hd, hρι]
    exact hj₀
  have := h (ρ i)
  rw [hE]
  omega

/-- **The numerator bound only sees the numerator lines.** -/
theorem refinedBound_map {α : Fin (n + 1) → Fin 2 → ℝ} {α' : Fin (q + 1) → Fin 2 → ℝ}
    {E : Finset (Fin (n + 1))} {k : ℕ} {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (ι : Fin (n + 1) ↪ Fin (q + 1)) (h : ∀ e ∈ E, α' (ι e) = α e) (hB : RefinedBound α E k F) :
    RefinedBound α' (E.map ι) k F := by
  obtain ⟨C, hC, hF⟩ := hB
  refine ⟨C, hC, fun A hA ℓ => ?_⟩
  have hw : lineWeight α' (E.map ι) A = lineWeight α E A := by
    unfold lineWeight
    rw [Finset.prod_map]
    exact Finset.prod_congr rfl fun e he => by rw [h e he]
  rw [hw]
  exact hF A hA ℓ

end Transfer

/-! ### Rescaled lines and the second Symanzik function -/

section Scale

variable {n : ℕ}

theorem dot_smul_smul_sq (t : ℝ) (x y : Fin 4 → ℝ) :
    Minkowski.dot (t • x) (t • y) = t ^ 2 * Minkowski.dot x y := by
  simp only [Minkowski.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring

theorem symanzikMatrix_scale (κ : Fin (n + 1) → ℝ) (α : Fin (n + 1) → Fin 2 → ℝ)
    (z : Fin (n + 1) → ℝ) :
    symanzikMatrix (fun i => κ i • α i) z = symanzikMatrix α fun i => κ i ^ 2 * z i := by
  ext s t
  simp only [symanzikMatrix, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symanzikVector_scale (κ : Fin (n + 1) → ℝ) (α : Fin (n + 1) → Fin 2 → ℝ)
    (p : Fin (n + 1) → Fin 4 → ℝ) (z : Fin (n + 1) → ℝ) :
    symanzikVector (fun i => κ i • α i) (fun i => κ i • p i) z =
      symanzikVector α p fun i => κ i ^ 2 * z i := by
  funext s μ
  simp only [symanzikVector, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symanzikMatrix_mul (t : ℝ) (α : Fin (n + 1) → Fin 2 → ℝ) (z : Fin (n + 1) → ℝ) :
    symanzikMatrix α (fun i => t * z i) = t • symanzikMatrix α z := by
  ext s u
  simp only [symanzikMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symanzikVector_mul (t : ℝ) (α : Fin (n + 1) → Fin 2 → ℝ) (p : Fin (n + 1) → Fin 4 → ℝ)
    (z : Fin (n + 1) → ℝ) :
    symanzikVector α p (fun i => t * z i) = fun s => t • symanzikVector α p z s := by
  funext s μ
  simp only [symanzikVector, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symanzikU_mul (t : ℝ) (α : Fin (n + 1) → Fin 2 → ℝ) (z : Fin (n + 1) → ℝ) :
    symanzikU α (fun i => t * z i) = t ^ 2 * symanzikU α z := by
  rw [symanzikU, symanzikMatrix_mul, Matrix.det_smul, Fintype.card_fin, symanzikU]

/-- The quadratic part of `V`: `∑ₛₜ (A⁻¹)ₛₜ Bₛ·Bₜ`. -/
noncomputable def vQuadPart (α : Fin (n + 1) → Fin 2 → ℝ) (p : Fin (n + 1) → Fin 4 → ℝ)
    (z : Fin (n + 1) → ℝ) : ℝ :=
  ∑ s, ∑ t, (symanzikMatrix α z)⁻¹ s t *
    Minkowski.dot (symanzikVector α p z s) (symanzikVector α p z t)

theorem quadPart_mul {t : ℝ} (ht : t ≠ 0) (α : Fin (n + 1) → Fin 2 → ℝ)
    (p : Fin (n + 1) → Fin 4 → ℝ) (z : Fin (n + 1) → ℝ) :
    vQuadPart α p (fun i => t * z i) = t * vQuadPart α p z := by
  unfold vQuadPart
  rw [symanzikMatrix_mul, symanzikVector_mul]
  have hinv : (t • symanzikMatrix α z)⁻¹ = t⁻¹ • (symanzikMatrix α z)⁻¹ := by
    by_cases hd : (symanzikMatrix α z).det = 0
    · have hd' : (t • symanzikMatrix α z).det = 0 := by
        rw [Matrix.det_smul, hd, mul_zero]
      rw [Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hd']; exact not_isUnit_zero),
        Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hd]; exact not_isUnit_zero), smul_zero]
    · have := Matrix.inv_smul' (symanzikMatrix α z) (Units.mk0 t ht)
        (isUnit_iff_ne_zero.mpr hd)
      simpa [Units.smul_def] using this
  rw [hinv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, dot_smul_smul_sq]
  field_simp

theorem symanzikV_eq_quadPart (α : Fin (n + 1) → Fin 2 → ℝ) (p : Fin (n + 1) → Fin 4 → ℝ)
    (M : Fin (n + 1) → ℝ) (z : Fin (n + 1) → ℝ) :
    symanzikV α p M z = ∑ i, z i * (M i ^ 2 + Minkowski.dot (p i) (p i)) - vQuadPart α p z :=
  rfl

/-- **`V` of a rescaled graph.** For `S = ∑ᵢ κᵢ² zᵢ ≠ 0` and any reference masses `M`,
`V(κα, κp, M'; z) = ∑ᵢ zᵢ (M'ᵢ² - κᵢ² Mᵢ²) + S · V(α, p, M; y)`, `yᵢ = κᵢ² zᵢ / S`. -/
theorem symanzikV_scale (κ : Fin (n + 1) → ℝ) (α : Fin (n + 1) → Fin 2 → ℝ)
    (p : Fin (n + 1) → Fin 4 → ℝ) (M' M : Fin (n + 1) → ℝ) (z : Fin (n + 1) → ℝ)
    (hS : ∑ i, κ i ^ 2 * z i ≠ 0) :
    symanzikV (fun i => κ i • α i) (fun i => κ i • p i) M' z =
      ∑ i, z i * (M' i ^ 2 - κ i ^ 2 * M i ^ 2) +
        (∑ i, κ i ^ 2 * z i) * symanzikV α p M fun i => κ i ^ 2 * z i / ∑ j, κ j ^ 2 * z j := by
  set S := ∑ i, κ i ^ 2 * z i with hSdef
  have hy : (fun i => κ i ^ 2 * z i) = fun i => S * (κ i ^ 2 * z i / S) := by
    funext i
    field_simp
  have hq : vQuadPart (fun i => κ i • α i) (fun i => κ i • p i) z =
      S * vQuadPart α p (fun i => κ i ^ 2 * z i / S) := by
    unfold vQuadPart
    rw [symanzikMatrix_scale, symanzikVector_scale]
    change vQuadPart α p (fun i => κ i ^ 2 * z i) = _
    conv_lhs => rw [hy]
    exact quadPart_mul hS _ _ _
  rw [symanzikV_eq_quadPart, symanzikV_eq_quadPart, hq, mul_sub, Finset.mul_sum]
  simp only [dot_smul_smul_sq]
  have h : ∀ i, S * (κ i ^ 2 * z i / S * (M i ^ 2 + Minkowski.dot (p i) (p i))) =
      κ i ^ 2 * z i * (M i ^ 2 + Minkowski.dot (p i) (p i)) := fun i => by
    field_simp
  simp only [h]
  have h2 : ∑ i, z i * (M' i ^ 2 + κ i ^ 2 * Minkowski.dot (p i) (p i)) =
      ∑ i, (z i * (M' i ^ 2 - κ i ^ 2 * M i ^ 2) +
        κ i ^ 2 * z i * (M i ^ 2 + Minkowski.dot (p i) (p i))) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h2, Finset.sum_add_distrib]
  ring

theorem symanzikU_scale (κ : Fin (n + 1) → ℝ) (α : Fin (n + 1) → Fin 2 → ℝ)
    (z : Fin (n + 1) → ℝ) :
    symanzikU (fun i => κ i • α i) z = symanzikU α fun i => κ i ^ 2 * z i := by
  rw [symanzikU, symanzikMatrix_scale, symanzikU]

variable {k : ℕ}

/-- **Repeated, rescaled lines preserve lower bounds.** If `c ≤ V(α, p, M)` on the simplex where
`U ≠ 0`, `0 ≤ c`, every scale is nonzero and `κᵢ² M_{σ i}² + (1 - κᵢ²) c ≤ M'ᵢ²`, then
`c ≤ V(κ α∘σ, κ p∘σ, M')` on the simplex where `U ≠ 0`. -/
theorem le_symanzikV_scale_comp_of {σ : Fin (k + 1) → Fin (n + 1)}
    {α : Fin (n + 1) → Fin 2 → ℝ} {p : Fin (n + 1) → Fin 4 → ℝ} {M : Fin (n + 1) → ℝ}
    {κ M' : Fin (k + 1) → ℝ} {c : ℝ}
    (hbase : ∀ w : Fin (n + 1) → ℝ, (∀ i, 0 ≤ w i) → ∑ i, w i = 1 → symanzikU α w ≠ 0 →
      c ≤ symanzikV α p M w)
    (hκ : ∀ i, κ i ≠ 0) (hM : ∀ i, κ i ^ 2 * M (σ i) ^ 2 + (1 - κ i ^ 2) * c ≤ M' i ^ 2)
    {z : Fin (k + 1) → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (fun i => κ i • α (σ i)) z ≠ 0) :
    c ≤ symanzikV (fun i => κ i • α (σ i)) (fun i => κ i • p (σ i)) M' z := by
  set S := ∑ i, κ i ^ 2 * z i with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hz i)
  have hS : S ≠ 0 := by
    intro h0
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (sq_nonneg (κ i)) (hz i)).mp h0
    have hz0 : ∀ i, z i = 0 := fun i =>
      (mul_eq_zero.mp (h i (Finset.mem_univ i))).resolve_left (pow_ne_zero 2 (hκ i))
    simp [hz0] at hz1
  have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
  set y : Fin (k + 1) → ℝ := fun i => κ i ^ 2 * z i / S with hydef
  have hy : ∀ i, 0 ≤ y i := fun i => div_nonneg (mul_nonneg (sq_nonneg _) (hz i)) hS0
  have hy1 : ∑ i, y i = 1 := by
    simp only [hydef, ← Finset.sum_div]
    exact div_self hS
  have hUy : symanzikU (fun i => α (σ i)) y ≠ 0 := by
    rw [symanzikU_scale (fun i => κ i) (fun i => α (σ i))] at hU
    have hyz : (fun i => κ i ^ 2 * z i) = fun i => S * y i := by
      funext i
      simp only [hydef]
      field_simp
    rw [hyz, symanzikU_mul] at hU
    exact right_ne_zero_of_mul hU
  have hb : c ≤ symanzikV (fun i => α (σ i)) (fun i => p (σ i)) (fun i => M (σ i)) y :=
    QED.Integration.TwoLoop.le_symanzikV_comp_of hbase (fun _ => le_rfl) hy hy1 hUy
  rw [symanzikV_scale κ (fun i => α (σ i)) (fun i => p (σ i)) M' (fun i => M (σ i)) z hS]
  change c ≤ ∑ i, z i * (M' i ^ 2 - κ i ^ 2 * M (σ i) ^ 2) + S * symanzikV _ _ _ y
  have h1 : c = ∑ i, z i * c := by rw [← Finset.sum_mul, hz1, one_mul]
  have h2 : ∑ i, z i * c ≤ ∑ i, z i * (M' i ^ 2 - κ i ^ 2 * M (σ i) ^ 2) + S * c := by
    rw [hSdef, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by nlinarith [hM i, hz i]
  have h3 : S * c ≤ S * symanzikV (fun i => α (σ i)) (fun i => p (σ i)) (fun i => M (σ i)) y :=
    mul_le_mul_of_nonneg_left hb hS0
  linarith

end Scale

/-! ### The spectral factor as a rescaled line -/

/-- **A rescaled line is a spectral factor.** The line momentum of `κ α`, `κ p` is `κ k`, so its
denominator is `κ² k² + M² - iε`; with `κ² = x(1-x)` this is `M² + x(1-x) k² - iε`. -/
theorem lineDenom_scale {n : ℕ} (κ : Fin (n + 1) → ℝ) (α : Fin (n + 1) → Fin 2 → ℝ)
    (p : Fin (n + 1) → Fin 4 → ℝ) (M : Fin (n + 1) → ℝ) (ε : ℝ) (i : Fin (n + 1))
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (fun i => κ i • α i) (fun i => κ i • p i) M ε i ℓ =
      ((κ i ^ 2 * Minkowski.dot (lineMomentum α p i ℓ) (lineMomentum α p i ℓ) + M i ^ 2 : ℝ) :
        ℂ) - (ε : ℂ) * I := by
  have h : lineMomentum (fun i => κ i • α i) (fun i => κ i • p i) i ℓ =
      κ i • lineMomentum α p i ℓ := by
    funext μ
    simp only [lineMomentum, Pi.smul_apply, smul_eq_mul]
    rw [mul_add]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [lineDenom, h, dot_smul_smul_sq]

/-- **The mixed prescription is a rescaled line.** For `w > 0`:
`(k² + μ² - iε/w)⁻¹ = w (w k² + w μ² - iε)⁻¹`. -/
theorem inv_spectral_eq {w : ℝ} (hw : 0 < w) (k2 μ ε : ℝ) :
    (((k2 + μ ^ 2 : ℝ) : ℂ) - ((ε / w : ℝ) : ℂ) * I)⁻¹ =
      (w : ℂ) * (((w * k2 + w * μ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ := by
  have hw' : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
  have e : ((w * k2 + w * μ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I =
      (w : ℂ) * (((k2 + μ ^ 2 : ℝ) : ℂ) - ((ε / w : ℝ) : ℂ) * I) := by
    push_cast
    field_simp
  rw [e, mul_inv, ← mul_assoc, mul_inv_cancel₀ hw', one_mul]

end QED.ChainProof.SetCUnitM

end
