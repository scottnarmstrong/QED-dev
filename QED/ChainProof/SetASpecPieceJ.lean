/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecForm

/-!
# Set (a): a two-loop vacuum-polarization piece has the spectral tensor form

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
The fixed-`ε` analogue of `QED.GradedProof.VP2.vpj_piece`: a numerator tensor with the refined
bound, covariant (`QED.GradedProof.VP2.TCov2`) and polynomial along affine loop momenta
(`SAPolyK`), over the lines of a shape `sh` of a vacuum-polarization routing (`base`, external
coefficients `c`) with the flow certificate of `vpj_piece`, gives a family `SAJ M_lo` (`saj_piece`).

* `coeffOne_congr`, `coeffTwo_congr`, `coeffThree_congr`, `saPieceSpec_congr`: the coefficients
  depend only on the numerator function;
* `measurable_saMass`, `measurable_saXiAt`: the parameters of the factor are measurable;
* `saFlow_sq_le`: the flow certificate `|f(y₁)| + |f(y₂)| ≤ 1` of `vpj_piece` gives the certificate
  `f((y₁ + y₂)/2)² ≤ 1/4` of `QED.ChainProof.SetASpec.setASpec_piece_eq_spectral`;
* **`saj_piece`**.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.VPHalfAtAssembly
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly propDenom)
open QED.GradedProof.VP2 (TCov2 good_of_poly)
open QED.TwoLoop.PauliZeroExplicit.NumeratorCongr (contractTwo_congr contractFour_congr)
open QED.TwoLoop.LimitCovariance (symanzikMatrix_transpose)

variable {m : ℕ}

/-! ### Congruence -/

section Congr

variable {Q Q' : LoopQuartic} (h : Q.eval = Q'.eval) (α : Fin (m + 1) → Fin 2 → ℝ)
include h

theorem coeffOne_congr (p : Fin (m + 1) → Fin 4 → ℝ) : coeffOne Q α p = coeffOne Q' α p := by
  funext x
  simp only [coeffOne, h]

theorem coeffTwo_congr (p : Fin (m + 1) → Fin 4 → ℝ) : coeffTwo Q α p = coeffTwo Q' α p := by
  funext x
  simp only [coeffTwo, contractTwo_congr h (symanzikMatrix_transpose α _)]

theorem coeffThree_congr : coeffThree Q α = coeffThree Q' α := by
  funext x
  simp only [coeffThree, contractFour_congr h (symanzikMatrix_transpose α _)]

theorem saPieceSpec_congr (c M : Fin (m + 1) → ℝ) (ε : ℝ) (k : Fin 4 → ℝ) :
    saPieceSpec Q α c M ε k = saPieceSpec Q' α c M ε k := by
  funext x
  simp only [saPieceSpec, coeffOne_congr h, coeffTwo_congr h, coeffThree_congr h]

end Congr

/-! ### Measurability -/

theorem measurable_saMass (M : Fin (m + 1) → ℝ) : Measurable (saMass (m := m) M) := by
  unfold saMass saMassSq
  exact (Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_simplexPoint').mul continuous_const)).measurable

theorem measurable_saXiAt (α : Fin (m + 1) → Fin 2 → ℝ) (c : Fin (m + 1) → ℝ) :
    Measurable (saXiAt α c) := by
  set e : Fin 4 → ℝ := ![0, 1, 0, 0]
  have he : Minkowski.dot e e = 1 := by simp [e, Minkowski.dot_eq]
  have hr : (fun x : Fin m → ℝ => remainder α (simplexPoint x) c) =
      fun x => symanzikV α (fun i => c i • e) 0 (simplexPoint x) := by
    funext x
    rw [setASpec_symanzikV_twoPoint, he]
    simp [saMassSq]
  have hm : Measurable fun x : Fin m → ℝ => remainder α (simplexPoint x) c := by
    rw [hr]
    exact (measurable_symanzikV α _ 0).comp continuous_simplexPoint'.measurable
  have hxi : Continuous saXi := by
    unfold saXi
    fun_prop
  exact hxi.measurable.comp hm

/-! ### The flow certificate -/

theorem saFlow_sq_le {a : Fin 2 → ℝ} {b : ℝ} {y₁ y₂ : Fin 2 → ℝ}
    (h : |∑ s, a s * y₁ s + b| + |∑ s, a s * y₂ s + b| ≤ 1) :
    (∑ s, a s * ((1 / 2 : ℝ) • (y₁ + y₂)) s + b) ^ 2 ≤ 1 / 4 := by
  have e : ∑ s, a s * ((1 / 2 : ℝ) • (y₁ + y₂)) s + b =
      ((∑ s, a s * y₁ s + b) + (∑ s, a s * y₂ s + b)) / 2 := by
    simp only [Fin.sum_univ_two, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [e]
  have h1 := abs_add_le (∑ s, a s * y₁ s + b) (∑ s, a s * y₂ s + b)
  have h2 : |((∑ s, a s * y₁ s + b) + (∑ s, a s * y₂ s + b)) / 2| ≤ 1 / 2 := by
    rw [abs_div, abs_two]
    linarith
  have h3 := sq_abs (((∑ s, a s * y₁ s + b) + (∑ s, a s * y₂ s + b)) / 2)
  nlinarith [abs_nonneg (((∑ s, a s * y₁ s + b) + (∑ s, a s * y₂ s + b)) / 2)]

/-! ### The piece -/

/-- **The spectral form of the joint integral of a piece with a covariant numerator.** -/
theorem setASpec_pieceSpec_form {N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hQ : ∀ k μ ν, ∃ Q : LoopQuartic, Q.eval = fun ℓ => N k ℓ μ ν) (hcov : TCov2 N)
    (hK : SAPolyK 4 N) (α : Fin (m + 1) → Fin 2 → ℝ) (c M : Fin (m + 1) → ℝ)
    (hI : ∀ k μ ν, IntegrableOn (fun x => saT1 N α c x k μ ν) (simplexSet m) ∧
      IntegrableOn (fun x => saT2 N α c x k μ ν) (simplexSet m) ∧
      IntegrableOn (fun x => saT3 N α x k μ ν) (simplexSet m))
    {Mlo : ℝ} (hae : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      Mlo ≤ saMass M x ∧ saXiAt α c x ∈ Ioo (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    SAForm Mlo ε fun k μ ν =>
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m, saPieceSpec (saQ N k μ ν) α c M ε k x := by
  have hmass := measurable_saMass (m := m) M
  have hxi := measurable_saXiAt (m := m) α c
  have hD : ∀ (r : ℕ) (k : Fin 4 → ℝ), AEStronglyMeasurable
      (fun x => (fDen (saMass M x) ε (saXiAt α c x) k ^ r)⁻¹) (volume.restrict (simplexSet m)) :=
    fun r k => (((measurable_fDen _ _ hmass hxi ε k).pow_const r).inv).aestronglyMeasurable
  have hDb : ∀ (r : ℕ) (k : Fin 4 → ℝ), ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      ‖(fDen (saMass M x) ε (saXiAt α c x) k ^ r)⁻¹‖ ≤ (ε ^ r)⁻¹ :=
    fun r k => Eventually.of_forall fun x => norm_fDen_inv_pow_le hε _ _ k r
  -- the three coefficient families, each `X(k²) g + Y(k²) k k`
  have F1 : SAForm Mlo ε fun k μ ν => ∫ x in simplexSet m, saT1 N α c x k μ ν *
      (fDen (saMass M x) ε (saXiAt α c x) k ^ (m - 3))⁻¹ :=
    ⟨saTerms5 (fun x => saT1 N α c x) (m - 3) (saMass M) (saXiAt α c),
      saTerms5_good _ _ _ hmass hxi (fun k μ ν => (hI k μ ν).1) hae,
      fun k μ ν => saTerms5_integral rfl hε _ _ _ hmass hxi (fun k μ ν => (hI k μ ν).1)
        (fun x => (saT1_cov α c hQ hcov x).eq_gk (saT1_poly α c hQ hK x)) k μ ν⟩
  have F2 : SAForm Mlo ε fun k μ ν => ∫ x in simplexSet m, saT2 N α c x k μ ν *
      (fDen (saMass M x) ε (saXiAt α c x) k ^ (m - 4))⁻¹ :=
    ⟨saTerms5 (fun x => saT2 N α c x) (m - 4) (saMass M) (saXiAt α c),
      saTerms5_good _ _ _ hmass hxi (fun k μ ν => (hI k μ ν).2.1) hae,
      fun k μ ν => saTerms5_integral rfl hε _ _ _ hmass hxi (fun k μ ν => (hI k μ ν).2.1)
        (fun x => (saT2_cov α c hQ hcov x).eq_gk (saT2_poly α c hQ hK x)) k μ ν⟩
  have F3 : SAForm Mlo ε fun k μ ν => ∫ x in simplexSet m, saT3 N α x k μ ν *
      (fDen (saMass M x) ε (saXiAt α c x) k ^ (m - 5))⁻¹ :=
    ⟨saTerms5 (fun x => saT3 N α x) (m - 5) (saMass M) (saXiAt α c),
      saTerms5_good _ _ _ hmass hxi (fun k μ ν => (hI k μ ν).2.2) hae,
      fun k μ ν => saTerms5_integral rfl hε _ _ _ hmass hxi (fun k μ ν => (hI k μ ν).2.2)
        (fun x => (saT3_cov α hQ hcov x).eq_gk (saT3_poly α hQ hK x)) k μ ν⟩
  refine ((F1.add F2).add F3).const_mul (-((π : ℂ) ^ 4)) |>.congr fun k μ ν => ?_
  congr 1
  have i1 := ((hI k μ ν).1.mul_bdd (hD _ k) (hDb (m - 3) k))
  have i2 := ((hI k μ ν).2.1.mul_bdd (hD _ k) (hDb (m - 4) k))
  have i3 := ((hI k μ ν).2.2.mul_bdd (hD _ k) (hDb (m - 5) k))
  have h3 := integral_add (i1.add i2) i3
  simp only [Pi.add_apply] at h3
  rw [← integral_add i1 i2, ← h3]
  rfl

/-- **A piece over a shape of a vacuum-polarization routing has the spectral form** (`SAJ`). -/
theorem saj_piece (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
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
    SAJ Mlo fun ε k ℓ i j => N k ℓ i j * ∏ l,
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
  -- the flow certificate of the spectral form
  have hy : ∀ i, (∑ s, α i s * ((1 / 2 : ℝ) • (y₁ + y₂)) s + c' i) ^ 2 ≤ 1 / 4 := by
    intro i
    have h := hflow (sh i)
    refine saFlow_sq_le (a := fun s => (base (sh i) s : ℝ)) (b := c (sh i)) (h.trans ?_)
    split_ifs <;> norm_num
  -- the coefficients are integrable
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
  intro ε hε
  have hint : ∀ k i j, QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => N k ℓ i j * ∏ l,
      (propDenom (Ms l) ε (lineMomentum (castLoopMatrix base) (fun r => c r • k) (sh l)
        ℓ))⁻¹ := by
    intro k i j
    have h := (show QED.TwoLoop.jointEnergyFirstIntegrable 2
        (fun ℓ => (Q k i j).eval ℓ * ∏ l, (lineDenom α (fun l => c' l • k) Ms ε l ℓ)⁻¹) from by
      rcases hq k i j with h7 | hq0
      · exact jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined _ _ _ _
          h7 hε hcrit' (hb k i j)
      · exact jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic _ _ _ _
          hq0 h6 hε hcrit' (hb k i j))
    rw [he] at h
    exact h
  refine ⟨hint, (setASpec_pieceSpec_form hQ hcov hK α c' Ms hI hae hε).congr fun k i j => ?_⟩
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
