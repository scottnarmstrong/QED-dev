/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellIBP
public import QED.ChainProof.SetCRegDispShellSEProd
public import QED.TwoLoop.VPHalfAtGenSpec
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (c): the spectral integrand of the self-energy class, decomposition and bounds

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S3 of the plan (the exchange of
the Feynman parameter `x` of the inner loop with the energy-first integral). The `x`-integrand
`seGInt` of `QED/ChainProof/SetCRegDispShellIBP.lean` is written as a combination of the
self-energy building blocks `QED.ChainProof.SetCRegDispSE.seProd` of
`QED/ChainProof/SetCRegDispShellSEProd.lean`:

* `seGInt_eq_dirac`: with `s = k²`, `D_e = (p - k)² + m² - iε`,
  `seGInt = K d(k)² R_x(s) D_e⁻¹ (i c₁ w₁(x) (s L(k) - 2 Q(k)) + ε c₂ x G(k))`, where
  `R_x = vpRatSum`, `L = (-3m - p̸ + 3k̸)_{αβ}`, `Q = (p·k) (k̸)_{αβ}`,
  `G = (-4m - 2p̸ + 2k̸)_{αβ}`;
* `seGInt_eq_pieces`: for `0 < x < 1`, using `d = (Λ² - m_γ²)/(D_{m_γ} D_Λ)` and the factored form
  `s/(M² + x(1-x)s - iε) = t⁻¹ (s - s² D_μ⁻¹)` (`t = M² - iε`, `μ² = M²/(x(1-x))`), the integrand
  is a sum over the loop flavours of `(k²)ʲ seProd` with the photon masses `m_γ, Λ, m_γ, Λ` and
  possibly `μ`, with coefficients bounded uniformly in `x`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.OneLoop
open QED.TwoLoop.VPHalfAt (vpRatSum)
open QED.TwoLoop.VPHalfAtAssembly (cOne cTwo wOne fDen specMu specEta denom_specMu
  fDen_ne_zero massShift_ne_zero)
open QED.TwoLoop.VPHalfAtLimit (massShift)
open QED.TwoLoop.Insertion (photonScalar)
open QED.ChainProof.SetCRegDispSE (seProd)
open QED.TwoLoop.VPUnitNested (EFInt)
open QED.ChainProof.HCSide (outerF)

/-! ### Numerators -/

/-- The affine numerator `c + b (ℓ̸)_{αβ}`. -/
noncomputable def seAff (c b : ℂ) (α β : Fin 4) (ℓ : Fin 4 → ℝ) : ℂ :=
  c + b * Dirac.slash ℓ α β

/-- The quadratic numerator `(p·ℓ) (ℓ̸)_{αβ}`. -/
noncomputable def seQuad (p : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 4 → ℝ) : ℂ :=
  (Minkowski.dot p ℓ : ℂ) * Dirac.slash ℓ α β

/-- The constant of the numerator of `γ^ν S γ_ν`: `(-4m - 2p̸)_{αβ}`. -/
noncomputable def seCG (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  (-4 * (P.m : ℂ)) * (1 : Matrix (Fin 4) (Fin 4) ℂ) α β - 2 * Dirac.slash p α β

/-- The constant of the numerator `L`: `(-3m - p̸)_{αβ}`. -/
noncomputable def seCL (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  (-3 * (P.m : ℂ)) * (1 : Matrix (Fin 4) (Fin 4) ℂ) α β - Dirac.slash p α β

theorem dot_sub_left (p k : Fin 4 → ℝ) :
    Minkowski.dot (p - k) k = Minkowski.dot p k - Minkowski.dot k k := by
  simp only [Minkowski.dot, Pi.sub_apply, Fin.sum_univ_four]; ring

theorem seChainG_apply (P : Params) (p k : Fin 4 → ℝ) (α β : Fin 4) :
    seChainG P p k α β = (seDen P p k)⁻¹ * seAff (seCG P p α β) 2 α β k := by
  rw [seChainG_eq]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Dirac.slash_sub, smul_eq_mul, seAff, seCG]
  ring

theorem seChainGK_apply (P : Params) (p k : Fin 4 → ℝ) (α β : Fin 4) :
    (Minkowski.dot k k : ℂ) * seChainG P p k α β - seChainK P p k α β =
      (seDen P p k)⁻¹ * ((Minkowski.dot k k : ℂ) * seAff (seCL P p α β) 3 α β k -
        2 * seQuad p α β k) := by
  rw [seChainG_eq, seChainK_eq, dot_sub_left]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Dirac.slash_sub,
    smul_eq_mul, seAff, seCL, seQuad]
  push_cast
  ring

/-- **The Dirac form of the `x`-integrand.** -/
theorem seGInt_eq_dirac (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (x : ℝ)
    (k : Fin 4 → ℝ) :
    seGInt P p α β x k =
      seVK P * photonScalar P.mγ P.Λ P.ε k ^ 2 * vpRatSum P P.ε (Minkowski.dot k k) x *
        (seDen P p k)⁻¹ *
        (I * cOne P * wOne x * ((Minkowski.dot k k : ℂ) * seAff (seCL P p α β) 3 α β k -
            2 * seQuad p α β k) +
          (P.ε : ℂ) * cTwo P * (x : ℂ) * seAff (seCG P p α β) 2 α β k) := by
  rw [seGInt, seChainGK_apply, seChainG_apply]
  ring

theorem seDen_eq_denom (P : Params) (p k : Fin 4 → ℝ) :
    seDen P p k = denom P.m P.ε (-p + k) := by
  have h : Minkowski.dot (-p + k) (-p + k) = Minkowski.dot (p - k) (p - k) := by
    simp only [Minkowski.dot, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Fin.sum_univ_four]
    ring
  rw [seDen, denom, h]

theorem photonScalar_eq_mul (mγ Λ ε : ℝ) (hε : 0 < ε) (k : Fin 4 → ℝ) :
    photonScalar mγ Λ ε k =
      (((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ)) * ((denom mγ ε k)⁻¹ * (denom Λ ε k)⁻¹) := by
  have h1 := QED.TwoLoop.VPHalfAtLimit.denom_ne_zero_of_pos (M := mγ) hε k
  have h2 := QED.TwoLoop.VPHalfAtLimit.denom_ne_zero_of_pos (M := Λ) hε k
  rw [photonScalar]
  change (denom mγ ε k)⁻¹ - (denom Λ ε k)⁻¹ = _
  field_simp
  simp only [denom]
  push_cast
  ring

/-- **The factored form of a spectral denominator**, for `0 < x < 1`:
`(M² + x(1-x)s - iε)⁻¹ = t⁻¹ (1 - s D_μ⁻¹)`. -/
theorem inv_fDen_eq (M : ℝ) {ε x : ℝ} (hε : 0 < ε) (hx : x ∈ Ioo (0 : ℝ) 1)
    (k : Fin 4 → ℝ) :
    (fDen M ε x k)⁻¹ = (massShift M ε)⁻¹ *
      (1 - (Minkowski.dot k k : ℂ) * (denom (specMu M x) (specEta ε x) k)⁻¹) := by
  have h0 : ((x * (1 - x) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (QED.TwoLoop.VPHalfAtAssembly.mem_Ioo_mul_pos hx).ne'
  have hD := fDen_ne_zero M hε x k
  have hS := massShift_ne_zero M hε
  have e : fDen M ε x k = massShift M ε +
      ((x * (1 - x) : ℝ) : ℂ) * ((Minkowski.dot k k : ℝ) : ℂ) := by
    simp only [fDen, massShift, QED.WickModel.vacuumPolarizationFeynmanMass]
    push_cast
    ring
  rw [denom_specMu hx]
  field_simp
  rw [e]
  ring

/-! ### The photon lists -/

/-- The four photon masses `m_γ, Λ, m_γ, Λ` of `d(k)²`. -/
noncomputable def seMs4 (P : Params) : Fin 4 → ℝ := ![P.mγ, P.Λ, P.mγ, P.Λ]

/-- The masses of `d(k)²` and the spectral line of mass `μ`. -/
noncomputable def seMs5 (P : Params) (μ : ℝ) : Fin 5 → ℝ := ![P.mγ, P.Λ, P.mγ, P.Λ, μ]

/-- The prescriptions `ε` of `d(k)²` and `η` of the spectral line. -/
noncomputable def seEs5 (P : Params) (η : ℝ) : Fin 5 → ℝ := ![P.ε, P.ε, P.ε, P.ε, η]

/-- The coefficient of the flavour `f`: `K (Λ² - m_γ²)² c_f (1 - 2x) t_f⁻¹`. -/
noncomputable def seCf (P : Params) (x : ℝ) (f : Fin 3) : ℂ :=
  seVK P * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ) * (P.loopCoeff f : ℂ) * ((1 - 2 * x : ℝ) : ℂ) *
    (massShift (P.mass f) P.ε)⁻¹

/-- The piece of one flavour, with numerators `L`, `Q`, `G` over four photon denominators and
over the four and the spectral line. -/
noncomputable def sePiece (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (x : ℝ) (f : Fin 3)
    (k : Fin 4 → ℝ) : ℂ :=
  let s : ℂ := (Minkowski.dot k k : ℂ)
  let L := seAff (seCL P p α β) 3 α β
  let Q := seQuad p α β
  let G := seAff (seCG P p α β) 2 α β
  let Ms5 := seMs5 P (specMu (P.mass f) x)
  let es5 := seEs5 P (specEta P.ε x)
  I * cOne P * wOne x *
      (s ^ 2 * seProd L P.m (seMs4 P) (fun _ => P.ε) P.ε (-p) k -
        2 * (s * seProd Q P.m (seMs4 P) (fun _ => P.ε) P.ε (-p) k) -
        s ^ 3 * seProd L P.m Ms5 es5 P.ε (-p) k +
        2 * (s ^ 2 * seProd Q P.m Ms5 es5 P.ε (-p) k)) +
    (P.ε : ℂ) * cTwo P * (x : ℂ) *
      (s * seProd G P.m (seMs4 P) (fun _ => P.ε) P.ε (-p) k -
        s ^ 2 * seProd G P.m Ms5 es5 P.ε (-p) k)

/-- **The decomposition of the `x`-integrand**, for `ε > 0` and `0 < x < 1`. -/
theorem seGInt_eq_pieces (P : Params) (hε : 0 < P.ε) (p : Fin 4 → ℝ) (α β : Fin 4) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (k : Fin 4 → ℝ) :
    seGInt P p α β x k = ∑ f, seCf P x f * sePiece P p α β x f k := by
  rw [seGInt_eq_dirac, photonScalar_eq_mul _ _ _ hε, seDen_eq_denom]
  have hR : vpRatSum P P.ε (Minkowski.dot k k) x = ∑ f, (P.loopCoeff f : ℂ) *
      ((1 - 2 * x : ℝ) : ℂ) * (Minkowski.dot k k : ℂ) * (fDen (P.mass f) P.ε x k)⁻¹ := by
    simp only [vpRatSum, fDen, div_eq_mul_inv]
    refine Finset.sum_congr rfl fun f _ => ?_
    push_cast
    ring
  rw [hR]
  simp only [inv_fDen_eq _ hε hx, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [sePiece, seCf, seProd, seMs4, seMs5, seEs5, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
  push_cast
  ring

/-! ### The numerators: energy dependence and growth -/

theorem continuous_slash_apply (α β : Fin 4) : Continuous fun ℓ : Fin 4 → ℝ =>
    Dirac.slash ℓ α β := by
  have hslash : Continuous Dirac.slash := by
    unfold Dirac.slash Minkowski.lower
    fun_prop
  exact hslash.matrix_elem α β

theorem continuous_seAff (c b : ℂ) (α β : Fin 4) : Continuous (seAff c b α β) := by
  unfold seAff
  exact continuous_const.add (continuous_const.mul (continuous_slash_apply α β))

theorem continuous_seQuad (p : Fin 4 → ℝ) (α β : Fin 4) : Continuous (seQuad p α β) := by
  have hd : Continuous fun ℓ : Fin 4 → ℝ => Minkowski.dot p ℓ := by
    unfold Minkowski.dot; fun_prop
  unfold seQuad
  exact (Complex.continuous_ofReal.comp hd).mul (continuous_slash_apply α β)

theorem slash_cons_apply (t : ℝ) (v : Fin 3 → ℝ) (α β : Fin 4) :
    Dirac.slash (Fin.cons t v : Fin 4 → ℝ) α β =
      t * Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ) α β +
        Dirac.slash (Fin.cons 0 v : Fin 4 → ℝ) α β := by
  have h := slash_add_cons 0 t v
  simp only [zero_add] at h
  rw [h, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem dot_cons_right (p : Fin 4 → ℝ) (t : ℝ) (v : Fin 3 → ℝ) :
    Minkowski.dot p (Fin.cons t v : Fin 4 → ℝ) =
      t * Minkowski.dot p (Fin.cons 1 0 : Fin 4 → ℝ) +
        Minkowski.dot p (Fin.cons 0 v : Fin 4 → ℝ) := by
  have e : ∀ (a : ℝ) (w : Fin 3 → ℝ), Minkowski.dot p (Fin.cons a w : Fin 4 → ℝ) =
      -(p 0 * a) + p 1 * w 0 + p 2 * w 1 + p 3 * w 2 := fun a w => by
    rw [Minkowski.dot_eq]; rfl
  rw [e, e, e]
  simp only [Pi.zero_apply]
  ring

theorem seAff_cons (c b : ℂ) (α β : Fin 4) (v : Fin 3 → ℝ) :
    ∃ β' γ : ℂ, ∀ t : ℝ, seAff c b α β (Fin.cons t v : Fin 4 → ℝ) = 0 * (t : ℂ) ^ 2 + β' * t + γ :=
  ⟨b * Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ) α β,
    c + b * Dirac.slash (Fin.cons 0 v : Fin 4 → ℝ) α β, fun t => by
      rw [seAff, slash_cons_apply]; ring⟩

theorem seQuad_cons (p : Fin 4 → ℝ) (α β : Fin 4) (v : Fin 3 → ℝ) :
    ∃ β' γ : ℂ, ∀ t : ℝ, seQuad p α β (Fin.cons t v : Fin 4 → ℝ) =
      ((Minkowski.dot p (Fin.cons 1 0 : Fin 4 → ℝ) : ℂ) *
        Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ) α β) * (t : ℂ) ^ 2 + β' * t + γ :=
  ⟨(Minkowski.dot p (Fin.cons 1 0 : Fin 4 → ℝ) : ℂ) *
      Dirac.slash (Fin.cons 0 v : Fin 4 → ℝ) α β +
    (Minkowski.dot p (Fin.cons 0 v : Fin 4 → ℝ) : ℂ) *
      Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ) α β,
    (Minkowski.dot p (Fin.cons 0 v : Fin 4 → ℝ) : ℂ) *
      Dirac.slash (Fin.cons 0 v : Fin 4 → ℝ) α β, fun t => by
      rw [seQuad, slash_cons_apply, dot_cons_right]; push_cast; ring⟩

/-- The sum of the moduli of the entries `(γ^κ)_{αβ}`. -/
noncomputable def seGs (α β : Fin 4) : ℝ := ∑ κ, ‖Dirac.gamma κ α β‖

theorem seGs_nonneg (α β : Fin 4) : 0 ≤ seGs α β :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_seAff_le (c b : ℂ) (α β : Fin 4) (ℓ : Fin 4 → ℝ) :
    ‖seAff c b α β ℓ‖ ≤ (‖c‖ + ‖b‖ * seGs α β) * (1 + ‖ℓ‖) ^ 1 := by
  have hs := QED.WickModel.SelfEnergyLimit.norm_slash_apply_le ℓ α β
  have hG := seGs_nonneg α β
  rw [seAff, pow_one]
  calc ‖c + b * Dirac.slash ℓ α β‖ ≤ ‖c‖ + ‖b‖ * (seGs α β * ‖ℓ‖) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
        gcongr
        exact hs
    _ ≤ (‖c‖ + ‖b‖ * seGs α β) * (1 + ‖ℓ‖) := by
        nlinarith [norm_nonneg ℓ, norm_nonneg c, mul_nonneg (norm_nonneg b) hG]

theorem norm_seAff_le_sq (c b : ℂ) (α β : Fin 4) (ℓ : Fin 4 → ℝ) :
    ‖seAff c b α β ℓ‖ ≤ (‖c‖ + ‖b‖ * seGs α β) * (1 + ‖ℓ‖) ^ 2 := by
  refine (norm_seAff_le c b α β ℓ).trans ?_
  have hG := seGs_nonneg α β
  gcongr
  · exact le_add_of_nonneg_right (norm_nonneg ℓ)
  · omega

theorem norm_seQuad_le (p : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 4 → ℝ) :
    ‖seQuad p α β ℓ‖ ≤ (4 * ‖p‖ * seGs α β) * (1 + ‖ℓ‖) ^ 2 := by
  have hs := QED.WickModel.SelfEnergyLimit.norm_slash_apply_le ℓ α β
  have hd := QED.WickModel.VacuumPolarizationLimit.abs_dot_le p ℓ
  have hG := seGs_nonneg α β
  rw [seQuad, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |Minkowski.dot p ℓ| * ‖Dirac.slash ℓ α β‖ ≤ (4 * (‖p‖ * ‖ℓ‖)) * (seGs α β * ‖ℓ‖) := by
        gcongr
        exact hs
    _ = (4 * ‖p‖ * seGs α β) * ‖ℓ‖ ^ 2 := by ring
    _ ≤ (4 * ‖p‖ * seGs α β) * (1 + ‖ℓ‖) ^ 2 := by
        gcongr
        linarith [norm_nonneg ℓ]

/-! ### The engine for the three numerators -/

section Engine

variable {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {Pv : Fin 4 → ℝ}
  (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot Pv Pv) y)

include hM₀ hc₀ hP in
theorem exists_goodEF4_seAff (c b : ℂ) (α β : Fin 4) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Ms es : Fin (k + 2) → ℝ, (∀ j, M₀ ≤ Ms j) → (∀ j, 0 < es j) →
      ∀ ε : ℝ, 0 < ε →
        SetCRegDispSE.GoodEF4 (seProd (seAff c b α β) m Ms es ε Pv) K :=
  SetCRegDispSE.exists_goodEF4_seProd hM₀ hc₀ hP (continuous_seAff c b α β)
    (seAff_cons c b α β) (norm_seAff_le_sq c b α β) (norm_seAff_le c b α β) k (by omega)
    (Or.inl rfl)

include hM₀ hc₀ hP in
theorem exists_goodEF4_seQuad (p : Fin 4 → ℝ) (α β : Fin 4) (k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Ms es : Fin (k + 2) → ℝ, (∀ j, M₀ ≤ Ms j) → (∀ j, 0 < es j) →
      ∀ ε : ℝ, 0 < ε →
        SetCRegDispSE.GoodEF4 (seProd (seQuad p α β) m Ms es ε Pv) K :=
  SetCRegDispSE.exists_goodEF4_seProd hM₀ hc₀ hP (continuous_seQuad p α β)
    (seQuad_cons p α β) (norm_seQuad_le p α β) (norm_seQuad_le p α β) k (by omega)
    (Or.inr hk)

end Engine

/-! ### `seGInt` is `GoodEF4` uniformly in the spectral parameter -/

theorem SEgoodEF4_const_mul_le {F : (Fin 4 → ℝ) → ℂ} {C B : ℝ}
    (hF : SetCRegDispSE.GoodEF4 F C) (c : ℂ) (hc : ‖c‖ ≤ B) :
    SetCRegDispSE.GoodEF4 (fun ℓ => c * F ℓ) (B * C) :=
  (hF.const_mul c).mono' (mul_le_mul_of_nonneg_right hc hF.nonneg_const)

theorem norm_wOne_le {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : ‖wOne x‖ ≤ 1 := by
  obtain ⟨h0, h1⟩ := hx
  rw [wOne, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0,
    mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 h1)]

/-- A bound on the loop coefficients. -/
noncomputable def seCc (P : Params) : ℝ := 1 + |P.c₁| + |P.c₂|

theorem abs_loopCoeff_le (P : Params) (f : Fin 3) : |P.loopCoeff f| ≤ seCc P := by
  have h1 := abs_nonneg P.c₁
  have h2 := abs_nonneg P.c₂
  unfold seCc
  fin_cases f <;> simp [Params.loopCoeff] <;> linarith

theorem norm_seCf_le (P : Params) {M₀ : ℝ} (hM₀ : 0 < M₀) (hmass : ∀ f, M₀ ≤ P.mass f)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (f : Fin 3) :
    ‖seCf P x f‖ ≤ ‖seVK P‖ * ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2) * seCc P * (M₀ ^ 2)⁻¹ := by
  have hMf : 0 < P.mass f := hM₀.trans_le (hmass f)
  have h1 : ‖(massShift (P.mass f) P.ε)⁻¹‖ ≤ (M₀ ^ 2)⁻¹ :=
    (QED.TwoLoop.VPHalfAtAssembly.norm_inv_massShift_le P.ε hMf).trans
      (inv_anti₀ (by positivity) (pow_le_pow_left₀ hM₀.le (hmass f) 2))
  have h2 : |1 - 2 * x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [seCf, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  have := abs_loopCoeff_le P f
  have hc0 : 0 ≤ seCc P := by unfold seCc; positivity
  calc ‖seVK P‖ * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * |P.loopCoeff f| * |1 - 2 * x| *
        ‖(massShift (P.mass f) P.ε)⁻¹‖
      ≤ ‖seVK P‖ * (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * seCc P * 1 * (M₀ ^ 2)⁻¹ := by gcongr
    _ = _ := by ring

/-- The engine bound for a numerator `N`, for `k₀ ≤ k ≤ 3`: one constant `K` for all photon
lists of length `k + 2` with masses `≥ M₀` and positive prescriptions. -/
def SEEng (N : (Fin 4 → ℝ) → ℂ) (m M₀ ε : ℝ) (Pv : Fin 4 → ℝ) (K : ℝ) (k₀ : ℕ) : Prop :=
  ∀ k : ℕ, k₀ ≤ k → k ≤ 3 → ∀ Ms es : Fin (k + 2) → ℝ, (∀ j, M₀ ≤ Ms j) → (∀ j, 0 < es j) →
    SetCRegDispSE.GoodEF4 (seProd N m Ms es ε Pv) K

section EngineK

variable {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {Pv : Fin 4 → ℝ}
  (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot Pv Pv) y)

include hM₀ hc₀ hP in
theorem exists_seEng_seAff (c b : ℂ) (α β : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ SEEng (seAff c b α β) m M₀ ε Pv K 0 := by
  obtain ⟨K0, h0, e0⟩ := exists_goodEF4_seAff hM₀ hc₀ hP c b α β 0
  obtain ⟨K1, h1, e1⟩ := exists_goodEF4_seAff hM₀ hc₀ hP c b α β 1
  obtain ⟨K2, h2, e2⟩ := exists_goodEF4_seAff hM₀ hc₀ hP c b α β 2
  obtain ⟨K3, h3, e3⟩ := exists_goodEF4_seAff hM₀ hc₀ hP c b α β 3
  refine ⟨K0 + K1 + K2 + K3, by positivity, fun k _ hk Ms es hMs hes => ?_⟩
  interval_cases k
  · exact (e0 Ms es hMs hes ε hε).mono' (by linarith)
  · exact (e1 Ms es hMs hes ε hε).mono' (by linarith)
  · exact (e2 Ms es hMs hes ε hε).mono' (by linarith)
  · exact (e3 Ms es hMs hes ε hε).mono' (by linarith)

include hM₀ hc₀ hP in
theorem exists_seEng_seQuad (p : Fin 4 → ℝ) (α β : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ SEEng (seQuad p α β) m M₀ ε Pv K 1 := by
  obtain ⟨K1, h1, e1⟩ := exists_goodEF4_seQuad hM₀ hc₀ hP p α β 1 le_rfl
  obtain ⟨K2, h2, e2⟩ := exists_goodEF4_seQuad hM₀ hc₀ hP p α β 2 (by norm_num)
  obtain ⟨K3, h3, e3⟩ := exists_goodEF4_seQuad hM₀ hc₀ hP p α β 3 (by norm_num)
  refine ⟨K1 + K2 + K3, by positivity, fun k hk0 hk Ms es hMs hes => ?_⟩
  interval_cases k
  · exact (e1 Ms es hMs hes ε hε).mono' (by linarith)
  · exact (e2 Ms es hMs hes ε hε).mono' (by linarith)
  · exact (e3 Ms es hMs hes ε hε).mono' (by linarith)

end EngineK

theorem seMs4_ge {P : Params} {M₀ : ℝ} (h1 : M₀ ≤ P.mγ) (h2 : M₀ ≤ P.Λ) :
    ∀ j, M₀ ≤ seMs4 P j := by
  intro j; fin_cases j <;> simp [seMs4] <;> assumption

theorem seMs5_ge {P : Params} {M₀ μ : ℝ} (h1 : M₀ ≤ P.mγ) (h2 : M₀ ≤ P.Λ) (h3 : M₀ ≤ μ) :
    ∀ j, M₀ ≤ seMs5 P μ j := by
  intro j; fin_cases j <;> simp [seMs5] <;> assumption

theorem seEs5_pos {P : Params} {η : ℝ} (h1 : 0 < P.ε) (h2 : 0 < η) : ∀ j, 0 < seEs5 P η j := by
  intro j; fin_cases j <;> simp [seEs5] <;> assumption

theorem le_tail_of_le {n : ℕ} {g : Fin (n + 1) → ℝ} {c : ℝ} (h : ∀ j, c ≤ g j) :
    ∀ j, c ≤ Fin.tail g j := fun j => by simpa only [Fin.tail] using h j.succ

theorem lt_tail_of_lt {n : ℕ} {g : Fin (n + 1) → ℝ} {c : ℝ} (h : ∀ j, c < g j) :
    ∀ j, c < Fin.tail g j := fun j => by simpa only [Fin.tail] using h j.succ

/-- The constant of one flavour piece. -/
noncomputable def seBp (P : Params) (K : ℝ) : ℝ :=
  ‖cOne P‖ * (6 * ((1 + (P.mγ ^ 2 + P.Λ ^ 2 + P.ε)) ^ 3 * K)) +
    P.ε * ‖cTwo P‖ * (2 * ((1 + (P.mγ ^ 2 + P.Λ ^ 2 + P.ε)) ^ 3 * K))

/-- **One flavour piece is `GoodEF4`**, with a constant independent of `x ∈ (0, 1)`. -/
theorem goodEF4_sePiece (P : Params) (hε : 0 < P.ε) {M₀ : ℝ} (hmγ : M₀ ≤ P.mγ)
    (hΛ : M₀ ≤ P.Λ) (p : Fin 4 → ℝ) (α β : Fin 4) {K : ℝ} (hK0 : 0 ≤ K)
    (hL : SEEng (seAff (seCL P p α β) 3 α β) P.m M₀ P.ε (-p) K 0)
    (hQ : SEEng (seQuad p α β) P.m M₀ P.ε (-p) K 1)
    (hG : SEEng (seAff (seCG P p α β) 2 α β) P.m M₀ P.ε (-p) K 1)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (f : Fin 3) (hf : M₀ ≤ P.mass f) (hMf : 0 < P.mass f) :
    SetCRegDispSE.GoodEF4 (sePiece P p α β x f) (seBp P K) := by
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have hT0 : 0 ≤ P.mγ ^ 2 + P.Λ ^ 2 + P.ε := by positivity
  have hTγ : ‖massShift P.mγ P.ε‖ ≤ P.mγ ^ 2 + P.Λ ^ 2 + P.ε :=
    (QED.TwoLoop.VPHalfAtAssembly.norm_massShift_le hε.le).trans (by nlinarith [sq_nonneg P.Λ])
  have hTΛ : ‖massShift P.Λ P.ε‖ ≤ P.mγ ^ 2 + P.Λ ^ 2 + P.ε :=
    (QED.TwoLoop.VPHalfAtAssembly.norm_massShift_le hε.le).trans (by nlinarith [sq_nonneg P.mγ])
  have hle : ∀ j : ℕ, j ≤ 3 → (1 + (P.mγ ^ 2 + P.Λ ^ 2 + P.ε)) ^ j * K ≤
      (1 + (P.mγ ^ 2 + P.Λ ^ 2 + P.ε)) ^ 3 * K := fun j hj =>
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hj) hK0
  have hMs4 := seMs4_ge hmγ hΛ
  have hle1 : (1 + (P.mγ ^ 2 + P.Λ ^ 2 + P.ε)) * K ≤ (1 + (P.mγ ^ 2 + P.Λ ^ 2 + P.ε)) ^ 3 * K := by
    have := hle 1 (by norm_num); rwa [pow_one] at this
  have hμ : M₀ ≤ specMu (P.mass f) x :=
    hf.trans (QED.TwoLoop.VPHalfAtAssembly.specMu_ge hMf hx)
  have hη : 0 < specEta P.ε x := hε.trans_le (QED.TwoLoop.VPHalfAtAssembly.specEta_ge hε hx)
  have hMs5 := seMs5_ge hmγ hΛ hμ
  have hes5 := seEs5_pos (P := P) hε hη
  have hes : ∀ j : Fin 4, 0 < (fun _ => P.ε) j := fun _ => hε
  have a1 := le_tail_of_le hMs4
  have a2 := le_tail_of_le a1
  have e1 := lt_tail_of_lt hes
  have e2 := lt_tail_of_lt e1
  have b1 := le_tail_of_le hMs5
  have b2 := le_tail_of_le b1
  have b3 := le_tail_of_le b2
  have f1 := lt_tail_of_lt hes5
  have f2 := lt_tail_of_lt f1
  have f3 := lt_tail_of_lt f2
  have A1 := SetCRegDispSE.goodEF4_s2 (k := 0) (seMs4 P) (fun _ => P.ε) hε hε hT0 hTγ hTΛ
    (hL 0 le_rfl (by norm_num) _ _ a2 e2)
    (hL 1 (by norm_num) (by norm_num) _ _ a1 e1)
    (hL 2 (by norm_num) (by norm_num) _ _ hMs4 hes)
  have A2 := SetCRegDispSE.goodEF4_s1 (k := 1) (seMs4 P) (fun _ => P.ε) hε hTγ
    (hQ 1 le_rfl (by norm_num) _ _ a1 e1)
    (hQ 2 (by norm_num) (by norm_num) _ _ hMs4 hes)
  have A3 := SetCRegDispSE.goodEF4_s3 (k := 0) (seMs5 P (specMu (P.mass f) x))
    (seEs5 P (specEta P.ε x)) hε hε hε hT0 hTγ hTΛ hTγ
    (hL 0 le_rfl (by norm_num) _ _ b3 f3)
    (hL 1 (by norm_num) (by norm_num) _ _ b2 f2)
    (hL 2 (by norm_num) (by norm_num) _ _ b1 f1)
    (hL 3 (by norm_num) le_rfl _ _ hMs5 hes5)
  have A4 := SetCRegDispSE.goodEF4_s2 (k := 1) (seMs5 P (specMu (P.mass f) x))
    (seEs5 P (specEta P.ε x)) hε hε hT0 hTγ hTΛ
    (hQ 1 le_rfl (by norm_num) _ _ b2 f2)
    (hQ 2 (by norm_num) (by norm_num) _ _ b1 f1)
    (hQ 3 (by norm_num) le_rfl _ _ hMs5 hes5)
  have A5 := SetCRegDispSE.goodEF4_s1 (k := 1) (seMs4 P) (fun _ => P.ε) hε hTγ
    (hG 1 le_rfl (by norm_num) _ _ a1 e1)
    (hG 2 (by norm_num) (by norm_num) _ _ hMs4 hes)
  have A6 := SetCRegDispSE.goodEF4_s2 (k := 1) (seMs5 P (specMu (P.mass f) x))
    (seEs5 P (specEta P.ε x)) hε hε hT0 hTγ hTΛ
    (hG 1 le_rfl (by norm_num) _ _ b2 f2)
    (hG 2 (by norm_num) (by norm_num) _ _ b1 f1)
    (hG 3 (by norm_num) le_rfl _ _ hMs5 hes5)
  have X1 := ((((A1.mono' (hle 2 (by norm_num))).sub
    (SEgoodEF4_const_mul_le (A2.mono' hle1) 2 (by norm_num : ‖(2 : ℂ)‖ ≤ 2))).sub
    (A3.mono' (hle 3 le_rfl))).add
    (SEgoodEF4_const_mul_le (A4.mono' (hle 2 (by norm_num))) 2 (by norm_num : ‖(2 : ℂ)‖ ≤ 2)))
  have X2 := (A5.mono' hle1).sub (A6.mono' (hle 2 (by norm_num)))
  have h1 : ‖I * cOne P * wOne x‖ ≤ ‖cOne P‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_wOne_le hxI)
  have h2 : ‖(P.ε : ℂ) * cTwo P * (x : ℂ)‖ ≤ P.ε * ‖cTwo P‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hε, abs_of_nonneg hxI.1]
    exact mul_le_of_le_one_right (by positivity) hxI.2
  have Y := (SEgoodEF4_const_mul_le X1 _ h1).add (SEgoodEF4_const_mul_le X2 _ h2)
  refine (Y.congr fun ℓ => ?_).mono' (le_of_eq ?_)
  · simp only [sePiece]
  · simp only [seBp]; ring

/-- **`seGInt` is `GoodEF4` with one constant for all `x ∈ (0, 1)`**, below threshold
(`c₀ ≤ y m² + (1 - y) M₀² + y (1 - y) p²` on `[0, 1]`, `M₀` below every mass). -/
theorem exists_goodEF4_seGInt (P : Params) (hε : 0 < P.ε) {M₀ : ℝ} (hM₀ : 0 < M₀)
    (hmγ : M₀ ≤ P.mγ) (hΛ : M₀ ≤ P.Λ) (hmass : ∀ f, M₀ ≤ P.mass f) {c₀ : ℝ} (hc₀ : 0 < c₀)
    {p : Fin 4 → ℝ}
    (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass P.m M₀ (Minkowski.dot (-p) (-p)) y)
    (α β : Fin 4) :
    ∃ C : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, SetCRegDispSE.GoodEF4 (seGInt P p α β x) C := by
  obtain ⟨KL, hKL, hL⟩ := exists_seEng_seAff hM₀.le hc₀ hP (seCL P p α β) 3 α β hε
  obtain ⟨KG, hKG, hG⟩ := exists_seEng_seAff hM₀.le hc₀ hP (seCG P p α β) 2 α β hε
  obtain ⟨KQ, hKQ, hQ⟩ := exists_seEng_seQuad hM₀.le hc₀ hP p α β hε
  set K := KL + KG + KQ
  have hK0 : 0 ≤ K := by positivity
  have mono : ∀ {N : (Fin 4 → ℝ) → ℂ} {K₁ : ℝ} {k₀ : ℕ}, K₁ ≤ K →
      SEEng N P.m M₀ P.ε (-p) K₁ k₀ → SEEng N P.m M₀ P.ε (-p) K k₀ :=
    fun hle h k h0 h3 Ms es hMs hes => (h k h0 h3 Ms es hMs hes).mono' hle
  have hL' := mono (by simp only [K]; linarith) hL
  have hG' := mono (k₀ := 1) (by simp only [K]; linarith)
    (fun k _ h3 => hG k (Nat.zero_le k) h3)
  have hQ' := mono (by simp only [K]; linarith) hQ
  set Bcf := ‖seVK P‖ * ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2) * seCc P * (M₀ ^ 2)⁻¹
  refine ⟨3 * (Bcf * seBp P K), fun x hx => ?_⟩
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have hpiece : ∀ f, SetCRegDispSE.GoodEF4 (sePiece P p α β x f) (seBp P K) := fun f =>
    goodEF4_sePiece P hε hmγ hΛ p α β hK0 hL' hQ' hG' hx f (hmass f)
      (hM₀.trans_le (hmass f))
  have hsum : ∀ ℓ, seGInt P p α β x ℓ = seCf P x 0 * sePiece P p α β x 0 ℓ +
      seCf P x 1 * sePiece P p α β x 1 ℓ + seCf P x 2 * sePiece P p α β x 2 ℓ := fun ℓ => by
    rw [seGInt_eq_pieces P hε p α β hx, Fin.sum_univ_three]
  have Z := ((SEgoodEF4_const_mul_le (hpiece 0) _ (norm_seCf_le P hM₀ hmass hxI 0)).add
    (SEgoodEF4_const_mul_le (hpiece 1) _ (norm_seCf_le P hM₀ hmass hxI 1))).add
    (SEgoodEF4_const_mul_le (hpiece 2) _ (norm_seCf_le P hM₀ hmass hxI 2))
  exact (Z.congr fun ℓ => (hsum ℓ).symm).mono' (le_of_eq (by ring))
/-! ### The pointwise bound at fixed `ε` -/

theorem abs_dot_cons_le (t : ℝ) (v : Fin 3 → ℝ) :
    |Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v)| ≤
      8 * (1 + ‖v‖ ^ 2) * (1 + t ^ 2) := by
  have h1 := QED.WickModel.VacuumPolarizationLimit.abs_dot_le (Fin.cons t v : Fin 4 → ℝ)
    (Fin.cons t v)
  have h2 := QED.Integration.norm_finCons_le t v
  have h3 : ‖(Fin.cons t v : Fin 4 → ℝ)‖ ^ 2 ≤ 2 * (t ^ 2 + ‖v‖ ^ 2) := by
    have h0 : 0 ≤ ‖(Fin.cons t v : Fin 4 → ℝ)‖ := norm_nonneg _
    have := pow_le_pow_left₀ h0 h2 2
    nlinarith [sq_abs t, sq_nonneg (|t| - ‖v‖)]
  nlinarith [sq_nonneg t, sq_nonneg ‖v‖, mul_nonneg (sq_nonneg t) (sq_nonneg ‖v‖)]

theorem norm_vpRatSum_le (P : Params) {ε : ℝ} (hε : 0 < ε) (s : ℝ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : ‖vpRatSum P ε s x‖ ≤ 3 * seCc P * |s| / ε := by
  have h2 : |1 - 2 * x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hterm : ∀ f : Fin 3, ‖(P.loopCoeff f : ℂ) * (((1 - 2 * x) * s : ℝ) : ℂ) /
      ((QED.WickModel.vacuumPolarizationFeynmanMass (P.mass f) s x : ℂ) - ε * I)‖ ≤
      seCc P * |s| / ε := fun f => by
    have hD : ε ≤ ‖(QED.WickModel.vacuumPolarizationFeynmanMass (P.mass f) s x : ℂ) - ε * I‖ := by
      have him : ((QED.WickModel.vacuumPolarizationFeynmanMass (P.mass f) s x : ℂ) -
          ε * I).im = -ε := by simp
      have := abs_im_le_norm
        ((QED.WickModel.vacuumPolarizationFeynmanMass (P.mass f) s x : ℂ) - ε * I)
      rwa [him, abs_neg, abs_of_pos hε] at this
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul]
    have hc := abs_loopCoeff_le P f
    have hc0 : 0 ≤ seCc P := by unfold seCc; positivity
    rw [div_le_div_iff₀ (hε.trans_le hD) hε]
    calc |P.loopCoeff f| * (|1 - 2 * x| * |s|) * ε ≤ seCc P * (1 * |s|) * ε := by gcongr
      _ = seCc P * |s| * ε := by ring
      _ ≤ seCc P * |s| * ‖(QED.WickModel.vacuumPolarizationFeynmanMass (P.mass f) s x : ℂ) -
          ε * I‖ := by
          gcongr
  rw [vpRatSum]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun f _ => hterm f).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **The pointwise bound**: at fixed `ε > 0` and spatial momentum `v`, `seGInt` is bounded by
`G(v) (1 + t²)⁻¹`, uniformly in `x ∈ [0, 1]`. -/
theorem exists_ptBd_seGInt (P : Params) (hε : 0 < P.ε) (p : Fin 4 → ℝ) (α β : Fin 4) :
    ∃ G : (Fin 3 → ℝ) → ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
      QED.TwoLoop.VPHalfAtAssembly.PtBd (seGInt P p α β x) G := by
  have key : ∀ v : Fin 3 → ℝ, ∃ Gv : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖seGInt P p α β x (Fin.cons t v : Fin 4 → ℝ)‖ ≤ Gv * (1 + t ^ 2)⁻¹ := by
    intro v
    set We : ℝ := ∑ j : Fin 3, (v j + (-p) j.succ) ^ 2 + P.m ^ 2
    set Wg : ℝ := ∑ j : Fin 3, (v j + 0) ^ 2 + P.mγ ^ 2
    set WL : ℝ := ∑ j : Fin 3, (v j + 0) ^ 2 + P.Λ ^ 2
    obtain ⟨c, hc, hcb⟩ := QED.Integration.exists_mul_one_add_sq_le_norm hε |p 0|
      (max We (max Wg WL))
    have hDph : ∀ (M : ℝ), (∑ j : Fin 3, (v j + 0) ^ 2 + M ^ 2 ≤ max We (max Wg WL)) →
        ∀ t : ℝ, c * (1 + t ^ 2) ≤ ‖denom M P.ε (Fin.cons t v : Fin 4 → ℝ)‖ := by
      intro M hM t
      rw [SetCRegDispSE.denom_cons_eq]
      exact hcb t 0 _ (by simp) hM
    have hDe : ∀ t : ℝ, c * (1 + t ^ 2) ≤ ‖denom P.m P.ε (-p + (Fin.cons t v : Fin 4 → ℝ))‖ := by
      intro t
      rw [QED.TwoLoop.VPHalfAtLimit.denom_add_cons]
      exact hcb t _ _ (by simp) (le_max_left _ _)
    set CL := ‖seCL P p α β‖ + ‖(3 : ℂ)‖ * seGs α β
    set CG := ‖seCG P p α β‖ + ‖(2 : ℂ)‖ * seGs α β
    set CQ := 4 * ‖p‖ * seGs α β
    have hGs := seGs_nonneg α β
    have hCL : 0 ≤ CL := by positivity
    have hCG : 0 ≤ CG := by positivity
    have hCQ : 0 ≤ CQ := by have := seGs_nonneg α β; positivity
    set V : ℝ := 8 * (1 + ‖v‖ ^ 2)
    set W2 : ℝ := 2 * (1 + ‖v‖) ^ 2
    set Dd : ℝ := |P.Λ ^ 2 - P.mγ ^ 2| * (c ^ 2)⁻¹
    set CR : ℝ := 3 * seCc P * V / P.ε
    set CB : ℝ := ‖cOne P‖ * (V * (CL * W2) + 2 * (CQ * W2)) + P.ε * ‖cTwo P‖ * (CG * W2)
    have hCc : 0 ≤ seCc P := by unfold seCc; positivity
    refine ⟨‖seVK P‖ * Dd ^ 2 * CR * c⁻¹ * CB, fun x hx t => ?_⟩
    set u : ℝ := 1 + t ^ 2
    have hu1 : 1 ≤ u := le_add_of_nonneg_right (sq_nonneg t)
    have hu0 : 0 < u := by positivity
    set ℓ : Fin 4 → ℝ := Fin.cons t v
    have hs : |Minkowski.dot ℓ ℓ| ≤ V * u := abs_dot_cons_le t v
    -- the photon factor
    have hd : ‖photonScalar P.mγ P.Λ P.ε ℓ‖ ≤ Dd * (u ^ 2)⁻¹ := by
      have h1 := hDph P.mγ (le_max_of_le_right (le_max_left _ _)) t
      have h2 := hDph P.Λ (le_max_of_le_right (le_max_right _ _)) t
      rw [photonScalar_eq_mul _ _ _ hε, norm_mul, norm_mul, norm_inv, norm_inv,
        Complex.norm_real, Real.norm_eq_abs]
      calc |P.Λ ^ 2 - P.mγ ^ 2| * (‖denom P.mγ P.ε ℓ‖⁻¹ * ‖denom P.Λ P.ε ℓ‖⁻¹)
          ≤ |P.Λ ^ 2 - P.mγ ^ 2| * ((c * u)⁻¹ * (c * u)⁻¹) := by
            gcongr
      _ = Dd * (u ^ 2)⁻¹ := by simp only [Dd]; field_simp
    have hR : ‖vpRatSum P P.ε (Minkowski.dot ℓ ℓ) x‖ ≤ CR * u := by
      refine (norm_vpRatSum_le P hε _ hx).trans ?_
      have h3 : 3 * seCc P * |Minkowski.dot ℓ ℓ| / P.ε ≤ 3 * seCc P * (V * u) / P.ε := by
        gcongr
      refine h3.trans (le_of_eq ?_)
      simp only [CR]
      ring
    have hE : ‖(seDen P p ℓ)⁻¹‖ ≤ c⁻¹ * u⁻¹ := by
      rw [seDen_eq_denom, norm_inv, ← mul_inv]
      exact inv_anti₀ (by positivity) (hDe t)
    have hNL := QED.TwoLoop.VPHalfAtLimit.norm_cons_numerator_le
      (norm_seAff_le_sq (seCL P p α β) 3 α β) hCL t v
    have hNG := QED.TwoLoop.VPHalfAtLimit.norm_cons_numerator_le
      (norm_seAff_le_sq (seCG P p α β) 2 α β) hCG t v
    have hNQ := QED.TwoLoop.VPHalfAtLimit.norm_cons_numerator_le (norm_seQuad_le p α β) hCQ t v
    have hB : ‖I * cOne P * wOne x * ((Minkowski.dot ℓ ℓ : ℂ) * seAff (seCL P p α β) 3 α β ℓ -
          2 * seQuad p α β ℓ) +
        (P.ε : ℂ) * cTwo P * (x : ℂ) * seAff (seCG P p α β) 2 α β ℓ‖ ≤ CB * u ^ 2 := by
      have hw := norm_wOne_le hx
      have hxn : ‖(x : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2
      have e1 : ‖I * cOne P * wOne x * ((Minkowski.dot ℓ ℓ : ℂ) * seAff (seCL P p α β) 3 α β ℓ -
          2 * seQuad p α β ℓ)‖ ≤ ‖cOne P‖ * 1 * ‖(Minkowski.dot ℓ ℓ : ℂ) *
          seAff (seCL P p α β) 3 α β ℓ - 2 * seQuad p α β ℓ‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul]
        gcongr
      have e2 : ‖(P.ε : ℂ) * cTwo P * (x : ℂ) * seAff (seCG P p α β) 2 α β ℓ‖ ≤
          P.ε * ‖cTwo P‖ * 1 * ‖seAff (seCG P p α β) 2 α β ℓ‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
        gcongr
      have hsub : ‖(Minkowski.dot ℓ ℓ : ℂ) * seAff (seCL P p α β) 3 α β ℓ - 2 * seQuad p α β ℓ‖
          ≤ V * (CL * W2) * u ^ 2 + 2 * (CQ * W2) * u := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
        calc |Minkowski.dot ℓ ℓ| * ‖seAff (seCL P p α β) 3 α β ℓ‖ + 2 * ‖seQuad p α β ℓ‖
            ≤ (V * u) * (CL * W2 * u) + 2 * (CQ * W2 * u) := by gcongr
          _ = V * (CL * W2) * u ^ 2 + 2 * (CQ * W2) * u := by ring
      have hV : 0 ≤ V := by positivity
      have hW2 : 0 ≤ W2 := by positivity
      refine (norm_add_le _ _).trans ((add_le_add e1 e2).trans ?_)
      calc ‖cOne P‖ * 1 * ‖(Minkowski.dot ℓ ℓ : ℂ) * seAff (seCL P p α β) 3 α β ℓ -
            2 * seQuad p α β ℓ‖ + P.ε * ‖cTwo P‖ * 1 * ‖seAff (seCG P p α β) 2 α β ℓ‖
          ≤ ‖cOne P‖ * 1 * (V * (CL * W2) * u ^ 2 + 2 * (CQ * W2) * u) +
              P.ε * ‖cTwo P‖ * 1 * (CG * W2 * u) := by gcongr
        _ ≤ ‖cOne P‖ * 1 * (V * (CL * W2) * u ^ 2 + 2 * (CQ * W2) * u ^ 2) +
              P.ε * ‖cTwo P‖ * 1 * (CG * W2 * u ^ 2) := by
            have hu2 : u ≤ u ^ 2 := by nlinarith
            gcongr
        _ = CB * u ^ 2 := by simp only [CB]; ring
    rw [seGInt_eq_dirac, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow]
    have hDd : 0 ≤ Dd := by positivity
    have hCR : 0 ≤ CR := by simp only [CR]; positivity
    calc ‖seVK P‖ * ‖photonScalar P.mγ P.Λ P.ε ℓ‖ ^ 2 * ‖vpRatSum P P.ε (Minkowski.dot ℓ ℓ) x‖ *
          ‖(seDen P p ℓ)⁻¹‖ * ‖I * cOne P * wOne x * ((Minkowski.dot ℓ ℓ : ℂ) *
            seAff (seCL P p α β) 3 α β ℓ - 2 * seQuad p α β ℓ) +
          (P.ε : ℂ) * cTwo P * (x : ℂ) * seAff (seCG P p α β) 2 α β ℓ‖
        ≤ ‖seVK P‖ * (Dd * (u ^ 2)⁻¹) ^ 2 * (CR * u) * (c⁻¹ * u⁻¹) * (CB * u ^ 2) := by
          gcongr
      _ = ‖seVK P‖ * Dd ^ 2 * CR * c⁻¹ * CB * (u ^ 2)⁻¹ := by
          field_simp
      _ ≤ ‖seVK P‖ * Dd ^ 2 * CR * c⁻¹ * CB * u⁻¹ := by
          have hCB : 0 ≤ CB := by simp only [CB]; positivity
          gcongr
          nlinarith
  choose G hG using key
  exact ⟨G, fun x hx v t => hG v x hx t⟩

/-! ### Joint measurability -/

theorem measurable_seGInt (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) :
    Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      seGInt P p α β q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
  have hℓ : Continuous fun q : ((Fin 3 → ℝ) × ℝ) × ℝ => (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd (continuous_fst.fst)
  have hs : Continuous fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) (Fin.cons q.2 q.1.1) :=
    QED.OneLoop.VertexLimit.continuous_dot_comp hℓ hℓ
  have hx : Continuous fun q : ((Fin 3 → ℝ) × ℝ) × ℝ => q.1.2 := continuous_fst.snd
  have hpe : Continuous fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      Minkowski.dot (p - Fin.cons q.2 q.1.1) (p - Fin.cons q.2 q.1.1) :=
    QED.OneLoop.VertexLimit.continuous_dot_comp (continuous_const.sub hℓ)
      (continuous_const.sub hℓ)
  have hA := ((continuous_seAff (seCL P p α β) 3 α β).comp hℓ).measurable
  have hG := ((continuous_seAff (seCG P p α β) 2 α β).comp hℓ).measurable
  have hQ := ((continuous_seQuad p α β).comp hℓ).measurable
  have hph : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      photonScalar P.mγ P.Λ P.ε (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
    unfold photonScalar
    exact (by fun_prop : Continuous fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      ((Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) (Fin.cons q.2 q.1.1) + P.mγ ^ 2 : ℝ) :
        ℂ) - (P.ε : ℂ) * I).measurable.inv.sub
      (by fun_prop : Continuous fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      ((Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) (Fin.cons q.2 q.1.1) + P.Λ ^ 2 : ℝ) :
        ℂ) - (P.ε : ℂ) * I).measurable.inv
  have hR : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      vpRatSum P P.ε (Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) (Fin.cons q.2 q.1.1))
        q.1.2 := by
    unfold vpRatSum QED.WickModel.vacuumPolarizationFeynmanMass
    refine Finset.measurable_sum _ fun f _ => ?_
    exact ((by fun_prop : Continuous fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      (P.loopCoeff f : ℂ) * (((1 - 2 * q.1.2) * Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)
        (Fin.cons q.2 q.1.1) : ℝ) : ℂ)).measurable).div
      ((by fun_prop : Continuous fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      (((P.mass f ^ 2 + q.1.2 * (1 - q.1.2) * Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)
        (Fin.cons q.2 q.1.1) : ℝ) : ℂ) - (P.ε : ℂ) * I)).measurable)
  have hD : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      (seDen P p (Fin.cons q.2 q.1.1 : Fin 4 → ℝ))⁻¹ := by
    unfold seDen
    exact (by fun_prop : Continuous fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      ((Minkowski.dot (p - Fin.cons q.2 q.1.1) (p - Fin.cons q.2 q.1.1) + P.m ^ 2 : ℝ) : ℂ) -
        (P.ε : ℂ) * I).measurable.inv
  have hw : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ => wOne q.1.2 := by
    unfold wOne; fun_prop
  simp_rw [seGInt_eq_dirac]
  have hsC : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ =>
      ((Minkowski.dot (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) (Fin.cons q.2 q.1.1) : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp hs).measurable
  have hxC : Measurable fun q : ((Fin 3 → ℝ) × ℝ) × ℝ => ((q.1.2 : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp hx).measurable
  exact ((((measurable_const.mul (hph.pow_const 2)).mul hR).mul hD).mul
    ((((measurable_const.mul hw).mul ((hsC.mul hA).sub (measurable_const.mul hQ)))).add
      ((measurable_const.mul hxC).mul hG)))

/-! ### The exchange (step S3) -/

/-- **The exchange of the spectral parameter with the energy-first integral**, at fixed `ε > 0`
and below threshold (`-(m + M₀)² < p²`, `M₀` below every mass). -/
theorem efi_integral_seGInt (P : Params) (hε : 0 < P.ε) {M₀ : ℝ} (hM₀ : 0 < M₀)
    (hmγ : M₀ ≤ P.mγ) (hΛ : M₀ ≤ P.Λ) (hmass : ∀ f, M₀ ≤ P.mass f) {p : Fin 4 → ℝ}
    (hp : -(P.m + M₀) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    EFInt (fun k => ∫ x in (0 : ℝ)..1, seGInt P p α β x k) ∧
      energyFirstIntegral (fun k => ∫ x in (0 : ℝ)..1, seGInt P p α β x k) =
        ∫ x in (0 : ℝ)..1, energyFirstIntegral (seGInt P p α β x) := by
  have hm : 0 < P.m := hM₀.trans_le (hmass 0)
  have hpp : Minkowski.dot (-p) (-p) = Minkowski.dot p p := by
    simp only [Minkowski.dot, Pi.neg_apply]; ring_nf
  obtain ⟨c₀, hc₀, hP⟩ := exists_pos_le_selfEnergyFeynmanMass hm hM₀ (hpp ▸ hp)
  obtain ⟨C, hC⟩ := exists_goodEF4_seGInt P hε hM₀ hmγ hΛ hmass hc₀ hP α β
  obtain ⟨G, hG⟩ := exists_ptBd_seGInt P hε p α β
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  have hI : ∀ g : ℝ → ℂ, ∫ x in (0 : ℝ)..1, g x = ∫ x in Ioo (0 : ℝ) 1, g x := fun g => by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  simp_rw [hI]
  have hae : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  exact SetCRegDispSE.efi_integral_eq_of_goodEF4 (ν := volume.restrict (Ioo (0 : ℝ) 1))
    (fun x => seGInt P p α β x) (measurable_seGInt P p α β)
    (hae.mono fun x hx => hC x hx) (hae.mono fun x hx => hG x (Ioo_subset_Icc_self hx))

/-! ### The class `V` at fixed `ε` in spectral form -/

/-- The constant (logarithmic) part of the outer integrand in spectral form. -/
noncomputable def seConst (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (k : Fin 4 → ℝ) : ℂ :=
  seVK P * photonScalar P.mγ P.Λ P.ε k ^ 2 *
    (I * cOne P * (1 / 6) * QED.TwoLoop.VPHalfAtAssembly.logSum P P.ε *
        ((Minkowski.dot k k : ℂ) * seChainG P p k α β - seChainK P p k α β) +
      (P.ε : ℂ) * cTwo P * QED.TwoLoop.VPHalfAtAssembly.logSum P P.ε * seChainG P p k α β)

theorem energyFirstIntegral_add_of_efInt {F G : (Fin 4 → ℝ) → ℂ} (hF : EFInt F)
    (hG : EFInt G) :
    energyFirstIntegral (fun ℓ => F ℓ + G ℓ) = energyFirstIntegral F + energyFirstIntegral G := by
  unfold energyFirstIntegral
  have e : (fun v : Fin 3 → ℝ => ∫ t : ℝ, (F (Fin.cons t v : Fin 4 → ℝ) +
      G (Fin.cons t v : Fin 4 → ℝ))) = fun v => (∫ t : ℝ, F (Fin.cons t v : Fin 4 → ℝ)) +
        ∫ t : ℝ, G (Fin.cons t v : Fin 4 → ℝ) :=
    funext fun v => integral_add (hF.1 v) (hG.1 v)
  rw [e, integral_add hF.2 hG.2]

open QED.GradedProof.SE2 in
/-- **The class `V` at fixed `ε` in spectral form** (steps S2 and S3): for admissible parameters
with `m < M₁, M₂`, below threshold, the value of `repV` at the self-energy kinematics is
`∫_D seConst - ∫₀¹ (∫_D seGInt x) dx`, every energy-first integral with both stages
integrable. -/
theorem contractionValue₂_repV_eq_spectral {P : Params} (hP : Adm P) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) {M₀ : ℝ} (hM₀ : 0 < M₀) (hmγ : M₀ ≤ P.mγ) (hΛ : M₀ ≤ P.Λ)
    (hmass : ∀ f, M₀ ≤ P.mass f) {p : Fin 4 → ℝ} (hp : -(P.m + M₀) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    contractionValue₂ P repV ![p] ![p] ![] ![α] ![β] ![] =
        energyFirstIntegral (seConst P p α β) -
          ∫ x in (0 : ℝ)..1, energyFirstIntegral (seGInt P p α β x) ∧
      EFInt (seConst P p α β) ∧ (∀ x ∈ Ioo (0 : ℝ) 1, EFInt (seGInt P p α β x)) := by
  obtain ⟨hv, hE⟩ := contractionValue₂_repV_eq_outerF hP hM₁ hM₂ p α β
  obtain ⟨hI, hEq⟩ := efi_integral_seGInt P hP.hε hM₀ hmγ hΛ hmass hp α β
  have hsp : seConst P p α β = fun k => outerF P (seVOuter P p α β) k +
      ∫ x in (0 : ℝ)..1, seGInt P p α β x k := by
    funext k
    rw [outerF_seVOuter_eq_spectral P hP.hε]
    simp only [seConst]
    ring
  have hC : EFInt (seConst P p α β) := by rw [hsp]; exact hE.add hI
  have hm : 0 < P.m := hM₀.trans_le (hmass 0)
  have hpp : Minkowski.dot (-p) (-p) = Minkowski.dot p p := by
    simp only [Minkowski.dot, Pi.neg_apply]; ring_nf
  obtain ⟨c₀, hc₀, hPc⟩ := exists_pos_le_selfEnergyFeynmanMass hm hM₀ (hpp ▸ hp)
  obtain ⟨C, hCx⟩ := exists_goodEF4_seGInt P hP.hε hM₀ hmγ hΛ hmass hc₀ hPc α β
  refine ⟨?_, hC, fun x hx => (hCx x hx).1⟩
  rw [hv, ← hEq, hsp, energyFirstIntegral_add_of_efInt hE hI]
  ring

end QED.ChainProof.SetCRegDisp

end
