/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetACovProd
public import QED.ChainProof.HCBB2CovBB
public import QED.ChainProof.SetASpecOuterTerm

/-!
# Covariance of the limit matrices of one set (a) spectral term

Helper level for `QED.ChainProof.SetAPauli.SetACovLink`. A good spectral term
`QED.ChainProof.SetASpec.SAOuterTerm` of the two-loop vacuum polarization, inserted in the outer
one-loop vertex, has the limit `∫_Δ w₀ · specLimit` (`QED.ChainProof.SetASpec.saLimTermLimit`)
over the four photon-type masses `(m_γ, Λ, m_γ, Λ)` and `r` spectral masses, with one of the four
outer numerators `numG`, `numS`, `numL`, `numQ`.

* `outMatG`, `outMatS`, `outMatL`, `outMatQ`: the numerators as matrix families;
  `isLoopPoly_outMatG`, …: every entry has degree `≤ 2` in the loop momentum (as
  `QED.ChainProof.SetACov.CovNum` needs);
* `CovNum.of_quadN`: a covariant family with `QuadN` entries satisfies `CovNum`;
* `integrableOn_specLimit`: the limit integrand `w₀ · specLimit` of a good term is integrable
  over the simplex;
* `termMat`: the limit matrices of one term; **`CovNum.covRel_termMat`**: they are covariant,
  for every power `j ≤ 2` of `k²` and every number `r` of spectral factors
  (by `QED.ChainProof.SetACov.CovNum.covRel_specM` at each Feynman parameter and
  `QED.ChainProof.HCBB2.covRel_integral`).
-/

@[expose] public section

open Complex Matrix MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetACov

open QED.OneLoop QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance QED.TwoLoop.VPHalfAtLimit
open QED.TwoLoop.VPHalfAtGen QED.TwoLoop.VPHalfAtAssembly QED.TwoLoop.VPUnitNested
open QED.Dirac QED.ChainProof.HCBB2 QED.ChainProof.SetASpec QED.TwoLoop.CountertermLimit
open QED.Integration.Feynman (simplexSet)

/-! ### The four numerators as covariant families of degree two -/

/-- The matrix family with entries `numG`. -/
noncomputable def outMatG (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => numG m p' p μ i j ℓ

/-- The matrix family with entries `numS`. -/
noncomputable def outMatS (_ _ : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => numS μ i j ℓ

/-- The matrix family with entries `numL`. -/
noncomputable def outMatL (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => numL m p' p μ i j ℓ

/-- The matrix family with entries `numQ`. -/
noncomputable def outMatQ (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => numQ m p' p μ i j ℓ

theorem outMatG_eq (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    outMatG m p' p μ ℓ = NG m p' p μ ℓ := by
  ext i j; exact (NG_apply m p' p μ i j ℓ).symm

theorem outMatS_eq (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) : outMatS p' p μ ℓ = NS μ ℓ := by
  ext i j; exact (NS_apply μ i j ℓ).symm

theorem outMatL_eq (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    outMatL m p' p μ ℓ = NL m p' p μ ℓ := by
  ext i j; exact (NL_apply m p' p μ i j ℓ).symm

theorem outMatQ_eq (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    outMatQ m p' p μ ℓ = NQ m p' p μ ℓ := by
  ext i j; exact (NQ_apply m p' p μ i j ℓ).symm

theorem isLoopPoly_outMatG (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    IsLoopPoly 2 2 fun ℓ => outMatG m p' p μ (ℓ 0) i j := by
  simp only [outMatG_eq, NG, IsSpinLift.chain, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine IsLoopPoly.sum _ fun ν _ => IsLoopPoly.sum _ fun ρ _ => IsLoopPoly.const_mul _ ?_
  have h := ((((IsLoopPolyMat.const (L := 2) (gamma ρ)).mul
    (isLoopPolyMat_electronNumerator_add m p')).mul (IsLoopPolyMat.const (gamma μ))).mul
    (isLoopPolyMat_electronNumerator_add m p)).mul (IsLoopPolyMat.const (gamma ν))
  exact (h i j).mono (by norm_num)

theorem isLoopPoly_outMatS (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    IsLoopPoly 2 2 fun ℓ => outMatS p' p μ (ℓ 0) i j := by
  have h := (isLoopPolyMat_slash_zero.mul isLoopPolyMat_slash_zero).mul
    (IsLoopPolyMat.const (L := 2) (gamma μ))
  refine ((congrArg (IsLoopPoly 2 (1 + 1 + 0)) (funext fun ℓ => ?_)).mp
    ((isLoopPolyMat_smul (-1) h) i j)).mono (by norm_num)
  dsimp only
  rw [outMatS_eq, slash_mul_slash]
  simp only [NS, Matrix.smul_apply, Matrix.smul_mul, Matrix.one_mul, smul_eq_mul]
  push_cast
  ring

theorem isLoopPoly_outMatL (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    IsLoopPoly 2 2 fun ℓ => outMatL m p' p μ (ℓ 0) i j := by
  have h := isLoopPolyMat_add (isLoopPolyMat_slash_zero.mul (IsLoopPolyMat.const (L := 2)
    (electronNumerator m p' * gamma μ)))
    ((IsLoopPolyMat.const (L := 2) (gamma μ * electronNumerator m p)).mul
      isLoopPolyMat_slash_zero)
  simp only [outMatL_eq]
  exact ((show IsLoopPolyMat 2 1 fun ℓ => NL m p' p μ (ℓ 0) from h) i j).mono (by norm_num)

theorem isLoopPoly_outMatQ (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    IsLoopPoly 2 2 fun ℓ => outMatQ m p' p μ (ℓ 0) i j := by
  have h := (isLoopPolyMat_slash_zero.mul (IsLoopPolyMat.const (L := 2)
    (electronNumerator m p' * gamma μ * electronNumerator m p))).mul isLoopPolyMat_slash_zero
  simp only [outMatQ_eq]
  exact (h i j).mono (by norm_num)

/-- **A covariant family whose entries are `QuadN` gives `CovNum`**, with the leading
coefficients chosen from `QuadN`. -/
theorem CovNum.of_quadN {m : ℝ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {S T : Matrix (Fin 4) (Fin 4) ℂ} {p' p : Fin 4 → ℝ}
    {Nf : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (hm : 0 < m) (h : IsSpinLift L S T) (hpq : QED.ChainProof.IsPairQ m p' p)
    (h0 : 0 < (L *ᵥ p') 0) (h1 : 0 < (L *ᵥ p) 0)
    (hQ : ∀ p' p μ i j, QuadN fun ℓ => Nf p' p μ ℓ i j)
    (hP : ∀ p' p μ i j, IsLoopPoly 2 2 fun ℓ => Nf p' p μ (ℓ 0) i j)
    (hC : ∀ μ ℓ, S * Nf (L *ᵥ p') (L *ᵥ p) μ (L *ᵥ ℓ) * T = vecAct L (fun ν => Nf p' p ν ℓ) μ) :
    CovNum m L S T p' p Nf (fun μ i j => (hQ p' p μ i j).quad.choose)
      (fun μ i j => (hQ (L *ᵥ p') (L *ᵥ p) μ i j).quad.choose) :=
  ⟨hm, h, hpq.1, hpq.2.1, hpq.2.2.2.2.le, hpq.2.2.1, hpq.2.2.2.1, h0, h1, hP, hC,
    fun p' p μ i j => (hQ p' p μ i j).cont, fun p' p μ i j => (hQ p' p μ i j).bound,
    fun μ i j => (hQ p' p μ i j).quad.choose_spec,
    fun μ i j => (hQ (L *ᵥ p') (L *ᵥ p) μ i j).quad.choose_spec⟩

/-! ### Integrability of the limit integrand of a spectral term -/

/-- **The limit integrand of a good spectral term is integrable** over the simplex: it is the
almost-everywhere limit of `w_ε · EFI(specInt …)`, which is bounded by the integrable majorant of
the weights times a constant. -/
theorem integrableOn_specLimit {m M₀ Mlo : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) (hMlo : M₀ ≤ Mlo)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} {α : ℂ} (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {j k : ℕ} (hjk : j ≤ k)
    (Ms : Fin (k + 2) → ℝ) (hMs : ∀ i, M₀ ≤ Ms i) {τ : SAOuterTerm} (hτ : τ.Good Mlo) :
    IntegrableOn (fun x => τ.w₀ x * specLimit α N m p' p j τ.r Ms (fun _ => √(τ.A x))
      (fun _ => τ.ξ x)) (simplexSet τ.n) := by
  obtain ⟨-, hA, hξ, hAlo, hξ01, ⟨h, hh, hw⟩, hwl⟩ := hτ
  set ν : Measure (Fin τ.n → ℝ) := volume.restrict (simplexSet τ.n) with hν
  have hsq : ∀ x, Mlo ≤ √(τ.A x) := fun x =>
    (le_abs_self Mlo).trans (Real.abs_le_sqrt (hAlo x))
  obtain ⟨K, -, hK⟩ := setASpec_exists_good_specPow hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMlo
    τ.r j k hjk
  set T : ℝ := ∑ i, Ms i ^ 2 + 1 with hT
  have hT0 : 0 ≤ T := by positivity
  have hgood : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ G : (Fin 3 → ℝ) → ℝ, ∀ᵐ x ∂ν,
      Good (specInt N m j Ms (fun _ => ε) (fun _ : Fin τ.r => √(τ.A x)) (fun _ => τ.ξ x) ε p' p)
        ((1 + T) ^ j * K) G := by
    intro ε hε hε1
    obtain ⟨G, -, hG⟩ := hK ε ε hε hε le_rfl
    refine ⟨fun v => (1 + T) ^ j * G v, ?_⟩
    filter_upwards [hξ01] with x hx
    exact hG T hT0 Ms (fun _ => ε) hMs (fun _ => le_rfl)
      (fun i _ => norm_massShift_le_T Ms hε.le hε1 i) (√(τ.A x)) (τ.ξ x) (hsq x) hx
  have hgm : ∀ ε : ℝ, Measurable fun q : ((Fin 3 → ℝ) × (Fin τ.n → ℝ)) × ℝ =>
      specInt N m j Ms (fun _ => ε) (fun _ : Fin τ.r => √(τ.A q.1.2)) (fun _ => τ.ξ q.1.2) ε
        p' p (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := fun ε =>
    saLim_measurable_comp_cons (g := fun x => specInt N m j Ms (fun _ => ε)
      (fun _ : Fin τ.r => √(τ.A x)) (fun _ => τ.ξ x) ε p' p)
      (saLim_measurable_specInt hNc m j Ms (fun _ => ε) (Msp := fun x _ => √(τ.A x))
        (xs := fun x _ => τ.ξ x) (fun _ => hA.sqrt) (fun _ => hξ) ε p' p)
  have hεn : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 :=
    fun n => ⟨by positivity, inv_succ_le_one n⟩
  set g : ℕ → (Fin τ.n → ℝ) → ℂ := fun n x => τ.w (1 / ((n : ℝ) + 1)) x *
    energyFirstIntegral (specInt N m j Ms (fun _ => 1 / ((n : ℝ) + 1))
      (fun _ : Fin τ.r => √(τ.A x)) (fun _ => τ.ξ x) (1 / ((n : ℝ) + 1)) p' p) with hg
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => g n x) atTop
      (𝓝 (τ.w₀ x * specLimit α N m p' p j τ.r Ms (fun _ => √(τ.A x)) (fun _ => τ.ξ x))) := by
    filter_upwards [hwl, hξ01] with x h1 hx
    exact (h1.comp tendsto_inv_succ_nhdsGT).mul
      ((tendsto_efi_specInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (l := 𝓝[>] (0 : ℝ))
        (ε := id) tendsto_id j τ.r k hjk Ms (fun t _ => t) (fun _ => √(τ.A x))
        (fun _ => τ.ξ x) hMs (fun _ => hMlo.trans (hsq x)) (fun _ => hx)
        (fun _ => tendsto_id)).comp tendsto_inv_succ_nhdsGT)
  have hmeas : ∀ n, AEStronglyMeasurable (g n) ν := fun n => by
    obtain ⟨G, hG⟩ := hgood _ (hεn n).1 (hεn n).2
    exact (hw _ (hεn n).1 (hεn n).2).1.mul (aestronglyMeasurable_efi_param _ (hgm _) hG)
  have hbd : ∀ n, ∀ᵐ x ∂ν, ‖g n x‖ ≤ h x * ((1 + T) ^ j * K * I5) := fun n => by
    obtain ⟨G, hG⟩ := hgood _ (hεn n).1 (hεn n).2
    filter_upwards [(hw _ (hεn n).1 (hεn n).2).2, hG] with x h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2.1.norm_efi_le (norm_nonneg _) ((norm_nonneg _).trans h1)
  refine Integrable.mono' (hh.mul_const ((1 + T) ^ j * K * I5))
    (aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim) ?_
  filter_upwards [hlim, ae_all_iff.2 hbd] with x h1 h2
  exact le_of_tendsto h1.norm (Eventually.of_forall h2)

/-! ### The limit matrix of one engine term and its covariance -/

/-- The limit matrices of a spectral term with the numerator family `Nf`, leading coefficients
`α`, power `j` of `k²` and photon-type masses `Ms`. -/
noncomputable def termMat (m : ℝ) (Ms : Fin (2 + 2) → ℝ)
    (Nf : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (α : Fin 4 → Fin 4 → Fin 4 → ℂ) (j : ℕ) (τ : SAOuterTerm) (p' p : Fin 4 → ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Matrix.of fun a b =>
    saLimTermLimit (α μ a b) (fun ℓ => Nf p' p μ ℓ a b) m p' p j Ms τ.r τ.A τ.ξ τ.w₀

/-- **Covariance of the limit matrices of one spectral term**, for a covariant numerator family
of degree two, `j ≤ 2` and four photon-type masses. -/
theorem CovNum.covRel_termMat {m M₀ Mlo : ℝ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {S T : Matrix (Fin 4) (Fin 4) ℂ} {p' p : Fin 4 → ℝ}
    {Nf : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    {α α₂ : Fin 4 → Fin 4 → Fin 4 → ℂ} (H : CovNum m L S T p' p Nf α α₂) (hM₀ : 0 < M₀)
    (hMlo : M₀ ≤ Mlo) {Ms : Fin (2 + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) {τ : SAOuterTerm}
    (hτ : τ.Good Mlo) {j : ℕ} (hj : j ≤ 2) :
    CovRel L S T (termMat m Ms Nf α j τ p' p) (termMat m Ms Nf α₂ j τ (L *ᵥ p') (L *ᵥ p)) := by
  have hsq : ∀ x, M₀ ≤ √(τ.A x) := fun x =>
    hMlo.trans ((le_abs_self Mlo).trans (Real.abs_le_sqrt (hτ.2.2.2.1 x)))
  have e : ∀ (q' q : Fin 4 → ℝ) (β : Fin 4 → Fin 4 → Fin 4 → ℂ),
      termMat m Ms Nf β j τ q' q = fun μ => Matrix.of fun a b => ∫ x,
        (τ.w₀ x • specM β (fun μ i j ℓ => Nf q' q μ ℓ i j) m q' q j τ.r Ms
          (fun _ => √(τ.A x)) (fun _ => τ.ξ x)) μ a b ∂(volume.restrict (simplexSet τ.n)) := by
    intro q' q β
    funext μ
    ext a b
    simp only [termMat, saLimTermLimit, specM, Matrix.of_apply, Pi.smul_apply,
      Matrix.smul_apply, smul_eq_mul]
  rw [e, e]
  refine covRel_integral (fun μ a b => ?_) (fun μ a b => ?_) ?_
  · obtain ⟨C, hC⟩ := H.bound p' p μ a b
    exact integrableOn_specLimit H.pos hM₀ hMlo H.hp' H.hp H.hp0' H.hp0 (H.cont p' p μ a b)
      (H.quad μ a b) hC hj Ms hMs hτ
  · obtain ⟨C, hC⟩ := H.bound (L *ᵥ p') (L *ᵥ p) μ a b
    exact integrableOn_specLimit H.pos hM₀ hMlo H.pL' H.pL H.h0 H.h1
      (H.cont (L *ᵥ p') (L *ᵥ p) μ a b) (H.quad₂ μ a b) hC hj Ms hMs hτ
  · filter_upwards [hτ.2.2.2.2.1] with x hx
    exact (H.covRel_specM hM₀ j τ.r 2 Ms _ _ (by omega) (by norm_num) hMs (fun _ => hsq x)
      (fun _ => hx)).smul (τ.w₀ x)

end QED.ChainProof.SetACov

end
