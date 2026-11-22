/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetACovTerm
public import QED.ChainProof.SetANestedAtPauli

/-!
# Covariance of the set (a) limits, from the nested form

Helper level for `QED.ChainProof.SetAPauli.SetACovLink`, one of the obligations of
`QED.ChainProof.SetAPauli.setAPauliLink_of_nested`. Under the nested form of the set (a) family
vertex at fixed `ε` (`QED.ChainProof.SetANestedAt.SetANestForm`, obligation (N), **not** proved
here) and the `ε`-uniform spectral form `T★ᵤ` of `Π⁽⁴⁾_ε` (proved,
`QED.ChainProof.SetANestedAt.regFlavors_spec`):

* `setATermLim`, `setALimMat`: the explicit limit matrices of one spectral term and of a list of
  terms (`setATermLim_apply`: the entries are the engine limits of `SAOuterTerm.pieces`);
* **`setALim_eq`**: every set (a) limit at an on-shell positive-energy pair with `q² > 0` is
  `setALimMat` of the `T★ᵤ` list, the same list at every such pair;
* `covRel_setATermLim`, `covRel_setALimMat`: these matrices are covariant, for every good term
  (any power `j ≤ 2` of `k²`, any number of spectral factors), by
  `QED.ChainProof.SetACov.CovNum.covRel_termMat` with the four numerators;
* **`setACovLink_of_nestForm`**: `SetANestForm P₀ → SetACovLink P₀`.

The fixed-`ε` energy-first integrals are not Lorentz covariant (they single out the energy
component), so covariance is proved on the limits, through their parametric representation.
-/

@[expose] public section

open Complex Matrix MeasureTheory Filter Topology Set
open scoped Real
open QED.WickModel (Params IsOnePI)

namespace QED.ChainProof.SetACov

open QED.OneLoop QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance QED.TwoLoop.VPHalfAtLimit
open QED.TwoLoop.VPHalfAtGen QED.TwoLoop.VPHalfAtAssembly QED.TwoLoop.VPUnitNested
open QED.Dirac QED.ChainProof.HCBB2 QED.ChainProof.SetASpec QED.ChainProof.SetANest
open QED.ChainProof.SetANestedAt QED.ChainProof.SetAPauli

/-! ### Lists of matrix families -/

/-- The entries of a list sum of matrix families. -/
theorem list_sum_apply {ι : Type*} (l : List ι) (F : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (μ a b : Fin 4) : (l.map F).sum μ a b = (l.map fun q => F q μ a b).sum := by
  induction l with
  | nil => simp
  | cons q l ih => simp only [List.map_cons, List.sum_cons, Pi.add_apply, Matrix.add_apply, ih]

/-- Covariance passes to list sums. -/
theorem CovRel.list_sum {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    {ι : Type*} (l : List ι) {A B : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ q ∈ l, CovRel L S T (A q) (B q)) : CovRel L S T (l.map A).sum (l.map B).sum := by
  induction l with
  | nil => simpa using (CovRel.zero : CovRel L S T 0 0)
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h q List.mem_cons_self).add (ih fun r hr => h r (List.mem_cons_of_mem _ hr))

/-! ### The limit matrices of the set (a) family vertex -/

/-- The limit matrices of one spectral term of `Π⁽⁴⁾` in the outer vertex: the engine terms
`SAOuterTerm.pieces`, as matrices. -/
noncomputable def setATermLim (e m mγ Λ : ℝ) (τ : SAOuterTerm) (p' p : Fin 4 → ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  (kap e * (((Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ)) •
    if τ.t then
      termMat m (saMs4 mγ Λ) outMatS (fun μ i j => (quadN_numS μ i j).quad.choose) (τ.j + 1)
          τ p' p +
        termMat m (saMs4 mγ Λ) (outMatL m) (fun μ i j => (quadN_numL m p' p μ i j).quad.choose)
          (τ.j + 1) τ p' p +
        termMat m (saMs4 mγ Λ) (outMatQ m) (fun μ i j => (quadN_numQ m p' p μ i j).quad.choose)
          τ.j τ p' p
    else termMat m (saMs4 mγ Λ) (outMatG m) (fun μ i j => (quadN_numG m p' p μ i j).quad.choose)
      τ.j τ p' p

/-- The entries of `setATermLim` are the engine limits of the pieces of the term. -/
theorem setATermLim_apply (e m mγ Λ : ℝ) (τ : SAOuterTerm) (p' p : Fin 4 → ℝ) (μ a b : Fin 4) :
    setATermLim e m mγ Λ τ p' p μ a b =
      ((τ.pieces e m mγ Λ p' p μ a b).map fun q => q.1 * q.2.lim m (saMs4 mγ Λ) p' p).sum := by
  unfold setATermLim SAOuterTerm.pieces
  cases τ.t
  · simp only [Bool.false_eq_true, ite_false, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, Pi.smul_apply, Matrix.smul_apply,
      smul_eq_mul, termMat, Matrix.of_apply, SALimTerm.lim, SAOuterTerm.engine, outMatG]
  · simp only [ite_true, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, Pi.smul_apply, Pi.add_apply, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, termMat, Matrix.of_apply, SALimTerm.lim,
      SAOuterTerm.engine, outMatS, outMatL, outMatQ]
    ring

/-- **The limit matrices of the set (a) family vertex** for a list of spectral terms. -/
noncomputable def setALimMat (e m mγ Λ : ℝ) (Lt : List (ℂ × SAOuterTerm)) (p' p : Fin 4 → ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / I) • (Lt.map fun q => q.1 • setATermLim e m mγ Λ q.2 p' p).sum

section Fixed

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt}

/-- **Every set (a) limit is the explicit limit matrix** of the `T★ᵤ` list, under the nested
form at fixed `ε`. -/
theorem setALim_eq (hm : 0 < P₀.m) (hN : SetANestForm P₀)
    (hA : SetAAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D) {Lt : List (ℂ × SAOuterTerm)}
    (hL : ∀ q ∈ Lt, q.2.Good (min P₀.m (min mγ Λ)))
    (hVP : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k a b,
      Graded.vacuumPolarizationPart { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
        (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) D 2 k a b = saOuterTensor Lt ε k a b)
    {p' p : Fin 4 → ℝ} (hpq : IsPairQ P₀.m p' p) {V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : setALim P₀ M₁ M₂ c₁ c₂ mγ Λ D p' p V) :
    V = setALimMat P₀.e P₀.m mγ Λ Lt p' p := by
  obtain ⟨hp', hp, hp0', hp0, -⟩ := id hpq
  obtain ⟨-, -, -, -, hmγ, hΛ, -, -, -⟩ := id hA
  set Mlo := min P₀.m (min mγ Λ)
  have hMlo : 0 < Mlo := lt_min hm (lt_min hmγ hΛ)
  have h1 : Mlo ≤ mγ := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : Mlo ≤ Λ := (min_le_right _ _).trans (min_le_right _ _)
  have hMs : ∀ i, Mlo ≤ saMs4 mγ Λ i := fun i => by
    fin_cases i <;> simp [saMs4, h1, h2]
  funext μ
  ext a b
  refine tendsto_nhds_unique (hV μ a b) ?_
  have hval : setALimMat P₀.e P₀.m mγ Λ Lt p' p μ a b = (1 / I) * (Lt.map fun q => q.1 *
      ((q.2.pieces P₀.e P₀.m mγ Λ p' p μ a b).map fun r =>
        r.1 * r.2.lim P₀.m (saMs4 mγ Λ) p' p).sum).sum := by
    simp only [setALimMat, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, list_sum_apply,
      setATermLim_apply]
  rw [hval]
  have hP := fun q (hq : q ∈ Lt) => SAOuterTerm.pieces_hyp (hL q hq) P₀.e P₀.m mγ Λ p' p μ a b
  have hT := tendsto_list_sum' Lt (l := 𝓝[>] (0 : ℝ))
    (f := fun q ε => q.1 * ((q.2.pieces P₀.e P₀.m mγ Λ p' p μ a b).map fun r =>
      r.1 * r.2.val P₀.m (saMs4 mγ Λ) p' p ε).sum)
    (a := fun q => q.1 * ((q.2.pieces P₀.e P₀.m mγ Λ p' p μ a b).map fun r =>
      r.1 * r.2.lim P₀.m (saMs4 mγ Λ) p' p).sum)
    fun q hq => (tendsto_list_sum' _ fun r hr => (SALimTerm.tendsto hm hMlo le_rfl hp' hp hp0'
      hp0 hMs (hP q hq r hr)).const_mul r.1).const_mul q.1
  refine (hT.const_mul (1 / I)).congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
  obtain ⟨-, he⟩ := hN M₁ M₂ c₁ c₂ mγ Λ D hA p' p hpq ε hε.1 hε.2 μ a b
  refine Eq.trans ?_ he.symm
  congr 1
  have hX : vpTwo P₀ M₁ M₂ c₁ c₂ mγ Λ D ε = fun k a b => saOuterTensor Lt ε k a b :=
    funext fun k => funext fun a => funext fun b => hVP ε hε.1 hε.2 k a b
  have e1 : nestInt P₀.e P₀.m mγ Λ ε p' p (vpTwo P₀ M₁ M₂ c₁ c₂ mγ Λ D ε) μ a b = fun ℓ =>
      (Lt.map fun q => q.1 * q.2.outer P₀.e P₀.m mγ Λ p' p μ a b ε ℓ).sum := by
    funext ℓ
    rw [hX]
    exact saOuterList_eq P₀.e P₀.m mγ Λ p' p μ a b Lt ε ℓ
  have hO : ∀ q ∈ Lt, EFInt (q.2.outer P₀.e P₀.m mγ Λ p' p μ a b ε) ∧
      energyFirstIntegral (q.2.outer P₀.e P₀.m mγ Λ p' p μ a b ε) =
        ((q.2.pieces P₀.e P₀.m mγ Λ p' p μ a b).map fun r =>
          r.1 * r.2.val P₀.m (saMs4 mγ Λ) p' p ε).sum := by
    intro q hq
    have e2 : q.2.outer P₀.e P₀.m mγ Λ p' p μ a b ε = fun ℓ =>
        ((q.2.pieces P₀.e P₀.m mγ Λ p' p μ a b).map fun r => r.1 * saLimTermInt r.2.N P₀.m r.2.j
          (saMs4 mγ Λ) r.2.r r.2.A r.2.ξ (r.2.w ε) ε p' p ℓ).sum :=
      funext fun ℓ => SAOuterTerm.outer_eq _ _ _ _ _ _ _ _ _ _ hε.1 ℓ
    have hI : ∀ r ∈ q.2.pieces P₀.e P₀.m mγ Λ p' p μ a b, EFInt fun ℓ =>
        r.1 * saLimTermInt r.2.N P₀.m r.2.j (saMs4 mγ Λ) r.2.r r.2.A r.2.ξ (r.2.w ε) ε p' p ℓ :=
      fun r hr => (SALimTerm.efInt_val hm hMlo le_rfl hp' hp hp0' hp0 hMs (hP q hq r hr) hε.1
        hε.2).const_mul r.1
    rw [e2]
    refine ⟨?_, ?_⟩
    · rw [← e2]
      obtain ⟨l, -, hf⟩ := SAOuterTerm.outerForm hm hMlo le_rfl h1 h2 hp' hp hp0' hp0 P₀.e
        (hL q hq) μ a b
      exact (hf ε hε.1 hε.2).1
    · rw [efi_list_sum _ _ hI]
      exact congrArg List.sum (List.map_congr_left fun r _ => by
        rw [efi_const_mul]; rfl)
  rw [e1, efi_list_sum Lt _ fun q hq => (hO q hq).1.const_mul q.1]
  exact congrArg List.sum (List.map_congr_left fun q hq => by rw [efi_const_mul, (hO q hq).2])

end Fixed

/-! ### Covariance -/

section Cov

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-- **Covariance of the limit matrices of one spectral term.** -/
theorem covRel_setATermLim {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (h : IsSpinLift L S T) {p' p : Fin 4 → ℝ} (hpq : IsPairQ m p' p) (h0 : 0 < (L *ᵥ p') 0)
    (h1 : 0 < (L *ᵥ p) 0) {τ : SAOuterTerm} (hτ : τ.Good (min m (min mγ Λ))) :
    CovRel L S T (setATermLim e m mγ Λ τ p' p) (setATermLim e m mγ Λ τ (L *ᵥ p') (L *ᵥ p)) := by
  set Mlo := min m (min mγ Λ)
  have hMlo : 0 < Mlo := lt_min hm (lt_min hmγ hΛ)
  have hMs : ∀ i, Mlo ≤ saMs4 mγ Λ i := fun i => by
    have h1 : Mlo ≤ mγ := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : Mlo ≤ Λ := (min_le_right _ _).trans (min_le_right _ _)
    fin_cases i <;> simp [saMs4, h1, h2]
  have hj := hτ.1
  have cG := (CovNum.of_quadN hm h hpq h0 h1 (Nf := outMatG m)
    (fun p' p μ i j => quadN_numG m p' p μ i j) (isLoopPoly_outMatG m)
    fun μ ℓ => by simp only [outMatG_eq]; exact NG_cov h m p' p μ ℓ).covRel_termMat hMlo le_rfl
    hMs hτ (j := τ.j)
  have cS := fun j => (CovNum.of_quadN hm h hpq h0 h1 (Nf := outMatS)
    (fun _ _ μ i j => quadN_numS μ i j) isLoopPoly_outMatS
    fun μ ℓ => by simp only [outMatS_eq]; exact NS_cov h μ ℓ).covRel_termMat hMlo le_rfl
    hMs hτ (j := j)
  have cL := fun j => (CovNum.of_quadN hm h hpq h0 h1 (Nf := outMatL m)
    (fun p' p μ i j => quadN_numL m p' p μ i j) (isLoopPoly_outMatL m)
    fun μ ℓ => by simp only [outMatL_eq]; exact NL_cov h m p' p μ ℓ).covRel_termMat hMlo le_rfl
    hMs hτ (j := j)
  have cQ := (CovNum.of_quadN hm h hpq h0 h1 (Nf := outMatQ m)
    (fun p' p μ i j => quadN_numQ m p' p μ i j) (isLoopPoly_outMatQ m)
    fun μ ℓ => by simp only [outMatQ_eq]; exact NQ_cov h m p' p μ ℓ).covRel_termMat hMlo le_rfl
    hMs hτ (j := τ.j)
  unfold setATermLim
  refine CovRel.smul _ ?_
  cases ht : τ.t
  · simp only [ht, Bool.false_eq_true, ite_false] at hj ⊢
    exact cG (by omega)
  · simp only [ht, ite_true] at hj ⊢
    exact ((cS (τ.j + 1) (by omega)).add (cL (τ.j + 1) (by omega))).add (cQ (by omega))

/-- **Covariance of the limit matrices of the set (a) family vertex** for a list of good
spectral terms. -/
theorem covRel_setALimMat {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    (h : IsSpinLift L S T) {p' p : Fin 4 → ℝ} (hpq : IsPairQ m p' p) (h0 : 0 < (L *ᵥ p') 0)
    (h1 : 0 < (L *ᵥ p) 0) {Lt : List (ℂ × SAOuterTerm)}
    (hL : ∀ q ∈ Lt, q.2.Good (min m (min mγ Λ))) :
    CovRel L S T (setALimMat e m mγ Λ Lt p' p) (setALimMat e m mγ Λ Lt (L *ᵥ p') (L *ᵥ p)) :=
  (CovRel.list_sum Lt fun q hq =>
    (covRel_setATermLim hm hmγ hΛ h hpq h0 h1 (hL q hq)).smul q.1).smul (1 / I)

end Cov

/-- **`SetACovLink` from the nested form**: if the set (a) family vertex has the nested form at
fixed `ε` (`QED.ChainProof.SetANestedAt.SetANestForm`, obligation (N), open), the set (a) limits
are covariant under every spin-lifted `L` that keeps positive energies. -/
theorem setACovLink_of_nestForm {P₀ : Params} (hm : 0 < P₀.m) (hN : SetANestForm P₀) :
    SetACovLink P₀ := by
  intro M₁ M₂ c₁ c₂ mγ Λ D hA L S T h p' p hpq h0 h1 V W hV hW
  obtain ⟨-, -, -, -, hmγ, hΛ, -, -, -⟩ := id hA
  obtain ⟨Lt, hLt, hVP⟩ := regFlavors_spec hm hA
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := id hpq
  have hpqL : IsPairQ P₀.m (L *ᵥ p') (L *ᵥ p) := by
    refine ⟨by rw [h.dot_mulVec]; exact hp', by rw [h.dot_mulVec]; exact hp, h0, h1, ?_⟩
    rw [← Matrix.mulVec_sub, h.dot_mulVec]
    exact hq
  rw [setALim_eq hm hN hA hLt hVP hpq hV, setALim_eq hm hN hA hLt hVP hpqL hW]
  exact covRel_setALimMat hm hmγ hΛ h hpq h0 h1 hLt

end QED.ChainProof.SetACov

end
