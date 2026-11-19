/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ParamCont
public import QED.GradedProof.VP2TensorForm

/-!
# Vacuum-polarization pieces: the limit, its covariance and the null ray

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, step L1. A
**vacuum-polarization piece** (`VPPiece`) is the two-index analogue of the self-energy piece
`QED.GradedProof.SE2.SEPiece`: parametric data `QED.GradedProof.SE2.SEData` (external line
momenta `cᵢ k`), a numerator tensor `N_k(ℓ)^{μν}` with admissible quartics, the positivity of `V`
on the region `k² > -T²`, and **reflection covariance**
`N_k(ℓ)^{μν} = (R_a)^μ_α (R_a)^ν_β N_{R_a k}(R_a ℓ)^{αβ}`.

* `VPPiece.W`, `VPPiece.tendsto`: the joint integrals converge to the parametric values `W`;
* `VPPiece.tcov`: `W` is reflection covariant (`QED.GradedProof.VP2.TCov`), as in
  `QED.GradedProof.SE2.SEPiece.conj_W` with the tensor action in place of the spinor one;
* `VPPiece.tendsto_nullVec`: `W(t n₀) → W(0)`, the proof of
  `QED.GradedProof.SE2.SEPiece.tendsto_nullVec` (which does not use the covariance).
* `HasVPLim T G`: a family `G ε k μ ν` converges on the region to a reflection-covariant limit
  that is continuous along the null ray; closed under sums, constant multiples and eventual
  equality, and satisfied by multiples of the joint integrals of a piece (`VPPiece.hasVPLim`).
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Matrix Set Polynomial
open scoped Real
open QED.Dirac

namespace QED.GradedProof.VP2

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.ReflCovariance QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.GradedProof.SE2

local notation "Rm" => QED.Dirac.reflectMatrix
local notation "Rf" => QED.Dirac.reflect

/-- **A vacuum-polarization piece.** -/
structure VPPiece (T : ℝ) where
  /-- The parametric data. -/
  D : SEData
  /-- The numerator tensor at the momentum `k`. -/
  N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ
  hQ : ∀ p i j, ∃ Q : LoopQuartic, D.Good Q ∧ Q.eval = fun ℓ => N p ℓ i j
  hV : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → D.VPos (D.mom p)
  hcov : ∀ a : Fin 4 → ℝ, Minkowski.dot a a ≠ 0 → ∀ p ℓ μ ν,
    N p ℓ μ ν = ∑ α, ∑ β, ((Rm a μ α : ℝ) : ℂ) * ((Rm a ν β : ℝ) : ℂ) *
      N (Rf a p) (loopAct (Rm a) ℓ) α β

/-- **A family with a covariant, null-continuous limit** on the region `k² > -T²`. -/
def HasVPLim (T : ℝ) (G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∃ W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ,
    (∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ μ ν : Fin 4,
      Tendsto (fun ε => G ε k μ ν) (𝓝[>] 0) (𝓝 (W k μ ν))) ∧ TCov T W ∧
    ∀ μ ν : Fin 4, Tendsto (fun t : ℝ => W (t • nullVec) μ ν) (𝓝[>] 0) (𝓝 (W 0 μ ν))

theorem rAct_add (a : Fin 4 → ℝ) (X Y : Fin 4 → Fin 4 → ℂ) :
    rAct a (fun μ ν => X μ ν + Y μ ν) = fun μ ν => rAct a X μ ν + rAct a Y μ ν := by
  funext μ ν
  simp only [rAct, mul_add, Finset.sum_add_distrib]

theorem rAct_zero (a : Fin 4 → ℝ) : rAct a (fun _ _ => 0) = fun _ _ => 0 := by
  funext μ ν
  simp [rAct]

namespace HasVPLim

variable {T : ℝ} {G H : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hG : HasVPLim T G) (hH : HasVPLim T H) :
    HasVPLim T fun ε k μ ν => G ε k μ ν + H ε k μ ν := by
  obtain ⟨W, hW, hWc, hWn⟩ := hG
  obtain ⟨V, hV, hVc, hVn⟩ := hH
  refine ⟨fun k μ ν => W k μ ν + V k μ ν, fun k hk μ ν => (hW k hk μ ν).add (hV k hk μ ν),
    fun a ha k hk => ?_, fun μ ν => (hWn μ ν).add (hVn μ ν)⟩
  rw [rAct_add, ← hWc a ha k hk, ← hVc a ha k hk]

theorem const_mul (c : ℂ) (hG : HasVPLim T G) : HasVPLim T fun ε k μ ν => c * G ε k μ ν := by
  obtain ⟨W, hW, hWc, hWn⟩ := hG
  refine ⟨fun k μ ν => c * W k μ ν, fun k hk μ ν => (hW k hk μ ν).const_mul c,
    fun a ha k hk => ?_, fun μ ν => (hWn μ ν).const_mul c⟩
  rw [rAct_mul, ← hWc a ha k hk]

theorem zero : HasVPLim T fun _ _ _ _ => 0 :=
  ⟨fun _ _ _ => 0, fun _ _ _ _ => tendsto_const_nhds, fun a _ _ _ => (rAct_zero a).symm,
    fun _ _ => tendsto_const_nhds⟩

theorem sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (h : ∀ i ∈ s, HasVPLim T (G i)) : HasVPLim T fun ε k μ ν => ∑ i ∈ s, G i ε k μ ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : HasVPLim T _)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (hG : HasVPLim T G)
    (h : ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ μ ν : Fin 4,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε k μ ν = H ε k μ ν) : HasVPLim T H := by
  obtain ⟨W, hW, hWc, hWn⟩ := hG
  exact ⟨W, fun k hk μ ν => (hW k hk μ ν).congr' (h k hk μ ν), hWc, hWn⟩

/-- **A family with a covariant, null-continuous limit whose contraction with `k` tends to `0`
converges to `Π(k²) (k² g - k k)`.** -/
theorem exists_pol (hG : HasVPLim T G)
    (htr : ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ ν : Fin 4,
      Tendsto (fun ε => ∑ μ, ((Minkowski.lower k μ : ℝ) : ℂ) * G ε k μ ν) (𝓝[>] 0) (𝓝 0)) :
    ∃ Pol : ℝ → ℂ, ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ μ ν : Fin 4,
      Tendsto (fun ε => G ε k μ ν) (𝓝[>] 0) (𝓝 (Pol (Minkowski.dot k k) * vpT k μ ν)) := by
  obtain ⟨W, hW, hWc, hWn⟩ := hG
  have hT : Transv T W := fun k hk ν =>
    tendsto_nhds_unique (tendsto_finsetSum _ fun μ _ => (hW k hk μ ν).const_mul _) (htr k hk ν)
  obtain ⟨Pol, hPol⟩ := exists_pol_of_cov hWc hT hWn
  exact ⟨Pol, fun k hk μ ν => by rw [← hPol k hk μ ν]; exact hW k hk μ ν⟩

end HasVPLim

namespace VPPiece

variable {T : ℝ} (P : VPPiece T)

/-- The chosen quartic of the entry `(i, j)` at `p`. -/
noncomputable def quartic (p : Fin 4 → ℝ) (i j : Fin 4) : LoopQuartic :=
  Classical.choose (P.hQ p i j)

theorem good_quartic (p : Fin 4 → ℝ) (i j : Fin 4) : P.D.Good (P.quartic p i j) :=
  (Classical.choose_spec (P.hQ p i j)).1

theorem eval_quartic (p : Fin 4 → ℝ) (i j : Fin 4) :
    (P.quartic p i j).eval = fun ℓ => P.N p ℓ i j :=
  (Classical.choose_spec (P.hQ p i j)).2

/-- **The limit tensor** of the piece. -/
noncomputable def W (p : Fin 4 → ℝ) (i j : Fin 4) : ℂ :=
  P.D.pv (P.quartic p i j) (P.D.mom p)

/-- **The joint integrals converge to `W`** on the region. -/
theorem tendsto {p : Fin 4 → ℝ} (hp : -T ^ 2 < Minkowski.dot p p) (i j : Fin 4) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.N p ℓ i j * ∏ k, (lineDenom P.D.α (P.D.mom p) P.D.M ε k ℓ)⁻¹)) (𝓝[>] 0)
      (𝓝 (P.W p i j)) := by
  have h := SEData.tendsto_pv (P.good_quartic p i j) (P.hV p hp)
  rw [P.eval_quartic] at h
  exact h

/-- Any admissible quartic with the values of an entry has the value of that entry. -/
theorem W_eq_pv {p : Fin 4 → ℝ} (hp : -T ^ 2 < Minkowski.dot p p) {i j : Fin 4}
    {Q : LoopQuartic} (hQ : P.D.Good Q) (he : Q.eval = fun ℓ => P.N p ℓ i j) :
    P.W p i j = P.D.pv Q (P.D.mom p) :=
  SEData.pv_unique (P.good_quartic p i j) hQ (by rw [P.eval_quartic, he]) (P.hV p hp)

/-- **Covariance of the limit** between `p` and `R_a p`. -/
theorem W_eq_rAct {a : Fin 4 → ℝ} (ha : Minkowski.dot a a ≠ 0) {p : Fin 4 → ℝ}
    (hp : -T ^ 2 < Minkowski.dot p p) : P.W p = rAct a (P.W (Rf a p)) := by
  classical
  have h := isSpinLift_reflect ha
  have hLp : -T ^ 2 < Minkowski.dot (Rf a p) (Rf a p) := by
    rw [QED.Dirac.dot_reflect ha]
    exact hp
  funext i j
  set L := Rm a
  set Q₂ := P.quartic (Rf a p)
  set c : Fin 4 × Fin 4 → ℂ := fun kl => ((L i kl.1 : ℝ) : ℂ) * ((L j kl.2 : ℝ) : ℂ)
  set Qs := qsum Finset.univ c (fun kl => lmap (blockL L) (Q₂ kl.1 kl.2))
  have hI : ∀ kl ∈ (Finset.univ : Finset (Fin 4 × Fin 4)),
      IntegrableOn (paramIntegrand (lmap (blockL L) (Q₂ kl.1 kl.2)) P.D.α (P.D.mom p) P.D.M 0)
        (simplexSet P.D.m) := fun kl _ => by
    have := SEData.integrableOn_pv (P.good_quartic (Rf a p) kl.1 kl.2) (P.hV _ hLp)
    rw [show P.D.mom (Rf a p) = fun i => L *ᵥ P.D.mom p i by
      rw [← QED.Dirac.reflectMatrix_mulVec, P.D.mom_mulVec]] at this
    exact this.congr_fun (fun x _ => paramIntegrand_map h _ _ _ _ _ x)
      (QED.Integration.Feynman.measurableSet_simplexSet _)
  have hev : Qs.eval = fun ℓ => P.N p ℓ i j := by
    funext ℓ
    rw [eval_qsum, P.hcov a ha p ℓ i j]
    simp only [eval_lmap_blockL, Q₂, P.eval_quartic, c, Fintype.sum_prod_type, L]
  have hgood : P.D.Good Qs := by
    refine ⟨?_, by rw [hev]; rw [← P.eval_quartic]; exact (P.good_quartic p i j).2⟩
    rcases Nat.lt_or_ge P.D.m 7 with h7 | h7
    · refine Or.inr (SEData.quart_qsum _ _ _ fun kl _ => SEData.quart_lmap _ _ ?_)
      rcases (P.good_quartic (Rf a p) kl.1 kl.2).1 with h' | h'
      · omega
      · exact h'
    · exact Or.inl h7
  rw [P.W_eq_pv hp hgood hev, SEData.pv_qsum _ _ _ hI]
  simp only [rAct, c, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← SEData.pv_map h, ← P.D.mom_mulVec, QED.Dirac.reflectMatrix_mulVec]
  rfl

/-- **The limit is reflection covariant** on the region. -/
theorem tcov : TCov T P.W := by
  intro a ha k hk
  have hk' : -T ^ 2 < Minkowski.dot (Rf a k) (Rf a k) := by
    rw [QED.Dirac.dot_reflect ha]
    exact hk
  have h := P.W_eq_rAct ha hk'
  rwa [QED.Dirac.reflect_reflect ha] at h

/-- **The limit along the null ray**: `W(t n₀) → W(0)` as `t → 0⁺`, for numerators polynomial
in the momentum at fixed loop momenta. -/
theorem tendsto_nullVec (hT : -T ^ 2 < 0) {d : ℕ}
    (hpoly : ∀ ℓ i j, IsLoopPoly 1 d fun y => P.N (y 0) ℓ i j) (i j : Fin 4) :
    Tendsto (fun t : ℝ => P.W (t • nullVec) i j) (𝓝[>] 0) (𝓝 (P.W 0 i j)) := by
  classical
  have hreg : ∀ t : ℝ, -T ^ 2 < Minkowski.dot (t • nullVec) (t • nullVec) := fun t => by
    rw [dot_smul_nullVec]; exact hT
  set mom : ℝ → Fin (P.D.m + 1) → Fin 4 → ℝ := fun u => P.D.mom (tpar u • nullVec) with hmom_def
  have hmom : ∀ k μ, IsUPoly (ι := Fin P.D.m → ℝ) 2 fun _ u => wt u * ((mom u k μ : ℝ) : ℂ) :=
    fun k μ => isUPoly_tpar_smul (P.D.cs k) nullVec μ
  -- `V` does not depend on `u`
  set V0 : (Fin P.D.m → ℝ) → ℝ := fun x => symanzikV P.D.α (P.D.mom 0) P.D.M (simplexPoint x)
  have hVc : ∀ u z, symanzikV P.D.α (mom u) P.D.M z =
      symanzikV P.D.α (P.D.mom 0) P.D.M z := fun u z => by
    have h1 := symanzikV_smul_null P.D.α P.D.cs (w := tpar u • nullVec) (dot_smul_nullVec _) P.D.M z
    have h2 := symanzikV_smul_null P.D.α P.D.cs (w := (0 : Fin 4 → ℝ)) (by simp [Minkowski.dot_eq])
      P.D.M z
    exact h1.trans h2.symm
  obtain ⟨c0, hc0, hV0⟩ := P.hV 0 (by simpa [Minkowski.dot_eq] using hT)
  have hm0 : 0 < P.D.m := by have := P.D.hm; omega
  have hspan : ∃ a b, P.D.α a 0 * P.D.α b 1 - P.D.α a 1 * P.D.α b 0 ≠ 0 :=
    NoSubdivergence.span (α := P.D.α) fun k => by
      have := P.D.hcrit.noSubdivergenceOfOrder k; have := P.D.hm; omega
  have hVae : ∀ᵐ x ∂(volume.restrict (simplexSet P.D.m)), c0 ≤ V0 x := by
    filter_upwards [ae_posDef P.D.α hm0 hspan] with x ⟨hxS, hPD⟩
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    exact hV0 _ hz.1 hz.2 hPD.det_pos.ne'
  -- interpolation of the numerator
  set F : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ := fun u ℓ => P.N (tpar u • nullVec) ℓ i j
  have hF : IsUPoly (2 * d) fun ℓ u => wt u ^ d * F u ℓ := fun ℓ => by
    have h := isUPoly_eval_of_isLoopPoly (hpoly ℓ i j) (ι := Unit)
      (ℓ := fun _ u _ => tpar u • nullVec) fun _ ν => by
        simpa using isUPoly_tpar_smul (ι := Unit) 1 nullVec ν
    exact h ()
  set Qk : Fin (2 * d + 1) → LoopQuartic := fun k =>
    P.quartic (tpar (node (2 * d) k) • nullVec) i j
  have hQk : ∀ k, (Qk k).eval = F (node (2 * d) k) := fun k => P.eval_quartic _ _ _
  set J : ℝ → LoopQuartic := fun u => jointQuartic (2 * d) d Qk u
  have hJe : ∀ u ∈ Ioo (-1 : ℝ) 1, (J u).eval = F u := fun u hu => eval_jointQuartic hF hQk hu
  have hJg : ∀ u ∈ Ioo (-1 : ℝ) 1, P.D.Good (J u) := fun u hu => by
    refine ⟨?_, ?_⟩
    swap
    · rw [hJe u hu]
      show RefinedBound _ _ _ (fun ℓ => P.N (tpar u • nullVec) ℓ i j)
      rw [← P.eval_quartic]
      exact (P.good_quartic _ i j).2
    rcases Nat.lt_or_ge P.D.m 7 with h7 | h7
    · refine Or.inr (SEData.quart_qsum _ _ _ fun k _ => ?_)
      rcases (P.good_quartic (tpar (node (2 * d) k) • nullVec) i j).1 with h' | h'
      · exact absurd h' (by omega)
      · exact h'
    · exact Or.inl h7
  -- the value as an integral of a polynomial family
  set A : (Fin P.D.m → ℝ) → ℝ → ℂ := fun x u => ∑ k, (wt (node (2 * d) k) ^ d *
    (lbasis (2 * d) k).eval (u : ℂ)) * (wt u ^ 4 * paramNum (Qk k) P.D.α (mom u) P.D.M x)
  have hA : IsUPoly (2 * d + 8) A :=
    IsUPoly.sum _ fun k _ => ((isUPoly_lbasis (2 * d) k).const_mul _).mul
      (isUPoly_paramNum (Qk k) P.D.α P.D.M mom hmom)
  have hAi : ∀ k, Integrable (fun x => A x (node (2 * d + 8) k))
      (volume.restrict (simplexSet P.D.m)) := fun k => by
    refine integrable_finsetSum _ fun l _ => Integrable.const_mul ?_ _
    exact (integrableOn_paramNum_good (P.good_quartic _ i j) _).const_mul _
  have hval : ∀ u ∈ Ioo (-1 : ℝ) 1, P.W (tpar u • nullVec) i j = -((π : ℂ) ^ 4) *
      ∫ x in simplexSet P.D.m, A x u / (wt u ^ (d + 4) * (V0 x : ℂ) ^ (P.D.m - 3)) := by
    intro u hu
    rw [P.W_eq_pv (hreg _) (hJg u hu) (hJe u hu), SEData.pv]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hVae] with x hx
    have hV0x : V0 x ≠ 0 := (hc0.trans_le hx).ne'
    have hV0x' : ((V0 x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hV0x
    have hw := wt_ne_zero hu
    simp only [J, jointQuartic, paramIntegrand_qsum, A, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hVu : symanzikV P.D.α (mom u) P.D.M (simplexPoint x) ≠ 0 := by rw [hVc]; exact hV0x
    rw [paramIntegrand_zero_eq (Qk k) P.D.α (mom u) P.D.M (by have := P.D.hm; omega) hVu]
    simp only [hVc, lam, V0] at hV0x' ⊢
    field_simp
    ring
  have hVm : AEStronglyMeasurable (fun x => ((V0 x : ℝ) : ℂ))
      (volume.restrict (simplexSet P.D.m)) :=
    (Complex.measurable_ofReal.comp ((measurable_symanzikV P.D.α (P.D.mom 0) P.D.M).comp
      continuous_simplexPoint'.measurable)).aestronglyMeasurable
  have hlim := (tendsto_integral_upoly (a := d + 4) (N := P.D.m - 3) hA hAi hc0 hVae hVm).const_mul
    (-((π : ℂ) ^ 4))
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hW0 : P.W 0 i j = -((π : ℂ) ^ 4) *
      ∫ x in simplexSet P.D.m, A x 0 / ((V0 x : ℂ) ^ (P.D.m - 3)) := by
    have := hval 0 h0
    simp only [tpar, zero_div, zero_smul, wt_zero, one_pow, one_mul] at this
    exact this
  rw [← hW0] at hlim
  have hg : Tendsto (fun u => P.W (tpar u • nullVec) i j) (𝓝 0) (𝓝 (P.W 0 i j)) := by
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
      with u hu
    exact (hval u hu).symm
  exact (hg.comp tendsto_upar).congr fun t => by simp only [Function.comp_apply, tpar_upar]


/-- **A multiple of the joint integrals of a piece** has a covariant, null-continuous limit. -/
theorem hasVPLim (hT : -T ^ 2 < 0) {d : ℕ}
    (hpoly : ∀ ℓ i j, IsLoopPoly 1 d fun y => P.N (y 0) ℓ i j) {h : ℝ → ℂ} {h₀ : ℂ}
    (hh : Tendsto h (𝓝[>] 0) (𝓝 h₀)) {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hG : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ i j : Fin 4,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε p i j = h ε * QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.N p ℓ i j * ∏ k, (lineDenom P.D.α (P.D.mom p) P.D.M ε k ℓ)⁻¹)) :
    HasVPLim T G := by
  refine ⟨fun p i j => h₀ * P.W p i j, fun p hp i j => ?_, fun a ha k hk => ?_, fun i j => ?_⟩
  · exact (hh.mul (P.tendsto hp i j)).congr' (by
      filter_upwards [hG p hp i j] with ε hε
      exact hε.symm)
  · rw [rAct_mul]
    exact congrArg (fun X => fun i j => h₀ * X i j) (P.tcov a ha k hk)
  · exact (P.tendsto_nullVec hT hpoly i j).const_mul h₀

end VPPiece

end QED.GradedProof.VP2

end
