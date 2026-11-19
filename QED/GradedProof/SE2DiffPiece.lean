/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2FormD
public import QED.GradedProof.SE2DiffCore

/-!
# Self-energy pieces: differentiability of the limit along lines

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 3. For a self-energy piece (`SEPiece`) whose numerator is polynomial in
the momentum at fixed loop momenta, the limit matrix `W` is differentiable along every line
`t ↦ t w` inside the region (`SEPiece.differentiableAt_line`), so a family converging to a multiple
of its joint integrals has `HasSEFormD` (`SEPiece.hasSEFormD`).

## Proof

Near `t₀` parametrize `t = t₀ + u / (1 - u²)`, `u ∈ (-1, 1)`, so that `(1 - u²)` times the line
momenta is polynomial in `u`. As in `SEPiece.tendsto_nullVec`, interpolation writes the value at
`u` as `-π⁴ ∫_Δ A(x, u) / ((1 - u²)ᵃ V(x, u)ᴺ)`, with `A(x, ·)` polynomial with integrable node
values; moreover `(1 - u²)² V(x, ·)` is polynomial with bounded node values
(`QED.TwoLoop.PauliZeroLimit.isUPoly_symanzikV`) and `V(x, 0) ≥ c > 0`. Hence the value is
`∫ A'(x, u) / V'(x, u)` for polynomial families `A'`, `V'`, differentiable at `u = 0`
(`differentiableAt_integral_upoly`). The inverse parametrization `u = upar(t - t₀)` is
differentiable.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Matrix Set Polynomial
open scoped Real

namespace QED.GradedProof.SE2

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge (IsLoopPoly)

theorem isUPoly_shift_smul {ι : Type*} (c t₀ : ℝ) (w : Fin 4 → ℝ) (μ : Fin 4) :
    IsUPoly (ι := ι) 2 fun _ u => wt u * (((c • ((t₀ + tpar u) • w)) μ : ℝ) : ℂ) := by
  have h : IsUPoly (ι := ι) 2 fun _ u =>
      ((c * w μ * t₀ : ℝ) : ℂ) * wt u + ((c * w μ : ℝ) : ℂ) * (u : ℂ) :=
    ((isUPoly_wt).const_mul fun _ => _).add ((IsUPoly.var.const_mul fun _ => _).mono (by norm_num))
  refine h.congr fun _ u hu => ?_
  have h1 : (1 : ℝ) - u ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
  have h' : (1 : ℂ) - (u : ℂ) ^ 2 ≠ 0 := by exact_mod_cast h1
  simp only [Pi.smul_apply, smul_eq_mul, tpar, wt]
  push_cast
  field_simp

theorem norm_wt_le_one {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) : ‖wt u‖ ≤ 1 := by
  have e : wt u = ((1 - u ^ 2 : ℝ) : ℂ) := by simp [wt]
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [hu.1, hu.2]

theorem continuousAt_tpar : ContinuousAt tpar 0 := by
  unfold tpar
  exact continuousAt_id.div (continuousAt_const.sub (continuousAt_id.pow 2)) (by norm_num)

theorem differentiableAt_upar : DifferentiableAt ℝ upar 0 := by
  unfold upar
  have h : DifferentiableAt ℝ (fun t : ℝ => 1 + 4 * t ^ 2) 0 := by fun_prop
  exact DifferentiableAt.div (by fun_prop) ((differentiableAt_const _).add (h.sqrt (by norm_num)))
    (by positivity)

namespace SEPiece

variable {T : ℝ} (P : SEPiece T)

/-- **The limit matrix is differentiable along lines inside the region**, for numerators
polynomial in the momentum at fixed loop momenta. -/
theorem differentiableAt_line {d : ℕ}
    (hpoly : ∀ ℓ i j, IsLoopPoly 1 d fun y => P.N (y 0) ℓ i j) (w : Fin 4 → ℝ) {t₀ : ℝ}
    (ht₀ : -T ^ 2 < Minkowski.dot (t₀ • w) (t₀ • w)) (i j : Fin 4) :
    DifferentiableAt ℝ (fun t : ℝ => P.W (t • w) i j) t₀ := by
  classical
  set tt : ℝ → ℝ := fun u => t₀ + tpar u with htt
  set mom : ℝ → Fin (P.D.m + 1) → Fin 4 → ℝ := fun u => P.D.mom (tt u • w) with hmom_def
  have hmom : ∀ k μ, IsUPoly (ι := Fin P.D.m → ℝ) 2 fun _ u => wt u * ((mom u k μ : ℝ) : ℂ) :=
    fun k μ => isUPoly_shift_smul (P.D.cs k) t₀ w μ
  set μS : Measure (Fin P.D.m → ℝ) := volume.restrict (simplexSet P.D.m) with hμS
  -- the region near `u = 0`
  have hreg : ∀ᶠ u in 𝓝 (0 : ℝ), -T ^ 2 < Minkowski.dot (tt u • w) (tt u • w) := by
    have hc : ContinuousAt (fun u => tt u * tt u * Minkowski.dot w w) 0 :=
      ((continuousAt_const.add continuousAt_tpar).mul
        (continuousAt_const.add continuousAt_tpar)).mul continuousAt_const
    have h0 : -T ^ 2 < (fun u => tt u * tt u * Minkowski.dot w w) 0 := by
      simpa [tt, tpar, dot_smul_smul] using ht₀
    filter_upwards [hc.tendsto.eventually (lt_mem_nhds h0)] with u hu
    rwa [dot_smul_smul]
  have hIoo : ∀ᶠ u in 𝓝 (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hm0 : 0 < P.D.m := by have := P.D.hm; omega
  have hspan : ∃ a b, P.D.α a 0 * P.D.α b 1 - P.D.α a 1 * P.D.α b 0 ≠ 0 :=
    NoSubdivergence.span (α := P.D.α) fun k => by
      have := P.D.hcrit.noSubdivergenceOfOrder k; have := P.D.hm; omega
  set V : (Fin P.D.m → ℝ) → ℝ → ℝ := fun x u =>
    symanzikV P.D.α (mom u) P.D.M (simplexPoint x) with hV_def
  have hVpos : ∀ u, -T ^ 2 < Minkowski.dot (tt u • w) (tt u • w) →
      ∃ c, 0 < c ∧ ∀ᵐ x ∂μS, c ≤ V x u := fun u hu => by
    obtain ⟨c, hc, hV⟩ := P.hV _ hu
    refine ⟨c, hc, ?_⟩
    filter_upwards [ae_posDef P.D.α hm0 hspan] with x ⟨hxS, hPD⟩
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    exact hV _ hz.1 hz.2 hPD.det_pos.ne'
  have htt0 : tt 0 = t₀ := by simp [tt, tpar]
  obtain ⟨c0, hc0, hV0⟩ := hVpos 0 (by rw [htt0]; exact ht₀)
  -- interpolation of the numerator
  set F : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ := fun u ℓ => P.N (tt u • w) ℓ i j
  have hF : IsUPoly (2 * d) fun ℓ u => wt u ^ d * F u ℓ := fun ℓ => by
    have h := isUPoly_eval_of_isLoopPoly (hpoly ℓ i j) (ι := Unit)
      (ℓ := fun _ u _ => tt u • w) fun _ ν => by
        have h1 := isUPoly_shift_smul (ι := Unit) 1 t₀ w ν
        simp only [one_smul] at h1
        exact h1
    exact h ()
  set Qk : Fin (2 * d + 1) → LoopQuartic := fun k => P.quartic (tt (node (2 * d) k) • w) i j
  have hQk : ∀ k, (Qk k).eval = F (node (2 * d) k) := fun k => P.eval_quartic _ _ _
  set J : ℝ → LoopQuartic := fun u => jointQuartic (2 * d) d Qk u
  have hJe : ∀ u ∈ Ioo (-1 : ℝ) 1, (J u).eval = F u := fun u hu => eval_jointQuartic hF hQk hu
  have hJg : ∀ u ∈ Ioo (-1 : ℝ) 1, P.D.Good (J u) := fun u hu => by
    refine ⟨?_, ?_⟩
    swap
    · rw [hJe u hu]
      show RefinedBound _ _ _ (fun ℓ => P.N (tt u • w) ℓ i j)
      rw [← P.eval_quartic]
      exact (P.good_quartic _ i j).2
    rcases Nat.lt_or_ge P.D.m 7 with h7 | h7
    · refine Or.inr (SEData.quart_qsum _ _ _ fun k _ => ?_)
      rcases (P.good_quartic (tt (node (2 * d) k) • w) i j).1 with h' | h'
      · exact absurd h' (by omega)
      · exact h'
    · exact Or.inl h7
  -- the value as an integral of a ratio of polynomial families
  set n : ℕ := P.D.m - 3 with hn
  set A : (Fin P.D.m → ℝ) → ℝ → ℂ := fun x u => ∑ k, (wt (node (2 * d) k) ^ d *
    (lbasis (2 * d) k).eval (u : ℂ)) * (wt u ^ 4 * paramNum (Qk k) P.D.α (mom u) P.D.M x)
  have hA : IsUPoly (2 * d + 8) A :=
    IsUPoly.sum _ fun k _ => ((isUPoly_lbasis (2 * d) k).const_mul _).mul
      (isUPoly_paramNum (Qk k) P.D.α P.D.M mom hmom)
  have hAi : ∀ u, Integrable (fun x => A x u) μS := fun u => by
    refine integrable_finsetSum _ fun l _ => Integrable.const_mul ?_ _
    exact (integrableOn_paramNum_good (P.good_quartic _ i j) _).const_mul _
  set A' : (Fin P.D.m → ℝ) → ℝ → ℂ := fun x u => A x u * wt u ^ (2 * n)
  set V' : (Fin P.D.m → ℝ) → ℝ → ℂ := fun x u =>
    wt u ^ (d + 4) * (wt u ^ 2 * ((V x u : ℝ) : ℂ)) ^ n
  have hA' : IsUPoly (2 * d + 8 + 2 * (2 * n)) A' := hA.mul (isUPoly_wt_pow _)
  have hV' : IsUPoly (2 * (d + 4) + n * 4) V' :=
    (isUPoly_wt_pow _).mul ((isUPoly_symanzikV P.D.α mom P.D.M (fun x => simplexPoint x)
      hmom).pow n)
  have hval : ∀ᶠ u in 𝓝 (0 : ℝ), P.W (tt u • w) i j = -((π : ℂ) ^ 4) *
      ∫ x, A' x u / V' x u ^ 1 ∂μS := by
    filter_upwards [hreg, hIoo] with u hreg hu
    obtain ⟨cu, hcu, hVu⟩ := hVpos u hreg
    rw [P.W_eq_pv hreg (hJg u hu) (hJe u hu), SEData.pv]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hVu] with x hx
    have hVx : V x u ≠ 0 := (hcu.trans_le hx).ne'
    have hVx' : ((V x u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hVx
    have hw := wt_ne_zero hu
    simp only [J, jointQuartic, paramIntegrand_qsum, A', A, V', Finset.sum_mul, Finset.sum_div,
      pow_one]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [paramIntegrand_zero_eq (Qk k) P.D.α (mom u) P.D.M (by have := P.D.hm; omega) hVx]
    simp only [lam, V] at hVx' ⊢
    field_simp
    ring
  -- differentiability at `u = 0`
  have hVm : ∀ u, AEStronglyMeasurable (fun x => ((V x u : ℝ) : ℂ)) μS := fun u =>
    (Complex.measurable_ofReal.comp ((measurable_symanzikV P.D.α (mom u) P.D.M).comp
      continuous_simplexPoint'.measurable)).aestronglyMeasurable
  set Kq : ℝ → ℝ := fun u => ∑ k, (P.D.M k ^ 2 + ∑ μ, mom u k μ ^ 2)
  have hKq0 : ∀ u, 0 ≤ Kq u := fun u => Finset.sum_nonneg fun _ _ => by positivity
  set E := 2 * (d + 4) + n * 4
  have hK : ∀ k, ∀ᵐ x ∂μS, ‖V' x (node E k)‖ ≤ ∑ k', Kq (node E k') ^ n := fun k => by
    filter_upwards [ae_abs_symanzikV_le P.D.α (mom (node E k)) P.D.M hm0 hspan] with x hx
    have hw1 := norm_wt_le_one (node_mem E k)
    simp only [V']
    rw [norm_mul, norm_pow, norm_pow, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc ‖wt (node E k)‖ ^ (d + 4) * (‖wt (node E k)‖ ^ 2 * |V x (node E k)|) ^ n
        ≤ 1 * (1 * Kq (node E k)) ^ n := by
          refine mul_le_mul (pow_le_one₀ (norm_nonneg _) hw1) (pow_le_pow_left₀ (by positivity)
            (mul_le_mul (pow_le_one₀ (norm_nonneg _) hw1) hx (abs_nonneg _) zero_le_one) n)
            (by positivity) zero_le_one
      _ = Kq (node E k) ^ n := by ring
      _ ≤ ∑ k', Kq (node E k') ^ n :=
          Finset.single_le_sum (f := fun k' => Kq (node E k') ^ n)
            (fun k' _ => pow_nonneg (hKq0 _) n) (Finset.mem_univ k)
  have hV0' : ∀ᵐ x ∂μS, c0 ^ n ≤ ‖V' x 0‖ := by
    filter_upwards [hV0] with x hx
    simp only [V', wt_zero, one_pow, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ hc0.le (hx.trans (le_abs_self _)) n
  have hg := (differentiableAt_integral_upoly (N := 1) hA'
    (fun k => (hAi _).mul_const _) hV'
    (fun k => aestronglyMeasurable_const.mul ((aestronglyMeasurable_const.mul (hVm _)).pow n))
    hK (pow_pos hc0 n) hV0').const_mul (-((π : ℂ) ^ 4))
  have hu : DifferentiableAt ℝ (fun u => P.W (tt u • w) i j) 0 :=
    hg.congr_of_eventuallyEq hval
  have hup : upar (t₀ - t₀) = 0 := by simp [upar]
  have hu' : DifferentiableAt ℝ (fun u => P.W (tt u • w) i j) (upar (t₀ - t₀)) := by
    rwa [hup]
  have e : (fun t : ℝ => P.W (t • w) i j) =
      (fun u => P.W (tt u • w) i j) ∘ fun t => upar (t - t₀) := by
    funext t
    simp only [Function.comp_apply, tt, tpar_upar, add_sub_cancel]
  have h1 : DifferentiableAt ℝ upar (t₀ - t₀) := by rw [sub_self]; exact differentiableAt_upar
  have hsub : DifferentiableAt ℝ (fun t : ℝ => upar (t - t₀)) t₀ :=
    DifferentiableAt.comp (g := upar) (f := fun t : ℝ => t - t₀) t₀ h1
      (differentiableAt_id.sub_const t₀)
  rw [e]
  exact DifferentiableAt.comp (f := fun t : ℝ => upar (t - t₀)) t₀ hu' hsub

/-- **A family converging to a multiple of the joint integrals of a piece has a limit
differentiable along lines.** Same hypotheses as `SEPiece.hasSEForm`. -/
theorem hasSEFormD (_hT : -T ^ 2 < 0) {d : ℕ}
    (hpoly : ∀ ℓ i j, IsLoopPoly 1 d fun y => P.N (y 0) ℓ i j) {h : ℝ → ℂ} {h₀ : ℂ}
    (hh : Tendsto h (𝓝[>] 0) (𝓝 h₀)) {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hG : ∀ p : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot p p → ∀ i j : Fin 4,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε p i j = h ε * QED.TwoLoop.jointEnergyFirstIntegral 2
        (fun ℓ => P.N p ℓ i j * ∏ k, (lineDenom P.D.α (P.D.mom p) P.D.M ε k ℓ)⁻¹)) :
    HasSEFormD T G := fun w =>
  ⟨fun t α β => h₀ * P.W (t • w) α β, fun t ht α β =>
    ⟨(hh.mul (P.tendsto ht α β)).congr' (by
      filter_upwards [hG _ ht α β] with ε hε
      exact hε.symm), (P.differentiableAt_line hpoly w ht α β).const_mul h₀⟩⟩

end SEPiece

end QED.GradedProof.SE2

end
