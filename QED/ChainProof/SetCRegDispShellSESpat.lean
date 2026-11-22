/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSEFub
public import QED.ChainProof.SetCRegDispShellSELim
public import QED.ChainProof.SetCRegDispShellSERad
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The spatial integral of the self-energy building block at zero prescription

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan (the closed form
of `QED.ChainProof.SetCRegDispSE.seProdLim`), for the affine numerators
`seAff c b = c + b (ℓ̸)_{αβ}`. At zero prescription and a Feynman parameter `y` with
`Δ = y m² + (1 - y) M² + y (1 - y) P² > 0`:

* `integral_seTime_seAff_zero`: after the translation `v⃗ ↦ v⃗ - y P⃗` the linear part of the
  numerator integrates to zero and
  `∫ seTime(0) d³v = (-1)^{n+2} K_{n+2} N(-y P) e^{-iπ(n+3/2)} 4π c_{n-1} Δ^{-n}`
  (`K` = `energyConst`, `c` = `seRadC`), for `n ≥ 1`;
* **`integral_seSpatial_seAff_zero`**: below threshold, `∫ seSpatial(0, 0) d³v` is the
  Feynman-parameter integral of that closed form.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.WickModel.SelfEnergyLimit QED.OneLoop QED.Integration
open QED.ChainProof.SetCRegDispSE (seTime seSpatial seWt seEff seRadC neg_ofReal_cpow_neg
  integral_sum_sq_add_rpow_half)
open QED.TwoLoop.VPHalfAtLimit (energyConst)

/-! ### The spatial slash -/

/-- The coefficients `(γ̸ₖ)_{αβ}` of the spatial slash, `γ̸ₖ = slash (0, eₖ)`. -/
noncomputable def seSl (α β : Fin 4) (k : Fin 3) : ℂ :=
  Dirac.slash (Fin.cons 0 (Pi.single k 1) : Fin 4 → ℝ) α β

theorem slash_cons_zero_apply (w : Fin 3 → ℝ) (α β : Fin 4) :
    Dirac.slash (Fin.cons 0 w : Fin 4 → ℝ) α β = ∑ k, (w k : ℂ) * seSl α β k := by
  have e : (Fin.cons 0 w : Fin 4 → ℝ) =
      w 0 • (Fin.cons 0 (Pi.single 0 1) : Fin 4 → ℝ) +
        (w 1 • (Fin.cons 0 (Pi.single 1 1) : Fin 4 → ℝ) +
          w 2 • (Fin.cons 0 (Pi.single 2 1) : Fin 4 → ℝ)) := by
    have c2 : ∀ (x : ℝ) (u : Fin 3 → ℝ), (Fin.cons x u : Fin 4 → ℝ) 2 = u 1 := fun _ _ => rfl
    have c3 : ∀ (x : ℝ) (u : Fin 3 → ℝ), (Fin.cons x u : Fin 4 → ℝ) 3 = u 2 := fun _ _ => rfl
    funext μ
    fin_cases μ <;> simp [c2, c3]
  rw [e, QED.Dirac.slash_add, QED.Dirac.slash_add, QED.Dirac.slash_smul, QED.Dirac.slash_smul,
    QED.Dirac.slash_smul]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three, seSl]
  ring

theorem neg_smul_eq_cons (y : ℝ) (P : Fin 4 → ℝ) :
    -(y • P) = (Fin.cons (-(y * P 0)) (fun k => -(y * P k.succ)) : Fin 4 → ℝ) := by
  funext μ
  refine Fin.cases ?_ (fun k => ?_) μ <;> simp

/-- The shifted affine numerator: `N((-y P⁰, v⃗ - y P⃗)) = N(-y P) + b ∑ₖ vₖ (γ̸ₖ)_{αβ}`. -/
theorem seAff_cons_shift (c b : ℂ) (α β : Fin 4) (y : ℝ) (P : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    seAff c b α β (Fin.cons (-(y * P 0)) (v - fun k => y * P k.succ) : Fin 4 → ℝ) =
      seAff c b α β (-(y • P)) + b * ∑ k, (v k : ℂ) * seSl α β k := by
  rw [neg_smul_eq_cons]
  unfold seAff
  rw [slash_cons_apply, slash_cons_apply (-(y * P 0)), slash_cons_zero_apply,
    slash_cons_zero_apply]
  simp only [Pi.sub_apply]
  push_cast
  simp only [sub_mul, Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib]
  ring

/-! ### The spatial integral at fixed Feynman parameter -/

theorem massW_sub_shift (m M : ℝ) (P : Fin 4 → ℝ) (y : ℝ) (v : Fin 3 → ℝ) :
    massW m M P y (v - fun k => y * P k.succ) =
      ∑ k, v k ^ 2 + selfEnergyFeynmanMass m M (Minkowski.dot P P) y := by
  simp only [massW, Pi.sub_apply, sub_add_cancel]

theorem integrable_coord_mul_rpow {D s : ℝ} (hD : 0 < D) (hs : 2 < s) (k : Fin 3) :
    Integrable fun v : Fin 3 → ℝ => v k * (∑ j, v j ^ 2 + D) ^ (-s) := by
  have hi := integrable_sum_sq_add_rpow hD (by linarith : 3 / 2 < s - 1 / 2)
  refine hi.mono' (by fun_prop : Measurable _).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have hX : 0 < ∑ j, v j ^ 2 + D := by positivity
  have hk : |v k| ≤ (∑ j, v j ^ 2 + D) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith [QED.OneLoop.VertexLimit.sq_le_sum_sq v k])
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hX _)]
  calc |v k| * (∑ j, v j ^ 2 + D) ^ (-s)
      ≤ (∑ j, v j ^ 2 + D) ^ (1 / 2 : ℝ) * (∑ j, v j ^ 2 + D) ^ (-s) := by gcongr
    _ = (∑ j, v j ^ 2 + D) ^ (-(s - 1 / 2)) := by rw [← Real.rpow_add hX]; ring_nf

/-- **The spatial integral of the closed form at zero prescription**, affine numerator,
`n = i + 1 ≥ 1`. -/
theorem integral_seTime_seAff_zero (c b : ℂ) (α β : Fin 4) (m M : ℝ) (i : ℕ) (P : Fin 4 → ℝ)
    {y : ℝ} (hΔ : 0 < selfEnergyFeynmanMass m M (Minkowski.dot P P) y) :
    ∫ v, seTime 0 (seAff c b α β) m M (i + 1) 0 P y v =
      (-1) ^ (i + 3) * ((energyConst (i + 3) : ℝ) : ℂ) * seAff c b α β (-(y • P)) *
        (exp (π * I * (-(((i : ℝ) + 5 / 2 : ℝ) : ℂ))) *
          ((4 * π * (seRadC i *
            selfEnergyFeynmanMass m M (Minkowski.dot P P) y ^ (-((i : ℝ) + 1))) : ℝ) : ℂ)) := by
  set Δ := selfEnergyFeynmanMass m M (Minkowski.dot P P) y with hΔdef
  set a : Fin 3 → ℝ := fun k => y * P k.succ
  set s : ℝ := (i : ℝ) + 5 / 2
  set K : ℂ := (-1) ^ (i + 3) * ((energyConst (i + 3) : ℝ) : ℂ)
  set ph : ℂ := exp (π * I * (-((s : ℝ) : ℂ)))
  have hs : ((i + 1 : ℕ) : ℝ) + 3 / 2 = s := by push_cast; simp only [s]; ring
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  -- the integrand after the translation
  have hpt : ∀ v : Fin 3 → ℝ, seTime 0 (seAff c b α β) m M (i + 1) 0 P y (v - a) =
      K * ph * (seAff c b α β (-(y • P)) * (((∑ k, v k ^ 2 + Δ) ^ (-s) : ℝ) : ℂ)) +
        ∑ k, K * ph * (b * seSl α β k) * ((v k * (∑ j, v j ^ 2 + Δ) ^ (-s) : ℝ) : ℂ) := by
    intro v
    have hX : 0 < ∑ k, v k ^ 2 + Δ := by positivity
    simp only [seTime]
    rw [massW_sub_shift, ← hΔdef, hs]
    simp only [ofReal_zero, zero_mul, add_zero, zero_add]
    rw [seAff_cons_shift, neg_ofReal_cpow_neg hX s]
    simp only [K, ph, Finset.mul_sum]
    push_cast
    rw [show i + 1 + 2 = i + 3 by ring]
    simp only [Fin.sum_univ_three]
    ring
  have hint1 : Integrable fun v : Fin 3 → ℝ =>
      (((∑ k, v k ^ 2 + Δ) ^ (-s) : ℝ) : ℂ) :=
    (integrable_sum_sq_add_rpow hΔ (by simp only [s]; linarith)).ofReal
  have hint2 : ∀ k : Fin 3, Integrable fun v : Fin 3 → ℝ =>
      ((v k * (∑ j, v j ^ 2 + Δ) ^ (-s) : ℝ) : ℂ) := fun k =>
    (integrable_coord_mul_rpow hΔ (by simp only [s]; linarith) k).ofReal
  have hodd : ∀ k : Fin 3, ∫ v : Fin 3 → ℝ, ((v k * (∑ j, v j ^ 2 + Δ) ^ (-s) : ℝ) : ℂ) = 0 := by
    intro k
    rw [integral_complex_ofReal]
    have h := integral_coord_smul_radial (fun x : ℝ => (x + Δ) ^ (-s)) k
    simp only [smul_eq_mul] at h
    rw [h, ofReal_zero]
  rw [← integral_sub_right_eq_self _ a]
  simp_rw [hpt]
  rw [integral_add ((hint1.const_mul (seAff c b α β (-(y • P)))).const_mul (K * ph))
    (integrable_finsetSum _ fun k _ => (hint2 k).const_mul (K * ph * (b * seSl α β k))),
    integral_finsetSum _ fun k _ => (hint2 k).const_mul (K * ph * (b * seSl α β k))]
  simp only [integral_const_mul, hodd, mul_zero, Finset.sum_const_zero, add_zero]
  rw [integral_complex_ofReal, integral_sum_sq_add_rpow_half hΔ i]
  simp only [K, ph, s]
  ring

/-! ### The Feynman-parameter integral -/

/-- The closed form of the spatial integral at the Feynman parameter `y`. -/
noncomputable def seAffY (c b : ℂ) (α β : Fin 4) (m M : ℝ) (i : ℕ) (P : Fin 4 → ℝ) (y : ℝ) :
    ℂ :=
  (-1) ^ (i + 3) * ((energyConst (i + 3) : ℝ) : ℂ) * seAff c b α β (-(y • P)) *
    (exp (π * I * (-(((i : ℝ) + 5 / 2 : ℝ) : ℂ))) *
      ((4 * π * (seRadC i *
        selfEnergyFeynmanMass m M (Minkowski.dot P P) y ^ (-((i : ℝ) + 1))) : ℝ) : ℂ))

/-- **The spatial integral of `seSpatial` at zero prescription**, affine numerator, below
threshold: `∫ seSpatial(0, 0) d³v = ∫₀¹ (i+2)(1-y)^{i+1} seAffY(y) dy`. -/
theorem integral_seSpatial_seAff_zero {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀)
    {P : Fin 4 → ℝ}
    (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)
    {M : ℝ} (hM : M₀ ≤ M) (c b : ℂ) (α β : Fin 4) (i : ℕ) :
    ∫ v, seSpatial 0 (seAff c b α β) m M (i + 1) 0 0 P v =
      ∫ y in Ioc (0 : ℝ) 1, seWt (i + 1) y * seAffY c b α β m M i P y := by
  obtain ⟨C, hC0, hC⟩ := SetCRegDispSE.exists_norm_seTime_le hM₀ hc₀ hP 0
    (norm_seAff_le c b α β) (n := i + 1) (by omega) (Or.inl rfl)
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hm : Measurable fun q : (Fin 3 → ℝ) × ℝ =>
      seWt (i + 1) q.2 * seTime 0 (seAff c b α β) m M (i + 1) (seEff 0 0 q.2) P q.2 q.1 :=
    (SetCRegDispSE.measurable_seTime (continuous_seAff c b α β) 0 m (i + 1) 0 0 P).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hint : Integrable (fun q : (Fin 3 → ℝ) × ℝ =>
      seWt (i + 1) q.2 * seTime 0 (seAff c b α β) m M (i + 1) (seEff 0 0 q.2) P q.2 q.1)
      ((volume : Measure (Fin 3 → ℝ)).prod ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))) := by
    refine Integrable.mono'
      ((SetCRegDispSE.integrable_one_add_norm_four.const_mul (((i + 1 : ℕ) : ℝ) + 1) |>.const_mul
        C).mul_prod (integrable_const (1 : ℝ))) hm.aestronglyMeasurable ?_
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin 3 → ℝ)))
      (ν := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))).ae
      (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [h2] with q hq
    have hy := Ioc_subset_Icc_self hq
    rw [norm_mul, mul_one]
    calc ‖seWt (i + 1) q.2‖ * ‖seTime 0 (seAff c b α β) m M (i + 1) (seEff 0 0 q.2) P q.2 q.1‖
        ≤ (((i + 1 : ℕ) : ℝ) + 1) * (C * (1 + ‖q.1‖) ^ (-(4 : ℝ))) :=
          mul_le_mul (SetCRegDispSE.seWt_norm_le hy) (hC M hM _ q.2 hy q.1) (norm_nonneg _)
            (by positivity)
      _ = C * ((((i + 1 : ℕ) : ℝ) + 1) * (1 + ‖q.1‖) ^ (-(4 : ℝ))) := by ring
  unfold seSpatial
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  have hyI := Ioc_subset_Icc_self hy
  have hΔ : 0 < selfEnergyFeynmanMass m M (Minkowski.dot P P) y :=
    hc₀.trans_le ((hP y hyI).trans (SetCRegDispSE.selfEnergyFeynmanMass_mono hM₀ hM hyI))
  rw [integral_const_mul]
  have e : seEff 0 0 y = 0 := by simp [seEff]
  rw [e, integral_seTime_seAff_zero c b α β m M i P hΔ]
  rfl

end QED.ChainProof.SetCRegDisp

end
