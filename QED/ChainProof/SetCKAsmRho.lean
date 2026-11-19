/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKScOutSDom
public import QED.ChainProof.SetCKScOutCMast
public import QED.ChainProof.SetCKPairInt

/-!
# Set (c), Stage K, assembly: from the `ρ`-form to the `Q`-derivative form

Helper level (no frozen statement). The pieces of the set (c) kernel are proved in two forms:
the Stieltjes (`ρ`-) form `∫₀¹ ρ Q/(Q + t)` (L pair, G1, G2) and the `Q`-derivative form
`∫₀¹ H Q'/(Q + t)²` (G3, G4S, G4C). The common form chosen for the assembly is the
`Q`-derivative form, because the conversion `ρ ↦ H` needs only one Fubini swap and the
integrability of `ρ Q/(Q + t)`, while the converse `H ↦ ρ = H'/Q` would need the
differentiability of the cube integrals `H` (no closed form is available for them).

**`setCKStieltjes_eq_rhoH`**: if `ρ Q/(Q + t)` is integrable on `(0, 1)`, then with
`H_ρ(X) = ∫₀^X ρ Q` (`setCKRhoH`),

`∫₀¹ ρ Q/(Q + t) = ∫₀¹ H_ρ(X) Q'(X)/(Q(X) + t)² dX`,

and the right-hand integrand is interval integrable. Proof: Fubini for
`1{x < X} ρ(x) Q(x) Q'(X)/(Q(X) + t)²` on `(0, 1)²`, with
`∫_x^1 Q'(X)/(Q(X) + t)² dX = 1/(Q(x) + t)` (`setCK_section_const`, via the node change of
variables `scOutS_section`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink

/-- `H_ρ(X) = ∫₀^X ρ Q`, the `Q`-derivative-form weight of a Stieltjes density `ρ`. -/
noncomputable def setCKRhoH (ρ : ℝ → ℝ) (X : ℝ) : ℝ := ∫ x in (0 : ℝ)..X, ρ x * setCKQ x

section

variable {t x : ℝ}

/-- `∫₀¹ 1{x < X} c Q'(X)/(Q(X) + t)² dX = c/(Q(x) + t)`. -/
theorem setCK_section_const (ht : 0 < t) (hx : x ∈ Ioo (0 : ℝ) 1) (c : ℝ) :
    Integrable (fun X => (if x < X then c else 0) * (setCKdQ X / (setCKQ X + t) ^ 2))
        (volume.restrict (Ioo (0 : ℝ) 1)) ∧
      ∫ X in Ioo (0 : ℝ) 1, (if x < X then c else 0) * (setCKdQ X / (setCKQ X + t) ^ 2) =
        c / (setCKQ x + t) := by
  have hu : 0 < setCKQ x + t := by
    have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩; linarith
  obtain ⟨i0, v0⟩ := scOutCI0 (M := setCKQ x + t) (c := 0) (by simpa using hu)
  have hk : IntegrableOn (fun v => (fun _ : ℝ => c) v / (setCKQ x + t + v) ^ 2) (Ioi 0) :=
    IntegrableOn.congr_fun (i0.const_mul c) (fun v _ => by simp only; ring) measurableSet_Ioi
  obtain ⟨hi, hv⟩ := scOutS_section (t := t) hx hk
  refine ⟨hi, hv.trans ?_⟩
  have e : (fun v => c / (setCKQ x + t + v) ^ 2) = fun v => c * (1 / (setCKQ x + t + v) ^ 2) := by
    funext v; ring
  rw [e, integral_const_mul, v0, add_zero]
  ring

theorem measurable_setCKdQ_div : Measurable fun X => setCKdQ X / (setCKQ X + t) ^ 2 := by
  unfold setCKdQ setCKQ; fun_prop

/-- **The `ρ`-form as a `Q`-derivative form.** -/
theorem setCKStieltjes_eq_rhoH {ρ : ℝ → ℝ} (ht : 0 < t)
    (hρ : IntegrableOn (fun x => ρ x * (setCKQ x / (setCKQ x + t))) (Ioo 0 1)) :
    IntervalIntegrable (fun X => setCKRhoH ρ X * (setCKdQ X / (setCKQ X + t) ^ 2)) volume 0 1 ∧
      setCKStieltjes ρ t =
        ∫ X in (0 : ℝ)..1, setCKRhoH ρ X * (setCKdQ X / (setCKQ X + t) ^ 2) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  set g : ℝ → ℝ := fun x => ρ x * setCKQ x with hgdef
  set w : ℝ → ℝ := fun X => setCKdQ X / (setCKQ X + t) ^ 2 with hwdef
  have hu : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < setCKQ x + t := fun x hx => by
    have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩; linarith
  have hg : AEStronglyMeasurable g μ := by
    refine (hρ.1.mul (measurable_setCKQ.add_const t).aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have := (hu x hx).ne'
    simp only [hgdef, Pi.mul_apply]
    field_simp
  set F : ℝ × ℝ → ℝ := fun p => ((if p.1 < p.2 then (1 : ℝ) else 0) * g p.1) * w p.2 with hF
  have hFm : AEStronglyMeasurable F (μ.prod μ) := by
    have h1 : Measurable fun p : ℝ × ℝ => if p.1 < p.2 then (1 : ℝ) else 0 :=
      Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const
        measurable_const
    exact (h1.aestronglyMeasurable.mul
      (hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)).mul
      (measurable_setCKdQ_div.comp measurable_snd).aestronglyMeasurable
  have hFx : ∀ x X, F (x, X) = (if x < X then g x else 0) * w X := fun x X => by
    simp only [hF]; split_ifs <;> ring
  have hsec : ∀ x ∈ Ioo (0 : ℝ) 1, Integrable (fun X => F (x, X)) μ ∧
      ∫ X, F (x, X) ∂μ = g x / (setCKQ x + t) := fun x hx => by
    simp only [hFx]
    exact setCK_section_const ht hx (g x)
  have hnorm : ∀ x ∈ Ioo (0 : ℝ) 1, ∫ X, ‖F (x, X)‖ ∂μ = |g x| / (setCKQ x + t) :=
    fun x hx => by
      have e : ∀ᵐ X ∂μ, ‖F (x, X)‖ = (if x < X then |g x| else 0) * w X := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with X hX
        rw [hFx, Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (setCKdQ_pos hX).le
          (sq_nonneg _))]
        by_cases h : x < X <;> simp [h, hwdef]
      rw [integral_congr_ae e]
      exact (setCK_section_const ht hx |g x|).2
  have H : Integrable F (μ.prod μ) := by
    rw [integrable_prod_iff hFm]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hsec x hx).1
    · refine hρ.norm.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [hnorm x hx, Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg
        (setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩) (hu x hx).le), hgdef, abs_mul,
        abs_of_nonneg (setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩)]
      ring
  have hXs : ∀ X ∈ Ioo (0 : ℝ) 1, ∫ x, F (x, X) ∂μ = setCKRhoH ρ X * w X := fun X hX => by
    simp only [hFx]
    rw [integral_mul_const]
    congr 1
    have e : (fun x => if x < X then g x else 0) = (Iio X).indicator g := by
      funext x; simp only [indicator, mem_Iio]
    rw [e, integral_indicator measurableSet_Iio, restrict_Iio_Ioo hX,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hX.1.le]
    rfl
  have hR : ∀ᵐ X ∂μ, ∫ x, F (x, X) ∂μ = setCKRhoH ρ X * w X := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with X hX
    exact hXs X hX
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
    (H.integral_prod_right.congr hR), ?_⟩
  have hswap := integral_integral_swap (f := fun x X => F (x, X)) H
  rw [setCKStieltjes, ← setIntegral_Ioo_eq_intervalIntegral,
    ← setIntegral_Ioo_eq_intervalIntegral, ← integral_congr_ae hR, ← hswap]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [(hsec x hx).2, hgdef]
  simp only
  ring

end

end QED.ChainProof.SetCK

end
