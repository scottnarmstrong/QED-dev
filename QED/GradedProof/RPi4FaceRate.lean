/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceVhat
public import QED.GradedProof.RPi4FaceMarg

/-!
# (R-Π₄) steps L6d1–L6d2: the face sector of a heavy-photon density, with rate `u^{-1/2}`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), steps L6d1–L6d2. For a
family of `FaceShape`s (indexed by the external momentum, say) with the photon last in the face
block, and face brackets with common exponents `≥ 2`, measurable and uniformly Lipschitz
coefficients, and a uniform lower bound `V₀ ≥ c₁ > 0` on the sector `0 < ρ ≤ ρ₀ < 1` (all
collected in `FamHyp`), the rescaled face functions `gJ` satisfy the hypotheses `SigData` of the
abstract `σ`-integration with common constants, so, uniformly over the family:

* **`FaceShape.face_rate`**: `‖u ∫₀^{ρ₀} gJ(ρ, ρu) dρ - ∫₀^∞ gJ(0, σ) dσ‖ ≤ C u^{-1/2}`;
* **`FaceShape.face_sector_rate`**: the same for `u` times the integral over the simplex of the
  collapsed integrand cut to `{∑_{face block} z ≤ ρ₀}` (the face sector of `pairDens`);
* `FaceShape.FamHyp`, `FaceShape.integrable_hJ`, `FaceShape.sigData`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  isCompact_simplexSet)

/-- The coefficients of a face bracket are jointly measurable. -/
def FaceBr.Meas {r : ℕ} (B : FaceBr r) : Prop :=
  ∀ j, Measurable fun y : ℝ × ℝ × ℝ × ℝ × (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
    B.C j y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2

namespace FaceShape

variable {p q r : ℕ} (S : FaceShape p q) (B : FaceBr r)

/-- The photon weight `θ = W_γ` on the product. -/
noncomputable def thetaX (x : (Fin p → ℝ) × (Fin q → ℝ)) : ℝ := simplexPoint x.1 S.γ

/-- The full coefficients on the product. -/
noncomputable def coefX (j : Fin r) (ρ : ℝ) (x : (Fin p → ℝ) × (Fin q → ℝ)) : ℂ :=
  S.coefJ B j ρ (simplexPoint x.1) (simplexPoint x.2)

/-- The rescaled `V₀` on the product. -/
noncomputable def vX (ρ : ℝ) (x : (Fin p → ℝ) × (Fin q → ℝ)) : ℝ :=
  S.vHat ρ (simplexPoint x.1) (simplexPoint x.2)

theorem gJ_eq_sigG (ρ σ : ℝ) :
    S.gJ B ρ σ = sigG (volume.restrict (simplexSet p ×ˢ simplexSet q)) q S.thetaX (S.coefX B)
      S.vX B.k ρ σ := rfl

theorem measurableSet_prod : MeasurableSet (simplexSet p ×ˢ simplexSet q) :=
  (measurableSet_simplexSet p).prod (measurableSet_simplexSet q)

instance isFiniteMeasure_prod :
    IsFiniteMeasure (volume.restrict (simplexSet p ×ˢ simplexSet q)) :=
  isFiniteMeasure_restrict.mpr
    ((isCompact_simplexSet p).prod (isCompact_simplexSet q)).measure_lt_top.ne

variable {S B}

theorem measurable_coefX (hB : B.Meas) (j : Fin r) :
    Measurable fun y : ℝ × ((Fin p → ℝ) × (Fin q → ℝ)) => S.coefX B j y.1 y.2 := by
  have h1 : Measurable fun x : Fin p → ℝ => simplexPoint x := continuous_simplexPoint'.measurable
  have h2 : Measurable fun x : Fin q → ℝ => simplexPoint x := continuous_simplexPoint'.measurable
  have hmap : Measurable fun y : ℝ × ((Fin p → ℝ) × (Fin q → ℝ)) =>
      (y.1, S.aJ y.1 (simplexPoint y.2.1) (simplexPoint y.2.2), S.b (simplexPoint y.2.1),
        S.c (simplexPoint y.2.1), S.PJ y.1 (simplexPoint y.2.1) (simplexPoint y.2.2),
        S.b₁ (simplexPoint y.2.1)) := by
    unfold aJ a0 a1 b c PJ P0 P1 b₁
    fun_prop
  have hC := (hB j).comp hmap
  unfold coefX coefJ uJ uHat aJ a0 a1 b c
  unfold aJ a0 a1 b c at hC
  exact (((by fun_prop : Measurable fun y : ℝ × ((Fin p → ℝ) × (Fin q → ℝ)) =>
    (((((∑ j, simplexPoint y.2.2 j) + y.1 * (∑ i, simplexPoint y.2.1 i * S.αF i 0 * S.αF i 0 -
      ∑ j, simplexPoint y.2.2 j)) * (∑ i, simplexPoint y.2.1 i * S.αF i 1 * S.αF i 1) -
        y.1 * (∑ i, simplexPoint y.2.1 i * S.αF i 0 * S.αF i 1) ^ 2) ^ 2 : ℝ) : ℂ))).inv).mul
    ((by fun_prop : Measurable fun y : ℝ × ((Fin p → ℝ) × (Fin q → ℝ)) =>
      (y.1 : ℂ) ^ (p - B.d)).mul hC)

theorem measurable_vX :
    Measurable fun y : ℝ × ((Fin p → ℝ) × (Fin q → ℝ)) => S.vX y.1 y.2 := by
  have h1 : Measurable fun x : Fin p → ℝ => simplexPoint x := continuous_simplexPoint'.measurable
  have h2 : Measurable fun x : Fin q → ℝ => simplexPoint x := continuous_simplexPoint'.measurable
  unfold vX vHat uJ uHat mR mF aJ a0 a1 b c PJ P0 P1 b₁ Minkowski.dot
  fun_prop

/-- The hypotheses on a family of face shapes and brackets, uniform over the family. -/
structure FamHyp {ι : Type*} (S : ι → FaceShape p q) (B : ι → FaceBr r) (k : Fin r → ℕ)
    (ρ₀ c₁ K KM : ℝ) : Prop where
  hρ₀ : 0 < ρ₀
  hρ₁ : ρ₀ < 1
  hc₁ : 0 < c₁
  hK : ∀ s, (S s).kF ≤ K
  hKM : ∀ s, (S s).kM ≤ KM
  hkc : ∀ s, (B s).k = k
  hk : ∀ j, 2 ≤ k j
  hB : ∀ s, (B s).Meas
  hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx p q) ρ =>
    (S i.1).coefJ (B i.1) j ρ (Wi i.2) (Vi i.2)
  hV : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet p ×ˢ simplexSet q,
    c₁ ≤ symanzikV (S s).α (S s).pp (S s).M (joinZ ρ (simplexPoint x.1) (simplexPoint x.2))

/-- **A family of face shapes satisfies the hypotheses of the `σ`-integration**, with constants
uniform over the family. -/
theorem sigData {ι : Type*} {S : ι → FaceShape p q} {B : ι → FaceBr r} {k : Fin r → ℕ}
    {ρ₀ c₁ K KM : ℝ} (h : FamHyp S B k ρ₀ c₁ K KM) :
    ∃ BD LD LV : ℝ, ∀ s, SigData (volume.restrict (simplexSet p ×ˢ simplexSet q)) ρ₀ c₁ BD LD LV
      (S s).thetaX ((S s).coefX (B s)) (S s).vX k := by
  choose Bf Lf hBL using h.hD
  obtain ⟨BV, LV, hBLV⟩ := unifLip_vHat S h.hK h.hρ₁ h.hKM
  have hBj : ∀ j, |Bf j| ≤ ∑ j, |Bf j| := fun j =>
    Finset.single_le_sum (f := fun j => |Bf j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hLj : ∀ j, |Lf j| ≤ ∑ j, |Lf j| := fun j =>
    Finset.single_le_sum (f := fun j => |Lf j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hm := measurableSet_prod (p := p) (q := q)
  refine ⟨∑ j, |Bf j|, ∑ j, |Lf j|, |LV|, fun s => ⟨h.hc₁, h.hρ₀, h.hρ₁.le, ?_, ?_, ?_, h.hk,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    abs_nonneg _, ?_, fun j => measurable_coefX (h.hB s) j, measurable_vX⟩⟩
  · exact ae_restrict_of_forall_mem hm fun x hx =>
      ⟨Wi_nonneg (⟨x, hx⟩ : FaceIdx p q) (S s).γ, Wi_le_one (⟨x, hx⟩ : FaceIdx p q) (S s).γ⟩
  · refine ae_restrict_of_forall_mem hm fun x hx j ρ hρ hρ' => ?_
    obtain ⟨h1, h2⟩ := hBL j (s, ⟨x, hx⟩) ρ hρ hρ'
    exact ⟨h1.trans ((le_abs_self _).trans (hBj j)),
      h2.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hLj j)) hρ)⟩
  · refine ae_restrict_of_forall_mem hm fun x hx ρ hρ hρ' => ⟨?_, ?_⟩
    · exact (S s).vHat_ge h.hρ₀ h.hρ₁ (h.hV s) ⟨x, hx⟩ hρ hρ'
    · have := (hBLV (s, ⟨x, hx⟩) ρ hρ hρ').2
      rw [← ofReal_sub, norm_real, Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hρ)
  · exact (continuous_apply (S s).γ).measurable.comp
      (continuous_simplexPoint'.measurable.comp measurable_fst)

/-- **The rescaled face integrand is integrable** on the product. -/
theorem integrable_hJ {ι : Type*} {S : ι → FaceShape p q} {B : ι → FaceBr r} {k : Fin r → ℕ}
    {ρ₀ c₁ K KM : ℝ} (h : FamHyp S B k ρ₀ c₁ K KM) (s : ι) {ρ σ : ℝ} (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ ρ₀) (hσ : 0 ≤ σ) :
    IntegrableOn (fun x : (Fin p → ℝ) × (Fin q → ℝ) =>
      (S s).hJ (B s) ρ σ (simplexPoint x.1) (simplexPoint x.2))
      (simplexSet p ×ˢ simplexSet q) := by
  obtain ⟨BD, LD, LV, hS⟩ := sigData h
  have := (hS s).integrable_sigH hρ hρ' hσ
  rw [← h.hkc s] at this
  exact this

end FaceShape

namespace FaceShape

variable {p q r : ℕ}

/-- **The face limit of a family of face shapes, with rate `u^{-1/2}` uniform over the family**
(photon last in the face block). -/
theorem face_rate {ι : Type*} {S : ι → FaceShape (p + 1) q} {B : ι → FaceBr r}
    {k : Fin r → ℕ} {ρ₀ c₁ K KM : ℝ} (h : FamHyp S B k ρ₀ c₁ K KM)
    (hγ : ∀ s, (S s).γ = Fin.last (p + 1)) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      ‖u • (∫ ρ in (0 : ℝ)..ρ₀, (S s).gJ (B s) ρ (ρ * u)) - ∫ σ in Ioi 0, (S s).gJ (B s) 0 σ‖ ≤
        C * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨BD, LD, LV, hS⟩ := sigData h
  set A := (volume (simplexSet q)).toReal * ((volume (simplexSet p)).toReal *
    (2 * c₁ ^ (-(1 / 2) : ℝ)))
  have hA : ∀ s σ, 0 < σ → ∫ x in simplexSet (p + 1) ×ˢ simplexSet q,
      sigM (S s).thetaX c₁ σ x ≤ A * σ ^ (-(3 / 2) : ℝ) := fun s σ hσ => by
    have e : (S s).thetaX = fun x : (Fin (p + 1) → ℝ) × (Fin q → ℝ) =>
        simplexPoint x.1 (Fin.last (p + 1)) := by
      funext x; simp only [thetaX, hγ]
    rw [e]
    refine (integral_sigM_prod_le h.hc₁ hσ).trans (le_of_eq ?_)
    simp only [A]; ring
  refine ⟨2 * A * ((q * sigK₀ c₁ BD k + sigK₁ c₁ BD LD LV k) * ρ₀ ^ (1 / 2 : ℝ) +
    sigK₀ c₁ BD k * ρ₀ ^ (-(1 / 2) : ℝ)), fun s u hu => ?_⟩
  have := (hS s).norm_sigma_face_le q (hA s) hu
  simp only [gJ_eq_sigG, h.hkc s]
  exact this

/-- **The face sector of the collapsed density, with rate `u^{-1/2}` uniform over the family**:
`u` times the integral of the collapsed integrand over the simplex, cut to
`{∑_{face block} z ≤ ρ₀}`, tends to the face value `∫₀^∞ gJ(0, σ) dσ` at rate `u^{-1/2}` (for
every `u` at which the integrand is integrable). -/
theorem face_sector_rate {ι : Type*} {S : ι → FaceShape (p + 1) q} {B : ι → FaceBr r}
    {k : Fin r → ℕ} {ρ₀ c₁ K KM : ℝ} (h : FamHyp S B k ρ₀ c₁ K KM)
    (hγ : ∀ s, (S s).γ = Fin.last (p + 1)) {n : ℕ} {Q : ι → LoopQuartic}
    (hRep : ∀ s, (B s).Rep n (p + 1) (Q s) (S s).α (S s).pp) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => (S s).fU n (Q s) u (simplexPoint x)) (simplexSet (p + 1 + 1 + q)) →
      ‖u • (∫ x in simplexSet (p + 1 + 1 + q),
          {z | blockSum z ≤ ρ₀}.indicator ((S s).fU n (Q s) u) (simplexPoint x)) -
        ∫ σ in Ioi 0, (S s).gJ (B s) 0 σ‖ ≤ C * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨C, hC⟩ := face_rate h hγ
  refine ⟨C, fun s u hu hf => ?_⟩
  rw [(S s).integral_faceCut_eq (hRep s) h.hρ₀ h.hρ₁ hf fun ρ hρ hρ' =>
    integrable_hJ h s hρ.le hρ' (mul_nonneg hρ.le hu.le)]
  exact hC s u hu

end FaceShape

end QED.GradedProof.RPi4

end
