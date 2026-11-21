/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceLoop0

/-!
# (R-Π₄) step L10, T2.UV: the face rate with the lower bound of `V₀` tracked

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (the rate input
(B) of `QED.GradedProof.RPi4.faceIdRay_of_size_rate`). The face rate
`QED.GradedProof.RPi4.face_rate_loop1` is uniform over a family with a common lower bound
`V₀ ≥ c₁`. Along the ray, after the dilation that makes the momenta bounded, the masses tend to
`0` and `c₁` is only a per-member bound. The bounds on the coefficients and on `vHat` do not
involve `c₁`, and the abstract `σ`-integration (`SigData.norm_sigma_face_le`) has an explicit
constant, so the face rate holds with the constant `C (1 + c₁⁻¹)^N`:

* `faceIdRayB_inv_pow_le`, `faceIdRayB_rpow_le`: `c^{-j} ≤ (1 + c⁻¹)^N` (`j ≤ N`) and
  `c^{-1/2} ≤ 1 + c⁻¹`;
* `faceIdRayB_sigData`: the `SigData` of each member, with common `BD`, `LD`, `LV`;
* `faceIdRayB_face_rate`, `faceIdRayB_face_sector_rate` (a `FaceShape` family);
* `faceIdRayB_face_rate_piece` (a sorted piece), **`faceIdRayB_face_rate_loop1`**,
  **`faceIdRayB_face_rate_loop0`** (a collapsed piece in its own line order).
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)
open QED.Integration.SimplexMerge (integral_simplex_comp_perm integrableOn_simplex_comp_perm_iff)

/-! ### Powers of the inverse lower bound -/

/-- `c^{-j} ≤ (1 + c⁻¹)^N` for `0 < c`, `j ≤ N`. -/
theorem faceIdRayB_inv_pow_le {c : ℝ} (hc : 0 < c) {j N : ℕ} (hj : j ≤ N) :
    (c ^ j)⁻¹ ≤ (1 + c⁻¹) ^ N := by
  have h1 : 1 ≤ 1 + c⁻¹ := by have := inv_pos.2 hc; linarith
  rw [← inv_pow]
  exact (pow_le_pow_left₀ (inv_pos.2 hc).le (by linarith) j).trans (pow_le_pow_right₀ h1 hj)

/-- `c^{-1/2} ≤ 1 + c⁻¹` for `0 < c`. -/
theorem faceIdRayB_rpow_le {c : ℝ} (hc : 0 < c) : c ^ (-(1 / 2) : ℝ) ≤ 1 + c⁻¹ := by
  rcases le_or_gt 1 c with h | h
  · have : c ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by norm_num)
    have := inv_pos.2 hc
    linarith
  · have e : c ^ (-(1 / 2) : ℝ) ≤ c ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hc h.le (by norm_num)
    rw [Real.rpow_neg_one] at e
    linarith

/-! ### The face rate of a family of face shapes -/

section Shape

variable {ι : Type*} {p q r : ℕ} {S : ι → FaceShape p q} {B : ι → FaceBr r} {k : Fin r → ℕ}
  {ρ₀ K KM : ℝ}

/-- **The `SigData` of each member, with common coefficient and Lipschitz constants** and the
member's own lower bound `c₁ s`. -/
theorem faceIdRayB_sigData (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hK : ∀ s, (S s).kF ≤ K)
    (hKM : ∀ s, (S s).kM ≤ KM) (hk : ∀ j, 2 ≤ k j) (hB : ∀ s, (B s).Meas)
    (hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx p q) ρ =>
      (S i.1).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2))
    (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hV : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet p ×ˢ simplexSet q,
      c₁ s ≤ symanzikV (S s).α (S s).pp (S s).M (joinZ ρ (simplexPoint x.1) (simplexPoint x.2))) :
    ∃ BD LD LV : ℝ, 0 ≤ BD ∧ 0 ≤ LD ∧ 0 ≤ LV ∧ ∀ s,
      SigData (volume.restrict (simplexSet p ×ˢ simplexSet q)) ρ₀ (c₁ s) BD LD LV
        (S s).thetaX ((S s).coefX (B s)) (S s).vX k := by
  choose Bf Lf hBL using hD
  obtain ⟨BV, LV, hBLV⟩ := FaceShape.unifLip_vHat S hK hρ₁ hKM
  have hBj : ∀ j, |Bf j| ≤ ∑ j, |Bf j| := fun j =>
    Finset.single_le_sum (f := fun j => |Bf j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hLj : ∀ j, |Lf j| ≤ ∑ j, |Lf j| := fun j =>
    Finset.single_le_sum (f := fun j => |Lf j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hm := FaceShape.measurableSet_prod (p := p) (q := q)
  refine ⟨∑ j, |Bf j|, ∑ j, |Lf j|, |LV|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, abs_nonneg _, fun s => ⟨hc₁ s, hρ₀, hρ₁.le, ?_,
    ?_, ?_, hk, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, abs_nonneg _, ?_,
    fun j => FaceShape.measurable_coefX (hB s) j, FaceShape.measurable_vX⟩⟩
  · exact ae_restrict_of_forall_mem hm fun x hx =>
      ⟨FaceShape.Wi_nonneg (⟨x, hx⟩ : FaceIdx p q) (S s).γ,
        FaceShape.Wi_le_one (⟨x, hx⟩ : FaceIdx p q) (S s).γ⟩
  · refine ae_restrict_of_forall_mem hm fun x hx j ρ hρ hρ' => ?_
    obtain ⟨h1, h2⟩ := hBL j (s, ⟨x, hx⟩) ρ hρ hρ'
    exact ⟨h1.trans ((le_abs_self _).trans (hBj j)),
      h2.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hLj j)) hρ)⟩
  · refine ae_restrict_of_forall_mem hm fun x hx ρ hρ hρ' => ⟨?_, ?_⟩
    · exact (S s).vHat_ge hρ₀ hρ₁ (hV s) ⟨x, hx⟩ hρ hρ'
    · have := (hBLV (s, ⟨x, hx⟩) ρ hρ hρ').2
      rw [← ofReal_sub, norm_real, Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hρ)
  · exact (continuous_apply (S s).γ).measurable.comp
      (continuous_simplexPoint'.measurable.comp measurable_fst)

/-- The two `σ`-constants are at most `(1 + c⁻¹)^N` times constants free of `c`. -/
theorem faceIdRayB_sigK_le {c BD LD LV : ℝ} (hc : 0 < c) (hBD : 0 ≤ BD) (hLD : 0 ≤ LD)
    (hLV : 0 ≤ LV) (k : Fin r → ℕ) :
    sigK₀ c BD k ≤ (∑ _j : Fin r, BD) * (1 + c⁻¹) ^ (∑ j, k j) ∧
      sigK₁ c BD LD LV k ≤ (∑ j, (LD + BD * k j * LV)) * (1 + c⁻¹) ^ (∑ j, k j) := by
  have hkj : ∀ j, k j ≤ ∑ j, k j := fun j =>
    Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  constructor
  · rw [sigK₀, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ hBD
    exact faceIdRayB_inv_pow_le hc ((Nat.sub_le _ _).trans (hkj j))
  · rw [sigK₁, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := faceIdRayB_inv_pow_le hc ((Nat.sub_le (k j) 2).trans (hkj j))
    have h2 := faceIdRayB_inv_pow_le hc (by have := hkj j; omega : k j + 1 - 2 ≤ ∑ j, k j)
    rw [add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hLD)
      (by
        exact mul_le_mul_of_nonneg_left h2 (by positivity))

end Shape

section ShapeRate

variable {ι : Type*} {p q r : ℕ} {S : ι → FaceShape (p + 1) q} {B : ι → FaceBr r}
  {k : Fin r → ℕ} {ρ₀ K KM : ℝ}

/-- **The face limit of a family of face shapes, with rate `C (1 + c₁⁻¹)^N u^{-1/2}`**
(photon last in the face block; `V₀ ≥ c₁ s` per member). -/
theorem faceIdRayB_face_rate (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hK : ∀ s, (S s).kF ≤ K)
    (hKM : ∀ s, (S s).kM ≤ KM) (hkc : ∀ s, (B s).k = k) (hk : ∀ j, 2 ≤ k j)
    (hB : ∀ s, (B s).Meas)
    (hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
      (S i.1).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2))
    (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hV : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet (p + 1) ×ˢ simplexSet q,
      c₁ s ≤ symanzikV (S s).α (S s).pp (S s).M (joinZ ρ (simplexPoint x.1) (simplexPoint x.2)))
    (hγ : ∀ s, (S s).γ = Fin.last (p + 1)) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ s, ∀ u : ℝ, 0 < u →
      ‖u • (∫ ρ in (0 : ℝ)..ρ₀, (S s).gJ (B s) ρ (ρ * u)) - ∫ σ in Ioi 0, (S s).gJ (B s) 0 σ‖ ≤
        C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨BD, LD, LV, hBD, hLD, hLV, hS⟩ :=
    faceIdRayB_sigData hρ₀ hρ₁ hK hKM hk hB hD c₁ hc₁ hV
  set V₀ := (volume (simplexSet q)).toReal * (volume (simplexSet p)).toReal with hV₀
  have hV₀0 : 0 ≤ V₀ := by positivity
  set K₀ := ∑ _j : Fin r, BD
  set K₁ := ∑ j, (LD + BD * k j * LV)
  have hK₀ : 0 ≤ K₀ := Finset.sum_nonneg fun _ _ => hBD
  have hK₁ : 0 ≤ K₁ := Finset.sum_nonneg fun _ _ => by positivity
  set N₀ := ∑ j, k j
  refine ⟨4 * V₀ * ((q * K₀ + K₁) * ρ₀ ^ (1 / 2 : ℝ) + K₀ * ρ₀ ^ (-(1 / 2) : ℝ)), N₀ + 1,
    fun s u hu => ?_⟩
  set c := c₁ s
  have hc := hc₁ s
  set A := (volume (simplexSet q)).toReal * ((volume (simplexSet p)).toReal *
    (2 * c ^ (-(1 / 2) : ℝ)))
  have hA : ∀ σ, 0 < σ → ∫ x in simplexSet (p + 1) ×ˢ simplexSet q,
      sigM (S s).thetaX c σ x ≤ A * σ ^ (-(3 / 2) : ℝ) := fun σ hσ => by
    have e : (S s).thetaX = fun x : (Fin (p + 1) → ℝ) × (Fin q → ℝ) =>
        simplexPoint x.1 (Fin.last (p + 1)) := by
      funext x; simp only [FaceShape.thetaX, hγ]
    rw [e]
    refine (integral_sigM_prod_le hc hσ).trans (le_of_eq ?_)
    simp only [A]; ring
  have h := (hS s).norm_sigma_face_le q hA hu
  simp only [FaceShape.gJ_eq_sigG, hkc s]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hu.le _))
  obtain ⟨e0, e1⟩ := faceIdRayB_sigK_le (r := r) hc hBD hLD hLV k
  have hW : 1 ≤ 1 + c⁻¹ := by have := inv_pos.2 hc; linarith
  have hWN : 0 ≤ (1 + c⁻¹) ^ N₀ := by positivity
  have hρa : 0 ≤ ρ₀ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hρ₀.le _
  have hρb : 0 ≤ ρ₀ ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hρ₀.le _
  have hs0 : 0 ≤ sigK₀ c BD k := (hS s).sigK₀_nonneg
  have hs1 : 0 ≤ sigK₁ c BD LD LV k := (hS s).sigK₁_nonneg
  have hA' : A ≤ 2 * V₀ * (1 + c⁻¹) := by
    have := faceIdRayB_rpow_le hc
    simp only [A, hV₀]
    have h0 : 0 ≤ (volume (simplexSet q)).toReal * (volume (simplexSet p)).toReal := by
      positivity
    nlinarith
  have hA0 : 0 ≤ A := by positivity
  have hX : (q * sigK₀ c BD k + sigK₁ c BD LD LV k) * ρ₀ ^ (1 / 2 : ℝ) +
      sigK₀ c BD k * ρ₀ ^ (-(1 / 2) : ℝ) ≤
      ((q * K₀ + K₁) * ρ₀ ^ (1 / 2 : ℝ) + K₀ * ρ₀ ^ (-(1 / 2) : ℝ)) * (1 + c⁻¹) ^ N₀ := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have f1 : q * sigK₀ c BD k ≤ q * (K₀ * (1 + c⁻¹) ^ N₀) := mul_le_mul_of_nonneg_left e0 hq
    have f2 := mul_le_mul_of_nonneg_right (add_le_add f1 e1) hρa
    have f3 := mul_le_mul_of_nonneg_right e0 hρb
    nlinarith
  have hX0 : 0 ≤ (q * sigK₀ c BD k + sigK₁ c BD LD LV k) * ρ₀ ^ (1 / 2 : ℝ) +
      sigK₀ c BD k * ρ₀ ^ (-(1 / 2) : ℝ) := by positivity
  set X := (q * K₀ + K₁) * ρ₀ ^ (1 / 2 : ℝ) + K₀ * ρ₀ ^ (-(1 / 2) : ℝ)
  calc 2 * A * ((q * sigK₀ c BD k + sigK₁ c BD LD LV k) * ρ₀ ^ (1 / 2 : ℝ) +
        sigK₀ c BD k * ρ₀ ^ (-(1 / 2) : ℝ))
      ≤ 2 * (2 * V₀ * (1 + c⁻¹)) * (X * (1 + c⁻¹) ^ N₀) :=
        mul_le_mul (by linarith) hX hX0 (by positivity)
    _ = 4 * V₀ * X * (1 + c⁻¹) ^ (N₀ + 1) := by rw [pow_succ]; ring

/-- **The face sector of the collapsed density of a family of face shapes, with rate
`C (1 + c₁⁻¹)^N u^{-1/2}`.** -/
theorem faceIdRayB_face_sector_rate (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hK : ∀ s, (S s).kF ≤ K)
    (hKM : ∀ s, (S s).kM ≤ KM) (hkc : ∀ s, (B s).k = k) (hk : ∀ j, 2 ≤ k j)
    (hB : ∀ s, (B s).Meas)
    (hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
      (S i.1).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2))
    (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hV : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet (p + 1) ×ˢ simplexSet q,
      c₁ s ≤ symanzikV (S s).α (S s).pp (S s).M (joinZ ρ (simplexPoint x.1) (simplexPoint x.2)))
    (hγ : ∀ s, (S s).γ = Fin.last (p + 1)) {n : ℕ} {Q : ι → LoopQuartic}
    (hRep : ∀ s, (B s).Rep n (p + 1) (Q s) (S s).α (S s).pp) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => (S s).fU n (Q s) u (simplexPoint x)) (simplexSet (p + 1 + 1 + q)) →
      ‖u • (∫ x in simplexSet (p + 1 + 1 + q),
          {z | FaceShape.blockSum z ≤ ρ₀}.indicator ((S s).fU n (Q s) u) (simplexPoint x)) -
        ∫ σ in Ioi 0, (S s).gJ (B s) 0 σ‖ ≤ C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨C, N, hC⟩ := faceIdRayB_face_rate hρ₀ hρ₁ hK hKM hkc hk hB hD c₁ hc₁ hV hγ
  obtain ⟨BD, LD, LV, -, -, -, hS⟩ := faceIdRayB_sigData hρ₀ hρ₁ hK hKM hk hB hD c₁ hc₁ hV
  refine ⟨C, N, fun s u hu hf => ?_⟩
  rw [(S s).integral_faceCut_eq (hRep s) hρ₀ hρ₁ hf fun ρ hρ hρ' => by
    have := (hS s).integrable_sigH hρ.le hρ' (mul_nonneg hρ.le hu.le)
    rw [← hkc s] at this
    exact this]
  exact hC s u hu

end ShapeRate

/-! ### A sorted piece -/

namespace FaceSort

variable {ι : Type*} {p q r : ℕ} {α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ}
  {e : Equiv.Perm (Fin (p + 1 + 1 + q + 1))}

/-- **The face sector of a family of pieces in their own line order, with rate
`C (1 + c₁⁻¹)^N u^{-1/2}`** (`faceIdRayB` form of `FaceSort.face_rate_piece`). -/
theorem faceIdRayB_face_rate_piece (h : FaceSort p q α e)
    (pp : ι → Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ) (M : ι → Fin (p + 1 + 1 + q + 1) → ℝ)
    (n : ℕ) (Q : ι → LoopQuartic) (B : ι → FaceBr r) (k : Fin r → ℕ) {ρ₀ K KM : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1)
    (hK : ∀ s, (h.shape (pp s) (M s)).kF ≤ K) (hKM : ∀ s, (h.shape (pp s) (M s)).kM ≤ KM)
    (hkc : ∀ s, (B s).k = k) (hk : ∀ j, 2 ≤ k j) (hB : ∀ s, (B s).Meas)
    (hD : ∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
      (h.shape (pp i.1) (M i.1)).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2))
    (hRep : ∀ s, (B s).Rep n (p + 1) (Q s) (fun i => α (e i)) (fun i => pp s (e i)))
    (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hV : ∀ s (w : Fin (p + 1 + 1 + q + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w (gam e) ≤ ρ₀ → c₁ s ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => pieceF n (Q s) α (pp s) (M s) (gam e) u (simplexPoint x))
        (simplexSet (p + 1 + 1 + q)) →
      ‖u • (∫ x in simplexSet (p + 1 + 1 + q),
          {w | faceSum α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) (gam e) u)
            (simplexPoint x)) -
        ∫ σ in Ioi 0, (h.shape (pp s) (M s)).gJ (B s) 0 σ‖ ≤
        C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  set S : ι → FaceShape (p + 1) q := fun s => h.shape (pp s) (M s) with hS
  have hVS : ∀ s ρ, 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ simplexSet (p + 1) ×ˢ simplexSet q,
      c₁ s ≤ symanzikV (S s).α (S s).pp (S s).M
        (joinZ ρ (simplexPoint x.1) (simplexPoint x.2)) := by
    intro s ρ hρ hρ' x hx
    obtain ⟨hW0, hW1⟩ := simplexPoint_mem_stdSimplex hx.1
    obtain ⟨hV0, hV1⟩ := simplexPoint_mem_stdSimplex hx.2
    set W := simplexPoint x.1
    set V := simplexPoint x.2
    set z := joinZ ρ W V with hz
    have hρ1 : ρ < 1 := hρ'.trans_lt hρ₁
    have hz0 : ∀ l, 0 ≤ z l := fun l => by
      refine Fin.addCases (m := p + 1 + 1) (n := q + 1) (fun i => ?_) (fun j => ?_) l
      · simp only [hz, joinZ, Fin.append_left, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg hρ.le (hW0 i)
      · simp only [hz, joinZ, Fin.append_right, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (by linarith) (hV0 j)
    have hz1 : ∑ l, z l = 1 := by
      rw [sum_join]
      simp only [hz, joinZ, Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul,
        ← Finset.mul_sum, hW1, hV1]
      ring
    have hU : symanzikU (S s).α z ≠ 0 := by
      rw [symanzikU, det_face ((S s).isFaceMat ρ W V)]
      have := (S s).uJ_ge ρ W V hW0 hW1 hV1 hρ.le
      exact mul_ne_zero hρ.ne' (by unfold FaceShape.uJ at this; linarith)
    have hzγ : z (S s).γJ ≤ ρ₀ := by
      rw [hz, (S s).joinZ_γJ]
      have hWγ : W (S s).γ ≤ 1 := by
        rw [← hW1]
        exact Finset.single_le_sum (fun i _ => hW0 i) (Finset.mem_univ _)
      nlinarith [hW0 (S s).γ]
    have := hV s (fun j => z (e.symm j)) (fun l => hz0 _)
      (by rw [← hz1]; exact e.symm.sum_comp z)
      (by rwa [← symanzikU_perm, ← h.shape_α (pp s) (M s)])
      (by simpa only [gam, Equiv.symm_apply_apply] using
        (show z (Fin.castAdd (q + 1) (Fin.last (p + 1))) ≤ ρ₀ from hzγ))
    rwa [← symanzikV_perm, ← h.shape_α (pp s) (M s), ← h.shape_pp (pp s) (M s),
      ← h.shape_M (pp s) (M s)] at this
  have hRep' : ∀ s, (B s).Rep n (p + 1) (Q s) (S s).α (S s).pp := fun s => by
    rw [hS]
    dsimp only
    rw [h.shape_α, h.shape_pp]
    exact hRep s
  obtain ⟨C, N, hC⟩ := faceIdRayB_face_sector_rate (S := S) hρ₀ hρ₁ hK hKM hkc hk hB hD c₁ hc₁
    hVS (fun s => rfl) hRep'
  refine ⟨C, N, fun s u hu hf => ?_⟩
  have hfU : ∀ z, (S s).fU n (Q s) u z =
      pieceF n (Q s) α (pp s) (M s) (gam e) u fun j => z (e.symm j) := fun z =>
    h.fU_eq (pp s) (M s) n (Q s) u z
  have hf' : IntegrableOn (fun x => (S s).fU n (Q s) u (simplexPoint x))
      (simplexSet (p + 1 + 1 + q)) := by
    simp only [hfU]
    exact (integrableOn_simplex_comp_perm_iff e.symm
      (pieceF n (Q s) α (pp s) (M s) (gam e) u)).mpr hf
  have hint : ∫ x in simplexSet (p + 1 + 1 + q),
      {w | faceSum α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) (gam e) u)
        (simplexPoint x) =
      ∫ x in simplexSet (p + 1 + 1 + q),
        {z | FaceShape.blockSum (p := p + 1) (q := q) z ≤ ρ₀}.indicator ((S s).fU n (Q s) u)
          (simplexPoint x) := by
    rw [← integral_simplex_comp_perm e.symm]
    refine setIntegral_congr_fun (measurableSet_simplexSet _) fun x _ => ?_
    simp only [indicator, mem_ofPred_eq, h.blockSum_eq, hfU]
    rfl
  rw [hint]
  exact hC s u hu hf'

end FaceSort

/-! ### A collapsed piece in its own line order -/

/-- **The loop-`1` face of a family of collapsed pieces, with rate `C (1 + c₁⁻¹)^N u^{-1/2}`**
(`faceIdRayB` form of `face_rate_loop1`; `V₀ ≥ c₁ s` near the face, per member). The lines are
sorted internally; the face bracket is the self-energy bracket when the
face block has two lines and the vertex bracket otherwise (three terms for `n = 7`, two for
`n = 6` with cubic numerators). -/
theorem faceIdRayB_face_rate_loop1 {ι : Type*} {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1))
    (hγ : α γ₀ = ![1, -1]) (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hA : 2 ≤ (Finset.univ.filter fun l => α l ≠ ![1, 0]).card) (hR : ∃ l, α l = ![1, 0])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ) (hd : ∀ s, LoopDegLe 1 3 (Q s))
    (hd1 : (Finset.univ.filter fun l => α l ≠ ![1, 0]).card = 2 → ∀ s, LoopDegLe 1 1 (Q s))
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP KM : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hP : ∀ s l, ‖pp s l‖ ≤ KP) (hM : ∀ s l, |M s l| ≤ KM)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w γ₀ ≤ ρ₀ → c₁ s ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => pieceF n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x))
        (simplexSet m) →
      ‖u • (∫ x in simplexSet m,
          {w | faceSum α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) γ₀ u)
            (simplexPoint x)) - L s‖ ≤ C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  classical
  set A := Finset.univ.filter fun l => α l ≠ ![1, 0] with hAdef
  have hmemA : ∀ l, l ∈ A ↔ α l ≠ ![1, 0] := fun l => by simp [hAdef]
  obtain ⟨p, hp⟩ : ∃ p, A.card = p + 1 + 1 := ⟨A.card - 2, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, Aᶜ.card = q + 1 := by
    obtain ⟨l, hl⟩ := hR
    have : 0 < Aᶜ.card := Finset.card_pos.mpr ⟨l, by simp [hAdef, hl]⟩
    exact ⟨Aᶜ.card - 1, by omega⟩
  have hm : m = p + 1 + 1 + q := by
    have := Finset.card_add_card_compl A
    simp only [Fintype.card_fin] at this
    omega
  subst hm
  have hγA : γ₀ ∈ A := (hmemA γ₀).mpr (by rw [hγ]; exact row1m1_ne)
  -- the sorting permutation
  have cA : Fintype.card {l // l ∈ A} = p + 1 + 1 := by simp [hp]
  have cR : Fintype.card {l // ¬l ∈ A} = q + 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
    have := Finset.card_add_card_compl A
    simp only [Fintype.card_fin] at this
    omega
  set e₀ : Equiv.Perm (Fin (p + 1 + 1 + q + 1)) :=
    (finSumFinEquiv (m := p + 1 + 1) (n := q + 1)).symm.trans
      (((Fintype.equivFinOfCardEq cA).symm.sumCongr (Fintype.equivFinOfCardEq cR).symm).trans
        (Equiv.sumCompl (· ∈ A))) with he₀
  have he₀F : ∀ i : Fin (p + 1 + 1), e₀ (Fin.castAdd (q + 1) i) ∈ A := fun i => by
    simp only [he₀, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact Subtype.prop _
  have he₀R : ∀ j : Fin (q + 1), e₀ (Fin.natAdd (p + 1 + 1) j) ∉ A := fun j => by
    simp only [he₀, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact ((Fintype.equivFinOfCardEq cR).symm j).2
  set l₁ := e₀ (Fin.castAdd (q + 1) (Fin.last (p + 1)))
  set e : Equiv.Perm (Fin (p + 1 + 1 + q + 1)) := e₀.trans (Equiv.swap l₁ γ₀) with he
  have hswA : ∀ x ∈ A, Equiv.swap l₁ γ₀ x ∈ A := fun x hx => by
    rw [Equiv.swap_apply_def]
    split_ifs
    · exact hγA
    · exact he₀F _
    · exact hx
  have hS : FaceSort p q α e := by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hx := (hmemA _).mp (hswA _ (he₀F i))
      rcases hrow (e (Fin.castAdd (q + 1) i)) with h1 | h1 | h1
      · exact absurd h1 hx
      · exact Or.inl h1
      · exact Or.inr h1
    · have hx := he₀R j
      have h1 : e₀ (Fin.natAdd (p + 1 + 1) j) ≠ l₁ := fun h => hx (h ▸ he₀F _)
      have h2 : e₀ (Fin.natAdd (p + 1 + 1) j) ≠ γ₀ := fun h => hx (h ▸ hγA)
      have : e (Fin.natAdd (p + 1 + 1) j) = e₀ (Fin.natAdd (p + 1 + 1) j) := by
        simp only [he, Equiv.trans_apply]
        exact Equiv.swap_apply_of_ne_of_ne h1 h2
      rw [this]
      by_contra hne
      exact hx ((hmemA _).mpr hne)
  have hgam : FaceSort.gam e = γ₀ := by
    simp only [FaceSort.gam, he, Equiv.trans_apply]
    exact Equiv.swap_apply_left _ _
  -- uniform bounds
  have hα : ∀ l s, |α l s| ≤ 1 := fun l s => by
    rcases hrow l with h1 | h1 | h1 <;> rw [h1] <;> fin_cases s <;> simp
  have hK := fun s => hS.kF_shape_le (M := M s) hα (hP s)
  have hKM := fun s => hS.kM_shape_le (pp := pp s) (hP s) (hM s)
  have hV' : ∀ s (w : Fin (p + 1 + 1 + q + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w (FaceSort.gam e) ≤ ρ₀ → c₁ s ≤ symanzikV α (pp s) (M s) w := by
    rw [hgam]; exact hV
  -- the bracket
  have fin : ∀ {r : ℕ} (B : ι → FaceBr r) (k : Fin r → ℕ), (∀ s, (B s).k = k) →
      (∀ j, 2 ≤ k j) → (∀ s, (B s).Meas) →
      (∀ j, UnifLip ρ₀ fun (i : ι × FaceIdx (p + 1) q) ρ =>
        (hS.shape (pp i.1) (M i.1)).coefJ (B i.1) j ρ (FaceShape.Wi i.2) (FaceShape.Vi i.2)) →
      (∀ s, (B s).Rep n (p + 1) (Q s) (fun i => α (e i)) (fun i => pp s (e i))) →
      ∃ C : ℝ, ∃ N : ℕ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 0 < u →
        IntegrableOn (fun x => pieceF n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x))
          (simplexSet (p + 1 + 1 + q)) →
        ‖u • (∫ x in simplexSet (p + 1 + 1 + q),
            {w | faceSum α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) γ₀ u)
              (simplexPoint x)) - L s‖ ≤ C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
    intro r B k hkc hk hB hD hRep
    obtain ⟨C, N, hC⟩ := hS.faceIdRayB_face_rate_piece pp M n Q B k hρ₀ hρ₁ hK hKM hkc hk hB hD
      hRep c₁ hc₁ hV'
    refine ⟨C, N, fun s => ∫ σ in Ioi 0, (hS.shape (pp s) (M s)).gJ (B s) 0 σ, fun s u hu hf => ?_⟩
    rw [← hgam] at hf ⊢
    exact hC s u hu hf
  set S : ι → FaceShape (p + 1) q := fun s => hS.shape (pp s) (M s)
  have hK' : ∀ s, (S s).kF ≤ 1 + 3 * (p + 1 + 1) + 4 * ((q + 1) + 2 * (p + 1 + 1)) * KP := hK
  rcases hn with rfl | ⟨rfl, hq0⟩
  · rcases Nat.eq_zero_or_pos p with rfl | hp1
    · exact fin (fun s => FaceBr.se 7 (Q s)) ![7 - 3, 7 - 4, 7 - 5] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp)
        (fun _ => FaceBr.meas_se) (FaceShape.unifLip_coefJ_se S hK' hρ₁ 7 hQ)
        (fun s => FaceBr.rep_se (hd1 (by omega) s) le_rfl)
    · exact fin (fun s => FaceBr.vtx 7 (Q s)) ![7 - 3, 7 - 4, 7 - 5] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp)
        (fun _ => FaceBr.meas_vtx) (FaceShape.unifLip_coefJ_vtx S hK' hρ₁ 7 hQ)
        (fun s => FaceBr.rep_vtx3 (hd s) (by omega))
  · rcases Nat.eq_zero_or_pos p with rfl | hp1
    · exact fin (fun s => FaceBr.se₂ 6 (Q s)) ![6 - 3, 6 - 4] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp)
        (fun _ => FaceBr.meas_se₂) (FaceShape.unifLip_coefJ_se₂ S hK' hρ₁ 6 hQ)
        (fun s => FaceBr.rep_se₂ (hd1 (by omega) s) (hq0 s) le_rfl)
    · exact fin (fun s => FaceBr.vtx₂ 6 (Q s)) ![6 - 3, 6 - 4] (fun _ => rfl)
        (fun j => by fin_cases j <;> simp)
        (fun _ => FaceBr.meas_vtx₂) (FaceShape.unifLip_coefJ_vtx₂ S hK' hρ₁ 6 hQ)
        (fun s => FaceBr.rep_vtx₂3 (hd s) (hq0 s) (by omega))

/-- **The loop-`0` face of a family of collapsed pieces, with rate `C (1 + c₁⁻¹)^N u^{-1/2}`**:
the mirror of `faceIdRayB_face_rate_loop1`, cut by `faceSum0`. -/
theorem faceIdRayB_face_rate_loop0 {ι : Type*} {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1))
    (hγ : α γ₀ = ![1, -1]) (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hA : 2 ≤ (Finset.univ.filter fun l => α l ≠ ![0, 1]).card) (hR : ∃ l, α l = ![0, 1])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ) (hd : ∀ s, LoopDegLe 0 3 (Q s))
    (hd1 : (Finset.univ.filter fun l => α l ≠ ![0, 1]).card = 2 → ∀ s, LoopDegLe 0 1 (Q s))
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP KM : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hP : ∀ s l, ‖pp s l‖ ≤ KP) (hM : ∀ s l, |M s l| ≤ KM)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w γ₀ ≤ ρ₀ → c₁ s ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun x => pieceF n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x))
        (simplexSet m) →
      ‖u • (∫ x in simplexSet m,
          {w | faceSum0 α w ≤ ρ₀}.indicator (pieceF n (Q s) α (pp s) (M s) γ₀ u)
            (simplexPoint x)) - L s‖ ≤ C * (1 + (c₁ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  have hrow' : ∀ l, swapFlip α l = ![1, 0] ∨ swapFlip α l = ![0, 1] ∨
      swapFlip α l = ![1, -1] := fun l => by
    rcases hrow l with h | h | h
    · exact Or.inr (Or.inl (swapFlip_row_10 h))
    · exact Or.inl (swapFlip_row_01 h)
    · exact Or.inr (Or.inr (swapFlip_row_1m1 h))
  obtain ⟨l, hl⟩ := hR
  obtain ⟨C, N, L, hC⟩ := faceIdRayB_face_rate_loop1 (swapFlip α) γ₀ (swapFlip_row_1m1 hγ) hrow'
    (by rw [filter_swapFlip hrow]; exact hA) ⟨l, swapFlip_row_01 hl⟩
    (fun s => flipMom (photonSign α) (pp s)) M n (fun s => swapQ (Q s)) (lqBdd_swapQ hQ)
    (fun s => loopDegLe_swapQ (hd s))
    (fun h s => loopDegLe_swapQ (hd1 (by rw [← filter_swapFlip hrow]; exact h) s))
    (by rcases hn with h | ⟨h, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, fun s => quart_swapQ (h' s)⟩)
    hρ₀ hρ₁ c₁ hc₁ (fun s => norm_flipMom_le (pp s) (hP s)) hM
    (fun s w hw hw1 hU hγw => by
      rw [symanzikV_swapFlip]
      exact hV s w hw hw1 (by rwa [symanzikU_swapFlip] at hU) hγw)
  refine ⟨C, N, L, fun s u hu hf => ?_⟩
  have e : ∀ w, pieceF n (swapQ (Q s)) (swapFlip α) (flipMom (photonSign α) (pp s)) (M s) γ₀ u w =
      pieceF n (Q s) α (pp s) (M s) γ₀ u w := fun w => pieceF_swapFlip α (pp s) (M s) w n _ γ₀ u
  have e' := funext e
  have hfs : faceSum (swapFlip α) = faceSum0 α := funext fun w => faceSum_swapFlip w hrow
  have h := hC s u hu (by simp only [e]; exact hf)
  rw [e', hfs] at h
  exact h

end QED.GradedProof.RPi4

end
