/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSProfile
public import QED.GradedProof.RPi4AsmCore
public import QED.GradedProof.RPi4DecRep
public import QED.GradedProof.RPi4MajGlue

/-!
# R-KS: the R-Π₄ limit `Π_∞` is the Källén–Sabry function (reduction)

Helper level for the identification (R-KS) needed by set (a): the regulator limit `Π_∞` of the
frozen goal (R-Π₄) `QED.Graded.vacuumPolarizationPart_two_lepton_limit` is existential; set (a)
needs `Π_∞(s) = Π̂⁽⁴⁾(s/m²)/(16π⁴)` with `QED.Chain.piHat4` the Källén–Sabry function of the value
side, at `s ≥ 0`.

The frozen anchor (still a draft) is not imported. `RPi4Body P₀ mH Pinf C` is the text of its
conclusion after `∃ (Pinf : ℝ → ℂ) (C : ℝ),`, verbatim, so that a consumer holding
`⟨Pinf, C, h⟩` from (R-Π₄) applies the results below to `h` directly.

Main results:

* `pinf_eq_of_decRep` (any `n = 0` flavour data): if `Π_∞` satisfies `RPi4Body`, the face-limit
  identity `AsmFaceIds` holds (R-Π₄ input L6d3), and the photon-regulator limit `asmPolLim` is the
  block sum of a per-flavour function `T` (`DecRep`) that decouples (`DecDecay`), then
  `Π_∞(s) = T(m, m², s)` for every `s > -4m²`. This is uniqueness of the limit: `Π_∞` is pinned by
  the body itself, whatever produced it.
* `decRep_ksG_of_scal`: the open input `SetAKSScal e` (the per-flavour scaling form of R-Π₄ step
  L9 with the profile `G` identified as Källén–Sabry) gives `DecRep` of `decT ksG φ κ`.
* `setAKS_pinf_eq`: **(R-KS), conditional**: `DecFaceGen e` (an open R-Π₄ input) and
  `SetAKSScal e` give `Π_∞(s) = ksPinf m s = Π̂⁽⁴⁾(s/m²)/(16π⁴)` for every `s > -4m²`, for every
  `Π_∞` satisfying the R-Π₄ body at `n = 0`.
* `setAKS_pinf_eq_of_nonneg`: the same at `s ≥ 0`, the range that set (a) consumes.

What remains is `SetAKSScal e`: the computation of the model's renormalized two-loop vacuum
polarization at fixed fermion regulators (photon regulators removed).
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded QED.GradedProof.RPi4

namespace QED.ChainProof.SetAKS

/-- **The body of (R-Π₄)** for a given limit function `Pinf` and majorant constant `C`: the text
of the conclusion of `QED.Graded.vacuumPolarizationPart_two_lepton_limit` after
`∃ (Pinf : ℝ → ℂ) (C : ℝ),`, verbatim. -/
def RPi4Body {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ) (Pinf : ℝ → ℂ) (C : ℝ) : Prop :=
  ∀ S₀ S η : ℝ, -(4 * P₀.m ^ 2) < S₀ → 0 < η →
      ∃ RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
        1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
        ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
          (∀ ℓ, RM < MH₁ ℓ) → (∀ ℓ, RM < MH₂ ℓ) → (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
          (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
        ∃ δ > 0, ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → 0 < Λ → mγ < δ → R < Λ →
          (∃ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
            IsRenormalizedThrough
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D leptonRep 2) ∧
          ∀ D : Counterterms (Fin 3 ⊕ Fin n × Fin 3),
            IsRenormalizedThrough
              { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
              (Lepton.leptonFlavors
                { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D leptonRep 2 →
            (∃ Pol : ℝ → ℂ, ∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) ∧
            ∀ Pol : ℝ → ℂ, (∀ k : Fin 4 → ℝ, -(4 * P₀.m ^ 2) < Minkowski.dot k k →
              ∀ μ ν : Fin 4, Tendsto (fun ε : ℝ => vacuumPolarizationPart
                  { P₀ with
                    M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ, ε := ε }
                  (Lepton.leptonFlavors
                    { P₀ with M₁ := M₁, M₂ := M₂, c₁ := c₁, c₂ := c₂, mγ := mγ, Λ := Λ }
                    fun ℓ => ⟨mH ℓ, MH₁ ℓ, MH₂ ℓ, cH₁ ℓ, cH₂ ℓ⟩) D 2 k μ ν) (𝓝[>] 0)
                (𝓝 (Pol (Minkowski.dot k k) *
                  ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) →
              (∀ s : ℝ, S₀ ≤ s → s ≤ S → ‖Pol s / (P₀.e : ℂ) ^ 4 - Pinf s‖ < η) ∧
              ∀ s : ℝ, 0 ≤ s →
                ‖Pol s / (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2

/-- The Pauli–Villars coefficients of a regulator pair `M₁ ≠ M₂` at the mass `m`. -/
noncomputable def pvC₁ (m M₁ M₂ : ℝ) : ℝ := (M₂ ^ 2 - m ^ 2) / (M₁ ^ 2 - M₂ ^ 2)

theorem pvC_sum (m M₁ M₂ : ℝ) : 1 + pvC₁ m M₁ M₂ + (-1 - pvC₁ m M₁ M₂) = 0 := by ring

theorem pvC_mass {m M₁ M₂ : ℝ} (h : M₁ ^ 2 - M₂ ^ 2 ≠ 0) :
    m ^ 2 + pvC₁ m M₁ M₂ * M₁ ^ 2 + (-1 - pvC₁ m M₁ M₂) * M₂ ^ 2 = 0 := by
  have e : pvC₁ m M₁ M₂ * (M₁ ^ 2 - M₂ ^ 2) = M₂ ^ 2 - m ^ 2 := by
    rw [pvC₁, div_mul_cancel₀ _ h]
  linear_combination e

section Ident

variable (P₀ : Params) (mH : Fin 0 → ℝ)

/-- **Uniqueness of the limit against a per-flavour representation** (`n = 0`): if `Pinf`
satisfies the body of (R-Π₄), the face-limit identity holds, and the photon-regulator limit is the
block sum of a per-flavour function `T` that decouples, then `Pinf s = T(m, m², s)` on the whole
region `s > -4m²`. -/
theorem pinf_eq_of_decRep (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hId : AsmFaceIds P₀ mH)
    {T : ℝ → ℝ → ℝ → ℂ} (hrep : DecRep P₀ mH T) (hdec : DecDecay T P₀.m)
    {Pinf : ℝ → ℂ} {C : ℝ} (hB : RPi4Body P₀ mH Pinf C) {s : ℝ} (hs : -(4 * P₀.m ^ 2) < s) :
    Pinf s = T P₀.m (P₀.m ^ 2) s := by
  have hz : ∀ ℓ : Fin 0, False := fun ℓ => ℓ.elim0
  refine eq_of_forall_dist_le fun ε hε => ?_
  set η : ℝ := ε / 4 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨RM, hRM⟩ := hB s s η hs hη0
  obtain ⟨R, hR⟩ := hdec s s η hη0
  -- the fermion regulators
  set M₁ : ℝ := |RM| + |R| + P₀.m + 1 with hM₁d
  set M₂ : ℝ := M₁ + 1 with hM₂d
  have hRM0 := le_abs_self RM
  have hR0 := le_abs_self R
  have hRa := abs_nonneg RM
  have hRb := abs_nonneg R
  have hM₁ : P₀.m < M₁ := by linarith
  have hM₂ : P₀.m < M₂ := by linarith
  have hRM₁ : RM < M₁ := by linarith
  have hRM₂ : RM < M₂ := by linarith
  have hM₁1 : 1 ≤ M₁ := by linarith
  have hR₁ : R ≤ M₁ ^ 2 := by nlinarith
  have hR₂ : R ≤ M₂ ^ 2 := by nlinarith
  have hne : M₁ ^ 2 - M₂ ^ 2 ≠ 0 := by nlinarith
  set c₁ : ℝ := pvC₁ P₀.m M₁ M₂
  have hc₁ := pvC_sum P₀.m M₁ M₂
  have hc₂ := pvC_mass (m := P₀.m) hne
  obtain ⟨δ, hδ, R', hR'⟩ := hRM M₁ M₂ c₁ (-1 - c₁) hM₁ hM₂ hRM₁ hRM₂ hc₁ hc₂ mH mH mH mH
    (fun ℓ => (hz ℓ).elim) (fun ℓ => (hz ℓ).elim) (fun ℓ => (hz ℓ).elim)
    (fun ℓ => (hz ℓ).elim) (fun ℓ => (hz ℓ).elim) (fun ℓ => (hz ℓ).elim)
  -- L8 at these regulators
  set Φ := asmΦ P₀ mH M₁ M₂ c₁ (-1 - c₁) mH mH mH mH with hΦ
  have hmH : ∀ ℓ, P₀.m < mH ℓ := fun ℓ => (hz ℓ).elim
  have hmass : ∀ g, P₀.m ≤ Φ.mass g :=
    le_leptonFlavors_mass (regP P₀ M₁ M₂ c₁ (-1 - c₁) P₀.mγ P₀.Λ) (heavyH mH mH mH mH mH) hM₁
      hM₂ hmH (fun ℓ => (hz ℓ).elim) (fun ℓ => (hz ℓ).elim)
  have hPV₁ := leptonFlavors_blockPV₁ (regP P₀ M₁ M₂ c₁ (-1 - c₁) P₀.mγ P₀.Λ)
    (heavyH mH mH mH mH mH) hc₁ (fun ℓ => (hz ℓ).elim)
  have hPV₂ := leptonFlavors_blockPV₂ (regP P₀ M₁ M₂ c₁ (-1 - c₁) P₀.mγ P₀.Λ)
    (heavyH mH mH mH mH mH) hc₂ (fun ℓ => (hz ℓ).elim)
  have h00 : -(4 * P₀.m ^ 2) < 0 := by nlinarith
  obtain ⟨C₈, hC₈⟩ := asm_exists_norm_sub_polLim_le Φ leptonRep P₀ hm hmass leptonRep_idem
    hPV₁ hPV₂ he hs fun s' h₀ h₁ =>
      hId M₁ M₂ c₁ (-1 - c₁) hM₁ hM₂ hc₁ hc₂ mH mH mH mH (fun ℓ => (hz ℓ).elim)
        (fun ℓ => (hz ℓ).elim) (fun ℓ => (hz ℓ).elim) (fun ℓ => (hz ℓ).elim) _ s'
        (by linarith [abs_nonneg (max s 0)]) ((lt_min hs h00).trans_le h₀)
        (h₁.trans_lt (asm_max_lt_two_mul_sq s))
  -- the photon regulators
  have he4 : 0 < |P₀.e| ^ 4 := by positivity
  set r : ℝ := η * |P₀.e| ^ 4 / (2 * (|C₈| + 1)) with hr
  have hr0 : 0 < r := by positivity
  set mγ : ℝ := min (δ / 2) (min 1 ((r / 2) ^ 2)) with hmγd
  set Λ : ℝ := max (|R'| + 1) (max 1 (2 / r)) with hΛd
  have hmγ : 0 < mγ := lt_min (by positivity) (lt_min one_pos (by positivity))
  have hmγδ : mγ < δ := (min_le_left _ _).trans_lt (by linarith)
  have hmγ1 : mγ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hmγr : mγ ≤ (r / 2) ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hΛ1 : 1 ≤ Λ := (le_max_left _ _).trans (le_max_right _ _)
  have hΛ0 : 0 < Λ := one_pos.trans_le hΛ1
  have hRΛ : R' < Λ := by
    have := le_abs_self R'
    have : |R'| + 1 ≤ Λ := le_max_left _ _
    linarith
  have hΛr : 2 / r ≤ Λ := (le_max_right _ _).trans (le_max_right _ _)
  have hsq : Real.sqrt mγ ≤ r / 2 := by
    rw [show r / 2 = Real.sqrt ((r / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hmγr
  have hinv : Λ⁻¹ ≤ r / 2 := by
    rw [inv_le_comm₀ hΛ0 (by positivity), inv_div]
    exact hΛr
  obtain ⟨⟨D, hD⟩, hall⟩ := hR' mγ Λ hmγ hΛ0 hmγδ hRΛ
  obtain ⟨⟨Pol, hPol⟩, hPolAll⟩ := hall D hD
  have hb := (hPolAll Pol hPol).1 s le_rfl le_rfl
  have hmass' : ∀ g, P₀.m ≤ (Lepton.leptonFlavors (regP P₀ M₁ M₂ c₁ (-1 - c₁) mγ Λ)
      (heavyH mH mH mH mH mH)).mass g := hmass
  have hpol : Pol s = qPair Φ leptonRep P₀.e mγ Λ s - qPair Φ leptonRep P₀.e mγ Λ 0 :=
    pol_eq_qPair_sub _ leptonRep hm hmass' leptonRep_idem hPV₁ hPV₂
      (regP P₀ M₁ M₂ c₁ (-1 - c₁) mγ Λ) D he hmγ hΛ0 hD hPol hs
  have e8 := hC₈ s le_rfl le_rfl mγ Λ hmγ hmγ1 hΛ1
  have h8 : ‖(qPair Φ leptonRep P₀.e mγ Λ s - qPair Φ leptonRep P₀.e mγ Λ 0 -
      asmPolLim Φ leptonRep P₀.e s) / (P₀.e : ℂ) ^ 4‖ ≤ η := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ he4]
    have hsum0 : 0 ≤ Real.sqrt mγ + Λ⁻¹ := by positivity
    have hC : |C₈| * r ≤ η * |P₀.e| ^ 4 / 2 := by
      rw [hr, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      have h1 : 0 ≤ η * |P₀.e| ^ 4 := by positivity
      nlinarith [abs_nonneg C₈]
    calc _ ≤ C₈ * (Real.sqrt mγ + Λ⁻¹) := e8
      _ ≤ |C₈| * (Real.sqrt mγ + Λ⁻¹) := mul_le_mul_of_nonneg_right (le_abs_self _) hsum0
      _ ≤ |C₈| * r := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ ≤ η * |P₀.e| ^ 4 := by linarith [mul_pos hη0 he4]
  -- the decoupling of the block
  have hrep' := hrep M₁ M₂ c₁ (-1 - c₁) hM₁ hM₂ hc₁ hc₂ mH mH mH mH (fun ℓ => (hz ℓ).elim)
    (fun ℓ => (hz ℓ).elim) (fun ℓ => (hz ℓ).elim) (fun ℓ => (hz ℓ).elim) s hs
  rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hrep'
  have h9 := dec_norm_decBlock_sub_le hm hM₁ hM₂ hc₁ hc₂ hR₁ hR₂
    (fun x y hx hxy => hR s le_rfl le_rfl x y hx hxy)
  have hsplit : Pinf s - T P₀.m (P₀.m ^ 2) s =
      -(Pol s / (P₀.e : ℂ) ^ 4 - Pinf s) +
        (qPair Φ leptonRep P₀.e mγ Λ s - qPair Φ leptonRep P₀.e mγ Λ 0 -
          asmPolLim Φ leptonRep P₀.e s) / (P₀.e : ℂ) ^ 4 +
        (decBlock T P₀.m M₁ M₂ c₁ (-1 - c₁) s - T P₀.m (P₀.m ^ 2) s) := by
    rw [← hrep', hpol]
    ring
  rw [dist_eq_norm, hsplit]
  calc _ ≤ ‖-(Pol s / (P₀.e : ℂ) ^ 4 - Pinf s)‖ +
        ‖(qPair Φ leptonRep P₀.e mγ Λ s - qPair Φ leptonRep P₀.e mγ Λ 0 -
          asmPolLim Φ leptonRep P₀.e s) / (P₀.e : ℂ) ^ 4‖ +
        ‖decBlock T P₀.m M₁ M₂ c₁ (-1 - c₁) s - T P₀.m (P₀.m ^ 2) s‖ :=
        norm_add₃_le
    _ ≤ η + η + 2 * η := by
        rw [norm_neg]
        exact add_le_add (add_le_add hb.le h8) h9
    _ = ε := by rw [hη]; ring

end Ident

/-- **The open analytic input of (R-KS)**: the per-flavour photon-regulator limit `decT₀` of
R-Π₄ step L9 has the scaling form `DecScalAff` with the profile `G` equal to the Källén–Sabry
profile `ksG`: `decT₀ e μ x s = ksG(s/x) + κ log(x/μ²) φ(s/x) + α(μ,s) + β(μ,s) x`, with a
mismatch profile `φ` vanishing at `0` and Lipschitz near `0`. -/
def SetAKSScal (e : ℝ) : Prop :=
  ∃ (φ : ℝ → ℂ) (κ : ℂ) (δ L : ℝ) (α β : ℝ → ℝ → ℂ), 0 < δ ∧ 0 ≤ L ∧ φ 0 = 0 ∧
    (∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖φ σ - φ σ'‖ ≤ L * |σ - σ'|) ∧
    ∀ μ x s : ℝ, 0 < μ → μ ^ 2 ≤ x → -(4 * μ ^ 2) < s →
      decT₀ e μ x s = decT ksG φ κ μ x s + (α μ s + β μ s * x)

/-- `SetAKSScal` is `DecScalAff` with the profile fixed. -/
theorem decScalAff_of_setAKSScal {e : ℝ} (h : SetAKSScal e) : DecScalAff e := by
  obtain ⟨φ, κ, δ, L, α, β, hδ, hL, hφ0, hφ, hT⟩ := h
  refine ⟨ksG, φ, κ, min δ 1, max L ksGLip, α, β, lt_min hδ one_pos,
    hL.trans (le_max_left _ _), ksG_zero, hφ0, fun σ σ' h h' => ?_, fun σ σ' h h' => ?_, hT⟩
  · exact (norm_ksG_sub_le (h.trans (min_le_right _ _)) (h'.trans (min_le_right _ _))).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
  · exact (hφ σ σ' (h.trans (min_le_left _ _)) (h'.trans (min_le_left _ _))).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

theorem decT_ksG_diag (φ : ℝ → ℂ) (κ : ℂ) {μ : ℝ} (hμ : μ ≠ 0) (s : ℝ) :
    decT ksG φ κ μ (μ ^ 2) s = ksPinf μ s := by
  simp [decT, ksPinf, div_self (pow_ne_zero 2 hμ)]

section Rep

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- **`SetAKSScal` gives the block representation** of the photon-regulator limit by the
Källén–Sabry scaling form, given the generic face-limit identity (an open R-Π₄ input). -/
theorem decRep_ksG_of_scal (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hF : DecFaceGen P₀.e) {φ : ℝ → ℂ} {κ : ℂ} {α β : ℝ → ℝ → ℂ}
    (hT : ∀ μ x s : ℝ, 0 < μ → μ ^ 2 ≤ x → -(4 * μ ^ 2) < s →
      decT₀ P₀.e μ x s = decT ksG φ κ μ x s + (α μ s + β μ s * x)) :
    DecRep P₀ mH (decT ksG φ κ) := by
  intro M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂ s hs
  rw [dec_rep_decT₀ P₀ mH he hm hmH hF M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂
    hcH₁ hcH₂ s hs]
  have hx : ∀ {μ M : ℝ}, 0 < μ → μ < M → μ ^ 2 ≤ M ^ 2 := fun hμ hM =>
    pow_le_pow_left₀ hμ.le hM.le 2
  have hblock : ∀ {μ N₁ N₂ d₁ d₂ : ℝ}, 0 < μ → μ < N₁ → μ < N₂ → 1 + d₁ + d₂ = 0 →
      μ ^ 2 + d₁ * N₁ ^ 2 + d₂ * N₂ ^ 2 = 0 → -(4 * μ ^ 2) < s →
      decBlock (decT₀ P₀.e) μ N₁ N₂ d₁ d₂ s = decBlock (decT ksG φ κ) μ N₁ N₂ d₁ d₂ s := by
    intro μ N₁ N₂ d₁ d₂ hμ h₁ h₂ hd hd' hsμ
    refine dec_decBlock_add_affine (α μ s) (β μ s) hd hd' fun x hx' => ?_
    refine hT μ x s hμ ?_ hsμ
    rcases hx' with rfl | rfl | rfl
    · exact le_rfl
    · exact hx hμ h₁
    · exact hx hμ h₂
  rw [hblock hm hM₁ hM₂ hc₁ hc₂ hs]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => hblock (hm.trans (hmH ℓ)) (hMH₁ ℓ) (hMH₂ ℓ) (hcH₁ ℓ)
    (hcH₂ ℓ) ?_
  have h1 := hmH ℓ
  nlinarith

end Rep

/-- **(R-KS), conditional on the open inputs `DecFaceGen` (R-Π₄) and `SetAKSScal`**: every
limit function `Pinf` of the (R-Π₄) body at `n = 0` is the Källén–Sabry function,
`Pinf s = Π̂⁽⁴⁾(s/m²)/(16π⁴)`, on the whole region `s > -4m²`. -/
theorem setAKS_pinf_eq (P₀ : Params) (mH : Fin 0 → ℝ) (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hF : DecFaceGen P₀.e) (hKS : SetAKSScal P₀.e) {Pinf : ℝ → ℂ} {C : ℝ}
    (hB : RPi4Body P₀ mH Pinf C) {s : ℝ} (hs : -(4 * P₀.m ^ 2) < s) :
    Pinf s = ksPinf P₀.m s := by
  obtain ⟨φ, κ, δ, L, α, β, hδ, hL, hφ0, hφ, hT⟩ := hKS
  have hmH : ∀ ℓ, P₀.m < mH ℓ := fun ℓ => ℓ.elim0
  rw [pinf_eq_of_decRep P₀ mH he hm (maj_asmFaceIds_of_decFaceGen P₀ mH hm hmH hF)
    (decRep_ksG_of_scal P₀ mH he hm hmH hF hT) (decDecay_decT_ksG hδ hL hφ0 hφ hm) hB hs,
    decT_ksG_diag φ κ hm.ne']

/-- **(R-KS) on the spacelike range `s ≥ 0`** that set (a) consumes. -/
theorem setAKS_pinf_eq_of_nonneg (P₀ : Params) (mH : Fin 0 → ℝ) (he : P₀.e ≠ 0)
    (hm : 0 < P₀.m) (hF : DecFaceGen P₀.e) (hKS : SetAKSScal P₀.e) {Pinf : ℝ → ℂ} {C : ℝ}
    (hB : RPi4Body P₀ mH Pinf C) {s : ℝ} (hs : 0 ≤ s) :
    Pinf s = ((QED.Chain.piHat4 (s / P₀.m ^ 2) / (16 * Real.pi ^ 4) : ℝ) : ℂ) :=
  setAKS_pinf_eq P₀ mH he hm hF hKS hB (by nlinarith)

end QED.ChainProof.SetAKS

end
