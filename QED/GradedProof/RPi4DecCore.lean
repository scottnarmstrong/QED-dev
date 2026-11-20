/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4AsmCore
public import QED.GradedProof.RPi4DecDD

/-!
# (R-Π₄) step L9: decoupling from a per-flavour representation

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9. The decoupling
`AsmDecoupling` of `RPi4AsmCore` is reduced to two properties of a per-flavour function
`T μ x s` (`μ` the lepton mass of the block, `x = M²` the squared mass of the flavour, `s` the
external invariant):

* `DecRep T`: the photon-regulator limit `asmPolLim` of the frozen flavours is, block by block,
  `T μ μ² s + c₁ T μ M₁² s + c₂ T μ M₂² s` (`decBlock`);
* `DecDecay T μ`: `T μ x s` is small and Lipschitz on the scale of `x` for `x` beyond a
  threshold, uniformly for `s` in a compact interval.

Affine functions of `x` are killed by a block (`dec_pv_affine`), so the representation is only
determined up to them; `DecDecay` fixes the normalization.

* `dec_asmDecoupling_of_rep`: **`DecRep T → DecDecay T` (lepton and heavy leptons) →
  `AsmDecoupling`**, with `Π_∞(s) = T m m² s + ∑_ℓ T m_ℓ m_ℓ² s`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

section Dec

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- The value of one block with the per-flavour function `T`:
`T μ μ² s + c₁ T μ M₁² s + c₂ T μ M₂² s`. -/
def decBlock (T : ℝ → ℝ → ℝ → ℂ) (μ M₁ M₂ c₁ c₂ s : ℝ) : ℂ :=
  T μ (μ ^ 2) s + (c₁ : ℂ) * T μ (M₁ ^ 2) s + (c₂ : ℂ) * T μ (M₂ ^ 2) s

/-- **(L9, representation) the photon-regulator limit is a sum of blocks** of the per-flavour
function `T`, at every fermion-regulator point of the frozen statement and every `s > -4m²`. -/
def DecRep (T : ℝ → ℝ → ℝ → ℂ) : Prop :=
  ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ →
    1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
    ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
      (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
      (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
      ∀ s : ℝ, -(4 * P₀.m ^ 2) < s →
        asmPolLim (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e s /
            (P₀.e : ℂ) ^ 4 =
          decBlock T P₀.m M₁ M₂ c₁ c₂ s +
            ∑ ℓ, decBlock T (mH ℓ) (MH₁ ℓ) (MH₂ ℓ) (cH₁ ℓ) (cH₂ ℓ) s

/-- **(L9, decay) the per-flavour function of the lepton of mass `μ` decouples**: for `x = M²`
beyond a threshold, `T μ x s` is small and Lipschitz on the scale of `x`, uniformly for `s` in a
compact interval. -/
def DecDecay (T : ℝ → ℝ → ℝ → ℂ) (μ : ℝ) : Prop :=
  ∀ S₀ S η : ℝ, 0 < η → ∃ R : ℝ, ∀ s : ℝ, S₀ ≤ s → s ≤ S → ∀ x y : ℝ, R ≤ x → x ≤ y →
    ‖T μ x s‖ ≤ η ∧ ‖T μ y s - T μ x s‖ ≤ η * ((y - x) / x)

/-- The regulator terms of one block are bounded by `2η` beyond the threshold of `DecDecay`. -/
theorem dec_norm_decBlock_sub_le {T : ℝ → ℝ → ℝ → ℂ} {μ M₁ M₂ c₁ c₂ s R η : ℝ} (hμ : 0 < μ)
    (h₁ : μ < M₁) (h₂ : μ < M₂) (hc : 1 + c₁ + c₂ = 0) (hc' : μ ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0)
    (hR₁ : R ≤ M₁ ^ 2) (hR₂ : R ≤ M₂ ^ 2)
    (hT : ∀ x y : ℝ, R ≤ x → x ≤ y → ‖T μ x s‖ ≤ η ∧ ‖T μ y s - T μ x s‖ ≤ η * ((y - x) / x)) :
    ‖decBlock T μ M₁ M₂ c₁ c₂ s - T μ (μ ^ 2) s‖ ≤ 2 * η := by
  have e : decBlock T μ M₁ M₂ c₁ c₂ s - T μ (μ ^ 2) s =
      (c₁ : ℂ) * T μ (M₁ ^ 2) s + (c₂ : ℂ) * T μ (M₂ ^ 2) s := by
    simp only [decBlock]
    ring
  rw [e]
  exact dec_norm_pv_le (r := fun x => T μ x s) hc hc' (sq_nonneg μ)
    (pow_lt_pow_left₀ h₁ hμ.le two_ne_zero) (pow_lt_pow_left₀ h₂ hμ.le two_ne_zero) hR₁ hR₂
    (fun x hx => (hT x x hx le_rfl).1) fun x y hx hxy => (hT x y hx hxy).2

/-- A mass above `1 + |R|` has its square above `R`. -/
theorem dec_le_sq_of_lt {R A M : ℝ} (hA : 1 + |R| ≤ A) (hM : A < M) : R ≤ M ^ 2 := by
  have h1 : 1 < M := by linarith [abs_nonneg R]
  nlinarith [le_abs_self R]

/-- **L9 from the per-flavour representation and its decay**: `DecRep T` and `DecDecay T` at the
lepton and at every heavy lepton give `AsmDecoupling`, with
`Π_∞(s) = T m m² s + ∑_ℓ T m_ℓ m_ℓ² s`. -/
theorem dec_asmDecoupling_of_rep (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (T : ℝ → ℝ → ℝ → ℂ) (hrep : DecRep P₀ mH T) (hdec : DecDecay T P₀.m)
    (hdecH : ∀ ℓ, DecDecay T (mH ℓ)) : AsmDecoupling P₀ mH := by
  refine ⟨fun s => T P₀.m (P₀.m ^ 2) s + ∑ ℓ, T (mH ℓ) (mH ℓ ^ 2) s,
    fun S₀ S η hS₀ hη => ?_⟩
  set η' : ℝ := η / (4 * (n + 1)) with hη'
  have hη'0 : 0 < η' := by positivity
  obtain ⟨R₀, hR₀⟩ := hdec S₀ S η' hη'0
  choose RH hRH using fun ℓ => hdecH ℓ S₀ S η' hη'0
  set A : ℝ := 1 + |R₀| + ∑ ℓ, |RH ℓ| with hA
  have hS : 0 ≤ ∑ ℓ, |RH ℓ| := Finset.sum_nonneg fun ℓ _ => abs_nonneg _
  have hA₀ : 1 + |R₀| ≤ A := by linarith
  have hAH : ∀ ℓ, 1 + |RH ℓ| ≤ A := fun ℓ => by
    have := Finset.single_le_sum (f := fun ℓ => |RH ℓ|) (fun ℓ _ => abs_nonneg _)
      (Finset.mem_univ ℓ)
    linarith [abs_nonneg R₀]
  refine ⟨A, fun M₁ M₂ c₁ c₂ hM₁ hM₂ hR₁ hR₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hRH₁ hRH₂
    hcH₁ hcH₂ s h₀ h₁ => ?_⟩
  rw [hrep M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂ s
    (hS₀.trans_le h₀)]
  have e0 := dec_norm_decBlock_sub_le hm hM₁ hM₂ hc₁ hc₂ (dec_le_sq_of_lt hA₀ hR₁)
    (dec_le_sq_of_lt hA₀ hR₂) (hR₀ s h₀ h₁)
  have eH : ∀ ℓ, ‖decBlock T (mH ℓ) (MH₁ ℓ) (MH₂ ℓ) (cH₁ ℓ) (cH₂ ℓ) s -
      T (mH ℓ) (mH ℓ ^ 2) s‖ ≤ 2 * η' := fun ℓ =>
    dec_norm_decBlock_sub_le (hm.trans (hmH ℓ)) (hMH₁ ℓ) (hMH₂ ℓ) (hcH₁ ℓ) (hcH₂ ℓ)
      (dec_le_sq_of_lt (hAH ℓ) (hRH₁ ℓ)) (dec_le_sq_of_lt (hAH ℓ) (hRH₂ ℓ)) (hRH ℓ s h₀ h₁)
  have e : decBlock T P₀.m M₁ M₂ c₁ c₂ s +
        ∑ ℓ, decBlock T (mH ℓ) (MH₁ ℓ) (MH₂ ℓ) (cH₁ ℓ) (cH₂ ℓ) s -
      (T P₀.m (P₀.m ^ 2) s + ∑ ℓ, T (mH ℓ) (mH ℓ ^ 2) s) =
      (decBlock T P₀.m M₁ M₂ c₁ c₂ s - T P₀.m (P₀.m ^ 2) s) +
        ∑ ℓ, (decBlock T (mH ℓ) (MH₁ ℓ) (MH₂ ℓ) (cH₁ ℓ) (cH₂ ℓ) s - T (mH ℓ) (mH ℓ ^ 2) s) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [e]
  have hsum : ‖∑ ℓ, (decBlock T (mH ℓ) (MH₁ ℓ) (MH₂ ℓ) (cH₁ ℓ) (cH₂ ℓ) s -
      T (mH ℓ) (mH ℓ ^ 2) s)‖ ≤ n * (2 * η') := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun ℓ _ => eH ℓ).trans ?_
    simp
  have hfin : 2 * η' + n * (2 * η') < η := by
    have hn : (0 : ℝ) < n + 1 := by positivity
    have : 2 * η' + n * (2 * η') = η / 2 := by
      rw [hη']
      field_simp
      ring
    rw [this]
    linarith
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 2 * η' + n * (2 * η') := add_le_add e0 hsum
    _ < η := hfin

end Dec

end QED.GradedProof.RPi4

end
