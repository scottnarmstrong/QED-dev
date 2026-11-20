/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecLin
public import QED.GradedProof.RPi4DecScal

/-!
# (R-Π₄) step L9, D1–D2: the per-flavour function with a fixed auxiliary pair

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
parts D1 and D2. Every flavour `f` of a PV-closed flavour set is replaced by the three-flavour
configuration `decCfg(M_{rep f}, M_f²)`, the measure `δ_x + (x/μ² - 2) δ_{μ²} + (1 - x/μ²) δ_{2μ²}`
(`x = M_f²`, `μ = M_{rep f}`, counterterms at `μ`), weighted by `c_f`; the auxiliary points cancel
block by block (Pauli–Villars), so the block measure is unchanged, and by linearity:

* `dec_asmPolLim_eq_sum` (**D1 + D2, generic**): `asmPolLim Φ = ∑_f c_f asmPolLim(decCfg(M_{rep f},
  M_f²))`, under `DecFaceGen`;
* `decT₀ e μ x s = asmPolLim(decCfg μ x)(s) / e⁴`, and `dec_rep_decT₀`: **`DecRep P₀ mH (decT₀ e)`**
  at the frozen flavours, under `DecFaceGen`;
* `dec_decBlock_add_affine`, `DecScalAff`, `dec_scal_of_aff`: the affine-part variant — if
  `decT₀ = decT G φ κ + α(μ, s) + β(μ, s) x` with `G`, `φ` as in `DecScal`, then `DecScal`.

What remains of L9 (step D3) is `DecScalAff`: the scaling form of `decT₀` up to an affine part.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

section Rep

/-- **The per-flavour configuration with the fixed auxiliary pair `(μ², 2μ²)`**: the flavours
`(μ, √2 μ, √x)` with coefficients `(x/μ² - 2, 1 - x/μ², 1)`, all with counterterms at the
first flavour (mass `μ`). It is the measure `δ_x + (x/μ² - 2) δ_{μ²} + (1 - x/μ²) δ_{2μ²}`. -/
noncomputable def decCfg (μ x : ℝ) : Lepton.Flavors (Fin 3) :=
  ⟨![μ, Real.sqrt 2 * μ, Real.sqrt x], ![x / μ ^ 2 - 2, 1 - x / μ ^ 2, 1], 0⟩

/-- **The per-flavour function with the fixed auxiliary pair** (step D2):
`T₀(μ, x, s) = asmPolLim(decCfg μ x)(s) / e⁴`. -/
noncomputable def decT₀ (e μ x s : ℝ) : ℂ :=
  asmPolLim (decCfg μ x) (fun _ => 0) e s / (e : ℂ) ^ 4

theorem dec_cfg_pv {μ x : ℝ} (hμ : μ ≠ 0) (hx : 0 ≤ x) :
    DecPV (decCfg μ x) (fun _ => 0) (decCfg μ x).coeff := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩ <;> obtain rfl : b = 0 := hb.symm <;>
    rw [Finset.filter_true_of_mem fun _ _ => rfl, Fin.sum_univ_three] <;>
    simp only [decCfg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  · ring
  · rw [mul_pow, h2, hx2]
    field_simp
    ring

theorem dec_cfg_mass_ge {m₀ μ x : ℝ} (hμ : m₀ ≤ μ) (hm₀ : 0 < m₀) (hx : m₀ ^ 2 ≤ x) (g : Fin 3) :
    m₀ ≤ (decCfg μ x).mass g := by
  have h2 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  fin_cases g <;> simp only [decCfg, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  · exact hμ
  · nlinarith
  · rw [← Real.sqrt_sq hm₀.le]
    exact Real.sqrt_le_sqrt hx

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- A sum of an affine function of `M_f²` (with block-dependent coefficients) vanishes on a
PV-closed flavour set. -/
theorem dec_sum_rep_affine (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (α β : F → ℂ) :
    ∑ f, (Φ.coeff f : ℂ) * (α (rep f) + β (rep f) * ((Φ.mass f ^ 2 : ℝ) : ℂ)) = 0 := by
  rw [← Finset.sum_fiberwise Finset.univ rep]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : rep b = b
  · have e1 : ∑ f ∈ Finset.univ.filter (fun f => rep f = b),
        (Φ.coeff f : ℂ) * (α (rep f) + β (rep f) * ((Φ.mass f ^ 2 : ℝ) : ℂ)) =
        α b * ((∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f : ℝ) : ℂ) +
          β b * ((∑ f ∈ Finset.univ.filter (fun f => rep f = b),
            Φ.coeff f * Φ.mass f ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f hf => ?_
      rw [(Finset.mem_filter.1 hf).2]
      ring
    rw [e1, hPV₁ b hb, hPV₂ b hb]
    simp
  · refine Finset.sum_eq_zero fun f hf => absurd ?_ hb
    rw [← (Finset.mem_filter.1 hf).2, hrep]

/-- **Every flavour replaced by its configuration**: the flavour set on `F × Fin 3` whose fibre
over `f` is `c_f · decCfg(M_{rep f}, M_f²)`, with counterterms at the first point of the fibre. -/
noncomputable def decBig : Lepton.Flavors (F × Fin 3) :=
  ⟨fun p => (decCfg (Φ.mass (rep p.1)) (Φ.mass p.1 ^ 2)).mass p.2,
    fun p => Φ.coeff p.1 * (decCfg (Φ.mass (rep p.1)) (Φ.mass p.1 ^ 2)).coeff p.2,
    (Φ.openLine, 0)⟩

/-- The counterterm flavour of `decBig`: the first point of the fibre. -/
def decBigRep : F × Fin 3 → F × Fin 3 := fun p => (p.1, 0)

/-- The PV conditions on `F × Fin 3` with `decBigRep`, fibre by fibre. -/
theorem dec_big_pv {Ψ : Lepton.Flavors (F × Fin 3)} {v : F × Fin 3 → ℝ}
    (h₁ : ∀ f, ∑ j, v (f, j) = 0) (h₂ : ∀ f, ∑ j, v (f, j) * Ψ.mass (f, j) ^ 2 = 0) :
    DecPV Ψ decBigRep v := by
  have key : ∀ (w : F × Fin 3 → ℝ) (b : F × Fin 3), decBigRep b = b →
      ∑ p ∈ Finset.univ.filter (fun p => decBigRep p = b), w p = ∑ j, w (b.1, j) := by
    intro w b hb
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b.1]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [ite_eq_left (by rw [← hb]; rfl)]
    · intro f _ hf
      refine Finset.sum_eq_zero fun j _ => ite_eq_right fun h => hf ?_
      exact congrArg Prod.fst h
    · simp
  exact ⟨fun b hb => (key v b hb).trans (h₁ b.1),
    fun b hb => (key (fun p => v p * Ψ.mass p ^ 2) b hb).trans (h₂ b.1)⟩

variable {Φ rep} {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
include hm₀ hmass hrep hPV₁ hPV₂

/-- **`decBig` has the block measure of `Φ`**: the auxiliary points of the configurations cancel
block by block (Pauli–Villars). -/
theorem dec_sameMeas_big : DecSameMeas Φ rep (decBig Φ rep) decBigRep := by
  intro g
  have hM : ∀ f, Real.sqrt (Φ.mass f ^ 2) = Φ.mass f := fun f =>
    Real.sqrt_sq (hm₀.le.trans (hmass f))
  have hμ : ∀ f, Φ.mass (rep f) ≠ 0 := fun f => (hm₀.trans_le (hmass (rep f))).ne'
  have hA := dec_sum_rep_affine Φ rep hrep hPV₁ hPV₂
    (fun b => -2 * g (Φ.mass b) (Φ.mass b))
    (fun b => g (Φ.mass b) (Φ.mass b) / ((Φ.mass b ^ 2 : ℝ) : ℂ))
  have hB := dec_sum_rep_affine Φ rep hrep hPV₁ hPV₂
    (fun b => g (Real.sqrt 2 * Φ.mass b) (Φ.mass b))
    (fun b => -g (Real.sqrt 2 * Φ.mass b) (Φ.mass b) / ((Φ.mass b ^ 2 : ℝ) : ℂ))
  rw [Fintype.sum_prod_type]
  simp only [decBig, decBigRep, decCfg, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hM]
  have e : ∀ f, ((Φ.coeff f * (Φ.mass f ^ 2 / Φ.mass (rep f) ^ 2 - 2) : ℝ) : ℂ) *
        g (Φ.mass (rep f)) (Φ.mass (rep f)) +
      ((Φ.coeff f * (1 - Φ.mass f ^ 2 / Φ.mass (rep f) ^ 2) : ℝ) : ℂ) *
        g (Real.sqrt 2 * Φ.mass (rep f)) (Φ.mass (rep f)) +
      ((Φ.coeff f * 1 : ℝ) : ℂ) * g (Φ.mass f) (Φ.mass (rep f)) =
      (Φ.coeff f : ℂ) * g (Φ.mass f) (Φ.mass (rep f)) +
      ((Φ.coeff f : ℂ) * (-2 * g (Φ.mass (rep f)) (Φ.mass (rep f)) +
          g (Φ.mass (rep f)) (Φ.mass (rep f)) / ((Φ.mass (rep f) ^ 2 : ℝ) : ℂ) *
            ((Φ.mass f ^ 2 : ℝ) : ℂ)) +
        (Φ.coeff f : ℂ) * (g (Real.sqrt 2 * Φ.mass (rep f)) (Φ.mass (rep f)) +
          -g (Real.sqrt 2 * Φ.mass (rep f)) (Φ.mass (rep f)) /
            ((Φ.mass (rep f) ^ 2 : ℝ) : ℂ) * ((Φ.mass f ^ 2 : ℝ) : ℂ))) := by
    intro f
    have h2 : ((Φ.mass (rep f) ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 (hμ f)
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl fun f _ => e f, Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB]
  simp

/-- **D1 + D2: the photon-regulator limit as a sum of per-flavour configurations** with the
fixed auxiliary pair: `asmPolLim Φ = ∑_f c_f asmPolLim(decCfg(M_{rep f}, M_f²))`, for every
PV-closed flavour set, given the generic face-limit identity. -/
theorem dec_asmPolLim_eq_sum (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e) {s : ℝ}
    (hs : -(4 * m₀ ^ 2) < s) :
    asmPolLim Φ rep P.e s = ∑ f, (Φ.coeff f : ℂ) *
      asmPolLim (decCfg (Φ.mass (rep f)) (Φ.mass f ^ 2)) (fun _ => 0) P.e s := by
  set Ψ := decBig Φ rep with hΨ
  have hμ : ∀ f, Φ.mass (rep f) ≠ 0 := fun f => (hm₀.trans_le (hmass (rep f))).ne'
  have hx : ∀ f, m₀ ^ 2 ≤ Φ.mass f ^ 2 := fun f => pow_le_pow_left₀ hm₀.le (hmass f) 2
  have hcfg : ∀ f, DecPV (decCfg (Φ.mass (rep f)) (Φ.mass f ^ 2)) (fun _ => 0)
      (decCfg (Φ.mass (rep f)) (Φ.mass f ^ 2)).coeff := fun f =>
    dec_cfg_pv (hμ f) (sq_nonneg _)
  have hΨm : ∀ p, m₀ ≤ Ψ.mass p := fun p =>
    dec_cfg_mass_ge (hmass (rep p.1)) hm₀ (hx p.1) p.2
  have hΨr : ∀ p : F × Fin 3, decBigRep (decBigRep p) = decBigRep p := fun _ => rfl
  -- the fibre coefficient vectors
  set v : F → F × Fin 3 → ℝ := fun f p => if p.1 = f then Ψ.coeff p else 0 with hv
  have hvPV : ∀ f ∈ Finset.univ, DecPV Ψ decBigRep (v f) := by
    intro f _
    refine dec_big_pv (fun f' => ?_) (fun f' => ?_)
    · by_cases h : f' = f
      · subst h
        simp only [hv, ite_true, hΨ, decBig]
        rw [← Finset.mul_sum]
        have := (hcfg f').1 0 rfl
        rw [Finset.filter_true_of_mem fun _ _ => rfl] at this
        rw [this, mul_zero]
      · simp [hv, h]
    · by_cases h : f' = f
      · subst h
        simp only [hv, ite_true, hΨ, decBig, mul_assoc]
        rw [← Finset.mul_sum]
        have := (hcfg f').2 0 rfl
        rw [Finset.filter_true_of_mem fun _ _ => rfl] at this
        rw [this, mul_zero]
      · simp [hv, h]
  have hsum : decWith Ψ (fun p => ∑ f ∈ Finset.univ, v f p) = Ψ := by
    have : (fun p => ∑ f ∈ Finset.univ, v f p) = Ψ.coeff := by
      funext p
      simp [hv]
    rw [this]
    rfl
  rw [dec_asmPolLim_congr (dec_sameMeas_big hm₀ hmass hrep hPV₁ hPV₂) P.e s, ← hΨ, ← hsum,
    dec_asmPolLim_sum hm₀ hΨm hΨr P he hF hs Finset.univ hvPV]
  refine Finset.sum_congr rfl fun f _ => ?_
  -- the fibre over `f` is `c_f · decCfg`
  have hmeas : DecSameMeas (decWith Ψ (v f)) decBigRep
      (decWith (decCfg (Φ.mass (rep f)) (Φ.mass f ^ 2))
        fun j => Φ.coeff f * (decCfg (Φ.mass (rep f)) (Φ.mass f ^ 2)).coeff j) fun _ => 0 := by
    intro g
    rw [Fintype.sum_prod_type, Finset.sum_eq_single f]
    · simp [decWith, hv, hΨ, decBig, decBigRep]
    · intro f' _ hf'
      simp [decWith, hv, hf']
    · simp
  rw [dec_asmPolLim_congr hmeas P.e s]
  exact dec_asmPolLim_smul (Φ := decCfg (Φ.mass (rep f)) (Φ.mass f ^ 2)) (rep := fun _ => 0) hm₀
    (dec_cfg_mass_ge (hmass (rep f)) hm₀ (hx f)) (fun _ => rfl) P he hF hs (hcfg f) (Φ.coeff f)

end Rep

section Frozen

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- **D2 at the frozen flavours: `DecRep` holds for the per-flavour function `decT₀` with the
fixed auxiliary pair**, given the generic face-limit identity. -/
theorem dec_rep_decT₀ (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hF : DecFaceGen P₀.e) : DecRep P₀ mH (decT₀ P₀.e) := by
  intro M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂ s hs
  have hmass : ∀ g, P₀.m ≤ (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂).mass g :=
    le_leptonFlavors_mass (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂) hM₁ hM₂
      hmH hMH₁ hMH₂
  have hPV₁ := leptonFlavors_blockPV₁ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ)
    (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₁ hcH₁
  have hPV₂ := leptonFlavors_blockPV₂ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ)
    (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₂ hcH₂
  rw [dec_asmPolLim_eq_sum hm hmass leptonRep_idem hPV₁ hPV₂ P₀ he hF hs, Finset.sum_div,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp only [Fin.sum_univ_three, decBlock, decT₀, mul_div_assoc, Finset.sum_add_distrib]
  simp [Lepton.leptonFlavors, leptonRep, Params.mass, Params.loopCoeff]

/-- `decBlock` does not see an affine function of `x = M²` added to the per-flavour function. -/
theorem dec_decBlock_add_affine {T T' : ℝ → ℝ → ℝ → ℂ} {μ M₁ M₂ c₁ c₂ s : ℝ} (α β : ℂ)
    (hc : 1 + c₁ + c₂ = 0) (hc' : μ ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0)
    (h : ∀ x : ℝ, x = μ ^ 2 ∨ x = M₁ ^ 2 ∨ x = M₂ ^ 2 → T' μ x s = T μ x s + (α + β * x)) :
    decBlock T' μ M₁ M₂ c₁ c₂ s = decBlock T μ M₁ M₂ c₁ c₂ s := by
  have hA := dec_pv_affine hc hc' α β
  simp only [decBlock]
  rw [h _ (Or.inl rfl), h _ (Or.inr (Or.inl rfl)), h _ (Or.inr (Or.inr rfl))]
  push_cast at hA ⊢
  linear_combination hA

/-- **(L9, D3 target) the affine-part variant of `DecScal`**: the per-flavour function with the
fixed auxiliary pair is of scaling form up to an affine function of `x`, with `G`, `φ` vanishing
at `0` and Lipschitz near `0`. -/
def DecScalAff (e : ℝ) : Prop :=
  ∃ (G φ : ℝ → ℂ) (κ : ℂ) (δ L : ℝ) (α β : ℝ → ℝ → ℂ), 0 < δ ∧ 0 ≤ L ∧ G 0 = 0 ∧ φ 0 = 0 ∧
    (∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖G σ - G σ'‖ ≤ L * |σ - σ'|) ∧
    (∀ σ σ' : ℝ, |σ| ≤ δ → |σ'| ≤ δ → ‖φ σ - φ σ'‖ ≤ L * |σ - σ'|) ∧
    ∀ μ x s : ℝ, 0 < μ → μ ^ 2 ≤ x → -(4 * μ ^ 2) < s →
      decT₀ e μ x s = decT G φ κ μ x s + (α μ s + β μ s * x)

/-- **`DecScalAff → DecScal`**, given the generic face-limit identity. -/
theorem dec_scal_of_aff (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hF : DecFaceGen P₀.e) (h : DecScalAff P₀.e) : DecScal P₀ mH := by
  obtain ⟨G, φ, κ, δ, L, α, β, hδ, hL, hG0, hφ0, hG, hφ, hT⟩ := h
  refine ⟨G, φ, κ, δ, L, hδ, hL, hG0, hφ0, hG, hφ, ?_⟩
  intro M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂ s hs
  rw [dec_rep_decT₀ P₀ mH he hm hmH hF M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂
    hcH₁ hcH₂ s hs]
  have hx : ∀ {μ M : ℝ}, 0 < μ → μ < M → μ ^ 2 ≤ M ^ 2 := fun hμ hM =>
    pow_le_pow_left₀ hμ.le hM.le 2
  have hblock : ∀ {μ N₁ N₂ d₁ d₂ : ℝ}, 0 < μ → μ < N₁ → μ < N₂ → 1 + d₁ + d₂ = 0 →
      μ ^ 2 + d₁ * N₁ ^ 2 + d₂ * N₂ ^ 2 = 0 → -(4 * μ ^ 2) < s →
      decBlock (decT₀ P₀.e) μ N₁ N₂ d₁ d₂ s = decBlock (decT G φ κ) μ N₁ N₂ d₁ d₂ s := by
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

end Frozen

end QED.GradedProof.RPi4

end
