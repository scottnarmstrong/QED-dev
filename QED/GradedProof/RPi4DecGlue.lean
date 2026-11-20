/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecOne
public import QED.GradedProof.RPi4DecRepCh

/-!
# (R-Π₄) step L9, D3 glue: the dilation anomaly `DecAnomT₀` with `κ = -3/(16π²)`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling).
For `Λ > 0` the per-flavour function `T = decT₀ e 1` satisfies
`T(Λx, Λs) + (x - 2) T(Λ, Λs) + (1 - x) T(2Λ, Λs) = T(x, s) + κ log Λ · decD₀ e 1 x s` with
**`κ = -3/(16π²)`** (`dec_anomT₀`). Proof, with the flavour sets on `Fin 4`
`Φ = (1, √Λ, √Λ√2, √Λ√x)` and `Ψ = (√Λ, √Λ, √Λ√2, √Λ√x)`, coefficients `(0, x - 2, 1 - x, 1)`,
counterterms at the first flavour:

* D1 (`dec_asmPolLim_eq_sum`): `asmPolLim Φ` is the left side (`e⁴` times);
* D3b (`dec_asmPolLim_sub_of_rep`): `Φ` and `Ψ` have the same measure, counterterm masses `1` and
  `√Λ`, so they differ by `i (3e²/16π²) log(1/Λ)` times the one-loop functional;
* D3a (`dec_asmPolLim_dil`, `dec_dilQ`): `Ψ` is the `√Λ`-dilation of `(1, 1, √2, √x)`, which has
  the measure and the counterterm mass of `decCfg 1 x`; the one-loop functional dilates the same
  way (`dec_projS_fLim_dil`).

Hence `dec_scalAff_of_lip`: `DecFaceGen → DecLipD → DecLipT → DecScalAff`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2

namespace QED.GradedProof.RPi4

/-- The flavour set `(1, √Λ, √Λ√2, √Λ√x)` with coefficients `(0, x - 2, 1 - x, 1)`. -/
noncomputable def decG4 (Λ x : ℝ) : Lepton.Flavors (Fin 4) :=
  ⟨![1, Real.sqrt Λ * 1, Real.sqrt Λ * Real.sqrt 2, Real.sqrt Λ * Real.sqrt x],
    ![0, x - 2, 1 - x, 1], 0⟩

/-- The flavour set `(1, 1, √2, √x)` with coefficients `(0, x - 2, 1 - x, 1)`. -/
noncomputable def decG1 (x : ℝ) : Lepton.Flavors (Fin 4) :=
  ⟨![1, 1, Real.sqrt 2, Real.sqrt x], ![0, x - 2, 1 - x, 1], 0⟩

/-- The PV conditions for a single block (all counterterms at flavour `0`). -/
theorem dec_pv_const {n : ℕ} {Φ : Lepton.Flavors (Fin (n + 1))}
    (h₁ : ∑ f, Φ.coeff f = 0) (h₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) :
    (∀ b, (fun _ => (0 : Fin (n + 1))) b = b →
      ∑ f ∈ Finset.univ.filter (fun f => (fun _ => (0 : Fin (n + 1))) f = b), Φ.coeff f = 0) ∧
    ∀ b, (fun _ => (0 : Fin (n + 1))) b = b →
      ∑ f ∈ Finset.univ.filter (fun f => (fun _ => (0 : Fin (n + 1))) f = b),
        Φ.coeff f * Φ.mass f ^ 2 = 0 := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩ <;> obtain rfl : b = 0 := hb.symm <;>
    rw [Finset.filter_true_of_mem fun _ _ => rfl]
  exacts [h₁, h₂]

theorem dec_g1_pv {x : ℝ} (hx : 0 ≤ x) :
    ∑ f, (decG1 x).coeff f = 0 ∧ ∑ f, (decG1 x).coeff f * (decG1 x).mass f ^ 2 = 0 := by
  simp only [decG1, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Real.sq_sqrt hx, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  constructor <;> ring

theorem dec_g4_pv {Λ x : ℝ} (hΛ : 0 ≤ Λ) (hx : 0 ≤ x) :
    ∑ f, (decG4 Λ x).coeff f = 0 ∧ ∑ f, (decG4 Λ x).coeff f * (decG4 Λ x).mass f ^ 2 = 0 := by
  simp only [decG4, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_pow,
    Real.sq_sqrt hx, Real.sq_sqrt hΛ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  constructor <;> ring

/-- The block of unit weight depends on the flavours only through the measure (any types). -/
theorem dec_fLim_one_congr₂ {F F' : Type} [Fintype F] [Fintype F'] [DecidableEq F]
    [DecidableEq F'] {Φ : Lepton.Flavors F} {rep : F → F} {Ψ : Lepton.Flavors F'}
    {rep' : F' → F'} (h : DecSameMeas Φ rep Ψ rep') (e : ℝ) :
    fLim Φ rep e (fun _ => 1) = fLim Ψ rep' e (fun _ => 1) := by
  unfold fLim dBlockD
  congr 1
  funext ε k i j
  congr 1
  funext q
  have := h fun x _ => (((1 : ℝ) * x : ℝ) : ℂ) * dBubbleW e x ε k q i j
  simpa only [mul_assoc] using this

/-- **The dilation anomaly with `κ = -3/(16π²)`.** -/
theorem dec_anomT₀ (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e) :
    DecAnomT₀ P.e ((-3 / (16 * Real.pi ^ 2) : ℝ) : ℂ) := by
  intro Λ x s hΛ hx hs hΛs
  have hΛx : 0 < Λ * x := mul_pos hΛ hx
  set m := min 1 (min (Λ * x) Λ) with hm
  have hm0 : 0 < m := lt_min one_pos (lt_min hΛx hΛ)
  have hreg : -(4 * m) < Λ * s := by
    have hsx : -(4 * x) < s := lt_of_le_of_lt (by nlinarith [min_le_right 1 x]) hs
    have : -(4 * (Λ * x)) < Λ * s := by nlinarith
    have h' : -(4 * min 1 Λ) < Λ * s := hΛs
    rcases min_choice 1 (min (Λ * x) Λ) with h | h <;> rw [hm, h]
    · have := min_le_left 1 Λ; linarith
    · rcases min_choice (Λ * x) Λ with h'' | h'' <;> rw [h''] <;> nlinarith [min_le_right 1 Λ]
  -- the common lower bound of the masses
  set m₀ := Real.sqrt m with hm₀d
  have hm₀ : 0 < m₀ := Real.sqrt_pos.2 hm0
  have hm₀2 : m₀ ^ 2 = m := Real.sq_sqrt hm0.le
  have hreg' : -(4 * m₀ ^ 2) < Λ * s := by rwa [hm₀2]
  have hreg0 : -(4 * m₀ ^ 2) < 0 := by nlinarith
  have hsΛ : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hΛ.le
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq2 : 1 ≤ Real.sqrt 2 := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
  have hl : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ
  have b1 : m₀ ≤ 1 := by
    calc m₀ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (min_le_left _ _)
      _ = 1 := Real.sqrt_one
  have bΛ : m₀ ≤ Real.sqrt Λ :=
    Real.sqrt_le_sqrt ((min_le_right _ _).trans (min_le_right _ _))
  have bΛx : m₀ ≤ Real.sqrt Λ * Real.sqrt x := by
    rw [← Real.sqrt_mul hΛ.le]
    exact Real.sqrt_le_sqrt ((min_le_right _ _).trans (min_le_left _ _))
  have bΛ2 : m₀ ≤ Real.sqrt Λ * Real.sqrt 2 :=
    bΛ.trans (le_mul_of_one_le_right hl.le hsq2)
  have hmΦ : ∀ g, m₀ ≤ (decG4 Λ x).mass g := by
    intro g
    fin_cases g <;> simp only [decG4, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, mul_one]
    exacts [b1, bΛ, bΛ2, bΛx]
  have hmΨ : ∀ g, m₀ ≤ (decDil (Real.sqrt Λ) (decG1 x)).mass g := by
    intro g
    fin_cases g <;> simp only [decDil, decG1, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, mul_one]
    exacts [bΛ, bΛ, bΛ2, bΛx]
  have pvΦ := dec_g4_pv hΛ.le hx.le
  have pvΦ' := dec_pv_const pvΦ.1 pvΦ.2
  have pv1 := dec_g1_pv hx.le
  have pvΨ' := dec_pv_const (Φ := decDil (Real.sqrt Λ) (decG1 x)) pv1.1 (by
    have h := pv1.2
    simp only [decDil, mul_pow, hsΛ]
    rw [show (∑ f, (decG1 x).coeff f * (Λ * (decG1 x).mass f ^ 2)) =
      Λ * ∑ f, (decG1 x).coeff f * (decG1 x).mass f ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, h, mul_zero])
  have hrep : ∀ f : Fin 4, (fun _ => (0 : Fin 4)) ((fun _ => (0 : Fin 4)) f) =
      (fun _ => (0 : Fin 4)) f := fun _ => rfl
  -- the same measure
  have hw : DecSameMass (decG4 Λ x) (decDil (Real.sqrt Λ) (decG1 x)) := by
    intro g
    simp only [decG4, decDil, decG1, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, mul_one]
    push_cast
    ring
  -- D1
  have E1 : asmPolLim (decG4 Λ x) (fun _ => 0) P.e (Λ * s) =
      ((x - 2 : ℝ) : ℂ) * asmPolLim (decCfg 1 Λ) (fun _ => 0) P.e (Λ * s) +
        ((1 - x : ℝ) : ℂ) * asmPolLim (decCfg 1 (2 * Λ)) (fun _ => 0) P.e (Λ * s) +
        asmPolLim (decCfg 1 (Λ * x)) (fun _ => 0) P.e (Λ * s) := by
    rw [dec_asmPolLim_eq_sum hm₀ hmΦ hrep pvΦ'.1 pvΦ'.2 P he hF hreg']
    simp only [Fin.sum_univ_four, decG4, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_one,
      mul_pow, hsΛ, hsx, hs2, ofReal_zero, zero_mul, zero_add, mul_comm Λ 2]
    push_cast
    ring
  -- D3b
  have E2 := dec_asmPolLim_sub_of_rep hm₀ hmΦ hrep pvΦ'.1 pvΦ'.2 hmΨ hrep pvΨ'.1 pvΨ'.2 hw P he
    hF one_pos hl (μ := 1) (μ' := Real.sqrt Λ) (fun _ => rfl)
    (fun _ => by simp [decDil, decG1]) hreg'
  -- D3a
  have hx1 : 0 < min 1 x := lt_min one_pos hx
  have hm1 : 0 < Real.sqrt (min 1 x) := Real.sqrt_pos.2 hx1
  have hm1' : Real.sqrt (min 1 x) ^ 2 = min 1 x := Real.sq_sqrt hx1.le
  have b1' : Real.sqrt (min 1 x) ≤ 1 := by
    calc Real.sqrt (min 1 x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (min_le_left _ _)
      _ = 1 := Real.sqrt_one
  have bx' : Real.sqrt (min 1 x) ≤ Real.sqrt x := Real.sqrt_le_sqrt (min_le_right _ _)
  have hm1Φ : ∀ g, Real.sqrt (min 1 x) ≤ (decG1 x).mass g := by
    intro g
    fin_cases g <;> simp only [decG1, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    exacts [b1', b1', b1'.trans hsq2, bx']
  have pv1' := dec_pv_const (Φ := decG1 x) pv1.1 pv1.2
  have hs1 : -(4 * Real.sqrt (min 1 x) ^ 2) < s := by rwa [hm1']
  have E3 := dec_asmPolLim_dil hm1 hm1Φ hrep pv1'.1 pv1'.2 P he (dec_dilQ P he) hF hl hs1
  rw [hsΛ] at E3
  have hmeas : DecSameMeas (decG1 x) (fun _ => 0) (decCfg 1 x) (fun _ => 0) := by
    intro g
    simp only [decG1, decCfg, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, one_pow, div_one, mul_one]
    push_cast
    ring
  rw [dec_asmPolLim_congr hmeas] at E3
  -- the one-loop functional
  have V1 := vpf_dBlockD (decG1 x) (fun _ => 0) hm1 hm1Φ hrep pv1'.1 pv1'.2 P he (fun _ => 1)
  have hT1 : 0 < Real.sqrt (min 1 x) + Real.sqrt (min 1 x) := by positivity
  have dil : ∀ t : ℝ, -(4 * min 1 x) < t →
      projS (fLim (decG4 Λ x) (fun _ => 0) P.e fun _ => 1) (Λ * t) =
        projS (fLim (decCfg 1 x) (fun _ => 0) P.e fun _ => 1) t := by
    intro t ht
    have h := dec_projS_fLim_dil (decG1 x) (fun _ => 0) P.e (fun _ => 1) V1 hT1 hl (s := t)
      (by rw [← two_mul, mul_pow, hm1']; linarith)
    rw [hsΛ] at h
    rw [dec_fLim_one_congr (repΦ := fun _ => 0) (repΨ := fun _ => 0) hw,
      ← dec_fLim_one_congr₂ hmeas, h]
  have d1 := dil s hs
  have d0 := dil 0 (by linarith)
  rw [mul_zero] at d0
  rw [E1, E3, d1, d0] at E2
  simp only [decT₀, decD₀]
  have hlog : Real.log (1 ^ 2 / Real.sqrt Λ ^ 2) = -Real.log Λ := by
    rw [one_pow, hsΛ, one_div, Real.log_inv]
  rw [hlog] at E2
  have he' : (P.e : ℂ) ≠ 0 := by exact_mod_cast he
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  generalize asmPolLim (decCfg 1 (2 * Λ)) (fun _ => 0) P.e (Λ * s) = A₂ at E2 ⊢
  push_cast at E2 ⊢
  field_simp at E2 ⊢
  linear_combination E2

/-- **`DecScalAff` modulo `DecFaceGen` and the two Lipschitz inputs.** -/
theorem dec_scalAff_of_lip (P : Params) (he : P.e ≠ 0) (hF : DecFaceGen P.e)
    (hDl : DecLipD P.e) (hTl : DecLipT P.e) : DecScalAff P.e :=
  dec_scalAff_of _ (dec_scaleT₀_of_faceGen P he hF) (dec_anomT₀ P he hF) (dec_dil_decD₀ P he)
    hDl hTl

end QED.GradedProof.RPi4

end
