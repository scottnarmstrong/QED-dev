/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCtJet
public import QED.TwoLoop.UnitSCCtTraceOut
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The second-order coefficient of the `δ₂, δ_m` class on the outgoing line

The analogue of `QED/TwoLoop/UnitSCCtJet.lean` for the class `kindsD2Out`: the jets of the three
coefficients of `QED/TwoLoop/UnitSCCtTraceOut.lean` along the curve, at `m = e = 1`, and the
pointwise identity `d2Pointwise_Out` (the same second-order coefficient `ctPoint` as the
incoming class, with `ξ = (z₀ + z₁ + z₂)/X₁`).
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

namespace QED.TwoLoop.UnitSCCt

open QED.Dirac QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace
open QED.TwoLoop.UnitSCGraph QED.TwoLoop.UnitLGraphTrace.Pl
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.ChengWu (openSimplex)
open QED.Integration.TwoLoop (castLoopMatrix symanzikV symanzikU symanzikMatrix)

/-! ### The jets of the slot numerators -/

theorem jet_eoOut {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasPJ (fun u => eoOut P z u) (ecJ 1 (-(ctSigOut z : ℂ) + (1 - (ctZetaOut z : ℂ)))
      (1 - (ctZetaOut z : ℂ))) :=
  (jet_ePl_slot hm P.m (-ctSigOut z) (1 - ctZetaOut z)).of_eq (fun _ => rfl)
    (by rw [hm]; push_cast; rfl) (by push_cast; rfl) (by push_cast; rfl)

theorem jet_eiOut {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasPJ (fun u => eiOut P z u) (ecJ 1 ((1 - (ctSigOut z : ℂ)) + -(ctZetaOut z : ℂ))
      (-(ctZetaOut z : ℂ))) :=
  (jet_ePl_slot hm P.m (1 - ctSigOut z) (-ctZetaOut z)).of_eq (fun _ => rfl)
    (by rw [hm]; push_cast; rfl) (by push_cast; rfl) (by push_cast; rfl)

theorem jet_ecOut {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) (c : ℝ) :
    HasPJ (fun u => ecOut P z u c) (ecJ c (-(ctSigOut z : ℂ) + (1 - (ctZetaOut z : ℂ)))
      (1 - (ctZetaOut z : ℂ))) :=
  (jet_ePl_slot hm c (-ctSigOut z) (1 - ctZetaOut z)).of_eq (fun _ => rfl)
    (by push_cast; rfl) (by push_cast; rfl) (by push_cast; rfl)

/-! ### The second-order coefficients of the patterns -/

section Values

variable (ζ σ d₂ dm : ℂ)

/-- The counterterm slot jet of the outgoing class. -/
abbrev ecoJ (c : ℂ) : PJ := ecJ c (-σ + (1 - ζ)) (1 - ζ)

/-- The jet combination of `T₁` (outgoing class), at the selector `sel`. -/
def t1OutJ (sel : PJ → ℂ) : ℂ :=
  -(d₂ + dm) * pwJk sel qJ0.gam qJ1.gam rJ.gamT (((eoJ ζ σ).mul (ecoJ ζ σ 0)).mul (eoJ ζ σ))
      (eiJ ζ σ) +
    dm * pwJk sel qJ0.gam qJ1.gam rJ.gamT (((eoJ ζ σ).mul (ecoJ ζ σ 1)).mul (eoJ ζ σ)) (eiJ ζ σ)

theorem t1OutJ_s0 : t1OutJ ζ σ d₂ dm PJ.s0 = 0 := by
  simp [t1OutJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, ecJ, qJ0, qJ1, rJ, g0, g1]

theorem t1OutJ_s1 : t1OutJ ζ σ d₂ dm PJ.s1 = 0 := by
  simp [t1OutJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, ecJ, qJ0, qJ1, rJ, g0, g1]

theorem t1OutJ_s2 : t1OutJ ζ σ d₂ dm PJ.s2 =
    256 * (ζ + σ) ^ 2 * (ζ + σ - 1) * (d₂ * (ζ + σ - 1) - dm) := by
  simp [t1OutJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, ecJ, qJ0, qJ1, rJ, g0, g1]
  ring

/-- The jet combination of one counterterm slot of `T₂` (outgoing class). -/
def t2OutJc (sel : PJ → ℂ) (c : ℂ) : ℂ :=
  -4 * pwJk sel qJ0.gam qJ1.gam rJ.gamT (eoJ ζ σ) (eiJ ζ σ) +
    pwJk sel qJ0.gam qJ1.gam rJ.gamT (ecoJ ζ σ c).gam (eiJ ζ σ) +
    pwJk sel qJ0.gam.gam qJ1.gam.gam rJ.gamT.gamT ((ecoJ ζ σ c).mul (eoJ ζ σ)) (PJ.c 1) +
    -4 * pwJk sel qJ0.gam qJ1.gam rJ.gamT (eoJ ζ σ) (eiJ ζ σ) +
    pwJk sel (qJ0.gam.mul (eoJ ζ σ)).gam (qJ1.gam.mul (eoJ ζ σ)).gam
      (rJ.gamT.mul (eoJ ζ σ).bar).gamT (eoJ ζ σ) (PJ.c 1) +
    2 * pwJk sel qJ0.gam qJ1.gam rJ.gamT ((eoJ ζ σ).mul (ecoJ ζ σ c)) (PJ.c 1)

/-- The jet combination of `T₂` (outgoing class). -/
def t2OutJ (sel : PJ → ℂ) : ℂ := -(d₂ + dm) * t2OutJc ζ σ sel 0 + dm * t2OutJc ζ σ sel 1

theorem t2OutJ_s0 : t2OutJ ζ σ d₂ dm PJ.s0 = 0 := by
  simp [t2OutJ, t2OutJc, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, ecJ, qJ0, qJ1, rJ,
    g0, g1]

theorem t2OutJ_s1 : t2OutJ ζ σ d₂ dm PJ.s1 = 0 := by
  simp [t2OutJ, t2OutJc, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, ecJ, qJ0, qJ1, rJ,
    g0, g1]

theorem t2OutJ_s2 : t2OutJ ζ σ d₂ dm PJ.s2 =
    -512 * (ζ + σ - 1) * (4 * d₂ * (ζ + σ) + 2 * d₂ - 3 * dm) := by
  simp [t2OutJ, t2OutJc, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, ecJ, qJ0, qJ1, rJ,
    g0, g1]
  ring

end Values

/-! ### The jets of the three coefficients, outgoing class -/

theorem jet_ecOut_zero {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasPJ (fun u => ecOut P z u (ctCm P 0)) (ecoJ (ctZetaOut z : ℂ) (ctSigOut z : ℂ) 0) :=
  (jet_ecOut hm z 0).of_eq (fun _ => rfl) (by simp [ecJ]) rfl rfl

theorem jet_ecOut_one {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasPJ (fun u => ecOut P z u (ctCm P 1)) (ecoJ (ctZetaOut z : ℂ) (ctSigOut z : ℂ) 1) :=
  (jet_ecOut hm z P.m).of_eq (fun _ => rfl) (by simp [ecJ, hm]) rfl rfl

section JetsOut

variable {P : Params} (hm : P.m = 1) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0) (hX2 : ctX2 z ≠ 0)
include hm hX1 hX2

/-- **The jet of `T₁` of the outgoing class.** -/
theorem hasJet2_ctT1Out :
    HasJet2 (ctT1Out P z) 0 0 (ctK P * ((symanzikU (ctAlpha kindsD2Out) z ^ 2 : ℝ) : ℂ)⁻¹ * 6 *
      t1OutJ (ctZetaOut z : ℂ) (ctSigOut z : ℂ) (P.δ₂ : ℂ) (P.δm : ℂ) PJ.s2) := by
  have hq0 := HasPJ.gam (x := qJ0) (jet_lQ0 hm)
  have hq1 := HasPJ.gam (x := qJ1) (jet_lQ1 hm)
  have hr := HasPJ.gamT (x := rJ) (jet_lR hm)
  have h0 := hasJet2_pwPl hq0 hq1 hr
    (((jet_eoOut hm z).mul (jet_ecOut_zero hm z)).mul (jet_eoOut hm z)) (jet_eiOut hm z)
  have h1 := hasJet2_pwPl hq0 hq1 hr
    (((jet_eoOut hm z).mul (jet_ecOut_one hm z)).mul (jet_eoOut hm z)) (jet_eiOut hm z)
  set W := ctK P * ((symanzikU (ctAlpha kindsD2Out) z ^ 2 : ℝ) : ℂ)⁻¹
  have h := ((h0.const_mul 6).const_mul (W * ctCf P 0)).add
    ((h1.const_mul 6).const_mul (W * ctCf P 1))
  refine h.of_eq (fun u => ?_) ?_ ?_ ?_
  · rw [ctT1Out_planar P hX1 hX2, Fin.sum_univ_two]
    ring
  · have e := t1OutJ_s0 (ctZetaOut z : ℂ) (ctSigOut z : ℂ) (P.δ₂ : ℂ) (P.δm : ℂ)
    simp only [t1OutJ] at e
    simp only [ctCf, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (W * 6) * e
  · have e := t1OutJ_s1 (ctZetaOut z : ℂ) (ctSigOut z : ℂ) (P.δ₂ : ℂ) (P.δm : ℂ)
    simp only [t1OutJ] at e
    simp only [ctCf, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (W * 6) * e
  · simp only [t1OutJ, ctCf, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- **The jet of `T₂` of the outgoing class.** -/
theorem hasJet2_ctT2Out :
    HasJet2 (ctT2Out P z) 0 0 (ctK P * ((symanzikU (ctAlpha kindsD2Out) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (((symanzikMatrix (ctAlpha kindsD2Out) z)⁻¹ 0 0 : ℝ) : ℂ) *
        t2OutJ (ctZetaOut z : ℂ) (ctSigOut z : ℂ) (P.δ₂ : ℂ) (P.δm : ℂ) PJ.s2) := by
  have hq0 := HasPJ.gam (x := qJ0) (jet_lQ0 hm)
  have hq1 := HasPJ.gam (x := qJ1) (jet_lQ1 hm)
  have hr := HasPJ.gamT (x := rJ) (jet_lR hm)
  have ho := jet_eoOut hm z
  have hi := jet_eiOut hm z
  have g4 := hasJet2_pwPl hq0 hq1 hr ho hi
  have g5 := hasJet2_pwPl (hq0.mul ho).gam (hq1.mul ho).gam (hr.mul ho.bar).gamT ho
    (HasPJ.const 1)
  have hc : ∀ (cc : ℂ) (j : Fin 2) (hcj : HasPJ (fun u => ecOut P z u (ctCm P j))
      (ecoJ (ctZetaOut z : ℂ) (ctSigOut z : ℂ) cc)), HasJet2
      (fun u => -4 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (eoOut P z u)
              (eiOut P z u) +
            pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u))
              (gam (ecOut P z u (ctCm P j))) (eiOut P z u) +
            pwPl (gam (gam (lQ0 P u))) (gam (gam (lQ1 P u))) (gamT (gamT (lR P u)))
              (ecOut P z u (ctCm P j) * eoOut P z u) 1 +
            -4 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (eoOut P z u)
              (eiOut P z u) +
            pwPl (gam (gam (lQ0 P u) * eoOut P z u)) (gam (gam (lQ1 P u) * eoOut P z u))
              (gamT (gamT (lR P u) * bar (eoOut P z u))) (eoOut P z u) 1 +
            2 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u))
              (eoOut P z u * ecOut P z u (ctCm P j)) 1)
      (t2OutJc (ctZetaOut z : ℂ) (ctSigOut z : ℂ) PJ.s0 cc)
      (t2OutJc (ctZetaOut z : ℂ) (ctSigOut z : ℂ) PJ.s1 cc)
      (t2OutJc (ctZetaOut z : ℂ) (ctSigOut z : ℂ) PJ.s2 cc) := fun cc j hcj => by
    have g2 := hasJet2_pwPl hq0 hq1 hr hcj.gam hi
    have g3 := hasJet2_pwPl hq0.gam hq1.gam hr.gamT (hcj.mul ho) (HasPJ.const 1)
    have g6 := hasJet2_pwPl hq0 hq1 hr (ho.mul hcj) (HasPJ.const 1)
    exact (((((g4.const_mul (-4)).add g2).add g3).add (g4.const_mul (-4))).add g5).add
      (g6.const_mul 2)
  have h0 := hc 0 0 (jet_ecOut_zero hm z)
  have h1 := hc 1 1 (jet_ecOut_one hm z)
  set W := ctK P * ((symanzikU (ctAlpha kindsD2Out) z ^ 2 : ℝ) : ℂ)⁻¹ *
    (((symanzikMatrix (ctAlpha kindsD2Out) z)⁻¹ 0 0 : ℝ) : ℂ)
  have h := (h0.const_mul (W * ctCf P 0)).add (h1.const_mul (W * ctCf P 1))
  refine h.of_eq (fun u => ?_) ?_ ?_ ?_
  · rw [ctT2Out_planar P hX1 hX2, Fin.sum_univ_two]
    simp only [W]
    ring
  · have e := t2OutJ_s0 (ctZetaOut z : ℂ) (ctSigOut z : ℂ) (P.δ₂ : ℂ) (P.δm : ℂ)
    simp only [t2OutJ] at e
    simp only [ctCf, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination W * e
  · have e := t2OutJ_s1 (ctZetaOut z : ℂ) (ctSigOut z : ℂ) (P.δ₂ : ℂ) (P.δm : ℂ)
    simp only [t2OutJ] at e
    simp only [ctCf, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination W * e
  · simp only [t2OutJ, ctCf, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

omit hX1 hX2 in
/-- **The jet of `T₃` of the outgoing class vanishes.** -/
theorem hasJet2_ctT3Out : HasJet2 (ctT3Out P z) 0 0 0 := by
  have hq0 := HasPJ.gam (x := qJ0) (jet_lQ0 hm)
  have hq1 := HasPJ.gam (x := qJ1) (jet_lQ1 hm)
  have hr := HasPJ.gamT (x := rJ) (jet_lR hm)
  have g := hasJet2_pwPl hq0 hq1 hr (HasPJ.const 1) (HasPJ.const 1)
  set W := ((symanzikU (ctAlpha kindsD2Out) z ^ 2 : ℝ) : ℂ)⁻¹ *
    (1 / 4 * ((((symanzikMatrix (ctAlpha kindsD2Out) z)⁻¹ 0 0 : ℝ) : ℂ) ^ 2 * (-12)))
  have h := (g.const_mul (ctK P * ctCf P 0 * W)).add (g.const_mul (ctK P * ctCf P 1 * W))
  refine h.of_eq (fun u => ?_) ?_ ?_ ?_
  · rw [ctT3Out_planar, Fin.sum_univ_two]
    simp only [W]
    ring
  · rw [pwJk_T3 PJ.s0 (Or.inl rfl)]; ring
  · rw [pwJk_T3 PJ.s1 (Or.inr (Or.inl rfl))]; ring
  · rw [show pwJ qJ0.gam qJ1.gam rJ.gamT (PJ.c 1) (PJ.c 1) = 0 from
      pwJk_T3 PJ.s2 (Or.inr (Or.inr rfl))]
    ring

end JetsOut

/-- **The pointwise identity, outgoing class** (`m = e = 1`). -/
theorem d2Pointwise_Out {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    D2Pointwise P kindsD2Out fun p' μ k => numD2Out P p' (restMomentum P.m) μ k := by
  intro x hx
  set z := simplexPoint x
  have hz := simplexPoint_pos_of_mem_openSimplex' hx
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
  have h4 := hz 4; have h5 := hz 5; have h6 := hz 6; have h7 := hz 7
  have hX1 : ctX1 z ≠ 0 := by unfold ctX1; positivity
  have hX2 : ctX2 z ≠ 0 := by unfold ctX2; positivity
  have hV := tendsto_symanzikV_kinds P hm kindsD2Out (Or.inr rfl) hX1 hX2
  have hJ := ((hasJet2_ctT1Out hm hX1 hX2).add
    (hasJet2_mul_tendsto (hasJet2_ctT2Out hm hX1 hX2) hV)).add
    (hasJet2_mul_tendsto (hasJet2_ctT3Out hm (z := z)) (hV.pow 2))
  have hJ' := hJ.of_eq (fun u => kindsNum_d2Out_eq_T P x u) (show (0 : ℂ) + 0 + 0 = 0 by ring)
    (show (0 : ℂ) + 0 + 0 = 0 by ring) rfl
  rw [hJ'.secondCoeff_eq, t1OutJ_s2, t2OutJ_s2, ctK_eq he,
    symanzikU_kinds kindsD2Out (Or.inr rfl),
    inv_symanzikMatrix_kinds_zero kindsD2Out (Or.inr rfl) hX2]
  have hξ : ((ctZetaOut z : ℝ) : ℂ) + ((ctSigOut z : ℝ) : ℂ) = ((ctE z / ctX1 z : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add]
    congr 1
    unfold ctZetaOut ctSigOut ctE
    ring
  rw [hξ]
  unfold ctPoint ctA ctB
  have hX1' : ((ctX1 z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX1
  have hX2' : ((ctX2 z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX2
  push_cast
  field_simp
  ring

end QED.TwoLoop.UnitSCCt

end
