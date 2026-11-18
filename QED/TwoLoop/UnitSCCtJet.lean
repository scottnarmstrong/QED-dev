/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCtAssembly
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The second-order coefficient of the `δ₂, δ_m` class on the incoming line

Section 5.2 of `docs/TWO-LOOP-UNITS.md`, the `δ₂, δ_m` half of the unit `S`, jet stage. From the
planar forms of `QED/TwoLoop/UnitSCCtTrace.lean`, the second-order jets along the curve `p'(u)`
(`QED/TwoLoop/UnitLGraphTraceJet.lean`, `QED.TwoLoop.UnitSCGraph.hasJet2_pwPl`), at `m = e = 1`:

* `hasJet2_ctT1In`: `T₁ = -(Λ² - m_γ²)/16 · 6 A(ξ)/(X₁X₂)² · u² + o(u²)`;
* `hasJet2_ctT2In`: `T₂ = -(Λ² - m_γ²)/16 · B(ξ)/(X₁ (X₁X₂)²) · u² + o(u²)`;
* `hasJet2_ctT3In`: `T₃ = o(u²)`;

with `ξ = e/X₁` and `A`, `B` of `QED.TwoLoop.UnitSCCt.ctA`, `ctB`. Hence the pointwise identity
`d2Pointwise_In`: on the open simplex, `c₂[kindsNum] = ctPoint`, the hypothesis `D2Pointwise` of
`QED/TwoLoop/UnitSCCtAssembly.lean` for the incoming class.
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
open QED.Integration.TwoLoop (castLoopMatrix symanzikV symanzikU symanzikMatrix symanzikVector)

/-! ### The jets of the slot numerators -/

/-- The jet of `(c, a + b p'⁰, -b p'¹, 0)`, with `α = a + b`, `β = b`. -/
def ecJ (c α β : ℂ) : PJ := ⟨⟨c, α, 0, 0⟩, ⟨0, 0, -2 * β, 0⟩, ⟨0, 2 * β, 0, 0⟩⟩

/-- **The jet of a slot numerator** `ePl c (a p + b p'(u))` at `m = 1`. -/
theorem jet_ePl_slot {P : Params} (hm : P.m = 1) (c a b : ℝ) :
    HasPJ (fun u => ePl c (fun μ => a * restMomentum P.m μ + b * curveMomentum P.m u μ))
      (ecJ c ((a : ℂ) + b) b) :=
  (HasPlJet.mk (HasJet2.const (c : ℂ)) ((HasJet2.const (a : ℂ)).add
    (jet_P0.const_mul (b : ℂ))) (jet_P1.const_mul (b : ℂ)).neg (HasJet2.const 0)).of_eq
    (fun u => by ext <;> simp [ePl, hm, restMomentum])
    (by ext <;> simp [ecJ]) (by ext <;> simp [ecJ, mul_comm]) (by ext <;> simp [ecJ, mul_comm])

theorem jet_eoIn {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasPJ (fun u => eoIn P z u) (ecJ 1 (-(ctSigIn z : ℂ) + (1 - (ctZetaIn z : ℂ)))
      (1 - (ctZetaIn z : ℂ))) :=
  (jet_ePl_slot hm P.m (-ctSigIn z) (1 - ctZetaIn z)).of_eq (fun _ => rfl)
    (by rw [hm]; push_cast; rfl) (by push_cast; rfl) (by push_cast; rfl)

theorem jet_eiIn {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasPJ (fun u => eiIn P z u) (ecJ 1 ((1 - (ctSigIn z : ℂ)) + -(ctZetaIn z : ℂ))
      (-(ctZetaIn z : ℂ))) :=
  (jet_ePl_slot hm P.m (1 - ctSigIn z) (-ctZetaIn z)).of_eq (fun _ => rfl)
    (by rw [hm]; push_cast; rfl) (by push_cast; rfl) (by push_cast; rfl)

theorem jet_ecIn {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) (c : ℝ) :
    HasPJ (fun u => ecIn P z u c) (ecJ c ((1 - (ctSigIn z : ℂ)) + -(ctZetaIn z : ℂ))
      (-(ctZetaIn z : ℂ))) :=
  (jet_ePl_slot hm c (1 - ctSigIn z) (-ctZetaIn z)).of_eq (fun _ => rfl)
    (by push_cast; rfl) (by push_cast; rfl) (by push_cast; rfl)

/-! ### The second-order coefficients of the patterns -/

section Values

variable (ζ σ d₂ dm : ℂ)

/-- The slot jets of the incoming class. -/
abbrev eoJ : PJ := ecJ 1 (-σ + (1 - ζ)) (1 - ζ)
/-- The slot jets of the incoming class. -/
abbrev eiJ : PJ := ecJ 1 ((1 - σ) + -ζ) (-ζ)
/-- The slot jets of the incoming class. -/
abbrev ecJc (c : ℂ) : PJ := ecJ c ((1 - σ) + -ζ) (-ζ)

/-- The jet combination of `T₁` (incoming class), at the selector `sel`. -/
def t1InJ (sel : PJ → ℂ) : ℂ :=
  -(d₂ + dm) * pwJk sel qJ0.gam qJ1.gam rJ.gamT (eoJ ζ σ)
      (((eiJ ζ σ).mul (ecJc ζ σ 0)).mul (eiJ ζ σ)) +
    dm * pwJk sel qJ0.gam qJ1.gam rJ.gamT (eoJ ζ σ) (((eiJ ζ σ).mul (ecJc ζ σ 1)).mul (eiJ ζ σ))

theorem t1InJ_s0 : t1InJ ζ σ d₂ dm PJ.s0 = 0 := by
  simp [t1InJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, ecJ, qJ0, qJ1, rJ, g0, g1]

theorem t1InJ_s1 : t1InJ ζ σ d₂ dm PJ.s1 = 0 := by
  simp [t1InJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, ecJ, qJ0, qJ1, rJ, g0, g1]

theorem t1InJ_s2 : t1InJ ζ σ d₂ dm PJ.s2 =
    256 * (ζ + σ) ^ 2 * (ζ + σ - 1) * (d₂ * (ζ + σ - 1) - dm) := by
  simp [t1InJ, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, ecJ, qJ0, qJ1, rJ, g0, g1]
  ring

/-- The jet combination of one counterterm slot of `T₂` (incoming class). -/
def t2InJc (sel : PJ → ℂ) (c : ℂ) : ℂ :=
  2 * pwJk sel qJ0.gam qJ1.gam rJ.gamT (PJ.c 1) ((ecJc ζ σ c).mul (eiJ ζ σ)) +
    pwJk sel ((eiJ ζ σ).mul qJ0.gam).gam ((eiJ ζ σ).mul qJ1.gam).gam
      ((eiJ ζ σ).mul rJ.gamT).gamT (PJ.c 1) (eiJ ζ σ) +
    pwJk sel qJ0.gam.gam qJ1.gam.gam rJ.gamT.gamT (PJ.c 1) ((eiJ ζ σ).mul (ecJc ζ σ c)) +
    -4 * pwJk sel qJ0.gam qJ1.gam rJ.gamT (eoJ ζ σ) (eiJ ζ σ) +
    pwJk sel qJ0.gam qJ1.gam rJ.gamT (eoJ ζ σ) (ecJc ζ σ c).gam +
    -4 * pwJk sel qJ0.gam qJ1.gam rJ.gamT (eoJ ζ σ) (eiJ ζ σ)

/-- The jet combination of `T₂` (incoming class). -/
def t2InJ (sel : PJ → ℂ) : ℂ := -(d₂ + dm) * t2InJc ζ σ sel 0 + dm * t2InJc ζ σ sel 1

theorem t2InJ_s0 : t2InJ ζ σ d₂ dm PJ.s0 = 0 := by
  simp [t2InJ, t2InJc, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, ecJ, qJ0, qJ1, rJ, g0,
    g1]

theorem t2InJ_s1 : t2InJ ζ σ d₂ dm PJ.s1 = 0 := by
  simp [t2InJ, t2InJc, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, ecJ, qJ0, qJ1, rJ, g0,
    g1]

theorem t2InJ_s2 : t2InJ ζ σ d₂ dm PJ.s2 =
    -512 * (ζ + σ - 1) * (4 * d₂ * (ζ + σ) + 2 * d₂ - 3 * dm) := by
  simp [t2InJ, t2InJc, pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, ecJ, qJ0, qJ1, rJ, g0,
    g1]
  ring

theorem pwJk_T3 (sel : PJ → ℂ) (hsel : sel = PJ.s0 ∨ sel = PJ.s1 ∨ sel = PJ.s2) :
    pwJk sel qJ0.gam qJ1.gam rJ.gamT (PJ.c 1) (PJ.c 1) = 0 := by
  rcases hsel with rfl | rfl | rfl
  · simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, qJ0, qJ1, rJ, g0, g1]
  · simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, qJ0, qJ1, rJ, g0, g1]
  · simp [pwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, qJ0, qJ1, rJ, g0, g1]
    norm_num

end Values

/-! ### The jets of the three coefficients, incoming class -/

theorem jet_ecIn_zero {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasPJ (fun u => ecIn P z u (ctCm P 0)) (ecJc (ctZetaIn z : ℂ) (ctSigIn z : ℂ) 0) :=
  (jet_ecIn hm z 0).of_eq (fun _ => rfl) (by simp [ecJ]) rfl rfl

theorem jet_ecIn_one {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) :
    HasPJ (fun u => ecIn P z u (ctCm P 1)) (ecJc (ctZetaIn z : ℂ) (ctSigIn z : ℂ) 1) :=
  (jet_ecIn hm z P.m).of_eq (fun _ => rfl) (by simp [ecJ, hm]) rfl rfl

section JetsIn

variable {P : Params} (hm : P.m = 1) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0) (hX2 : ctX2 z ≠ 0)
include hm hX1 hX2

/-- **The jet of `T₁` of the incoming class.** -/
theorem hasJet2_ctT1In :
    HasJet2 (ctT1In P z) 0 0 (ctK P * ((symanzikU (ctAlpha kindsD2In) z ^ 2 : ℝ) : ℂ)⁻¹ * 6 *
      t1InJ (ctZetaIn z : ℂ) (ctSigIn z : ℂ) (P.δ₂ : ℂ) (P.δm : ℂ) PJ.s2) := by
  have hq0 := HasPJ.gam (x := qJ0) (jet_lQ0 hm)
  have hq1 := HasPJ.gam (x := qJ1) (jet_lQ1 hm)
  have hr := HasPJ.gamT (x := rJ) (jet_lR hm)
  have h0 := hasJet2_pwPl hq0 hq1 hr (jet_eoIn hm z)
    (((jet_eiIn hm z).mul (jet_ecIn_zero hm z)).mul (jet_eiIn hm z))
  have h1 := hasJet2_pwPl hq0 hq1 hr (jet_eoIn hm z)
    (((jet_eiIn hm z).mul (jet_ecIn_one hm z)).mul (jet_eiIn hm z))
  set W := ctK P * ((symanzikU (ctAlpha kindsD2In) z ^ 2 : ℝ) : ℂ)⁻¹
  have h := ((h0.const_mul 6).const_mul (W * ctCf P 0)).add ((h1.const_mul 6).const_mul (W * ctCf P 1))
  refine h.of_eq (fun u => ?_) ?_ ?_ ?_
  · rw [ctT1In_planar P hX1 hX2, Fin.sum_univ_two]
    ring
  · have e := t1InJ_s0 (ctZetaIn z : ℂ) (ctSigIn z : ℂ) (P.δ₂ : ℂ) (P.δm : ℂ)
    simp only [t1InJ] at e
    simp only [ctCf, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (W * 6) * e
  · have e := t1InJ_s1 (ctZetaIn z : ℂ) (ctSigIn z : ℂ) (P.δ₂ : ℂ) (P.δm : ℂ)
    simp only [t1InJ] at e
    simp only [ctCf, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (W * 6) * e
  · simp only [t1InJ, ctCf, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- **The jet of `T₂` of the incoming class.** -/
theorem hasJet2_ctT2In :
    HasJet2 (ctT2In P z) 0 0 (ctK P * ((symanzikU (ctAlpha kindsD2In) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (((symanzikMatrix (ctAlpha kindsD2In) z)⁻¹ 0 0 : ℝ) : ℂ) *
        t2InJ (ctZetaIn z : ℂ) (ctSigIn z : ℂ) (P.δ₂ : ℂ) (P.δm : ℂ) PJ.s2) := by
  have hq0 := HasPJ.gam (x := qJ0) (jet_lQ0 hm)
  have hq1 := HasPJ.gam (x := qJ1) (jet_lQ1 hm)
  have hr := HasPJ.gamT (x := rJ) (jet_lR hm)
  have ho := jet_eoIn hm z
  have hi := jet_eiIn hm z
  have g2 := hasJet2_pwPl (hi.mul hq0).gam (hi.mul hq1).gam (hi.mul hr).gamT (HasPJ.const 1) hi
  have g4 := hasJet2_pwPl hq0 hq1 hr ho hi
  have hc : ∀ (cc : ℂ) (j : Fin 2) (hcj : HasPJ (fun u => ecIn P z u (ctCm P j))
      (ecJc (ctZetaIn z : ℂ) (ctSigIn z : ℂ) cc)), HasJet2
      (fun u => 2 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) 1
              (ecIn P z u (ctCm P j) * eiIn P z u) +
            pwPl (gam (eiIn P z u * gam (lQ0 P u))) (gam (eiIn P z u * gam (lQ1 P u)))
              (gamT (eiIn P z u * gamT (lR P u))) 1 (eiIn P z u) +
            pwPl (gam (gam (lQ0 P u))) (gam (gam (lQ1 P u))) (gamT (gamT (lR P u))) 1
              (eiIn P z u * ecIn P z u (ctCm P j)) +
            -4 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (eoIn P z u) (eiIn P z u) +
            pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (eoIn P z u)
              (gam (ecIn P z u (ctCm P j))) +
            -4 * pwPl (gam (lQ0 P u)) (gam (lQ1 P u)) (gamT (lR P u)) (eoIn P z u)
              (eiIn P z u))
      (t2InJc (ctZetaIn z : ℂ) (ctSigIn z : ℂ) PJ.s0 cc)
      (t2InJc (ctZetaIn z : ℂ) (ctSigIn z : ℂ) PJ.s1 cc)
      (t2InJc (ctZetaIn z : ℂ) (ctSigIn z : ℂ) PJ.s2 cc) := fun cc j hcj => by
    have g1 := hasJet2_pwPl hq0 hq1 hr (HasPJ.const 1) (hcj.mul hi)
    have g3 := hasJet2_pwPl hq0.gam hq1.gam hr.gamT (HasPJ.const 1) (hi.mul hcj)
    have g5 := hasJet2_pwPl hq0 hq1 hr ho hcj.gam
    exact (((((g1.const_mul 2).add g2).add g3).add (g4.const_mul (-4))).add g5).add
      (g4.const_mul (-4))
  have h0 := hc 0 0 (jet_ecIn_zero hm z)
  have h1 := hc 1 1 (jet_ecIn_one hm z)
  set W := ctK P * ((symanzikU (ctAlpha kindsD2In) z ^ 2 : ℝ) : ℂ)⁻¹ *
    (((symanzikMatrix (ctAlpha kindsD2In) z)⁻¹ 0 0 : ℝ) : ℂ)
  have h := (h0.const_mul (W * ctCf P 0)).add (h1.const_mul (W * ctCf P 1))
  refine h.of_eq (fun u => ?_) ?_ ?_ ?_
  · rw [ctT2In_planar P hX1 hX2, Fin.sum_univ_two]
    simp only [W]
    ring
  · have e := t2InJ_s0 (ctZetaIn z : ℂ) (ctSigIn z : ℂ) (P.δ₂ : ℂ) (P.δm : ℂ)
    simp only [t2InJ] at e
    simp only [ctCf, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination W * e
  · have e := t2InJ_s1 (ctZetaIn z : ℂ) (ctSigIn z : ℂ) (P.δ₂ : ℂ) (P.δm : ℂ)
    simp only [t2InJ] at e
    simp only [ctCf, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination W * e
  · simp only [t2InJ, ctCf, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

omit hX1 hX2 in
/-- **The jet of `T₃` of the incoming class vanishes.** -/
theorem hasJet2_ctT3In : HasJet2 (ctT3In P z) 0 0 0 := by
  have hq0 := HasPJ.gam (x := qJ0) (jet_lQ0 hm)
  have hq1 := HasPJ.gam (x := qJ1) (jet_lQ1 hm)
  have hr := HasPJ.gamT (x := rJ) (jet_lR hm)
  have g := hasJet2_pwPl hq0 hq1 hr (HasPJ.const 1) (HasPJ.const 1)
  set W := ((symanzikU (ctAlpha kindsD2In) z ^ 2 : ℝ) : ℂ)⁻¹ *
    (1 / 4 * ((((symanzikMatrix (ctAlpha kindsD2In) z)⁻¹ 0 0 : ℝ) : ℂ) ^ 2 * (-12)))
  have h := (g.const_mul (ctK P * ctCf P 0 * W)).add (g.const_mul (ctK P * ctCf P 1 * W))
  refine h.of_eq (fun u => ?_) ?_ ?_ ?_
  · rw [ctT3In_planar, Fin.sum_univ_two]
    simp only [W]
    ring
  · rw [pwJk_T3 PJ.s0 (Or.inl rfl)]; ring
  · rw [pwJk_T3 PJ.s1 (Or.inr (Or.inl rfl))]; ring
  · rw [show pwJ qJ0.gam qJ1.gam rJ.gamT (PJ.c 1) (PJ.c 1) = 0 from
      pwJk_T3 PJ.s2 (Or.inr (Or.inr rfl))]
    ring

end JetsIn

/-! ### The second-order coefficient of the projected numerator, incoming class -/

@[fun_prop] theorem continuous_lineKind_mom (κ : LineKind) (r : Fin 4 → ℝ) (μ : Fin 4) :
    Continuous fun p' : Fin 4 → ℝ => κ.mom r p' μ := by
  cases κ <;> simp [LineKind.mom] <;> fun_prop

theorem continuous_symanzikV_kinds (κ : Fin 8 → LineKind) (r : Fin 4 → ℝ) (M z : Fin 8 → ℝ) :
    Continuous fun p' : Fin 4 → ℝ =>
      symanzikV (ctAlpha κ) (fun i => (κ i).mom r p') M z := by
  unfold symanzikV symanzikVector QED.Minkowski.dot
  fun_prop

/-- The second Symanzik function along the curve tends to its value at `q = 0`. -/
theorem tendsto_symanzikV_kinds (P : Params) (hm : P.m = 1) (κ : Fin 8 → LineKind)
    (hκ : κ = kindsD2In ∨ κ = kindsD2Out) {z : Fin 8 → ℝ} (hX1 : ctX1 z ≠ 0) (hX2 : ctX2 z ≠ 0) :
    Tendsto (fun u => ((symanzikV (ctAlpha κ) (ctMom κ P u) (massesD2In P) z : ℝ) : ℂ))
      (𝓝 0) (𝓝 ((ctV (P.mγ ^ 2) (P.Λ ^ 2) z : ℝ) : ℂ)) := by
  have h := ((continuous_symanzikV_kinds κ (restMomentum P.m) (massesD2In P) z).tendsto
    (restMomentum P.m)).comp (tendsto_curveMomentum P.m)
  rw [← symanzikV_kinds_eq P hm κ hκ hX1 hX2]
  exact (Complex.continuous_ofReal.tendsto _).comp h

theorem ctK_eq {P : Params} (he : P.e = 1) : ctK P = (((P.Λ ^ 2 - P.mγ ^ 2) / 16 : ℝ) : ℂ) := by
  unfold ctK vcConst
  rw [he]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf

theorem symanzikU_kinds (κ : Fin 8 → LineKind) (hκ : κ = kindsD2In ∨ κ = kindsD2Out)
    (z : Fin 8 → ℝ) : symanzikU (ctAlpha κ) z = ctX1 z * ctX2 z := by
  rw [symanzikU, symanzikMatrix_kinds κ hκ, Matrix.det_fin_two_of]
  ring

theorem inv_symanzikMatrix_kinds_zero (κ : Fin 8 → LineKind) (hκ : κ = kindsD2In ∨ κ = kindsD2Out)
    {z : Fin 8 → ℝ} (hX2 : ctX2 z ≠ 0) :
    (symanzikMatrix (ctAlpha κ) z)⁻¹ 0 0 = (ctX1 z)⁻¹ := by
  rw [inv_symanzikMatrix_kinds κ hκ]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.of_apply]
  field_simp

/-- **The pointwise identity, incoming class** (`m = e = 1`). -/
theorem d2Pointwise_In {P : Params} (hm : P.m = 1) (he : P.e = 1) :
    D2Pointwise P kindsD2In fun p' μ k => numD2In P p' (restMomentum P.m) μ k := by
  intro x hx
  set z := simplexPoint x
  have hz := simplexPoint_pos_of_mem_openSimplex' hx
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
  have h4 := hz 4; have h5 := hz 5; have h6 := hz 6; have h7 := hz 7
  have hX1 : ctX1 z ≠ 0 := by unfold ctX1; positivity
  have hX2 : ctX2 z ≠ 0 := by unfold ctX2; positivity
  have hV := tendsto_symanzikV_kinds P hm kindsD2In (Or.inl rfl) hX1 hX2
  have hJ := ((hasJet2_ctT1In hm hX1 hX2).add
    (hasJet2_mul_tendsto (hasJet2_ctT2In hm hX1 hX2) hV)).add
    (hasJet2_mul_tendsto (hasJet2_ctT3In hm (z := z)) (hV.pow 2))
  have hJ' := hJ.of_eq (fun u => kindsNum_d2In_eq_T P x u) (show (0 : ℂ) + 0 + 0 = 0 by ring)
    (show (0 : ℂ) + 0 + 0 = 0 by ring) rfl
  rw [hJ'.secondCoeff_eq, t1InJ_s2, t2InJ_s2, ctK_eq he, symanzikU_kinds kindsD2In (Or.inl rfl),
    inv_symanzikMatrix_kinds_zero kindsD2In (Or.inl rfl) hX2]
  have hξ : ((ctZetaIn z : ℝ) : ℂ) + ((ctSigIn z : ℝ) : ℂ) = ((ctE z / ctX1 z : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add]
    congr 1
    unfold ctZetaIn ctSigIn ctE
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
