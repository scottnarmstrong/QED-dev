/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCLimitNested
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The bubble–bubble integrand at complex loop energies

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53), the integrability of the
three-loop bubble–bubble representative `QED.ChainProof.Enum.repBB`. The route rotates all three
loop energies by a common complex factor (`QED.Integration.ThreeLoop.integral_eq_rotate`); this
file supplies the integrand at complex momenta.

* `dotC`, `slashC`, `denC`, `numC`, `epC`, `phC`: the Minkowski product, the slash, the
  denominator `p·p + M² - iε`, the electron numerator `M - p̸`, the electron and the
  Pauli–Villars photon propagators, all at complex four-momenta `Fin 4 → ℂ`.
* `chainOuterC`, `vpC`, `bbC`: the outer factor `QED.ChainProof.HCLimit.chainOuter`, the vacuum
  polarization integrand and the bubble–bubble integrand `QED.ChainProof.HCLimit.bbIntegrand` at
  complex momenta.
* **`bbC_real`**: at real momenta (`cv`) they are the original integrand.
* `mk X y = (X, y)`: a four-momentum with complex energy `X` and real spatial part `y`, with
  `denC M ε (mk X y) = -X² + (|y|² + M²) - iε` (`denC_mk`).
* **`differentiableAt_bbC`**: the integrand is complex differentiable in all loop momenta at every
  point where no denominator vanishes (`NZ`).
-/

@[expose] public section

open Complex

namespace QED.ChainProof.RepsIntBB

open QED.WickModel

/-! ### Complex four-momenta -/

/-- The Minkowski product at complex four-momenta. -/
def dotC (p q : Fin 4 → ℂ) : ℂ :=
  ∑ μ, ∑ ν, (Minkowski.metric μ ν : ℂ) * p μ * q ν

/-- The slash at complex four-momenta. -/
noncomputable def slashC (p : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ μ, (∑ ν, (Minkowski.metric μ ν : ℂ) * p ν) • Dirac.gamma μ

/-- The denominator `p·p + M² - iε`. -/
def denC (M ε : ℝ) (p : Fin 4 → ℂ) : ℂ :=
  dotC p p + (M : ℂ) ^ 2 - (ε : ℂ) * I

/-- The electron numerator `M - p̸`. -/
noncomputable def numC (M : ℝ) (p : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (M : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - slashC p

/-- The electron propagator. -/
noncomputable def epC (M ε : ℝ) (p : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (denC M ε p)⁻¹ • numC M p

/-- The Pauli–Villars photon propagator. -/
noncomputable def phC (mγ Λ ε : ℝ) (k : Fin 4 → ℂ) (μ ν : Fin 4) : ℂ :=
  (Minkowski.metric μ ν : ℂ) * ((denC mγ ε k)⁻¹ - (denC Λ ε k)⁻¹)

/-- A real four-momentum as a complex one. -/
def cv (p : Fin 4 → ℝ) : Fin 4 → ℂ := fun μ => (p μ : ℂ)

/-- The open-line chain at complex photon momentum. -/
noncomputable def outerChainC (P : Params) (p kext k : Fin 4 → ℂ) (μ ρ ν : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Dirac.gamma ν * epC P.m P.ε (p + kext - k) * Dirac.gamma μ * epC P.m P.ε (p - k) *
    Dirac.gamma ρ

/-- The outer factor `chainOuter` at complex photon momentum. -/
noncomputable def chainOuterC (P : Params) (p kext : Fin 4 → ℂ) (α β μ : Fin 4)
    (k : Fin 4 → ℂ) (a b : Fin 4 × Fin 4) : ℂ :=
  (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ * (I * P.e) ^ 3 * (1 / I) ^ 5 *
    ∑ l0 : Fin 4, ∑ l2 : Fin 4, outerChainC P p kext k μ l0 l2 α β *
      phC P.mγ P.Λ P.ε k l0 a.1 * phC P.mγ P.Λ P.ε k a.2 b.1 * phC P.mγ P.Λ P.ε (-k) l2 b.2

/-- The constant of the vacuum polarization integrand. -/
noncomputable def vpConst (P : Params) : ℂ :=
  (-1) * (I * P.e) ^ 2 * (1 / I) ^ 2 * (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹

/-- The vacuum polarization integrand at complex momenta, at `ε = P.ε`. -/
noncomputable def vpC (P : Params) (k q : Fin 4 → ℂ) (μ ν : Fin 4) : ℂ :=
  vpConst P * ∑ f, (P.loopCoeff f : ℂ) *
    Matrix.trace (epC (P.mass f) P.ε (q + k) * Dirac.gamma μ * epC (P.mass f) P.ε q *
      Dirac.gamma ν)

/-- The bubble–bubble integrand at complex momenta: `ℓ 0`, `ℓ 1` on the bubbles, `ℓ 2` on the
photon. -/
noncomputable def bbC (P : Params) (O : (Fin 4 → ℂ) → Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℂ)
    (ℓ : Fin 3 → Fin 4 → ℂ) : ℂ :=
  ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4, O (ℓ 2) a b * vpC P (ℓ 2) (ℓ 0) a.1 a.2 *
    vpC P (ℓ 2) (ℓ 1) b.1 b.2

/-! ### Agreement at real momenta -/

theorem cv_add (p q : Fin 4 → ℝ) : cv (p + q) = cv p + cv q := by
  funext μ; simp [cv]

theorem cv_sub (p q : Fin 4 → ℝ) : cv (p - q) = cv p - cv q := by
  funext μ; simp [cv]

theorem cv_neg (p : Fin 4 → ℝ) : cv (-p) = -cv p := by
  funext μ; simp [cv]

theorem dotC_cv (p q : Fin 4 → ℝ) : dotC (cv p) (cv q) = (Minkowski.dot p q : ℂ) := by
  simp [dotC, cv, Minkowski.dot]

theorem slashC_cv (p : Fin 4 → ℝ) : slashC (cv p) = Dirac.slash p := by
  simp [slashC, cv, Dirac.slash, Minkowski.lower]

theorem denC_cv (M ε : ℝ) (p : Fin 4 → ℝ) :
    denC M ε (cv p) = ((Minkowski.dot p p + M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I := by
  simp [denC, dotC_cv]

theorem epC_cv (M ε : ℝ) (p : Fin 4 → ℝ) :
    epC M ε (cv p) = QED.OneLoop.electronPropagator M ε p := by
  rw [epC, numC, denC_cv, slashC_cv, QED.OneLoop.electronPropagator]

theorem phC_cv (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    phC mγ Λ ε (cv k) μ ν = QED.OneLoop.photonPropagator mγ Λ ε k μ ν := by
  rw [phC, denC_cv, denC_cv, QED.OneLoop.photonPropagator]

theorem chainOuterC_cv (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (k : Fin 4 → ℝ)
    (a b : Fin 4 × Fin 4) :
    chainOuterC P (cv p) (cv kext) α β μ (cv k) a b =
      QED.ChainProof.HCLimit.chainOuter P p kext k α β μ a b := by
  simp only [chainOuterC, QED.ChainProof.HCLimit.chainOuter, outerChainC,
    QED.TwoLoop.NestedVP.outerChain, ← cv_add, ← cv_sub, ← cv_neg, epC_cv, phC_cv]

theorem vpC_cv (P : Params) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    vpC P (cv k) (cv q) μ ν = vacuumPolarizationIntegrand P P.ε k q μ ν := by
  simp only [vpC, vpConst, vacuumPolarizationIntegrand, ← cv_add, epC_cv]

/-- **At real momenta the complex integrand is the bubble–bubble integrand.** -/
theorem bbC_real (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (ℓ : Fin 3 → Fin 4 → ℝ) :
    bbC P (chainOuterC P (cv p) (cv kext) α β μ) (fun s => cv (ℓ s)) =
      QED.ChainProof.HCLimit.bbIntegrand P
        (fun k => QED.ChainProof.HCLimit.chainOuter P p kext k α β μ) ℓ := by
  simp only [bbC, QED.ChainProof.HCLimit.bbIntegrand, chainOuterC_cv, vpC_cv]

/-! ### Momenta with complex energy and real spatial part -/

/-- The four-momentum `(X, y)` with complex energy `X` and real spatial part `y`. -/
def mk (X : ℂ) (y : Fin 3 → ℝ) : Fin 4 → ℂ :=
  Fin.cons X fun i => (y i : ℂ)

@[simp] theorem mk_zero (X : ℂ) (y : Fin 3 → ℝ) : mk X y 0 = X := rfl
@[simp] theorem mk_one (X : ℂ) (y : Fin 3 → ℝ) : mk X y 1 = (y 0 : ℂ) := rfl
@[simp] theorem mk_two (X : ℂ) (y : Fin 3 → ℝ) : mk X y 2 = (y 1 : ℂ) := rfl
@[simp] theorem mk_three (X : ℂ) (y : Fin 3 → ℝ) : mk X y 3 = (y 2 : ℂ) := rfl

theorem mk_add (X X' : ℂ) (y y' : Fin 3 → ℝ) : mk X y + mk X' y' = mk (X + X') (y + y') := by
  funext μ
  refine Fin.cases ?_ (fun i => ?_) μ <;> simp [mk]

theorem mk_sub (X X' : ℂ) (y y' : Fin 3 → ℝ) : mk X y - mk X' y' = mk (X - X') (y - y') := by
  funext μ
  refine Fin.cases ?_ (fun i => ?_) μ <;> simp [mk]

theorem mk_neg (X : ℂ) (y : Fin 3 → ℝ) : -mk X y = mk (-X) (-y) := by
  funext μ
  refine Fin.cases ?_ (fun i => ?_) μ <;> simp [mk]

theorem cv_eq_mk (p : Fin 4 → ℝ) : cv p = mk (p 0 : ℂ) (Fin.tail p) := by
  funext μ
  refine Fin.cases ?_ (fun _ => ?_) μ <;> simp [mk, cv, Fin.tail]

theorem cv_cons (t : ℝ) (w : Fin 3 → ℝ) : cv (Fin.cons t w) = mk (t : ℂ) w := by
  rw [cv_eq_mk]
  rfl

/-- The spatial square `|y|² = ∑ yᵢ²`. -/
def sq3 (y : Fin 3 → ℝ) : ℝ := ∑ i, y i ^ 2

theorem sq3_nonneg (y : Fin 3 → ℝ) : 0 ≤ sq3 y := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem dotC_mk (X : ℂ) (y : Fin 3 → ℝ) : dotC (mk X y) (mk X y) = -X ^ 2 + (sq3 y : ℂ) := by
  simp only [dotC, Fin.sum_univ_four, Minkowski.metric, sq3, Fin.sum_univ_three, mk_zero,
    mk_one, mk_two, mk_three]
  simp
  ring

theorem denC_mk (M ε : ℝ) (X : ℂ) (y : Fin 3 → ℝ) :
    denC M ε (mk X y) = -X ^ 2 + ((sq3 y + M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I := by
  rw [denC, dotC_mk]
  push_cast
  ring

/-! ### Complex differentiability -/

/-- No denominator vanishes at the momentum `q`, whatever the mass. -/
def NZ (ε : ℝ) (q : Fin 4 → ℂ) : Prop := ∀ M : ℝ, denC M ε q ≠ 0

section Diff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem differentiable_dotC : Differentiable ℂ fun p : Fin 4 → ℂ => dotC p p := by
  unfold dotC
  fun_prop

theorem differentiableAt_slashC {q : E → Fin 4 → ℂ} {x : E} (hq : DifferentiableAt ℂ q x) :
    DifferentiableAt ℂ (fun y => slashC (q y)) x := by
  unfold slashC
  refine DifferentiableAt.fun_sum fun μ _ => ?_
  refine DifferentiableAt.smul_const ?_ _
  refine DifferentiableAt.fun_sum fun ν _ => ?_
  exact (differentiableAt_const _).mul (differentiableAt_pi.1 hq ν)

theorem differentiableAt_inv_denC (M ε : ℝ) {q : E → Fin 4 → ℂ} {x : E}
    (hq : DifferentiableAt ℂ q x) (hne : denC M ε (q x) ≠ 0) :
    DifferentiableAt ℂ (fun y => (denC M ε (q y))⁻¹) x := by
  refine DifferentiableAt.inv ?_ hne
  unfold denC
  exact (((differentiable_dotC (q x)).comp x hq).add_const ((M : ℂ) ^ 2)).sub_const
    ((ε : ℂ) * I)

theorem differentiableAt_epC (M ε : ℝ) {q : E → Fin 4 → ℂ} {x : E}
    (hq : DifferentiableAt ℂ q x) (hne : denC M ε (q x) ≠ 0) :
    DifferentiableAt ℂ (fun y => epC M ε (q y)) x := by
  unfold epC numC
  exact (differentiableAt_inv_denC M ε hq hne).smul
    ((differentiableAt_const _).sub (differentiableAt_slashC hq))

theorem differentiableAt_phC (mγ Λ ε : ℝ) {q : E → Fin 4 → ℂ} {x : E}
    (hq : DifferentiableAt ℂ q x) (hne : NZ ε (q x)) (μ ν : Fin 4) :
    DifferentiableAt ℂ (fun y => phC mγ Λ ε (q y) μ ν) x := by
  unfold phC
  exact (differentiableAt_const _).mul ((differentiableAt_inv_denC mγ ε hq (hne _)).sub
    (differentiableAt_inv_denC Λ ε hq (hne _)))

theorem differentiableAt_entry {A : E → Matrix (Fin 4) (Fin 4) ℂ} {x : E}
    (hA : DifferentiableAt ℂ A x) (i j : Fin 4) : DifferentiableAt ℂ (fun y => A y i j) x := by
  have : DifferentiableAt ℂ (fun y => (A y : Fin 4 → Fin 4 → ℂ)) x := hA
  exact differentiableAt_pi.1 (differentiableAt_pi.1 this i) j

theorem differentiableAt_trace {A : E → Matrix (Fin 4) (Fin 4) ℂ} {x : E}
    (hA : DifferentiableAt ℂ A x) : DifferentiableAt ℂ (fun y => (A y).trace) x := by
  unfold Matrix.trace Matrix.diag
  exact DifferentiableAt.fun_sum fun i _ => differentiableAt_entry hA i i

theorem differentiableAt_vpC (P : Params) {k q : E → Fin 4 → ℂ} {x : E}
    (hk : DifferentiableAt ℂ k x) (hq : DifferentiableAt ℂ q x) (h1 : NZ P.ε (q x + k x))
    (h2 : NZ P.ε (q x)) (μ ν : Fin 4) : DifferentiableAt ℂ (fun y => vpC P (k y) (q y) μ ν) x := by
  unfold vpC
  refine (differentiableAt_const _).mul (DifferentiableAt.fun_sum fun f _ =>
    (differentiableAt_const _).mul (differentiableAt_trace ?_))
  exact (((differentiableAt_epC _ _ (hq.add hk) (h1 _)).mul (differentiableAt_const _)).mul
    (differentiableAt_epC _ _ hq (h2 _))).mul (differentiableAt_const _)

theorem differentiableAt_chainOuterC (P : Params) (p kext : Fin 4 → ℂ) (α β μ : Fin 4)
    {k : E → Fin 4 → ℂ} {x : E} (hk : DifferentiableAt ℂ k x) (h1 : NZ P.ε (p + kext - k x))
    (h2 : NZ P.ε (p - k x)) (h3 : NZ P.ε (k x)) (h4 : NZ P.ε (-k x)) (a b : Fin 4 × Fin 4) :
    DifferentiableAt ℂ (fun y => chainOuterC P p kext α β μ (k y) a b) x := by
  unfold chainOuterC
  refine (differentiableAt_const _).mul (DifferentiableAt.fun_sum fun l0 _ =>
    DifferentiableAt.fun_sum fun l2 _ => ?_)
  refine (((differentiableAt_entry ?_ α β).mul (differentiableAt_phC _ _ _ hk h3 _ _)).mul
    (differentiableAt_phC _ _ _ hk h3 _ _)).mul (differentiableAt_phC _ _ _ hk.neg h4 _ _)
  unfold outerChainC
  exact ((((differentiableAt_const _).mul (differentiableAt_epC _ _
    ((differentiableAt_const _).sub hk) (h1 _))).mul (differentiableAt_const _)).mul
    (differentiableAt_epC _ _ ((differentiableAt_const _).sub hk) (h2 _))).mul
    (differentiableAt_const _)

/-- The momenta of the bubble–bubble integrand at which no denominator vanishes. -/
def GoodBB (P : Params) (p kext : Fin 4 → ℂ) (ℓ : Fin 3 → Fin 4 → ℂ) : Prop :=
  NZ P.ε (ℓ 0 + ℓ 2) ∧ NZ P.ε (ℓ 0) ∧ NZ P.ε (ℓ 1 + ℓ 2) ∧ NZ P.ε (ℓ 1) ∧ NZ P.ε (ℓ 2) ∧
    NZ P.ε (-ℓ 2) ∧ NZ P.ε (p + kext - ℓ 2) ∧ NZ P.ε (p - ℓ 2)

/-- **Complex differentiability of the bubble–bubble integrand** at momenta where no
denominator vanishes. -/
theorem differentiableAt_bbC (P : Params) (p kext : Fin 4 → ℂ) (α β μ : Fin 4)
    {ℓ : E → Fin 3 → Fin 4 → ℂ} {x : E} (hℓ : DifferentiableAt ℂ ℓ x)
    (hg : GoodBB P p kext (ℓ x)) :
    DifferentiableAt ℂ (fun y => bbC P (chainOuterC P p kext α β μ) (ℓ y)) x := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hg
  have d : ∀ s, DifferentiableAt ℂ (fun y => ℓ y s) x := fun s => differentiableAt_pi.1 hℓ s
  unfold bbC
  exact DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
    ((differentiableAt_chainOuterC P p kext α β μ (d 2) g7 g8 g5 g6 a b).mul
      (differentiableAt_vpC P (d 2) (d 0) g1 g2 _ _)).mul
      (differentiableAt_vpC P (d 2) (d 1) g3 g4 _ _)

end Diff

end QED.ChainProof.RepsIntBB

end
