/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraphTraceWick
public import QED.TwoLoop.UnitLGraphTraceContract
import Mathlib.Tactic.Ring

/-!
# The planar evaluation of the nested patterns of the crossed ladder

Section 8 of `docs/TWO-LOOP-UNITS.md`, the graph half of the X unit. When the Pauli matrices are
planar for `μ = 0, 1` and of the form `R γ^μ` for `μ = 2, 3`
(`QED.TwoLoop.UnitLGraphTrace.PlanarPauli`) and the inserted matrices lie in the planar
subalgebra of `QED/TwoLoop/UnitLGraphTracePlanar.lean`, the patterns `om0`, `omG`, `bs`, `hg` of
`QED/TwoLoop/UnitXGraphTraceReduce.lean` are explicit planar expressions (`om0_planar`,
`omG_planar`, `bs_planar`, `hg_planar`), by the same moves as the ladder patterns
(`QED.TwoLoop.UnitLGraphTrace.lw_planar`): the transverse `γ^μ` are moved to the right by
`γⁱ X = X̄ γⁱ` and the sandwiches are `Σ(X) = Γ(X)`, `Σ(X γⁱ) = Γ_T(X) γⁱ`.
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.UnitXGraph

open QED.Dirac QED.TwoLoop.UnitLGraphTrace
open Pl

local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The planar values -/

section Planar

variable (Q₀ Q₁ R a b z : Pl)

/-- The planar value of `om0`. -/
def om0Pl : ℂ := 4 * (Q₀ * a * g0 * b).s + 4 * (Q₁ * a * g1 * b).s - 8 * (R * bar a * b).s

/-- The planar value of `omG`. -/
def omGPl : ℂ :=
  4 * (gam Q₀ * a * g0 * b).s + 4 * (gam Q₁ * a * g1 * b).s - 8 * (gamT R * bar a * b).s

/-- The planar value of `bs`. -/
def bsPl : ℂ :=
  4 * (gam (Q₀ * a * g0 * b) * z).s + 4 * (gam (Q₁ * a * g1 * b) * z).s -
    8 * (gam (R * bar a * b) * z).s

/-- The planar value of `hg`. -/
def hgPl (y₁ y₂ z : Pl) : ℂ :=
  4 * (Q₀ * gam (y₁ * g0 * y₂) * z).s + 4 * (Q₁ * gam (y₁ * g1 * y₂) * z).s -
    8 * (R * bar (gamT (y₁ * bar y₂)) * z).s

end Planar

theorem gam_neg (x : Pl) : gam (-x) = -gam x := by
  ext <;> simp [gam]

theorem sig_toMat (x : Pl) : sig (toMat x) = toMat (gam x) := sum_gamma_toMat x

theorem sig_toMat_gamma_two (x : Pl) : sig (toMat x * gamma 2) = toMat (gamT x) * gamma 2 :=
  sum_gamma_toMat_gamma_two x

theorem sig_toMat_gamma_three (x : Pl) : sig (toMat x * gamma 3) = toMat (gamT x) * gamma 3 :=
  sum_gamma_toMat_gamma_three x

/-- **The planar evaluation of `om0`.** -/
theorem om0_planar {P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {Q₀ Q₁ R : Pl}
    (hP : PlanarPauli P Q₀ Q₁ R) (a b : Pl) :
    om0 P (toMat a) (toMat b) = om0Pl Q₀ Q₁ R a b := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  unfold om0
  rw [Fin.sum_univ_four, h0, h1, h2, h3]
  simp only [gamma_zero, gamma_one, toMat_mul, toMat_mul_gamma_two_mul, toMat_mul_gamma_three_mul,
    toMat_gamma_two_sq, toMat_gamma_three_sq, trace_toMat, neg_mul', neg_s, om0Pl]
  ring

/-- **The planar evaluation of `omG`.** -/
theorem omG_planar {P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {Q₀ Q₁ R : Pl}
    (hP : PlanarPauli P Q₀ Q₁ R) (a b : Pl) :
    omG P (toMat a) (toMat b) = omGPl Q₀ Q₁ R a b := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  unfold omG
  rw [Fin.sum_univ_four, h0, h1, h2, h3]
  simp only [sig_toMat, sig_toMat_gamma_two, sig_toMat_gamma_three, gamma_zero, gamma_one,
    toMat_mul, toMat_mul_gamma_two_mul, toMat_mul_gamma_three_mul, toMat_gamma_two_sq,
    toMat_gamma_three_sq, trace_toMat, neg_mul', neg_s, omGPl]
  ring

/-- **The planar evaluation of `bs`.** -/
theorem bs_planar {P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {Q₀ Q₁ R : Pl}
    (hP : PlanarPauli P Q₀ Q₁ R) (a b z : Pl) :
    bs P (toMat a) (toMat b) (toMat z) = bsPl Q₀ Q₁ R a b z := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  unfold bs
  rw [Fin.sum_univ_four, h0, h1, h2, h3]
  simp only [gamma_zero, gamma_one, toMat_mul, toMat_mul_gamma_two_mul, toMat_mul_gamma_three_mul,
    toMat_gamma_two_sq, toMat_gamma_three_sq, sig_toMat, trace_toMat, neg_mul', gam_neg, neg_s,
    bsPl]
  ring

/-- **The planar evaluation of `hg`.** -/
theorem hg_planar {P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {Q₀ Q₁ R : Pl}
    (hP : PlanarPauli P Q₀ Q₁ R) (y₁ y₂ z : Pl) :
    hg P (toMat y₁) (toMat y₂) (toMat z) = hgPl Q₀ Q₁ R y₁ y₂ z := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  unfold hg
  rw [Fin.sum_univ_four, h0, h1, h2, h3]
  simp only [gamma_zero, gamma_one, toMat_mul, toMat_mul_gamma_two_mul, toMat_mul_gamma_three_mul,
    sig_toMat, sig_toMat_gamma_two, sig_toMat_gamma_three, toMat_gamma_two_mul_toMat_gamma_two,
    toMat_gamma_three_mul_toMat_gamma_three, trace_toMat, neg_mul', neg_s, hgPl]
  ring

end QED.TwoLoop.UnitXGraph

end
