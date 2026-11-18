/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraph
import Mathlib.Tactic.Ring

/-!
# Planar Pauli families and the base contraction pattern

Infrastructure for the Dirac traces of the self-energy classes `S₊, S₋` (section 8 of
`docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link). A family `P_μ` of matrices is planar with
data `(Q₀, Q₁, R)` (`QED.TwoLoop.UnitLGraphTrace.PlanarPauli`) if `P₀, P₁` are planar and
`P_μ = R γ^μ` for `μ = 2, 3`. This class is closed under

* the contraction `P_μ ↦ γ^ν P_μ γ_ν`, with data `(Γ Q₀, Γ Q₁, Γ_T R)` (`planarPauli_contractP`);
* right multiplication by a planar `y`, with data `(Q₀ y, Q₁ y, R ȳ)` (`planarPauli_mulRightP`);
* left multiplication by a planar `y`, with data `(y Q₀, y Q₁, y R)` (`planarPauli_mulLeftP`).

Every trace of the classes `S±` reduces to the base pattern
`pw(P; W, Z) = ∑_μ tr(P_μ W γ^μ Z)`, whose planar value is
`4 (Q₀ w γ⁰ z)_s + 4 (Q₁ w γ¹ z)_s - 8 (R w̄ z)_s` (`pw_planar`). Its second-order jet along the
curve follows from the planar jet rules of `QED/TwoLoop/UnitLGraphTraceJet.lean`
(`hasJet2_pwPl`).
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.UnitSCGraph

open QED.Dirac QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.UnitLGraphTrace.Pl

/-! ### Closure of planar Pauli families -/

/-- The contracted family `γ^ν P_μ γ_ν`. -/
noncomputable def contractP (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => ∑ ν, gamma ν * P μ * gammaLower ν

/-- The family `P_μ Y`. -/
def mulRightP (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y : Matrix (Fin 4) (Fin 4) ℂ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => P μ * Y

/-- The family `Y P_μ`. -/
def mulLeftP (Y : Matrix (Fin 4) (Fin 4) ℂ) (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => Y * P μ

variable {P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {Q₀ Q₁ R : Pl}

theorem planarPauli_contractP (hP : PlanarPauli P Q₀ Q₁ R) :
    PlanarPauli (contractP P) (gam Q₀) (gam Q₁) (gamT R) := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [contractP, h0, h1, h2, h3, sum_gamma_toMat, sum_gamma_toMat_gamma_two,
      sum_gamma_toMat_gamma_three]

theorem planarPauli_mulRightP (hP : PlanarPauli P Q₀ Q₁ R) (y : Pl) :
    PlanarPauli (mulRightP P (toMat y)) (Q₀ * y) (Q₁ * y) (R * bar y) := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [mulRightP, h0, h1, h2, h3, toMat_mul, toMat_mul_gamma_two_mul,
      toMat_mul_gamma_three_mul]

theorem planarPauli_mulLeftP (hP : PlanarPauli P Q₀ Q₁ R) (y : Pl) :
    PlanarPauli (mulLeftP (toMat y) P) (y * Q₀) (y * Q₁) (y * R) := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [mulLeftP, h0, h1, h2, h3, toMat_mul, toMat_mul_toMat_gamma]

/-! ### The base pattern -/

/-- **The base pattern** `pw(P; W, Z) = ∑_μ tr(P_μ W γ^μ Z)`. -/
noncomputable def pw (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (W Z : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ∑ μ, trace (P μ * W * gamma μ * Z)

/-- The planar value of `pw`. -/
def pwPl (Q₀ Q₁ R w z : Pl) : ℂ :=
  4 * (Q₀ * w * g0 * z).s + 4 * (Q₁ * w * g1 * z).s - 8 * (R * bar w * z).s

/-- **The planar evaluation of the base pattern.** -/
theorem pw_planar (hP : PlanarPauli P Q₀ Q₁ R) (w z : Pl) :
    pw P (toMat w) (toMat z) = pwPl Q₀ Q₁ R w z := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  unfold pw
  rw [Fin.sum_univ_four, h0, h1, h2, h3, gamma_zero, gamma_one]
  simp only [toMat_mul, toMat_mul_gamma_two_mul, toMat_mul_gamma_three_mul, toMat_gamma_two_sq,
    toMat_gamma_three_sq, trace_toMat, neg_mul', neg_s, pwPl]
  ring

theorem pw_smul_left (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ) (W Z : Matrix (Fin 4) (Fin 4) ℂ) :
    pw P (c • W) Z = c * pw P W Z := by
  unfold pw
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]

theorem pw_smul_right (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ) (W Z : Matrix (Fin 4) (Fin 4) ℂ) :
    pw P W (c • Z) = c * pw P W Z := by
  unfold pw
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]

/-! ### Contraction identities -/

/-- `γ^ρ γ^σ γ_ρ = 2 γ^σ`. -/
theorem sum_gamma_gamma_gammaLower (σ : Fin 4) :
    ∑ ρ, gamma ρ * gamma σ * gammaLower ρ = (2 : ℂ) • gamma σ := by
  rw [← sum_gammaLower_swap, sum_gammaLower_gamma_gamma]

/-- `γ^ρ γ_σ γ_ρ = 2 γ_σ`. -/
theorem sum_gamma_gammaLower_gammaLower (σ : Fin 4) :
    ∑ ρ, gamma ρ * gammaLower σ * gammaLower ρ = (2 : ℂ) • gammaLower σ := by
  rw [← sum_gammaLower_swap, sum_gammaLower_gammaLower_gamma]

/-- `∑_τ pw(P; W γ_τ, γ^τ Z) = 2 pw(P; W, Z)`. -/
theorem sum_pw_gammaLower_gamma (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (W Z : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ τ, pw P (W * gammaLower τ) (gamma τ * Z) = 2 * pw P W Z := by
  unfold pw
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  calc ∑ τ, trace (P μ * (W * gammaLower τ) * gamma μ * (gamma τ * Z))
      = trace (P μ * W * (∑ τ, gammaLower τ * gamma μ * gamma τ) * Z) := by
        simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    _ = _ := by
        rw [sum_gammaLower_gamma_gamma]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-! ### Second-order jets -/

section Jets

variable {Q₀ Q₁ R W Z : ℝ → Pl} {q₀ q₁ r w z : PJ}

/-- The jet coefficients of `pwPl` from the jets of its arguments. -/
def pwJk (sel : PJ → ℂ) (q₀ q₁ r w z : PJ) : ℂ :=
  4 * sel (((q₀.mul w).mul (PJ.c g0)).mul z) + 4 * sel (((q₁.mul w).mul (PJ.c g1)).mul z) -
    8 * sel ((r.mul w.bar).mul z)

/-- The second-order coefficient of the pattern. -/
abbrev pwJ (q₀ q₁ r w z : PJ) : ℂ := pwJk PJ.s2 q₀ q₁ r w z

theorem hasJet2_pwPl (hQ₀ : HasPJ Q₀ q₀) (hQ₁ : HasPJ Q₁ q₁) (hR : HasPJ R r) (hW : HasPJ W w)
    (hZ : HasPJ Z z) :
    HasJet2 (fun u => pwPl (Q₀ u) (Q₁ u) (R u) (W u) (Z u)) (pwJk PJ.s0 q₀ q₁ r w z)
      (pwJk PJ.s1 q₀ q₁ r w z) (pwJ q₀ q₁ r w z) := by
  have h1 := (((hQ₀.mul hW).mul (HasPJ.const g0)).mul hZ).s
  have h2 := (((hQ₁.mul hW).mul (HasPJ.const g1)).mul hZ).s
  have h3 := ((hR.mul hW.bar).mul hZ).s
  exact ((h1.const_mul 4).add (h2.const_mul 4)).sub (h3.const_mul 8)

end Jets

end QED.TwoLoop.UnitSCGraph

end
