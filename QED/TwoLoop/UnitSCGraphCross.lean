/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCGraphSpTrace
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The vertex-subgraph pattern of the corner classes

Infrastructure for the Dirac traces of the corner classes `C₊, C₋` (section 8 of
`docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link). In a corner class the inner photon
encloses one vertex of the outer photon, so the inner contraction is the one-loop vertex
numerator `H_ν(Y₀, Y₁) = Γ(Y₀ γ_ν Y₁) = ∑_σ γ^σ Y₀ γ_ν Y₁ γ_σ` (`hfam`), a family indexed by the
outer photon index `ν`. This file provides:

* the sandwich calculus `Γ(X γ^σ) = -Γ(X) γ^σ - 2 γ^σ X`, `Γ(γ^σ X) = -γ^σ Γ(X) - 2 X γ^σ` and
  their versions with `γ_σ` (`gamM_mul_gamma`, `gamM_gamma_mul`, …);
* the double pattern `pp(P, H; W, Z) = ∑_{μν} tr(H_ν W γ^μ Z γ^ν P_μ)` (`pp`), linear in `H`;
* the closure of planar Pauli families under sums and scalar multiples, and the planar family
  `γ_ν` (`planarPauli_gammaLower`), so that `H(y₀, y₁)` is planar with data
  `(Γ(y₀ γ_0 y₁), Γ(y₀ γ_1 y₁), Γ_T(y₀ ȳ₁))` (`planarPauli_hfam`);
* **the planar evaluation** `pp_planar`: for planar families `P` (data `Q₀, Q₁, R`) and `H`
  (data `A₀, A₁, B`) and planar `w, z`,
  `pp = 4 ∑_{μ,ν ∈ {0,1}} (A_ν w γ^μ z γ^ν Q_μ)_s - 8 ∑_{μ ∈ {0,1}} (B (w γ^μ z)‾ Q_μ)_s
    - 8 ∑_{ν ∈ {0,1}} (A_ν w (z γ^ν R)‾)_s` (`ppPl`), and its second-order jet
  (`hasJet2_ppPl`).
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.UnitSCGraph

open QED.Dirac QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.UnitLGraphTrace.Pl

/-- The identity matrix. -/
local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-! ### The sandwich calculus -/

section Sandwich

variable (X Y : Matrix (Fin 4) (Fin 4) ℂ)

theorem gamM_add : gamM (X + Y) = gamM X + gamM Y := by
  simp only [gamM, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem gamM_sub : gamM (X - Y) = gamM X - gamM Y := by
  simp only [gamM, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem gamM_neg : gamM (-X) = -gamM X := by
  simp only [gamM, Matrix.mul_neg, Matrix.neg_mul, Finset.sum_neg_distrib]

theorem gamM_smul (c : ℂ) : gamM (c • X) = c • gamM X := by
  simp only [gamM, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem gamM_one : gamM 𝟙 = (-4 : ℂ) • 𝟙 := by
  simp only [gamM, Matrix.mul_one, QED.Dirac.contract_one]

theorem gamM_gamma (σ : Fin 4) : gamM (gamma σ) = (2 : ℂ) • gamma σ :=
  sum_gamma_gamma_gammaLower σ

theorem gamM_gammaLower (σ : Fin 4) : gamM (gammaLower σ) = (2 : ℂ) • gammaLower σ :=
  sum_gamma_gammaLower_gammaLower σ

/-- `Γ(X a̸) = -Γ(X) a̸ - 2 a̸ X`. -/
theorem gamM_mul_slash (a : Fin 4 → ℝ) :
    gamM (X * slash a) = -(gamM X * slash a) - (2 : ℂ) • (slash a * X) := by
  have h := QED.Dirac.contract_mul_slash X a
  simp only [gamM, Matrix.mul_assoc] at h ⊢
  exact h

/-- `Γ(a̸ X) = -a̸ Γ(X) - 2 X a̸`. -/
theorem gamM_slash_mul (a : Fin 4 → ℝ) :
    gamM (slash a * X) = -(slash a * gamM X) - (2 : ℂ) • (X * slash a) := by
  have h : ∀ μ, gamma μ * (slash a * X) * gammaLower μ =
      -(slash a * (gamma μ * X * gammaLower μ))
        - (2 : ℂ) • (X * (((a μ : ℝ) : ℂ) • gammaLower μ)) := by
    intro μ
    have e : gamma μ * slash a = ((-2 * a μ : ℝ) : ℂ) • 𝟙 - slash a * gamma μ := by
      rw [← QED.Dirac.gamma_slash_anticomm]; abel
    calc gamma μ * (slash a * X) * gammaLower μ = (gamma μ * slash a) * X * gammaLower μ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [e, Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
          simp only [Matrix.mul_assoc, Matrix.mul_smul]
          push_cast
          module
  have hs : ∑ μ, ((a μ : ℝ) : ℂ) • gammaLower μ = slash a := by
    simp [slash, Fin.sum_univ_four, QED.Dirac.gammaLower_eq, Minkowski.lower_eq]
  rw [gamM, Finset.sum_congr rfl fun μ _ => h μ, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.smul_sum, ← Matrix.mul_sum, ← Matrix.mul_sum, hs]

theorem gamM_mul_gamma (σ : Fin 4) :
    gamM (X * gamma σ) = -(gamM X * gamma σ) - (2 : ℂ) • (gamma σ * X) := by
  have h := gamM_mul_slash X (upV σ)
  rwa [slash_upV] at h

theorem gamM_mul_gammaLower (σ : Fin 4) :
    gamM (X * gammaLower σ) = -(gamM X * gammaLower σ) - (2 : ℂ) • (gammaLower σ * X) := by
  have h := gamM_mul_slash X (loV σ)
  rwa [slash_loV] at h

theorem gamM_gamma_mul (σ : Fin 4) :
    gamM (gamma σ * X) = -(gamma σ * gamM X) - (2 : ℂ) • (X * gamma σ) := by
  have h := gamM_slash_mul X (upV σ)
  rwa [slash_upV] at h

theorem gamM_gammaLower_mul (σ : Fin 4) :
    gamM (gammaLower σ * X) = -(gammaLower σ * gamM X) - (2 : ℂ) • (X * gammaLower σ) := by
  have h := gamM_slash_mul X (loV σ)
  rwa [slash_loV] at h

/-- `∑_σ γ_σ X γ^σ = Γ(X)`. -/
theorem sum_gammaLower_mul_gamma' : ∑ σ, gammaLower σ * X * gamma σ = gamM X :=
  sum_gammaLower_swap X

/-- `∑_ν γ^ν Γ(γ_ν X) = 2 Γ(X)`. -/
theorem sum_gamma_mul_gamM_gammaLower_mul :
    ∑ ν, gamma ν * gamM (gammaLower ν * X) = (2 : ℂ) • gamM X := by
  simp only [gamM, Matrix.mul_sum]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have h : ∀ ν, gamma ν * (gamma ρ * (gammaLower ν * X) * gammaLower ρ) =
      (gamma ν * gamma ρ * gammaLower ν) * X * gammaLower ρ := fun ν => by
    simp only [Matrix.mul_assoc]
  simp only [h, ← Finset.sum_mul, sum_gamma_gamma_gammaLower, Matrix.smul_mul]

end Sandwich

/-! ### The double pattern -/

/-- **The double pattern** `pp(P, H; W, Z) = ∑_{μν} tr(H_ν W γ^μ Z γ^ν P_μ)`. -/
noncomputable def pp (P H : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (W Z : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ∑ μ, ∑ ν, trace (H ν * W * gamma μ * Z * gamma ν * P μ)

section PPLinear

variable (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (W Z : Matrix (Fin 4) (Fin 4) ℂ)

theorem pp_add (H G : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pp P (fun ν => H ν + G ν) W Z = pp P H W Z + pp P G W Z := by
  simp only [pp, Matrix.add_mul, Matrix.trace_add, Finset.sum_add_distrib]

theorem pp_smul (c : ℂ) (H : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pp P (fun ν => c • H ν) W Z = c * pp P H W Z := by
  simp only [pp, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]

theorem pp_neg (H : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pp P (fun ν => -H ν) W Z = -pp P H W Z := by
  simp only [pp, Matrix.neg_mul, Matrix.trace_neg, Finset.sum_neg_distrib]

theorem pp_sum (H : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ τ, pp P (H τ) W Z = pp P (fun ν => ∑ τ, H τ ν) W Z := by
  simp only [pp, Matrix.sum_mul, Matrix.trace_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]

/-- Moving the left slot into the family. -/
theorem pp_left (H : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pp P H W Z = pp P (mulRightP H W) 𝟙 Z := by
  simp only [pp, mulRightP, Matrix.mul_one]

theorem pp_smul_left (H : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ) :
    pp P H (c • W) Z = c * pp P H W Z := by
  simp only [pp, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Finset.mul_sum]

theorem pp_smul_right (H : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ) :
    pp P H W (c • Z) = c * pp P H W Z := by
  simp only [pp, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Finset.mul_sum]

theorem pp_add_left (H : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (W' : Matrix (Fin 4) (Fin 4) ℂ) :
    pp P H (W + W') Z = pp P H W Z + pp P H W' Z := by
  simp only [pp, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Finset.sum_add_distrib]

theorem pp_sub_left (H : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (W' : Matrix (Fin 4) (Fin 4) ℂ) :
    pp P H (W - W') Z = pp P H W Z - pp P H W' Z := by
  simp only [pp, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Finset.sum_sub_distrib]

theorem pp_neg_left (H : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    pp P H (-W) Z = -pp P H W Z := by
  simp only [pp, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg, Finset.sum_neg_distrib]

end PPLinear

/-! ### Planar families -/

section Families

variable {F G : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {A₀ A₁ B C₀ C₁ D : Pl}

theorem planarPauli_gammaLower : PlanarPauli gammaLower g0L g1 1 :=
  ⟨gammaLower_zero, gammaLower_one, by rw [gammaLower_two, toMat_one, Matrix.one_mul],
    by rw [gammaLower_three, toMat_one, Matrix.one_mul]⟩

theorem planarPauli_add (hF : PlanarPauli F A₀ A₁ B) (hG : PlanarPauli G C₀ C₁ D) :
    PlanarPauli (fun ν => F ν + G ν) (A₀ + C₀) (A₁ + C₁) (B + D) := by
  obtain ⟨f0, f1, f2, f3⟩ := hF
  obtain ⟨g0', g1', g2, g3⟩ := hG
  exact ⟨by simp only [f0, g0', toMat_add], by simp only [f1, g1', toMat_add],
    by simp only [f2, g2, toMat_add, Matrix.add_mul], by simp only [f3, g3, toMat_add, Matrix.add_mul]⟩

theorem planarPauli_smul (hF : PlanarPauli F A₀ A₁ B) (c : ℂ) :
    PlanarPauli (fun ν => c • F ν) (c • A₀) (c • A₁) (c • B) := by
  obtain ⟨f0, f1, f2, f3⟩ := hF
  exact ⟨by simp only [f0, toMat_smul], by simp only [f1, toMat_smul],
    by simp only [f2, toMat_smul, Matrix.smul_mul], by simp only [f3, toMat_smul, Matrix.smul_mul]⟩

theorem planarPauli_neg (hF : PlanarPauli F A₀ A₁ B) :
    PlanarPauli (fun ν => -F ν) (-A₀) (-A₁) (-B) := by
  obtain ⟨f0, f1, f2, f3⟩ := hF
  exact ⟨by simp only [f0, toMat_neg], by simp only [f1, toMat_neg],
    by simp only [f2, toMat_neg, Matrix.neg_mul], by simp only [f3, toMat_neg, Matrix.neg_mul]⟩

theorem planarPauli_congr (hF : PlanarPauli F A₀ A₁ B) (hFG : ∀ ν, G ν = F ν) :
    PlanarPauli G A₀ A₁ B := by
  have : G = F := funext hFG
  rwa [this]

end Families

/-- **The vertex family** `H_ν(Y₀, Y₁) = Γ(Y₀ γ_ν Y₁)`. -/
noncomputable def hfam (Y₀ Y₁ : Matrix (Fin 4) (Fin 4) ℂ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  contractP (mulRightP (mulLeftP Y₀ gammaLower) Y₁)

theorem hfam_apply (Y₀ Y₁ : Matrix (Fin 4) (Fin 4) ℂ) (ν : Fin 4) :
    hfam Y₀ Y₁ ν = gamM (Y₀ * gammaLower ν * Y₁) := rfl

theorem planarPauli_hfam (y₀ y₁ : Pl) :
    PlanarPauli (hfam (toMat y₀) (toMat y₁)) (gam (y₀ * g0L * y₁)) (gam (y₀ * g1 * y₁))
      (gamT (y₀ * 1 * bar y₁)) :=
  planarPauli_contractP (planarPauli_mulRightP (planarPauli_mulLeftP planarPauli_gammaLower y₀) y₁)

/-! ### The planar evaluation of the double pattern -/

/-- The planar value of `pp`. -/
def ppPl (Q₀ Q₁ R A₀ A₁ B w z : Pl) : ℂ :=
  4 * ((A₀ * w * g0 * z * g0 * Q₀).s + (A₁ * w * g0 * z * g1 * Q₀).s +
      (A₀ * w * g1 * z * g0 * Q₁).s + (A₁ * w * g1 * z * g1 * Q₁).s) -
    8 * ((B * bar (w * g0 * z) * Q₀).s + (B * bar (w * g1 * z) * Q₁).s) -
    8 * ((A₀ * w * bar (z * g0 * R)).s + (A₁ * w * bar (z * g1 * R)).s)

section PlanarMoves

variable (M : Matrix (Fin 4) (Fin 4) ℂ) (x y : Pl)

theorem mul_toMat_mul_toMat : M * toMat x * toMat y = M * toMat (x * y) := by
  rw [Matrix.mul_assoc, toMat_mul]

theorem mul_gamma_two_mul_toMat : M * gamma 2 * toMat x = M * toMat (bar x) * gamma 2 := by
  rw [Matrix.mul_assoc, gamma_two_mul_toMat, ← Matrix.mul_assoc]

theorem mul_gamma_three_mul_toMat : M * gamma 3 * toMat x = M * toMat (bar x) * gamma 3 := by
  rw [Matrix.mul_assoc, gamma_three_mul_toMat, ← Matrix.mul_assoc]

theorem mul_gamma_two_mul_gamma_two : M * gamma 2 * gamma 2 = -M := by
  rw [Matrix.mul_assoc, gamma_two_mul_self, Matrix.mul_neg, Matrix.mul_one]

theorem mul_gamma_three_mul_gamma_three : M * gamma 3 * gamma 3 = -M := by
  rw [Matrix.mul_assoc, gamma_three_mul_self, Matrix.mul_neg, Matrix.mul_one]

theorem mul_gamma_three_two_three_two : M * gamma 3 * gamma 2 * gamma 3 * gamma 2 = -M := by
  calc M * gamma 3 * gamma 2 * gamma 3 * gamma 2 = M * (gamma 3 * gamma 2 * gamma 3) * gamma 2 := by
        simp only [Matrix.mul_assoc]
    _ = -M := by rw [gamma_three_two_three, mul_gamma_two_mul_gamma_two]

theorem mul_gamma_two_three_two_three : M * gamma 2 * gamma 3 * gamma 2 * gamma 3 = -M := by
  calc M * gamma 2 * gamma 3 * gamma 2 * gamma 3 = M * (gamma 2 * gamma 3 * gamma 2) * gamma 3 := by
        simp only [Matrix.mul_assoc]
    _ = -M := by rw [gamma_two_three_two, mul_gamma_three_mul_gamma_three]

end PlanarMoves

/-- **The planar evaluation of the double pattern.** -/
theorem pp_planar {P H : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} {Q₀ Q₁ R A₀ A₁ B : Pl}
    (hP : PlanarPauli P Q₀ Q₁ R) (hH : PlanarPauli H A₀ A₁ B) (w z : Pl) :
    pp P H (toMat w) (toMat z) = ppPl Q₀ Q₁ R A₀ A₁ B w z := by
  obtain ⟨p0, p1, p2, p3⟩ := hP
  obtain ⟨h0, h1, h2, h3⟩ := hH
  unfold pp
  simp only [Fin.sum_univ_four, p0, p1, p2, p3, h0, h1, h2, h3, gamma_zero, gamma_one]
  simp only [← Matrix.mul_assoc]
  simp only [mul_gamma_two_mul_toMat, mul_gamma_three_mul_toMat]
  simp only [toMat_mul]
  simp only [mul_gamma_two_mul_gamma_two, mul_gamma_three_mul_gamma_three,
    mul_gamma_three_two_three_two, mul_gamma_two_three_two_three, Matrix.trace_neg, neg_neg,
    trace_toMat]
  unfold ppPl
  simp only [mul_s, mul_a, mul_b, mul_c, bar_s, bar_a, bar_b, bar_c, g0, g1]
  ring

/-! ### The jet of the planar value -/

section Jets

variable {Q₀ Q₁ R A₀ A₁ B W Z : ℝ → Pl} {q₀ q₁ r a₀ a₁ b w z : PJ}

/-- The jet coefficients of `ppPl`. -/
def ppJk (sel : PJ → ℂ) (q₀ q₁ r a₀ a₁ b w z : PJ) : ℂ :=
  4 * (sel (((((a₀.mul w).mul (PJ.c g0)).mul z).mul (PJ.c g0)).mul q₀) +
      sel (((((a₁.mul w).mul (PJ.c g0)).mul z).mul (PJ.c g1)).mul q₀) +
      sel (((((a₀.mul w).mul (PJ.c g1)).mul z).mul (PJ.c g0)).mul q₁) +
      sel (((((a₁.mul w).mul (PJ.c g1)).mul z).mul (PJ.c g1)).mul q₁)) -
    8 * (sel ((b.mul ((w.mul (PJ.c g0)).mul z).bar).mul q₀) +
      sel ((b.mul ((w.mul (PJ.c g1)).mul z).bar).mul q₁)) -
    8 * (sel ((a₀.mul w).mul ((z.mul (PJ.c g0)).mul r).bar) +
      sel ((a₁.mul w).mul ((z.mul (PJ.c g1)).mul r).bar))

/-- The second-order coefficient of `ppPl`. -/
abbrev ppJ (q₀ q₁ r a₀ a₁ b w z : PJ) : ℂ := ppJk PJ.s2 q₀ q₁ r a₀ a₁ b w z

theorem hasJet2_ppPl (hQ₀ : HasPJ Q₀ q₀) (hQ₁ : HasPJ Q₁ q₁) (hR : HasPJ R r)
    (hA₀ : HasPJ A₀ a₀) (hA₁ : HasPJ A₁ a₁) (hB : HasPJ B b) (hW : HasPJ W w) (hZ : HasPJ Z z) :
    HasJet2 (fun u => ppPl (Q₀ u) (Q₁ u) (R u) (A₀ u) (A₁ u) (B u) (W u) (Z u))
      (ppJk PJ.s0 q₀ q₁ r a₀ a₁ b w z) (ppJk PJ.s1 q₀ q₁ r a₀ a₁ b w z)
      (ppJ q₀ q₁ r a₀ a₁ b w z) := by
  have g0' := HasPJ.const g0
  have g1' := HasPJ.const g1
  have h1 := (((((hA₀.mul hW).mul g0').mul hZ).mul g0').mul hQ₀).s
  have h2 := (((((hA₁.mul hW).mul g0').mul hZ).mul g1').mul hQ₀).s
  have h3 := (((((hA₀.mul hW).mul g1').mul hZ).mul g0').mul hQ₁).s
  have h4 := (((((hA₁.mul hW).mul g1').mul hZ).mul g1').mul hQ₁).s
  have h5 := ((hB.mul ((hW.mul g0').mul hZ).bar).mul hQ₀).s
  have h6 := ((hB.mul ((hW.mul g1').mul hZ).bar).mul hQ₁).s
  have h7 := ((hA₀.mul hW).mul ((hZ.mul g0').mul hR).bar).s
  have h8 := ((hA₁.mul hW).mul ((hZ.mul g1').mul hR).bar).s
  exact (((((h1.add h2).add h3).add h4).const_mul 4).sub ((h5.add h6).const_mul 8)).sub
    ((h7.add h8).const_mul 8)

end Jets

end QED.TwoLoop.UnitSCGraph

end
