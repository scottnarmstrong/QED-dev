/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ParamNumEval
public import QED.Algebra.FormFactorIndependence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The canonical parametric numerator of a chain of four affine matrix factors

Infrastructure for stage 1 of section 8 of `docs/TWO-LOOP-UNITS.md`. The numerators of the open
two-loop classes, after the Pauli projection, are traces of chains
`tr(B₀ E₀ B₁ E₁ B₂ E₂ B₃ E₃)` with constant matrices `Bₖ` and four affine factors
`Eₖ(ℓ) = Ēₖ + ∑ₐ ℓₐ Nₖₐ` (the electron propagator numerators). This file gives the explicit
quartic of such a chain, centered at any point (`chainQuartic`, `eval_chainQuartic`), and hence,
with `QED.TwoLoop.ParamNumEval.paramNumOf_eq_shifted`, its canonical parametric numerator:

`paramNumOf F = U⁻² ((m-4)! ch(Ē) + (m-5)!/2 · V ∑_{k<l} ∑ₐ_b ch(Ē; k ↦ Nₖₐ, l ↦ N_lb) Gₐ_b
  + (m-6)!/4 · V² ∑ₐ_bcd ch(N₀ₐ, N₁_b, N₂_c, N₃_d) Πₐ_bcd(G))`

with `Ē = E(-S)` (`paramNumOf_chain4`): the four factors are expanded at the shifted point and the
pairs of linear parts are contracted with `G` (Wick's rule).
-/

@[expose] public section

open Complex Matrix

namespace QED.TwoLoop.ParamNumEval

open QED.Integration.TwoLoop QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Dirac
open QED.TwoLoop.Bridge (electronNumerator)

/-! ### The chain and its quartic -/

/-- The trace chain `tr(B₀ Y₀ B₁ Y₁ B₂ Y₂ B₃ Y₃)`. -/
def ch (B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  trace (B 0 * Y₀ * B 1 * Y₁ * B 2 * Y₂ * B 3 * Y₃)

/-- The affine matrix `Ē + ∑ₐ Xₐ Nₐ`. -/
def affMat (E : Matrix (Fin 4) (Fin 4) ℂ) (N : LoopIndex → Matrix (Fin 4) (Fin 4) ℂ)
    (X : LoopIndex → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  E + ∑ a, X a • N a

/-- **The quartic of a chain of four affine factors** `Ēₖ + ∑ₐ Xₐ Nₖₐ`, expanded at `X = 0`. -/
def chainQuartic (B E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (N : Fin 4 → LoopIndex → Matrix (Fin 4) (Fin 4) ℂ) : LoopQuartic where
  const := ch B (E 0) (E 1) (E 2) (E 3)
  lin a := ch B (N 0 a) (E 1) (E 2) (E 3) + ch B (E 0) (N 1 a) (E 2) (E 3) +
    ch B (E 0) (E 1) (N 2 a) (E 3) + ch B (E 0) (E 1) (E 2) (N 3 a)
  quad a b := ch B (N 0 a) (N 1 b) (E 2) (E 3) + ch B (N 0 a) (E 1) (N 2 b) (E 3) +
    ch B (N 0 a) (E 1) (E 2) (N 3 b) + ch B (E 0) (N 1 a) (N 2 b) (E 3) +
    ch B (E 0) (N 1 a) (E 2) (N 3 b) + ch B (E 0) (E 1) (N 2 a) (N 3 b)
  cub a b c := ch B (N 0 a) (N 1 b) (N 2 c) (E 3) + ch B (N 0 a) (N 1 b) (E 2) (N 3 c) +
    ch B (N 0 a) (E 1) (N 2 b) (N 3 c) + ch B (E 0) (N 1 a) (N 2 b) (N 3 c)
  quart a b c d := ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d)

section Reorder

variable (X : LoopIndex → ℂ)

theorem sum_reorder₁ (T : LoopIndex → ℂ) : ∑ a, T a * X a = ∑ a, X a * T a :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem sum_reorder₂ (T : LoopIndex → LoopIndex → ℂ) :
    ∑ a, ∑ b, T a b * (X a * X b) = ∑ b, X b * ∑ a, X a * T a b := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem sum_reorder₃ (T : LoopIndex → LoopIndex → LoopIndex → ℂ) :
    ∑ a, ∑ b, ∑ c, T a b c * (X a * X b * X c) =
      ∑ c, X c * ∑ b, X b * ∑ a, X a * T a b c := by
  have e : ∀ a, ∑ b, ∑ c, T a b c * (X a * X b * X c) =
      ∑ c, ∑ b, X a * (X b * (X c * T a b c)) := fun a => by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

omit X in
theorem sum_rev₄ (f : LoopIndex → LoopIndex → LoopIndex → LoopIndex → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ c, ∑ b, ∑ a, f a b c d := by
  have h1 : ∀ a b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ c, f a b c d := fun _ _ => Finset.sum_comm
  have h2 : ∀ a, ∑ b, ∑ d, ∑ c, f a b c d = ∑ d, ∑ b, ∑ c, f a b c d := fun _ => Finset.sum_comm
  have h3 : ∀ d b, ∑ a, ∑ c, f a b c d = ∑ c, ∑ a, f a b c d := fun _ _ => Finset.sum_comm
  have h4 : ∀ d, ∑ a, ∑ b, ∑ c, f a b c d = ∑ c, ∑ b, ∑ a, f a b c d := fun d => by
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun b _ => h3 d b).trans ?_
    exact Finset.sum_comm
  simp only [h1, h2]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => h4 d

theorem sum_reorder₄ (T : LoopIndex → LoopIndex → LoopIndex → LoopIndex → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, T a b c d * (X a * X b * X c * X d) =
      ∑ d, X d * ∑ c, X c * ∑ b, X b * ∑ a, X a * T a b c d := by
  have e : ∀ a b c d, T a b c d * (X a * X b * X c * X d) =
      X d * (X c * (X b * (X a * T a b c d))) := fun _ _ _ _ => by ring
  simp only [e]
  rw [sum_rev₄]
  simp only [Finset.mul_sum]

end Reorder

theorem evalC_chainQuartic (B E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (N : Fin 4 → LoopIndex → Matrix (Fin 4) (Fin 4) ℂ) (X : LoopIndex → ℂ) :
    (chainQuartic B E N).evalC X =
      ch B (affMat (E 0) (N 0) X) (affMat (E 1) (N 1) X) (affMat (E 2) (N 2) X)
        (affMat (E 3) (N 3) X) := by
  simp only [LoopQuartic.evalC, chainQuartic, ch, affMat, Matrix.mul_add,
    Matrix.trace_add, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, add_mul, Finset.sum_add_distrib]
  simp only [sum_reorder₁ X, sum_reorder₂ X, sum_reorder₃ X, sum_reorder₄ X]
  ring


theorem eval_chainQuartic (B E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (N : Fin 4 → LoopIndex → Matrix (Fin 4) (Fin 4) ℂ) (D : Fin 2 → Fin 4 → ℝ) :
    (chainQuartic B E N).eval D =
      ch B (affMat (E 0) (N 0) (loopComp D)) (affMat (E 1) (N 1) (loopComp D))
        (affMat (E 2) (N 2) (loopComp D)) (affMat (E 3) (N 3) (loopComp D)) :=
  evalC_chainQuartic B E N (loopComp D)

/-! ### Linearity of the chain in each slot -/

section Slots

variable (B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ)

theorem ch_smul₀ : ch B (c • Y₀) Y₁ Y₂ Y₃ = c * ch B Y₀ Y₁ Y₂ Y₃ := by
  simp [ch, Matrix.trace_smul]

theorem ch_smul₁ : ch B Y₀ (c • Y₁) Y₂ Y₃ = c * ch B Y₀ Y₁ Y₂ Y₃ := by
  simp [ch, Matrix.trace_smul]

theorem ch_smul₂ : ch B Y₀ Y₁ (c • Y₂) Y₃ = c * ch B Y₀ Y₁ Y₂ Y₃ := by
  simp [ch, Matrix.trace_smul]

theorem ch_smul₃ : ch B Y₀ Y₁ Y₂ (c • Y₃) = c * ch B Y₀ Y₁ Y₂ Y₃ := by
  simp [ch, Matrix.trace_smul]

end Slots

/-! ### The electron propagator numerators -/

section Electron

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)

/-- The linear part of the electron numerator `m - k̸ᵢ(ℓ)` of line `i`:
`N_{(s,ν)} = -αᵢₛ γ_ν`, so that `m - k̸ᵢ(c + D) = (m - k̸ᵢ(c)) + ∑ₐ Dₐ Nₐ`. -/
noncomputable def elecLin (i : Fin (m + 1)) (a : LoopIndex) : Matrix (Fin 4) (Fin 4) ℂ :=
  (-((α i a.1 : ℝ) : ℂ)) • gammaLower a.2

theorem slash_loopPart (i : Fin (m + 1)) (D : Fin 2 → Fin 4 → ℝ) :
    slash (fun μ => ∑ s, α i s * D s μ) =
      ∑ a : LoopIndex, ((α i a.1 : ℝ) : ℂ) • (((D a.1 a.2 : ℝ) : ℂ) • gammaLower a.2) := by
  rw [← sum_smul_gammaLower, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Complex.ofReal_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_smul]
  push_cast
  rfl

theorem electronNumerator_lineMomentum_add (mass : ℝ) (i : Fin (m + 1))
    (c D : Fin 2 → Fin 4 → ℝ) :
    electronNumerator mass (lineMomentum α p i (c + D)) =
      affMat (electronNumerator mass (lineMomentum α p i c)) (elecLin α i) (loopComp D) := by
  have hk : lineMomentum α p i (c + D) =
      lineMomentum α p i c + fun μ => ∑ s, α i s * D s μ := by
    funext μ
    simp only [lineMomentum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  have hs : ∑ a, loopComp D a • elecLin α i a =
      -∑ a : LoopIndex, ((α i a.1 : ℝ) : ℂ) • (((D a.1 a.2 : ℝ) : ℂ) • gammaLower a.2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [elecLin, loopComp, smul_smul, neg_smul, smul_neg]
    rw [mul_comm]
  rw [hk, electronNumerator, electronNumerator, slash_add, slash_loopPart, affMat, hs]
  abel

/-- The chain of four electron numerators of lines `i k` with masses `mass k`. -/
noncomputable def elecChain (B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (mass : Fin 4 → ℝ)
    (i : Fin 4 → Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ch B (electronNumerator (mass 0) (lineMomentum α p (i 0) ℓ))
    (electronNumerator (mass 1) (lineMomentum α p (i 1) ℓ))
    (electronNumerator (mass 2) (lineMomentum α p (i 2) ℓ))
    (electronNumerator (mass 3) (lineMomentum α p (i 3) ℓ))

/-- The electron numerators at the point `c`. -/
noncomputable def elecAt (mass : Fin 4 → ℝ) (i : Fin 4 → Fin (m + 1)) (c : Fin 2 → Fin 4 → ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun k => electronNumerator (mass k) (lineMomentum α p (i k) c)

/-- **The electron chain expanded at any point `c`.** -/
theorem eval_chainQuartic_elec (B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (mass : Fin 4 → ℝ)
    (i : Fin 4 → Fin (m + 1)) (c D : Fin 2 → Fin 4 → ℝ) :
    (chainQuartic B (elecAt α p mass i c) (fun k => elecLin α (i k))).eval D =
      elecChain α p B mass i (c + D) := by
  rw [eval_chainQuartic]
  simp only [elecChain, elecAt, electronNumerator_lineMomentum_add]

theorem exists_quartic_elecChain (B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (mass : Fin 4 → ℝ)
    (i : Fin 4 → Fin (m + 1)) : ∃ Q : LoopQuartic, Q.eval = elecChain α p B mass i :=
  ⟨chainQuartic B (elecAt α p mass i 0) (fun k => elecLin α (i k)), funext fun D => by
    rw [eval_chainQuartic_elec, zero_add]⟩

end Electron

/-! ### Contraction of two linear parts -/

section Contract

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)

/-- The contraction coefficient `C_{ij} = ∑ₛᵣ αᵢₛ (A⁻¹)ₛᵣ αⱼᵣ` of two lines. -/
noncomputable def contrC (A : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin (m + 1)) : ℝ :=
  ∑ s, ∑ r, α i s * A⁻¹ s r * α j r

theorem sum_prod_sep (f : Fin 2 → Fin 2 → ℂ) (h : Fin 4 → Fin 4 → ℂ) :
    ∑ a : LoopIndex, ∑ b : LoopIndex, f a.1 b.1 * h a.2 b.2 =
      (∑ s, ∑ r, f s r) * ∑ ν, ∑ ν', h ν ν' := by
  calc ∑ a : LoopIndex, ∑ b : LoopIndex, f a.1 b.1 * h a.2 b.2
      = ∑ s, ∑ ν, ∑ r, ∑ ν', f s r * h ν ν' := by simp only [Fintype.sum_prod_type]
    _ = ∑ s, ∑ r, ∑ ν, ∑ ν', f s r * h ν ν' :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = (∑ s, ∑ r, f s r) * ∑ ν, ∑ ν', h ν ν' := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.mul_sum]

theorem gammaLower_eq_metric_smul (β : Fin 4) :
    gammaLower β = ((Minkowski.metric β β : ℝ) : ℂ) • gamma β := by
  fin_cases β <;> simp [gammaLower, Minkowski.metric]

theorem metric_mul_self' (β : Fin 4) : Minkowski.metric β β * Minkowski.metric β β = 1 := by
  fin_cases β <;> simp [Minkowski.metric]

theorem sum_metric_contract (Φ : Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 4) (Fin 4) ℂ → ℂ)
    (h2 : ∀ (c : ℂ) X Y, Φ X (c • Y) = c * Φ X Y) :
    ∑ ν, ∑ ν', ((Minkowski.metric ν ν' : ℝ) : ℂ) * Φ (gammaLower ν) (gammaLower ν') =
      ∑ ν, Φ (gammaLower ν) (gamma ν) := by
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hd : ∀ ν', ((Minkowski.metric ν ν' : ℝ) : ℂ) * Φ (gammaLower ν) (gammaLower ν') =
      if ν' = ν then ((Minkowski.metric ν ν : ℝ) : ℂ) * Φ (gammaLower ν) (gammaLower ν) else 0 :=
    fun ν' => by
      by_cases h : ν' = ν
      · subst h; simp
      · simp [h, Minkowski.metric, Ne.symm h]
  rw [Finset.sum_congr rfl fun ν' _ => hd ν', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  rw [← h2, gammaLower_eq_metric_smul ν, smul_smul, ← ofReal_mul, metric_mul_self', ofReal_one,
    one_smul]

/-- **Contraction of two electron linear parts with `G = loopMetricInv A`**: for `Φ` bilinear,
`∑ₐ_b Φ(Nᵢₐ, Nⱼ_b) Gₐ_b = C_{ij} ∑_ν Φ(γ_ν, γ^ν)`. -/
theorem sum_contract (A : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin (m + 1))
    (Φ : Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 4) (Fin 4) ℂ → ℂ)
    (h1 : ∀ (c : ℂ) X Y, Φ (c • X) Y = c * Φ X Y) (h2 : ∀ (c : ℂ) X Y, Φ X (c • Y) = c * Φ X Y) :
    ∑ a, ∑ b, Φ (elecLin α i a) (elecLin α j b) * ((loopMetricInv A a b : ℝ) : ℂ) =
      (contrC α A i j : ℂ) * ∑ ν, Φ (gammaLower ν) (gamma ν) := by
  have e : ∀ a b : LoopIndex, Φ (elecLin α i a) (elecLin α j b) * ((loopMetricInv A a b : ℝ) : ℂ) =
      (((α i a.1 : ℝ) : ℂ) * ((A⁻¹ a.1 b.1 : ℝ) : ℂ) * ((α j b.1 : ℝ) : ℂ)) *
        (((Minkowski.metric a.2 b.2 : ℝ) : ℂ) * Φ (gammaLower a.2) (gammaLower b.2)) :=
    fun a b => by
      simp only [elecLin, h1, h2, loopMetricInv]
      push_cast
      ring
  simp only [e]
  rw [sum_prod_sep (fun s r => ((α i s : ℝ) : ℂ) * ((A⁻¹ s r : ℝ) : ℂ) * ((α j r : ℝ) : ℂ))
    (fun ν ν' => ((Minkowski.metric ν ν' : ℝ) : ℂ) * Φ (gammaLower ν) (gammaLower ν')),
    sum_metric_contract Φ h2, contrC]
  push_cast
  rfl

end Contract


/-! ### The contracted chains -/

section Contracted

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (B E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (i : Fin 4 → Fin (m + 1)) (A : Matrix (Fin 2) (Fin 2) ℝ)

/-- The single contractions: `∑_{k<l} C_{kl} ∑_ν ch(Ē; k ↦ γ_ν, l ↦ γ^ν)`. -/
noncomputable def chainTwo : ℂ :=
  (contrC α A (i 0) (i 1) : ℂ) * ∑ ν, ch B (gammaLower ν) (gamma ν) (E 2) (E 3) +
    (contrC α A (i 0) (i 2) : ℂ) * ∑ ν, ch B (gammaLower ν) (E 1) (gamma ν) (E 3) +
    (contrC α A (i 0) (i 3) : ℂ) * ∑ ν, ch B (gammaLower ν) (E 1) (E 2) (gamma ν) +
    (contrC α A (i 1) (i 2) : ℂ) * ∑ ν, ch B (E 0) (gammaLower ν) (gamma ν) (E 3) +
    (contrC α A (i 1) (i 3) : ℂ) * ∑ ν, ch B (E 0) (gammaLower ν) (E 2) (gamma ν) +
    (contrC α A (i 2) (i 3) : ℂ) * ∑ ν, ch B (E 0) (E 1) (gammaLower ν) (gamma ν)

/-- The double contractions over the three pairings of the four slots. -/
noncomputable def chainFour : ℂ :=
  (contrC α A (i 0) (i 1) : ℂ) * (contrC α A (i 2) (i 3) : ℂ) *
      ∑ ν, ∑ ρ, ch B (gammaLower ν) (gamma ν) (gammaLower ρ) (gamma ρ) +
    (contrC α A (i 0) (i 2) : ℂ) * (contrC α A (i 1) (i 3) : ℂ) *
      ∑ ν, ∑ ρ, ch B (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ) +
    (contrC α A (i 0) (i 3) : ℂ) * (contrC α A (i 1) (i 2) : ℂ) *
      ∑ ν, ∑ ρ, ch B (gammaLower ν) (gammaLower ρ) (gamma ρ) (gamma ν)

theorem quad_contract :
    ∑ a, ∑ b, (chainQuartic B E (fun k => elecLin α (i k))).quad a b *
        ((loopMetricInv A a b : ℝ) : ℂ) = chainTwo α B E i A := by
  simp only [chainQuartic, add_mul, Finset.sum_add_distrib]
  rw [sum_contract α A (i 0) (i 1) (fun X Y => ch B X Y (E 2) (E 3))
      (fun c X Y => ch_smul₀ B c X Y _ _) (fun c X Y => ch_smul₁ B c X Y _ _),
    sum_contract α A (i 0) (i 2) (fun X Y => ch B X (E 1) Y (E 3))
      (fun c X Y => ch_smul₀ B c X _ Y _) (fun c X Y => ch_smul₂ B c X _ Y _),
    sum_contract α A (i 0) (i 3) (fun X Y => ch B X (E 1) (E 2) Y)
      (fun c X Y => ch_smul₀ B c X _ _ Y) (fun c X Y => ch_smul₃ B c X _ _ Y),
    sum_contract α A (i 1) (i 2) (fun X Y => ch B (E 0) X Y (E 3))
      (fun c X Y => ch_smul₁ B c _ X Y _) (fun c X Y => ch_smul₂ B c _ X Y _),
    sum_contract α A (i 1) (i 3) (fun X Y => ch B (E 0) X (E 2) Y)
      (fun c X Y => ch_smul₁ B c _ X _ Y) (fun c X Y => ch_smul₃ B c _ X _ Y),
    sum_contract α A (i 2) (i 3) (fun X Y => ch B (E 0) (E 1) X Y)
      (fun c X Y => ch_smul₂ B c _ _ X Y) (fun c X Y => ch_smul₃ B c _ _ X Y)]
  rfl

theorem contractFour_chainQuartic :
    (chainQuartic B E (fun k => elecLin α (i k))).contractFour A = chainFour α B i A := by
  set G : LoopIndex → LoopIndex → ℂ := fun a b => ((loopMetricInv A a b : ℝ) : ℂ) with hG
  set N : Fin 4 → LoopIndex → Matrix (Fin 4) (Fin 4) ℂ := fun k => elecLin α (i k) with hN
  set C : Fin 4 → Fin 4 → ℂ := fun k l => (contrC α A (i k) (i l) : ℂ) with hC
  have hsplit : (chainQuartic B E N).contractFour A =
      (∑ a, ∑ b, ∑ c, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * (G a b * G c d)) +
      (∑ a, ∑ b, ∑ c, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * (G a c * G b d)) +
      (∑ a, ∑ b, ∑ c, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * (G a d * G b c)) := by
    simp only [LoopQuartic.contractFour, chainQuartic, matPair, hG]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
  -- linearity of the partially contracted chains
  have l0 : ∀ (c : ℂ) X Y Z W, ch B (c • X) Y Z W = c * ch B X Y Z W := fun c X Y Z W =>
    ch_smul₀ B c X Y Z W
  have l1 : ∀ (c : ℂ) X Y Z W, ch B X (c • Y) Z W = c * ch B X Y Z W := fun c X Y Z W =>
    ch_smul₁ B c X Y Z W
  have l2 : ∀ (c : ℂ) X Y Z W, ch B X Y (c • Z) W = c * ch B X Y Z W := fun c X Y Z W =>
    ch_smul₂ B c X Y Z W
  have l3 : ∀ (c : ℂ) X Y Z W, ch B X Y Z (c • W) = c * ch B X Y Z W := fun c X Y Z W =>
    ch_smul₃ B c X Y Z W
  -- the pairing `(01)(23)`
  have s1 : (∑ a, ∑ b, ∑ c, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * (G a b * G c d)) =
      C 0 1 * C 2 3 * ∑ ν, ∑ ρ, ch B (gammaLower ν) (gamma ν) (gammaLower ρ) (gamma ρ) := by
    have hin : ∀ a b, ∑ c, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * G c d =
        C 2 3 * ∑ ρ, ch B (N 0 a) (N 1 b) (gammaLower ρ) (gamma ρ) := fun a b =>
      sum_contract α A (i 2) (i 3) (fun X Y => ch B (N 0 a) (N 1 b) X Y)
        (fun c X Y => l2 c _ _ X Y) (fun c X Y => l3 c _ _ X Y)
    have hout := sum_contract α A (i 0) (i 1)
      (fun X Y => ∑ ρ, ch B X Y (gammaLower ρ) (gamma ρ))
      (fun c X Y => by simp only [l0, Finset.mul_sum]) (fun c X Y => by simp only [l1, Finset.mul_sum])
    calc (∑ a, ∑ b, ∑ c, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * (G a b * G c d))
        = ∑ a, ∑ b, (∑ c, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * G c d) * G a b := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          simp only [Finset.sum_mul]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
      _ = C 2 3 * ∑ a, ∑ b, (∑ ρ, ch B (N 0 a) (N 1 b) (gammaLower ρ) (gamma ρ)) * G a b := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hin a b]
          ring
      _ = _ := by
          rw [hout]
          ring
  -- the pairing `(02)(13)`
  have s2 : (∑ a, ∑ b, ∑ c, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * (G a c * G b d)) =
      C 0 2 * C 1 3 * ∑ ν, ∑ ρ, ch B (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ) := by
    have hin : ∀ a c, ∑ b, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * G b d =
        C 1 3 * ∑ ρ, ch B (N 0 a) (gammaLower ρ) (N 2 c) (gamma ρ) := fun a c =>
      sum_contract α A (i 1) (i 3) (fun X Y => ch B (N 0 a) X (N 2 c) Y)
        (fun c' X Y => l1 c' _ X _ Y) (fun c' X Y => l3 c' _ X _ Y)
    have hout := sum_contract α A (i 0) (i 2)
      (fun X Y => ∑ ρ, ch B X (gammaLower ρ) Y (gamma ρ))
      (fun c X Y => by simp only [l0, Finset.mul_sum]) (fun c X Y => by simp only [l2, Finset.mul_sum])
    calc (∑ a, ∑ b, ∑ c, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * (G a c * G b d))
        = ∑ a, ∑ c, (∑ b, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * G b d) * G a c := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring
      _ = C 1 3 * ∑ a, ∑ c, (∑ ρ, ch B (N 0 a) (gammaLower ρ) (N 2 c) (gamma ρ)) * G a c := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hin a b]
          ring
      _ = _ := by
          rw [hout]
          ring
  -- the pairing `(03)(12)`
  have s3 : (∑ a, ∑ b, ∑ c, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * (G a d * G b c)) =
      C 0 3 * C 1 2 * ∑ ν, ∑ ρ, ch B (gammaLower ν) (gammaLower ρ) (gamma ρ) (gamma ν) := by
    have hin : ∀ a d, ∑ b, ∑ c, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * G b c =
        C 1 2 * ∑ ρ, ch B (N 0 a) (gammaLower ρ) (gamma ρ) (N 3 d) := fun a d =>
      sum_contract α A (i 1) (i 2) (fun X Y => ch B (N 0 a) X Y (N 3 d))
        (fun c' X Y => l1 c' _ X Y _) (fun c' X Y => l2 c' _ X Y _)
    have hout := sum_contract α A (i 0) (i 3)
      (fun X Y => ∑ ρ, ch B X (gammaLower ρ) (gamma ρ) Y)
      (fun c X Y => by simp only [l0, Finset.mul_sum]) (fun c X Y => by simp only [l3, Finset.mul_sum])
    calc (∑ a, ∑ b, ∑ c, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * (G a d * G b c))
        = ∑ a, ∑ d, (∑ b, ∑ c, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * G b c) * G a d := by
          refine Finset.sum_congr rfl fun a _ => ?_
          have e : ∀ b, ∑ c, ∑ d, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * (G a d * G b c) =
              ∑ d, ∑ c, ch B (N 0 a) (N 1 b) (N 2 c) (N 3 d) * (G a d * G b c) := fun b =>
            Finset.sum_comm
          simp only [e]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          simp only [Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
      _ = C 1 2 * ∑ a, ∑ d, (∑ ρ, ch B (N 0 a) (gammaLower ρ) (gamma ρ) (N 3 d)) * G a d := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hin a b]
          ring
      _ = _ := by
          rw [hout]
          ring
  rw [hsplit, s1, s2, s3]
  rfl

end Contracted


/-! ### The canonical parametric numerator of an electron chain -/

section Main

variable {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ) (x : Fin m → ℝ)

/-- **Wick's rule for a chain of four electron propagator numerators.** For the numerator
`F(ℓ) = tr(B₀ E₀(ℓ) B₁ E₁(ℓ) B₂ E₂(ℓ) B₃ E₃(ℓ))`, `Eₖ(ℓ) = mₖ - k̸_{iₖ}(ℓ)`,

`paramNumOf F = U⁻² ((m-4)! ch(Ē) + (m-5)!/2 · V · chainTwo + (m-6)!/4 · V² · chainFour)`,

with `Ē = E(-S)` the numerators at the shifted loop momenta, `chainTwo` the six single
contractions `C_{kl} ∑_ν ch(Ē; k ↦ γ_ν, l ↦ γ^ν)` and `chainFour` the three double contractions,
`C_{kl} = ∑ₛᵣ α_{iₖ s} (A⁻¹)ₛᵣ α_{iₗ r}`. -/
theorem paramNumOf_elecChain (B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (mass : Fin 4 → ℝ)
    (i : Fin 4 → Fin (m + 1)) :
    paramNumOf (elecChain α p B mass i) α p M x =
      ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((m - 4).factorial : ℂ) *
            ch B (elecAt α p mass i (-loopShift α p (simplexPoint x)) 0)
              (elecAt α p mass i (-loopShift α p (simplexPoint x)) 1)
              (elecAt α p mass i (-loopShift α p (simplexPoint x)) 2)
              (elecAt α p mass i (-loopShift α p (simplexPoint x)) 3) +
          ((m - 5).factorial : ℂ) / 2 *
            chainTwo α B (elecAt α p mass i (-loopShift α p (simplexPoint x))) i
              (symanzikMatrix α (simplexPoint x)) *
            ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) +
          ((m - 6).factorial : ℂ) / 4 * chainFour α B i (symanzikMatrix α (simplexPoint x)) *
            ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) ^ 2) := by
  rw [paramNumOf_eq_shifted α p M x (exists_quartic_elecChain α p B mass i)
    (Q' := chainQuartic B (elecAt α p mass i (-loopShift α p (simplexPoint x)))
      (fun k => elecLin α (i k)))
    (fun D => eval_chainQuartic_elec α p B mass i _ D),
    quad_contract, contractFour_chainQuartic]
  rfl

end Main

end QED.TwoLoop.ParamNumEval

end
