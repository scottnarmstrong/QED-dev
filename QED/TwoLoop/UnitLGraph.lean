/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ParamNumEvalChain
public import QED.TwoLoop.PauliZeroExplicitOpen
import Mathlib.Tactic.Ring

/-!
# The ladder graph: its projected parametric numerator by Wick's rule

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the L link, graph half, first step. The ladder
value is `openZero .L P = ∫_{Δ₇} c₂[N(x, ·)] / V(x)⁴` with
`N(x, u) = ∑ⱼ wⱼ(u) (-π⁴) paramNumOf (F_{u,j}) α p(u) M x` (`openNum`), `F_{u,j}` the entries of the
class numerator at `p'(u)` and `wⱼ` the Pauli weights. This file evaluates `N` by the Dirac and
Gaussian-moment algebra:

* `sum_pauliWt_mul`: the Pauli weights are a trace, `∑ᵢⱼ w_{μij} Xᵢⱼ = tr(X P_μ)` with
  `P_μ = m(4m² + q²) N(p) γ_μ N(p') + (q² - 2m²)(p' + p)_μ N(p) N(p')` (`pauliMat`);
* `sum_pauliWt_openF_L`: the projected ladder numerator is a combination of electron chains,
  `∑ⱼ wⱼ F_{u,j}(ℓ) = κ ∑_μ ∑_l c_{μ,l} tr(B_{μ,l,0} E₃ B_{μ,l,1} E₂ B_{μ,l,2} E₁ B_{μ,l,3} E₀)`,
  `κ = (2π)⁻⁸ (ie)⁵ (1/i)⁴`, with `c_{μ,l}` the photon weights of the pairing of `L`
  (`ladderWeight`) and `B_{μ,l} = (γ^{l₀} P_μ γ^{l₄}, γ^{l₃}, γ^{l₂}, γ^{l₁})` (`ladderB`);
* `openNum_L_eq`: hence
  `N(x, u) = -π⁴ κ ∑_μ ∑_l c_{μ,l} paramNumOf (chain_{μ,l}) α p(u) M x`, and with Wick's rule
  (`QED.TwoLoop.ParamNumEval.paramNumOf_elecChain`) the explicit form `openNum_L_explicit`:
  `N(x, u) = -π⁴ κ ∑_μ ∑_l c_{μ,l} U⁻² (6 ch(Ē) + V · chainTwo + V²/4 · chainFour)`, with
  `Ē = E(-S)` the four electron numerators at the shifted loop momenta and the contractions
  `C_{kl} = α_k A⁻¹ α_l`.

**What remains for the graph half** (numerically confirmed, not proved). Write `z_A = z₀ + z₃`,
`z_B = z₁ + z₂` (outer and inner electron pairs), `z_a = z₄ + z₆`, `z_b = z₅ + z₇` (outer and
inner photon, each a Pauli–Villars pair), and, at `m = 1`, `e = 1`, in the frame `z_B + z_b = 1`
(the general case by homogeneity), `Y = z_B`, `c = Y(1-Y)`, `a = z_A + c`, `U = a + z_a`,
`Q₀ = (3Y-2)a² + (4Y-Y²-2)a z_a - 2c z_a²`. With `paramNum = T₁ + T₂ V + T₃ V²` of the projected
numerator, the second-order coefficients are

`c₂[T₁] = (Λ² - m_γ²)² · (6/K) · z_a Q₀/(2U⁵)`, `c₂[T₂] = (Λ² - m_γ²)² · (2/K) · z_a (9c+a)/(2U⁴)`,
`c₂[T₃] = 0`, `K = 16π⁴/(64 i)`,

independent of the splits of the electron pairs (checked at random points to `10⁻¹⁰`; the
`c₂` of `V` and the cross terms vanish since `V` is even in `u`). Integrating over the four
splits (the electron pairs give the factor `z_A z_B`, the Pauli–Villars pairs the differences
`∫₀¹ w ds (V_Λ + s w (m_γ² - Λ²))⁻ⁿ`) turns `c₂[N]/V⁴` into the signed sum over the photon masses
of `z_A z_B (c₂[T₁]/(6V²) + c₂[T₂]/(2V))/(Λ² - m_γ²)²`, which is
`(1/K)` times the integrand `f_L` of eq. (3.1) of `docs/TWO-LOOP-UNITS.md`; this was checked
against the engine of `scripts/numerics/two_loop_unit_integrals.py` at random points (agreement
`10⁻¹⁰`). The steps left are: (i) the Dirac traces of the contracted chains in
`openNum_L_explicit` (all momenta lie in the plane of `p, p'`) and the second-order jets in `u`
(`QED/TwoLoop/ParamNumEvalJet.lean`), giving the formulas above pointwise; (ii) the integration
over the splits and the Cheng–Wu change of variables to eq. (3.1).
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitLGraph

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.ParamNumEval
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic castLoopMatrix class5LoopMatrixPV symanzikV symanzikU
  symanzikMatrix lineMomentum loopShift)

/-! ### The Pauli weights as a trace -/

/-- The matrix of the Pauli weights:
`P_μ = m(4m² + q²) N(p) γ_μ N(p') + (q² - 2m²)(p' + p)_μ N(p) N(p')`, `N(k) = m - k̸`. -/
noncomputable def pauliMat (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((m : ℂ) * (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ))) •
      (electronNumerator m p * gammaLower μ * electronNumerator m p') +
    (((Minkowski.dot (p' - p) (p' - p) : ℂ) - 2 * (m : ℂ) ^ 2) *
      ((Minkowski.lower (p' + p) μ : ℝ) : ℂ)) • (electronNumerator m p * electronNumerator m p')

theorem pauliWt_eq_pauliMat (m : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    pauliWt m p' p μ i j = pauliMat m p' p μ j i := by
  simp only [pauliWt, pauliMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- **The Pauli weights are a trace**: `∑ᵢⱼ w_{μij} Xᵢⱼ = tr(X P_μ)`. -/
theorem sum_pauliWt_mul (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ i, ∑ j, pauliWt m p' p μ i j * X i j = trace (X * pauliMat m p' p μ) := by
  simp only [pauliWt_eq_pauliMat, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

/-! ### The ladder chain -/

/-- The photon weight of the ladder pairing (external photon at vertex `2`, photons `0–4` and
`1–3`): `c_{μ,l} = [l₂ = μ] η'_{l₀ l₄} η'_{l₁ l₃}`. -/
noncomputable def ladderWeight (P : Params) (μ : Fin 4) (l : Fin 5 → Fin 4) : ℂ :=
  kron μ (l (permL 0)) * pvEta P (l (permL 1)) (l (permL 2)) * pvEta P (l (permL 3)) (l (permL 4))

/-- The constant matrices of the ladder chain, after the cyclic move of `γ^{l₀}` and the Pauli
matrix: `(γ^{l₀} P_μ γ^{l₄}, γ^{l₃}, γ^{l₂}, γ^{l₁})`. -/
noncomputable def ladderB (m : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) (l : Fin 5 → Fin 4) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![gamma (l 0) * pauliMat m p' p μ * gamma (l 4), gamma (l 3), gamma (l 2), gamma (l 1)]

/-- The lines of the Pauli–Villars form carrying the four chain slots: `E₃, E₂, E₁, E₀`. -/
def ladderLines : Fin 4 → Fin 8 := ![3, 2, 1, 0]

/-- The loop matrix of the Pauli–Villars form of the ladder. -/
noncomputable abbrev ladderAlpha : Fin 8 → Fin 2 → ℝ := castLoopMatrix (class5LoopMatrixPV .L)

/-- The overall constant `κ = (2π)⁻⁸ (ie)⁵ (1/i)⁴`. -/
noncomputable def ladderConst (P : Params) : ℂ := twoLoopNorm * ((I * P.e) ^ 5 * (1 / I) ^ 4)

theorem trace_openChain_mul (G : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    trace (openChain G E * X) = ch ![G 0 * X * G 4, G 3, G 2, G 1] (E 3) (E 2) (E 1) (E 0) := by
  have h1 : openChain G E * X =
      (G 4 * E 3 * G 3 * E 2 * G 2 * E 1 * G 1 * E 0) * (G 0 * X) := by
    simp only [openChain, Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  simp only [ch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.mul_assoc]

theorem classMomE_L_eq (p p' : Fin 4 → ℝ) (k : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    classMomE .L p p' ℓ (.inl (lineL k)) =
      lineMomentum ladderAlpha (pvMomentaE .L p p') (ladderLines (3 - k)) ℓ := by
  fin_cases k <;> rfl

theorem sum_sum_sum_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c :=
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm

/-- **The projected ladder numerator as a combination of electron chains.** -/
theorem sum_pauliWt_openF_L (P : Params) (p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ j : Idx, pauliWt P.m p' (restMomentum P.m) j.1 j.2.1 j.2.2 * openF .L P p' j ℓ =
      ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4, ladderWeight P μ l *
        elecChain ladderAlpha (pvMomentaE .L (restMomentum P.m) p')
          (ladderB P.m p' (restMomentum P.m) μ l) (fun _ => P.m) ladderLines ℓ := by
  have hF : ∀ j : Idx, openF .L P p' j ℓ = ladderConst P *
      ∑ l : Fin 5 → Fin 4, ladderWeight P j.1 l *
        openChain (fun t => gamma (l t))
          (fun i => electronNumerator P.m (classMomE .L (restMomentum P.m) p' ℓ (.inl (lineL i))))
          j.2.1 j.2.2 := fun j => by
    simp only [openF, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul, chain_L,
      chainNum, Matrix.sum_apply, ladderConst, ladderWeight]
    ring
  simp only [hF, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e : ∀ i j, pauliWt P.m p' (restMomentum P.m) μ i j * (ladderConst P *
      ∑ l : Fin 5 → Fin 4, ladderWeight P μ l *
        openChain (fun t => gamma (l t))
          (fun i => electronNumerator P.m (classMomE .L (restMomentum P.m) p' ℓ (.inl (lineL i))))
          i j) =
      ladderConst P * ∑ l : Fin 5 → Fin 4, ladderWeight P μ l *
        (pauliWt P.m p' (restMomentum P.m) μ i j *
          openChain (fun t => gamma (l t))
            (fun i => electronNumerator P.m (classMomE .L (restMomentum P.m) p' ℓ (.inl (lineL i))))
            i j) := fun i j => by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [e, ← Finset.mul_sum]
  congr 1
  rw [sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [← Finset.mul_sum, sum_pauliWt_mul, trace_openChain_mul, classMomE_L_eq]
  rfl


/-! ### The projected parametric numerator of the ladder -/

theorem exists_quartic_openF_L (P : Params) (p' : Fin 4 → ℝ) (j : Idx) :
    ∃ Q : LoopQuartic, Q.eval = openF .L P p' j := by
  have hc : Class5.L ∈ QED.TwoLoop.ClassIntegrable.openClasses := by decide
  obtain ⟨Q, hQ⟩ := ((QED.TwoLoop.ClassIntegrable.isLoopPoly_classNumeratorE hc P
    (fun _ => p') (fun _ => restMomentum P.m) (fun _ => p' - restMomentum P.m) (fun _ => j.2.1)
    (fun _ => j.2.2) (fun _ => j.1)).const_mul twoLoopNorm).exists_loopQuartic
  refine ⟨Q, hQ.trans (funext fun ℓ => ?_)⟩
  simp only [openF, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul]

/-- The ladder chain at the Pauli index `μ` and Lorentz indices `l`, along the curve. -/
noncomputable def ladderChain (P : Params) (u : ℝ) (μ : Fin 4) (l : Fin 5 → Fin 4) :
    (Fin 2 → Fin 4 → ℝ) → ℂ :=
  elecChain ladderAlpha (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u))
    (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l) (fun _ => P.m) ladderLines

/-- **The projected parametric numerator of the ladder as a combination of chain numerators**:
`N(x, u) = -π⁴ κ ∑_μ ∑_l c_{μ,l} paramNumOf (chain_{μ,l})`. -/
theorem openNum_L_eq (P : Params) (x : Fin 7 → ℝ) (u : ℝ) :
    openNum .L P x u = -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4,
      ladderWeight P μ l * paramNumOf (ladderChain P u μ l) ladderAlpha
        (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u)) (pvMasses P) x := by
  set α := ladderAlpha
  set pm := pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u)
  have hq : ∀ μ l, ∃ Q : LoopQuartic, Q.eval = ladderChain P u μ l := fun μ l =>
    exists_quartic_elecChain _ _ _ _ _
  have hqμ : ∀ μ, ∃ Q : LoopQuartic,
      Q.eval = fun ℓ => ∑ l : Fin 5 → Fin 4, ladderWeight P μ l * ladderChain P u μ l ℓ :=
    fun μ => exists_quartic_sum _ _ (hq μ)
  have h1 : openNum .L P x u = -((π : ℂ) ^ 4) * paramNumOf (fun ℓ => ∑ j : Idx,
      pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
        openF .L P (curveMomentum P.m u) j ℓ) α pm (pvMasses P) x := by
    rw [paramNumOf_sum _ _ _ _ _ _ fun j => exists_quartic_openF_L P _ j, openNum,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (fun ℓ => ∑ j : Idx,
      pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
        openF .L P (curveMomentum P.m u) j ℓ) =
      fun ℓ => ladderConst P * ∑ μ, (1 : ℂ) *
        ∑ l : Fin 5 → Fin 4, ladderWeight P μ l * ladderChain P u μ l ℓ := by
    funext ℓ
    rw [sum_pauliWt_openF_L]
    simp only [one_mul]
    rfl
  rw [h1, h2, paramNumOf_const_mul _ _ _ _ _ (exists_quartic_sum _ _ hqμ),
    paramNumOf_sum _ _ _ _ _ _ hqμ]
  simp only [one_mul]
  rw [mul_assoc]
  congr 2
  exact Finset.sum_congr rfl fun μ _ => paramNumOf_sum _ _ _ _ _ _ (hq μ)

/-- **The projected parametric numerator of the ladder, explicit** (Wick's rule): with
`Ē_{μ,l} = E(-S)` the four electron numerators at the shifted loop momenta,
`N(x, u) = -π⁴ κ ∑_μ ∑_l c_{μ,l} U⁻² (6 ch(Ē) + V chainTwo + ¼ V² chainFour)`. -/
theorem openNum_L_explicit (P : Params) (x : Fin 7 → ℝ) (u : ℝ) :
    openNum .L P x u = -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4,
      ladderWeight P μ l *
        (((symanzikU ladderAlpha (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
          (6 * ch (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
              (elecAt ladderAlpha (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u))
                (fun _ => P.m) ladderLines (-loopShift ladderAlpha
                  (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u)) (simplexPoint x)) 0)
              (elecAt ladderAlpha (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u))
                (fun _ => P.m) ladderLines (-loopShift ladderAlpha
                  (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u)) (simplexPoint x)) 1)
              (elecAt ladderAlpha (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u))
                (fun _ => P.m) ladderLines (-loopShift ladderAlpha
                  (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u)) (simplexPoint x)) 2)
              (elecAt ladderAlpha (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u))
                (fun _ => P.m) ladderLines (-loopShift ladderAlpha
                  (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u)) (simplexPoint x)) 3) +
            chainTwo ladderAlpha (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
                (elecAt ladderAlpha (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u))
                  (fun _ => P.m) ladderLines (-loopShift ladderAlpha
                    (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u)) (simplexPoint x)))
                ladderLines (symanzikMatrix ladderAlpha (simplexPoint x)) *
              ((symanzikV ladderAlpha (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u))
                (pvMasses P) (simplexPoint x) : ℝ) : ℂ) +
            1 / 4 * chainFour ladderAlpha (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
                ladderLines (symanzikMatrix ladderAlpha (simplexPoint x)) *
              ((symanzikV ladderAlpha (pvMomentaE .L (restMomentum P.m) (curveMomentum P.m u))
                (pvMasses P) (simplexPoint x) : ℝ) : ℂ) ^ 2)) := by
  rw [openNum_L_eq]
  simp only [ladderChain, paramNumOf_elecChain]
  norm_num [Nat.factorial]

end QED.TwoLoop.UnitLGraph

end
