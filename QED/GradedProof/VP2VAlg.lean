/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2FAlg
public import QED.GradedProof.SE2TwoLoopGggg
public import QED.TwoLoop.ClassIntegrableVP

/-!
# The two-loop classes `VA`, `VB`, `VC`: algebra and integrable pieces

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 2, for the classes
`VA`, `VB`, `VC` (one closed electron loop through four `gauge` vertices with one internal
photon). For one loop flavour of mass `M` the integrand is a constant times the photon factor
`D_{m_γ}(q)⁻¹ D_Λ(q)⁻¹` times `N(M) ∏_{l < 4} D_M(y_l)⁻¹`, with
`N(M) = Tr[A₀ (M - y̸₀) A₁ (M - y̸₁) A₂ (M - y̸₂) A₃ (M - y̸₃)]`.

* `trace4_expand`: `N(M) = E₀ + M² E₂ + M⁴ E₄` (odd traces vanish), with `E₂` of degree `2` and
  `E₄` constant.
* `dd1`, `dd2`, `tri_eq_dd2`, `dd2_mul`: divided differences; `tri_v_eq`: the three-flavour
  Pauli–Villars combination is `(s₁ - s₀)(s₂ - s₀)` times the second divided difference in the
  squared mass, a sum of ten products of six inverse denominators (numerator `N(M)`), four of
  five (numerator `E₂ + (s₀ + s₁) E₄`) and one of four (numerator `E₄`).
* `jef_pieceA`, `jef_pieceB`: such products over the line data of a class (rows `base`, shifts
  `pp`) are integrable in both stages (T₉′), by the refined two-loop theorems (quartic with eight
  lines, cubic with seven), under the decidable criteria.
* `jef_vBlock`: the block-summed flavour sum of one class integrand is integrable.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.VP2

open QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat jointEnergyFirstIntegrable_add)
open QED.Integration.TwoLoop (lineMomentum lineDenom castLoopMatrix RefinedBound
  IntNoSubdivergenceRefined LoopQuartic refinedBound_lineMomentum)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### Divided differences -/

/-- The first divided difference. -/
noncomputable def dd1 (f : ℂ → ℂ) (x y : ℂ) : ℂ := (f y - f x) / (y - x)

/-- The second divided difference. -/
noncomputable def dd2 (f : ℂ → ℂ) (x y z : ℂ) : ℂ := (dd1 f y z - dd1 f x y) / (z - x)

section DD

variable {x y z : ℂ} (hxy : x - y ≠ 0) (hxz : x - z ≠ 0) (hyz : y - z ≠ 0)
include hxy hxz hyz

/-- The three-point Pauli–Villars combination is a multiple of the second divided difference. -/
theorem tri_eq_dd2 (f : ℂ → ℂ) :
    f x + (z - x) / (y - z) * f y + (x - y) / (y - z) * f z =
      (y - x) * (z - x) * dd2 f x y z := by
  have h1 : y - x ≠ 0 := fun h => hxy (by linear_combination -h)
  have h2 : z - x ≠ 0 := fun h => hxz (by linear_combination -h)
  have h3 : z - y ≠ 0 := fun h => hyz (by linear_combination -h)
  unfold dd2 dd1
  field_simp
  ring

/-- The Leibniz rule for the second divided difference. -/
theorem dd2_mul (f g : ℂ → ℂ) :
    dd2 (fun s => f s * g s) x y z = f x * dd2 g x y z + dd1 f x y * dd1 g y z +
      dd2 f x y z * g z := by
  have h1 : y - x ≠ 0 := fun h => hxy (by linear_combination -h)
  have h2 : z - x ≠ 0 := fun h => hxz (by linear_combination -h)
  have h3 : z - y ≠ 0 := fun h => hyz (by linear_combination -h)
  unfold dd2 dd1
  field_simp
  ring

end DD

/-- The Leibniz rule for the first divided difference. -/
theorem dd1_mul {x y : ℂ} (hxy : x - y ≠ 0) (f g : ℂ → ℂ) :
    dd1 (fun s => f s * g s) x y = f x * dd1 g x y + dd1 f x y * g y := by
  have h1 : y - x ≠ 0 := fun h => hxy (by linear_combination -h)
  unfold dd1
  field_simp
  ring

theorem dd1_inv {V x y : ℂ} (hx : V + x ≠ 0) (hy : V + y ≠ 0) (hxy : x - y ≠ 0) :
    dd1 (fun s => (V + s)⁻¹) x y = -((V + x)⁻¹ * (V + y)⁻¹) := by
  have h1 : y - x ≠ 0 := fun h => hxy (by linear_combination -h)
  unfold dd1
  field_simp
  ring

theorem dd2_inv {V x y z : ℂ} (hx : V + x ≠ 0) (hy : V + y ≠ 0) (hz : V + z ≠ 0)
    (hxy : x - y ≠ 0) (hxz : x - z ≠ 0) (hyz : y - z ≠ 0) :
    dd2 (fun s => (V + s)⁻¹) x y z = (V + x)⁻¹ * (V + y)⁻¹ * (V + z)⁻¹ := by
  have h2 : z - x ≠ 0 := fun h => hxz (by linear_combination -h)
  unfold dd2
  rw [dd1_inv hy hz hyz, dd1_inv hx hy hxy]
  field_simp
  ring

theorem dd1_quad (E0 E2 E4 : ℂ) {x y : ℂ} (hxy : x - y ≠ 0) :
    dd1 (fun s => E0 + s * E2 + s ^ 2 * E4) x y = E2 + (x + y) * E4 := by
  have h1 : y - x ≠ 0 := fun h => hxy (by linear_combination -h)
  unfold dd1
  field_simp
  ring

theorem dd2_quad (E0 E2 E4 : ℂ) {x y z : ℂ} (hxy : x - y ≠ 0) (hxz : x - z ≠ 0)
    (hyz : y - z ≠ 0) :
    dd2 (fun s => E0 + s * E2 + s ^ 2 * E4) x y z = E4 := by
  have h2 : z - x ≠ 0 := fun h => hxz (by linear_combination -h)
  unfold dd2
  rw [dd1_quad _ _ _ hyz, dd1_quad _ _ _ hxy]
  field_simp
  ring

/-- **The second divided difference of a quadratic over four inverse denominators.** -/
theorem dd2_quad_inv4 (V : Fin 4 → ℂ) (s0 s1 s2 E0 E2 E4 : ℂ) (h01 : s0 - s1 ≠ 0)
    (h02 : s0 - s2 ≠ 0) (h12 : s1 - s2 ≠ 0) (h0 : ∀ i, V i + s0 ≠ 0) (h1 : ∀ i, V i + s1 ≠ 0)
    (h2 : ∀ i, V i + s2 ≠ 0) :
    dd2 (fun s : ℂ => (E0 + s * E2 + s ^ 2 * E4) *
      ((V 0 + s)⁻¹ * (V 1 + s)⁻¹ * (V 2 + s)⁻¹ * (V 3 + s)⁻¹)) s0 s1 s2 =
        (E0 + s0 * E2 + s0 ^ 2 * E4) *
          (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then
            (∏ l : Fin 4, (V l + if l ≤ i then s0 else if l ≤ j then s1 else s2)⁻¹) *
              (V i + s1)⁻¹ * (V j + s2)⁻¹ else 0) -
          (E2 + (s0 + s1) * E4) *
            (∑ i : Fin 4, (∏ l : Fin 4, (V l + if l ≤ i then s1 else s2)⁻¹) * (V i + s2)⁻¹) +
          E4 * ∏ l : Fin 4, (V l + s2)⁻¹ := by
  rw [dd2_mul h01 h02 h12, dd2_mul h01 h02 h12, dd2_mul h01 h02 h12, dd2_mul h01 h02 h12]
  simp only [dd1_mul h01, dd1_mul h12, dd2_quad _ _ _ h01 h02 h12, dd1_quad _ _ _ h01,
    dd1_inv (h0 _) (h1 _) h01, dd1_inv (h1 _) (h2 _) h12,
    dd2_inv (h0 _) (h1 _) (h2 _) h01 h02 h12]
  simp only [Fin.sum_univ_four, Fin.prod_univ_four]
  simp (config := {decide := true}) only [Fin.isValue, ite_true, ite_false]
  ring

/-- **The three-flavour combination of one class integrand as fifteen pieces.** -/
theorem tri_v_eq (V : Fin 4 → ℂ) (K E0 E2 E4 s0 s1 s2 : ℂ) (h01 : s0 - s1 ≠ 0)
    (h02 : s0 - s2 ≠ 0) (h12 : s1 - s2 ≠ 0) (h0 : ∀ i, V i + s0 ≠ 0) (h1 : ∀ i, V i + s1 ≠ 0)
    (h2 : ∀ i, V i + s2 ≠ 0) :
    K * ((E0 + s0 * E2 + s0 ^ 2 * E4) * ∏ l, (V l + s0)⁻¹) +
        (s2 - s0) / (s1 - s2) * (K * ((E0 + s1 * E2 + s1 ^ 2 * E4) * ∏ l, (V l + s1)⁻¹)) +
        (s0 - s1) / (s1 - s2) * (K * ((E0 + s2 * E2 + s2 ^ 2 * E4) * ∏ l, (V l + s2)⁻¹)) =
      ∑ i : Fin 4, ∑ j : Fin 4, (if i ≤ j then
          K * (s1 - s0) * (s2 - s0) * (E0 + s0 * E2 + s0 ^ 2 * E4) *
            ((∏ l : Fin 4, (V l + if l ≤ i then s0 else if l ≤ j then s1 else s2)⁻¹) *
              (V i + s1)⁻¹ * (V j + s2)⁻¹) else 0) +
        ∑ i : Fin 4, -(K * (s1 - s0) * (s2 - s0)) * (E2 + (s0 + s1) * E4) *
          ((∏ l : Fin 4, (V l + if l ≤ i then s1 else s2)⁻¹) * (V i + s2)⁻¹) +
        K * (s1 - s0) * (s2 - s0) * E4 * ∏ l : Fin 4, (V l + s2)⁻¹ := by
  set H : ℂ → ℂ := fun s => (E0 + s * E2 + s ^ 2 * E4) *
    ((V 0 + s)⁻¹ * (V 1 + s)⁻¹ * (V 2 + s)⁻¹ * (V 3 + s)⁻¹) with hH
  have hT := tri_eq_dd2 h01 h02 h12 H
  have hL := dd2_quad_inv4 V s0 s1 s2 E0 E2 E4 h01 h02 h12 h0 h1 h2
  rw [← hH] at hL
  have e : ∀ s, (E0 + s * E2 + s ^ 2 * E4) * ∏ l, (V l + s)⁻¹ = H s := fun s => by
    simp only [hH, Fin.prod_univ_four]
  rw [e, e, e]
  calc K * H s0 + (s2 - s0) / (s1 - s2) * (K * H s1) + (s0 - s1) / (s1 - s2) * (K * H s2)
      = K * (H s0 + (s2 - s0) / (s1 - s2) * H s1 + (s0 - s1) / (s1 - s2) * H s2) := by ring
    _ = K * ((s1 - s0) * (s2 - s0) * dd2 H s0 s1 s2) := by rw [hT]
    _ = _ := by
      rw [hL]
      simp only [Fin.sum_univ_four, Fin.prod_univ_four]
      simp (config := {decide := true}) only [Fin.isValue, ite_true, ite_false]
      ring

/-! ### The trace of the loop -/

theorem IsOddG.trace7 {A B C D E G H : Mat} (hA : IsOddG A) (hB : IsOddG B) (hC : IsOddG C)
    (hD : IsOddG D) (hE : IsOddG E) (hG : IsOddG G) (hH : IsOddG H) :
    (A * (B * (C * (D * (E * (G * H)))))).trace = 0 := by
  apply trace_eq_zero_of_gamma5_conj
  rw [gamma5_conj_mul, gamma5_conj_mul, gamma5_conj_mul, gamma5_conj_mul, gamma5_conj_mul,
    gamma5_conj_mul, hA, hB, hC, hD, hE, hG, hH]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem isOddG_eN0 (p : Fin 4 → ℝ) : IsOddG (electronNumerator 0 p) := by
  have h : electronNumerator 0 p = -Dirac.slash p := by simp [electronNumerator]
  rw [h, IsOddG, Matrix.mul_neg, Matrix.neg_mul, isOddG_slash p]

theorem eN_eq_add (M : ℝ) (p : Fin 4 → ℝ) :
    electronNumerator M p = (M : ℂ) • (1 : Mat) + electronNumerator 0 p := by
  simp [electronNumerator, sub_eq_add_neg]

/-- **The evenness in the mass of a loop of four odd vertex factors.** -/
theorem trace4_expand {A1 A2 A3 A4 Y1 Y2 Y3 Y4 : Mat} (h1 : IsOddG A1) (h2 : IsOddG A2)
    (h3 : IsOddG A3) (h4 : IsOddG A4) (g1 : IsOddG Y1) (g2 : IsOddG Y2) (g3 : IsOddG Y3)
    (g4 : IsOddG Y4) (M : ℂ) :
    (A1 * (M • 1 + Y1) * A2 * (M • 1 + Y2) * A3 * (M • 1 + Y3) * A4 * (M • 1 + Y4)).trace =
      (A1 * (Y1 * (A2 * (Y2 * (A3 * (Y3 * (A4 * Y4))))))).trace +
        M ^ 2 * ((A1 * (A2 * (A3 * (Y3 * (A4 * Y4))))).trace +
          (A1 * (A2 * (Y2 * (A3 * (A4 * Y4))))).trace +
          (A1 * (A2 * (Y2 * (A3 * (Y3 * A4))))).trace +
          (A1 * (Y1 * (A2 * (A3 * (A4 * Y4))))).trace +
          (A1 * (Y1 * (A2 * (A3 * (Y3 * A4))))).trace +
          (A1 * (Y1 * (A2 * (Y2 * (A3 * A4))))).trace) +
        M ^ 4 * (A1 * (A2 * (A3 * A4))).trace := by
  have o := fun {A B C D E G H : Mat} (hA : IsOddG A) (hB : IsOddG B) (hC : IsOddG C)
    (hD : IsOddG D) (hE : IsOddG E) (hG : IsOddG G) (hH : IsOddG H) =>
    IsOddG.trace7 hA hB hC hD hE hG hH
  have p := fun {A B C D E : Mat} (hA : IsOddG A) (hB : IsOddG B) (hC : IsOddG C)
    (hD : IsOddG D) (hE : IsOddG E) => IsOddG.trace5 hA hB hC hD hE
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.mul_assoc, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, smul_add, smul_smul]
  rw [o h1 g1 h2 g2 h3 g3 h4, o h1 g1 h2 g2 h3 h4 g4, o h1 g1 h2 h3 g3 h4 g4,
    o h1 h2 g2 h3 g3 h4 g4, p h1 h2 h3 h4 g4, p h1 h2 h3 g3 h4, p h1 h2 g2 h3 h4,
    p h1 g1 h2 h3 h4]
  ring

/-- The trace of the loop at mass `M` and the four line momenta `y`. -/
noncomputable def vT (A : Fin 4 → Mat) (M : ℝ) (y : Fin 4 → Fin 4 → ℝ) : ℂ :=
  (A 0 * electronNumerator M (y 0) * A 1 * electronNumerator M (y 1) * A 2 *
    electronNumerator M (y 2) * A 3 * electronNumerator M (y 3)).trace

/-- The coefficient of `M⁰` in `vT`. -/
noncomputable def vE0 (A : Fin 4 → Mat) (y : Fin 4 → Fin 4 → ℝ) : ℂ :=
  (A 0 * (electronNumerator 0 (y 0) * (A 1 * (electronNumerator 0 (y 1) * (A 2 *
    (electronNumerator 0 (y 2) * (A 3 * electronNumerator 0 (y 3)))))))).trace

/-- The coefficient of `M²` in `vT`. -/
noncomputable def vE2 (A : Fin 4 → Mat) (y : Fin 4 → Fin 4 → ℝ) : ℂ :=
  (A 0 * (A 1 * (A 2 * (electronNumerator 0 (y 2) * (A 3 * electronNumerator 0 (y 3)))))).trace +
    (A 0 * (A 1 * (electronNumerator 0 (y 1) * (A 2 * (A 3 * electronNumerator 0 (y 3)))))).trace +
    (A 0 * (A 1 * (electronNumerator 0 (y 1) * (A 2 * (electronNumerator 0 (y 2) *
      A 3))))).trace +
    (A 0 * (electronNumerator 0 (y 0) * (A 1 * (A 2 * (A 3 * electronNumerator 0 (y 3)))))).trace +
    (A 0 * (electronNumerator 0 (y 0) * (A 1 * (A 2 * (electronNumerator 0 (y 2) *
      A 3))))).trace +
    (A 0 * (electronNumerator 0 (y 0) * (A 1 * (electronNumerator 0 (y 1) * (A 2 *
      A 3))))).trace

/-- The coefficient of `M⁴` in `vT`. -/
noncomputable def vE4 (A : Fin 4 → Mat) : ℂ := (A 0 * (A 1 * (A 2 * A 3))).trace

theorem vT_eq {A : Fin 4 → Mat} (hA : ∀ l, IsOddG (A l)) (M : ℝ) (y : Fin 4 → Fin 4 → ℝ) :
    vT A M y = vE0 A y + (M : ℂ) ^ 2 * vE2 A y + ((M : ℂ) ^ 2) ^ 2 * vE4 A := by
  unfold vT vE0 vE2 vE4
  simp only [eN_eq_add M]
  rw [trace4_expand (hA 0) (hA 1) (hA 2) (hA 3) (isOddG_eN0 _) (isOddG_eN0 _) (isOddG_eN0 _)
    (isOddG_eN0 _)]
  ring

/-! ### Energy-first integrability of two-loop integrands -/

namespace JEF

variable {L : ℕ}

theorem congr {F G : (Fin L → Fin 4 → ℝ) → ℂ} (h : QED.TwoLoop.jointEnergyFirstIntegrable L F)
    (e : ∀ ℓ, F ℓ = G ℓ) : QED.TwoLoop.jointEnergyFirstIntegrable L G := by
  rwa [show G = F from funext fun ℓ => (e ℓ).symm]

theorem const_mul {F : (Fin L → Fin 4 → ℝ) → ℂ} (h : QED.TwoLoop.jointEnergyFirstIntegrable L F)
    (c : ℂ) : QED.TwoLoop.jointEnergyFirstIntegrable L fun ℓ => c * F ℓ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun v => (h1 v).const_mul c, ?_⟩
  have e : (fun v : Fin L → Fin 3 → ℝ => ∫ t : Fin L → ℝ,
      c * F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) =
      fun v => c * ∫ t : Fin L → ℝ, F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ) :=
    funext fun v => integral_const_mul c _
  rw [e]
  exact h2.const_mul c

theorem zero : QED.TwoLoop.jointEnergyFirstIntegrable L fun _ => 0 := by
  refine ⟨fun v => integrable_zero _ _ _, ?_⟩
  simp only [integral_zero]
  exact integrable_zero _ _ _

theorem sum {ι : Type*} (s : Finset ι) {F : ι → (Fin L → Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegrable L (F i)) :
    QED.TwoLoop.jointEnergyFirstIntegrable L fun ℓ => ∑ i ∈ s, F i ℓ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : QED.TwoLoop.jointEnergyFirstIntegrable L fun _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact jointEnergyFirstIntegrable_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end JEF

/-! ### The line data of a class and the pieces -/

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (pp : Fin 5 → Fin 4 → ℝ)

/-- The momentum of the fermion line `l` (row `l`). -/
noncomputable abbrev fm (l : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix base) pp l.castSucc ℓ

/-- The momentum of the photon line (row `4`). -/
noncomputable abbrev phm (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 4 → ℝ :=
  lineMomentum (castLoopMatrix base) pp (Fin.last 4) ℓ

/-- The rows of a piece with eight lines: the four fermion lines, the fermion lines `i`, `j`
again, the photon line twice. -/
def shA (i j : Fin 4) : Fin 8 → Fin 5 :=
  ![(0 : Fin 4).castSucc, (1 : Fin 4).castSucc, (2 : Fin 4).castSucc, (3 : Fin 4).castSucc,
    i.castSucc, j.castSucc, Fin.last 4, Fin.last 4]

/-- The rows of a piece with seven lines: the four fermion lines, the fermion line `i` again,
the photon line twice. -/
def shB (i : Fin 4) : Fin 7 → Fin 5 :=
  ![(0 : Fin 4).castSucc, (1 : Fin 4).castSucc, (2 : Fin 4).castSucc, (3 : Fin 4).castSucc,
    i.castSucc, Fin.last 4, Fin.last 4]

theorem lineMomentum_sh {m : ℕ} (sh : Fin (m + 1) → Fin 5) (n : Fin (m + 1))
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (castLoopMatrix fun n => base (sh n)) (fun n => pp (sh n)) n ℓ =
      lineMomentum (castLoopMatrix base) pp (sh n) ℓ := rfl

theorem lineDenom_sh {m : ℕ} (sh : Fin (m + 1) → Fin 5) (Ms : Fin (m + 1) → ℝ) (ε : ℝ)
    (n : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (castLoopMatrix fun n => base (sh n)) (fun n => pp (sh n)) Ms ε n ℓ =
      propDenom (Ms n) ε (lineMomentum (castLoopMatrix base) pp (sh n) ℓ) := rfl

/-- **A piece with eight lines** (quartic numerator). -/
theorem jef_pieceA (i j : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (Mf : Fin 4 → ℝ) (X Y mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hpoly : IsLoopPoly 2 4 F)
    (hB : RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4 F) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => F ℓ *
      ((∏ l : Fin 4, (propDenom (Mf l) ε (fm base pp l ℓ))⁻¹) *
        (propDenom X ε (fm base pp i ℓ))⁻¹ * (propDenom Y ε (fm base pp j ℓ))⁻¹ *
        ((propDenom mγ ε (phm base pp ℓ))⁻¹ * (propDenom Λ ε (phm base pp ℓ))⁻¹)) := by
  obtain ⟨Q, rfl⟩ := hpoly.exists_loopQuartic
  have h :=
    QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
      Q (castLoopMatrix fun n => base (shA i j n)) (fun n => pp (shA i j n))
      ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, mγ, Λ] (by norm_num) hε
      ((QED.Integration.TwoLoop.noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit) hB
  refine JEF.congr h fun ℓ => ?_
  rw [Fin.prod_univ_eight]
  simp only [Fin.prod_univ_four, lineDenom_sh, shA, Matrix.cons_val, fm, phm]
  ring

/-- **A piece with seven lines** (cubic numerator). -/
theorem jef_pieceB (i : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Mf : Fin 4 → ℝ) (Y mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) {F : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hpoly : IsLoopPoly 2 3 F)
    (hB : RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3, 4} 4 F) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ => F ℓ *
      ((∏ l : Fin 4, (propDenom (Mf l) ε (fm base pp l ℓ))⁻¹) *
        (propDenom Y ε (fm base pp i ℓ))⁻¹ *
        ((propDenom mγ ε (phm base pp ℓ))⁻¹ * (propDenom Λ ε (phm base pp ℓ))⁻¹)) := by
  obtain ⟨Q, hq, rfl⟩ := QED.GradedProof.SE2.IsLoopPoly.exists_loopQuartic_cubic hpoly
  have h :=
    QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic
      Q (castLoopMatrix fun n => base (shB i n)) (fun n => pp (shB i n))
      ![Mf 0, Mf 1, Mf 2, Mf 3, Y, mγ, Λ] hq (le_refl 6) hε
      ((QED.Integration.TwoLoop.noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit) hB
  refine JEF.congr h fun ℓ => ?_
  rw [Fin.prod_univ_seven]
  simp only [Fin.prod_univ_four, lineDenom_sh, shB, Matrix.cons_val, fm, phm]
  ring

end Setting

end QED.GradedProof.VP2

end
