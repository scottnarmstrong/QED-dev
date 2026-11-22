/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSEFub
public import QED.ChainProof.SetCRegDispShellSELim
import QED.TwoLoop.VPHalfAtAssemblyLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (c): the limit of vanishing prescription of the spectral integrand of the class `V`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, steps S4 (second half) and S6 (first
part) of the plan. The prescription `ε` of the parameters is sent to `0⁺` in the `x`-integrand
`seGInt` of `QED/ChainProof/SetCRegDispShellIBP.lean`, written as a combination of photon
products by `QED.ChainProof.SetCRegDisp.seGInt_eq_pieces`. All statements are below threshold:
`M₀ > 0` below the photon masses `m_γ, Λ` and the loop masses, and `-(m + M₀)² < p²`.

* `SEEngU`, `SELimU`: the engine bound uniform in `ε`, and the engine limit, for one numerator;
  provided for the three numerators `L`, `Q`, `G` (`exists_seEngU_seAff`, `seLimU_seAff`, ...).
* `tendsto_efi_s1`, `tendsto_efi_s2`, `tendsto_efi_s3`: the limits of `(k²)ʲ seProd`.
* **`tendsto_efi_seGInt`**: for `0 < x < 1`, `efi (seGInt_ε x) → seGIntLim x`.
* **`exists_goodEF4_seGInt_unif`**: one `GoodEF4` constant for all `ε ∈ (0, 1]`, `x ∈ (0, 1)`.
* **`tendsto_integral_efi_seGInt`**: `∫₀¹ efi (seGInt_ε x) dx → ∫₀¹ seGIntLim x dx`
  (`tendsto_integral_efi_seGInt_of_lt`: from the threshold hypotheses alone).
* `tendsto_efi_seConst`: the constant part `seConst` tends to `seConstLim`.
* **`tendsto_contractionValue₂_repV`**: the class `V` at the self-energy kinematics tends to
  `seConstLim - ∫₀¹ seGIntLim x dx`.

The limits are explicit iterated integrals of the closed form `seSpatial` at zero prescription;
their covariant form and their value on the shell are not computed here.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.OneLoop
open QED.TwoLoop.VPHalfAtAssembly (cOne cTwo wOne specMu specEta logSum)
open QED.TwoLoop.VPHalfAtLimit (massShift tendsto_massShift)
open QED.ChainProof.SetCRegDispSE (seProd seProdLim seL1 seL2 seL3 GoodEF4 seProd_mul_s
  goodEF4_s1 goodEF4_s2 tendsto_efi_of_eq_sub efi_const_mul_se energyFirstIntegral_sub_of_efInt)
open QED.TwoLoop.VPUnitNested (EFInt)

/-! ### Engine predicates uniform in the prescription -/

/-- The engine bound of `N` with one constant for every electron prescription `ε > 0`. -/
def SEEngU (N : (Fin 4 → ℝ) → ℂ) (m M₀ : ℝ) (Pv : Fin 4 → ℝ) (K : ℝ) (k₀ : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → SEEng N m M₀ ε Pv K k₀

/-- The engine limit of `N`: for `k₀ ≤ k ≤ 3`, masses `≥ M₀` and photon prescriptions tending to
`0⁺` with the electron prescription `ε`, `efi seProd → seProdLim`. -/
def SELimU (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m M₀ : ℝ) (Pv : Fin 4 → ℝ) (k₀ : ℕ) : Prop :=
  ∀ k : ℕ, k₀ ≤ k → k ≤ 3 → ∀ Ms : Fin (k + 2) → ℝ, (∀ j, M₀ ≤ Ms j) →
    ∀ es : ℝ → Fin (k + 2) → ℝ, (∀ j, Tendsto (fun ε => es ε j) (𝓝[>] 0) (𝓝[>] 0)) →
      Tendsto (fun ε => energyFirstIntegral (seProd N m Ms (es ε) ε Pv)) (𝓝[>] 0)
        (𝓝 (seProdLim α N m Ms Pv))

section Providers

variable {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {Pv : Fin 4 → ℝ}
  (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot Pv Pv) y)

include hM₀ hc₀ hP in
theorem exists_seEngU_seAff (c b : ℂ) (α β : Fin 4) :
    ∃ K : ℝ, 0 ≤ K ∧ SEEngU (seAff c b α β) m M₀ Pv K 0 := by
  obtain ⟨K0, h0, e0⟩ := exists_goodEF4_seAff hM₀ hc₀ hP c b α β 0
  obtain ⟨K1, h1, e1⟩ := exists_goodEF4_seAff hM₀ hc₀ hP c b α β 1
  obtain ⟨K2, h2, e2⟩ := exists_goodEF4_seAff hM₀ hc₀ hP c b α β 2
  obtain ⟨K3, h3, e3⟩ := exists_goodEF4_seAff hM₀ hc₀ hP c b α β 3
  refine ⟨K0 + K1 + K2 + K3, by positivity, fun ε hε k _ hk Ms es hMs hes => ?_⟩
  interval_cases k
  · exact (e0 Ms es hMs hes ε hε).mono' (by linarith)
  · exact (e1 Ms es hMs hes ε hε).mono' (by linarith)
  · exact (e2 Ms es hMs hes ε hε).mono' (by linarith)
  · exact (e3 Ms es hMs hes ε hε).mono' (by linarith)

include hM₀ hc₀ hP in
theorem exists_seEngU_seQuad (p : Fin 4 → ℝ) (α β : Fin 4) :
    ∃ K : ℝ, 0 ≤ K ∧ SEEngU (seQuad p α β) m M₀ Pv K 1 := by
  obtain ⟨K1, h1, e1⟩ := exists_goodEF4_seQuad hM₀ hc₀ hP p α β 1 le_rfl
  obtain ⟨K2, h2, e2⟩ := exists_goodEF4_seQuad hM₀ hc₀ hP p α β 2 (by norm_num)
  obtain ⟨K3, h3, e3⟩ := exists_goodEF4_seQuad hM₀ hc₀ hP p α β 3 (by norm_num)
  refine ⟨K1 + K2 + K3, by positivity, fun ε hε k hk0 hk Ms es hMs hes => ?_⟩
  interval_cases k
  · exact (e1 Ms es hMs hes ε hε).mono' (by linarith)
  · exact (e2 Ms es hMs hes ε hε).mono' (by linarith)
  · exact (e3 Ms es hMs hes ε hε).mono' (by linarith)

include hM₀ hc₀ hP in
theorem seLimU_seAff (c b : ℂ) (α β : Fin 4) : SELimU 0 (seAff c b α β) m M₀ Pv 0 :=
  fun _ _ _ _ hMs _ hes =>
    SetCRegDispSE.tendsto_efi_seProd hM₀ hc₀ hP (continuous_seAff c b α β) (seAff_cons c b α β)
      (norm_seAff_le_sq c b α β) (norm_seAff_le c b α β) (by omega) (Or.inl rfl) hMs
      tendsto_id hes

/-- The energy-squared coefficient of `seQuad p`. -/
noncomputable def seQuadA (p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  (Minkowski.dot p (Fin.cons 1 0 : Fin 4 → ℝ) : ℂ) * Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ) α β

include hM₀ hc₀ hP in
theorem seLimU_seQuad (p : Fin 4 → ℝ) (α β : Fin 4) :
    SELimU (seQuadA p α β) (seQuad p α β) m M₀ Pv 1 :=
  fun _ hk _ _ hMs _ hes =>
    SetCRegDispSE.tendsto_efi_seProd hM₀ hc₀ hP (continuous_seQuad p α β) (seQuad_cons p α β)
      (norm_seQuad_le p α β) (norm_seQuad_le p α β) (by omega) (Or.inr hk) hMs tendsto_id hes

end Providers

/-! ### Factors `k²` in the limit -/

section Absorb

variable {α : ℂ} {N : (Fin 4 → ℝ) → ℂ} {m M₀ K : ℝ} {Pv : Fin 4 → ℝ} {k₀ : ℕ}
  (hE : SEEngU N m M₀ Pv K k₀) (hL : SELimU α N m M₀ Pv k₀)

/-- The square `k²` as a complex number. -/
noncomputable def sqC (ℓ : Fin 4 → ℝ) : ℂ := ((Minkowski.dot ℓ ℓ : ℝ) : ℂ)

theorem tendsto_tail {k : ℕ} {es : ℝ → Fin (k + 1) → ℝ}
    (hes : ∀ j, Tendsto (fun ε => es ε j) (𝓝[>] 0) (𝓝[>] 0)) :
    ∀ j, Tendsto (fun ε => Fin.tail (es ε) j) (𝓝[>] 0) (𝓝[>] 0) :=
  fun j => hes j.succ

theorem eventually_pos_of_tendsto {k : ℕ} {es : ℝ → Fin k → ℝ}
    (hes : ∀ j, Tendsto (fun ε => es ε j) (𝓝[>] 0) (𝓝[>] 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ∀ j, 0 < es ε j := by
  have h0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  exact h0.and (eventually_all.2 fun j => (hes j) self_mem_nhdsWithin)

include hE in
theorem efInt_s0 {k : ℕ} (hk : k₀ ≤ k) (hk3 : k ≤ 3) {Ms es : Fin (k + 2) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) :
    EFInt (seProd N m Ms es ε Pv) :=
  (hE ε hε k hk hk3 Ms es hMs hes).1

include hE in
theorem goodEF4_s1' {k : ℕ} (hk : k₀ ≤ k) (hk3 : k + 1 ≤ 3) {Ms es : Fin (k + 3) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) :
    GoodEF4 (fun ℓ => sqC ℓ * seProd N m Ms es ε Pv ℓ)
      ((1 + ‖massShift (Ms 0) (es 0)‖) * K) :=
  goodEF4_s1 Ms es (hes 0) le_rfl
    (hE ε hε k hk (by omega) _ _ (le_tail_of_le hMs) (lt_tail_of_lt hes))
    (hE ε hε (k + 1) (by omega) hk3 Ms es hMs hes)

include hE hL in
theorem tendsto_efi_s1 {k : ℕ} (hk : k₀ ≤ k) (hk3 : k + 1 ≤ 3) {Ms : Fin (k + 3) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) {es : ℝ → Fin (k + 3) → ℝ}
    (hes : ∀ j, Tendsto (fun ε => es ε j) (𝓝[>] 0) (𝓝[>] 0)) :
    Tendsto (fun ε => energyFirstIntegral (fun ℓ => sqC ℓ * seProd N m Ms (es ε) ε Pv ℓ))
      (𝓝[>] 0) (𝓝 (seL1 α N m Ms Pv)) := by
  have hpos := eventually_pos_of_tendsto hes
  refine tendsto_efi_of_eq_sub (Y := fun ε => seProd N m (Fin.tail Ms) (Fin.tail (es ε)) ε Pv)
    (Z := fun ε => seProd N m Ms (es ε) ε Pv) (c := fun ε => massShift (Ms 0) (es ε 0))
    ?_ ?_ ?_ (hL k hk (by omega) _ (le_tail_of_le hMs) _ (tendsto_tail hes))
    (hL (k + 1) (by omega) hk3 Ms hMs _ hes)
    (tendsto_massShift (Ms 0) ((hes 0).mono_right nhdsWithin_le_nhds))
  · filter_upwards [hpos] with ε h ℓ
    exact seProd_mul_s N m Ms (es ε) (h.2 0) ε Pv ℓ
  · filter_upwards [hpos] with ε h
    exact efInt_s0 hE hk (by omega) (le_tail_of_le hMs) (lt_tail_of_lt h.2) h.1
  · filter_upwards [hpos] with ε h
    exact efInt_s0 hE (by omega) hk3 hMs h.2 h.1

include hE hL in
theorem tendsto_efi_s2 {k : ℕ} (hk : k₀ ≤ k) (hk3 : k + 2 ≤ 3) {Ms : Fin (k + 4) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) {es : ℝ → Fin (k + 4) → ℝ}
    (hes : ∀ j, Tendsto (fun ε => es ε j) (𝓝[>] 0) (𝓝[>] 0)) :
    Tendsto (fun ε => energyFirstIntegral (fun ℓ => sqC ℓ ^ 2 * seProd N m Ms (es ε) ε Pv ℓ))
      (𝓝[>] 0) (𝓝 (seL2 α N m Ms Pv)) := by
  have hpos := eventually_pos_of_tendsto hes
  refine tendsto_efi_of_eq_sub
    (Y := fun ε ℓ => sqC ℓ * seProd N m (Fin.tail Ms) (Fin.tail (es ε)) ε Pv ℓ)
    (Z := fun ε ℓ => sqC ℓ * seProd N m Ms (es ε) ε Pv ℓ)
    (c := fun ε => massShift (Ms 0) (es ε 0)) ?_ ?_ ?_
    (tendsto_efi_s1 hE hL hk (by omega) (le_tail_of_le hMs) (tendsto_tail hes))
    (tendsto_efi_s1 hE hL (k := k + 1) (by omega) hk3 hMs hes)
    (tendsto_massShift (Ms 0) ((hes 0).mono_right nhdsWithin_le_nhds))
  · filter_upwards [hpos] with ε h ℓ
    have := seProd_mul_s N m Ms (es ε) (h.2 0) ε Pv ℓ
    simp only [sqC] at this ⊢
    linear_combination ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) * this
  · filter_upwards [hpos] with ε h
    exact (goodEF4_s1' hE hk (by omega) (le_tail_of_le hMs) (lt_tail_of_lt h.2) h.1).1
  · filter_upwards [hpos] with ε h
    exact (goodEF4_s1' hE (k := k + 1) (by omega) (by omega) hMs h.2 h.1).1

include hE in
theorem goodEF4_s2' {k : ℕ} (hk : k₀ ≤ k) (hk3 : k + 2 ≤ 3) {Ms es : Fin (k + 4) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) :
    EFInt (fun ℓ => sqC ℓ ^ 2 * seProd N m Ms es ε Pv ℓ) := by
  have h := goodEF4_s2 (k := k) (T := ‖massShift (Ms 0) (es 0)‖ + ‖massShift (Ms 1) (es 1)‖)
    Ms es (hes 0) (hes 1) (by positivity) (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))
    (hE ε hε k hk (by omega) _ _ (le_tail_of_le (le_tail_of_le hMs))
      (lt_tail_of_lt (lt_tail_of_lt hes)))
    (hE ε hε (k + 1) (by omega) (by omega) _ _ (le_tail_of_le hMs) (lt_tail_of_lt hes))
    (hE ε hε (k + 2) (by omega) hk3 Ms es hMs hes)
  exact h.1

include hE hL in
theorem tendsto_efi_s3 {k : ℕ} (hk : k₀ ≤ k) (hk3 : k + 3 ≤ 3) {Ms : Fin (k + 5) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) {es : ℝ → Fin (k + 5) → ℝ}
    (hes : ∀ j, Tendsto (fun ε => es ε j) (𝓝[>] 0) (𝓝[>] 0)) :
    Tendsto (fun ε => energyFirstIntegral (fun ℓ => sqC ℓ ^ 3 * seProd N m Ms (es ε) ε Pv ℓ))
      (𝓝[>] 0) (𝓝 (seL3 α N m Ms Pv)) := by
  have hpos := eventually_pos_of_tendsto hes
  refine tendsto_efi_of_eq_sub
    (Y := fun ε ℓ => sqC ℓ ^ 2 * seProd N m (Fin.tail Ms) (Fin.tail (es ε)) ε Pv ℓ)
    (Z := fun ε ℓ => sqC ℓ ^ 2 * seProd N m Ms (es ε) ε Pv ℓ)
    (c := fun ε => massShift (Ms 0) (es ε 0)) ?_ ?_ ?_
    (tendsto_efi_s2 hE hL hk (by omega) (le_tail_of_le hMs) (tendsto_tail hes))
    (tendsto_efi_s2 hE hL (k := k + 1) (by omega) (by omega) hMs hes)
    (tendsto_massShift (Ms 0) ((hes 0).mono_right nhdsWithin_le_nhds))
  · filter_upwards [hpos] with ε h ℓ
    have := seProd_mul_s N m Ms (es ε) (h.2 0) ε Pv ℓ
    simp only [sqC] at this ⊢
    linear_combination ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ 2 * this
  · filter_upwards [hpos] with ε h
    exact goodEF4_s2' hE hk (by omega) (le_tail_of_le hMs) (lt_tail_of_lt h.2) h.1
  · filter_upwards [hpos] with ε h
    exact goodEF4_s2' hE (k := k + 1) (by omega) (by omega) hMs h.2 h.1

include hE in
theorem goodEF4_s3' {k : ℕ} (hk : k₀ ≤ k) (hk3 : k + 3 ≤ 3) {Ms es : Fin (k + 5) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) :
    EFInt (fun ℓ => sqC ℓ ^ 3 * seProd N m Ms es ε Pv ℓ) := by
  have n0 := norm_nonneg (massShift (Ms 0) (es 0))
  have n1 := norm_nonneg (massShift (Ms 1) (es 1))
  have n2 := norm_nonneg (massShift (Ms 2) (es 2))
  have h := SetCRegDispSE.goodEF4_s3 (k := k)
    (T := ‖massShift (Ms 0) (es 0)‖ + ‖massShift (Ms 1) (es 1)‖ + ‖massShift (Ms 2) (es 2)‖)
    Ms es (hes 0) (hes 1) (hes 2) (by positivity) (by linarith) (by linarith) (by linarith)
    (hE ε hε k hk (by omega) _ _ (le_tail_of_le (le_tail_of_le (le_tail_of_le hMs)))
      (lt_tail_of_lt (lt_tail_of_lt (lt_tail_of_lt hes))))
    (hE ε hε (k + 1) (by omega) (by omega) _ _ (le_tail_of_le (le_tail_of_le hMs))
      (lt_tail_of_lt (lt_tail_of_lt hes)))
    (hE ε hε (k + 2) (by omega) (by omega) _ _ (le_tail_of_le hMs) (lt_tail_of_lt hes))
    (hE ε hε (k + 3) (by omega) hk3 Ms es hMs hes)
  exact h.1

end Absorb

/-! ### Linear combinations -/

theorem efi_sum_eq {n : ℕ} (c : Fin n → ℂ) (X : Fin n → (Fin 4 → ℝ) → ℂ)
    (hX : ∀ i, EFInt (X i)) :
    energyFirstIntegral (fun ℓ => ∑ i, c i * X i ℓ) =
      ∑ i, c i * energyFirstIntegral (X i) := by
  unfold energyFirstIntegral
  have e : (fun v : Fin 3 → ℝ => ∫ t : ℝ, ∑ i, c i * X i (Fin.cons t v : Fin 4 → ℝ)) =
      fun v => ∑ i, c i * ∫ t : ℝ, X i (Fin.cons t v : Fin 4 → ℝ) := by
    funext v
    rw [integral_finsetSum _ fun i _ => ((hX i).1 v).const_mul (c i)]
    simp_rw [integral_const_mul]
  rw [e, integral_finsetSum _ fun i _ => ((hX i).2).const_mul (c i)]
  simp_rw [integral_const_mul]

theorem tendsto_efi_sum {n : ℕ} {l : Filter ℝ} {c : Fin n → ℝ → ℂ}
    {X : Fin n → ℝ → (Fin 4 → ℝ) → ℂ} {c₀ a : Fin n → ℂ}
    (hX : ∀ᶠ ε in l, ∀ i, EFInt (X i ε))
    (ha : ∀ i, Tendsto (fun ε => energyFirstIntegral (X i ε)) l (𝓝 (a i)))
    (hc : ∀ i, Tendsto (c i) l (𝓝 (c₀ i))) :
    Tendsto (fun ε => energyFirstIntegral (fun ℓ => ∑ i, c i ε * X i ε ℓ)) l
      (𝓝 (∑ i, c₀ i * a i)) := by
  refine (tendsto_finsetSum _ fun i _ => (hc i).mul (ha i)).congr' ?_
  filter_upwards [hX] with ε h
  exact (efi_sum_eq (fun i => c i ε) (fun i => X i ε) h).symm

/-! ### The limit of one flavour piece -/

/-- The parameters with the prescription `ε`. -/
def withEps (P : Params) (ε : ℝ) : Params := { P with ε := ε }

@[simp] theorem withEps_m (P : Params) (ε : ℝ) : (withEps P ε).m = P.m := rfl
@[simp] theorem withEps_ε (P : Params) (ε : ℝ) : (withEps P ε).ε = ε := rfl
@[simp] theorem withEps_mass (P : Params) (ε : ℝ) (f : Fin 3) :
    (withEps P ε).mass f = P.mass f := rfl
@[simp] theorem cOne_withEps (P : Params) (ε : ℝ) : cOne (withEps P ε) = cOne P := rfl
@[simp] theorem cTwo_withEps (P : Params) (ε : ℝ) : cTwo (withEps P ε) = cTwo P := rfl
@[simp] theorem seCL_withEps (P : Params) (ε : ℝ) (p : Fin 4 → ℝ) (α β : Fin 4) :
    seCL (withEps P ε) p α β = seCL P p α β := rfl
@[simp] theorem seCG_withEps (P : Params) (ε : ℝ) (p : Fin 4 → ℝ) (α β : Fin 4) :
    seCG (withEps P ε) p α β = seCG P p α β := rfl
@[simp] theorem seMs4_withEps (P : Params) (ε : ℝ) : seMs4 (withEps P ε) = seMs4 P := rfl
@[simp] theorem seMs5_withEps (P : Params) (ε μ : ℝ) :
    seMs5 (withEps P ε) μ = seMs5 P μ := rfl

/-- The limit of one flavour piece. -/
noncomputable def sePieceLim (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (x : ℝ) (f : Fin 3) :
    ℂ :=
  I * cOne P * wOne x *
    (seL2 0 (seAff (seCL P p α β) 3 α β) P.m (seMs4 P) (-p) -
      2 * seL1 (seQuadA p α β) (seQuad p α β) P.m (seMs4 P) (-p) -
      seL3 0 (seAff (seCL P p α β) 3 α β) P.m (seMs5 P (specMu (P.mass f) x)) (-p) +
      2 * seL2 (seQuadA p α β) (seQuad p α β) P.m (seMs5 P (specMu (P.mass f) x)) (-p))

theorem tendsto_seEs5 {P : Params} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∀ j, Tendsto (fun ε => seEs5 (withEps P ε) (specEta ε x) j) (𝓝[>] 0) (𝓝[>] 0) := by
  intro j
  fin_cases j <;> simp [seEs5, withEps] <;>
    first | exact tendsto_id | exact QED.TwoLoop.VPHalfAtAssembly.tendsto_specEta hx

section Piece

variable {P : Params} {M₀ K : ℝ} (hM₀ : 0 < M₀) (hmγ : M₀ ≤ P.mγ) (hΛ : M₀ ≤ P.Λ)
  {p : Fin 4 → ℝ} {α β : Fin 4}
  (hEL : SEEngU (seAff (seCL P p α β) 3 α β) P.m M₀ (-p) K 0)
  (hEQ : SEEngU (seQuad p α β) P.m M₀ (-p) K 1)
  (hEG : SEEngU (seAff (seCG P p α β) 2 α β) P.m M₀ (-p) K 0)
  (hLL : SELimU 0 (seAff (seCL P p α β) 3 α β) P.m M₀ (-p) 0)
  (hLQ : SELimU (seQuadA p α β) (seQuad p α β) P.m M₀ (-p) 1)
  (hLG : SELimU 0 (seAff (seCG P p α β) 2 α β) P.m M₀ (-p) 0)

include hM₀ hmγ hΛ hEL hEQ hEG hLL hLQ hLG in
/-- **The limit of one flavour piece**, for `0 < x < 1`. -/
theorem tendsto_efi_sePiece {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (f : Fin 3)
    (hf : M₀ ≤ P.mass f) :
    Tendsto (fun ε => energyFirstIntegral (sePiece (withEps P ε) p α β x f)) (𝓝[>] 0)
      (𝓝 (sePieceLim P p α β x f)) := by
  have hMf : 0 < P.mass f := hM₀.trans_le hf
  have hμ : M₀ ≤ specMu (P.mass f) x :=
    hf.trans (QED.TwoLoop.VPHalfAtAssembly.specMu_ge hMf hx)
  have hMs4 : ∀ j, M₀ ≤ seMs4 P j := seMs4_ge hmγ hΛ
  have hMs5 : ∀ j, M₀ ≤ seMs5 P (specMu (P.mass f) x) j := seMs5_ge hmγ hΛ hμ
  have hes4 : ∀ j : Fin 4, Tendsto (fun ε : ℝ => (fun _ : Fin 4 => ε) j) (𝓝[>] 0) (𝓝[>] 0) :=
    fun _ => tendsto_id
  have hes5 := tendsto_seEs5 (P := P) hx
  set Ms5 := seMs5 P (specMu (P.mass f) x)
  set L := seAff (seCL P p α β) 3 α β
  set Q := seQuad p α β
  set G := seAff (seCG P p α β) 2 α β
  set es5 : ℝ → Fin 5 → ℝ := fun ε => seEs5 (withEps P ε) (specEta ε x)
  set a0 : ℂ := I * cOne P * wOne x
  set X : Fin 6 → ℝ → (Fin 4 → ℝ) → ℂ := ![
    fun ε ℓ => sqC ℓ ^ 2 * seProd L P.m (seMs4 P) (fun _ => ε) ε (-p) ℓ,
    fun ε ℓ => sqC ℓ * seProd Q P.m (seMs4 P) (fun _ => ε) ε (-p) ℓ,
    fun ε ℓ => sqC ℓ ^ 3 * seProd L P.m Ms5 (es5 ε) ε (-p) ℓ,
    fun ε ℓ => sqC ℓ ^ 2 * seProd Q P.m Ms5 (es5 ε) ε (-p) ℓ,
    fun ε ℓ => sqC ℓ * seProd G P.m (seMs4 P) (fun _ => ε) ε (-p) ℓ,
    fun ε ℓ => sqC ℓ ^ 2 * seProd G P.m Ms5 (es5 ε) ε (-p) ℓ] with hX
  set c : Fin 6 → ℝ → ℂ := ![fun _ => a0, fun _ => -(2 * a0), fun _ => -a0, fun _ => 2 * a0,
    fun ε => (ε : ℂ) * cTwo P * (x : ℂ), fun ε => -((ε : ℂ) * cTwo P * (x : ℂ))] with hc
  have hEG1 : SEEngU G P.m M₀ (-p) K 1 := fun ε hε k _ hk => hEG ε hε k (Nat.zero_le k) hk
  have hLG1 : SELimU 0 G P.m M₀ (-p) 1 := fun k _ hk => hLG k (Nat.zero_le k) hk
  have hpt : ∀ ε ℓ, sePiece (withEps P ε) p α β x f ℓ = ∑ i, c i ε * X i ε ℓ := by
    intro ε ℓ
    simp only [sePiece, Fin.sum_univ_succ, Fin.sum_univ_zero, hX, hc, Matrix.cons_val_zero,
      Matrix.cons_val_succ, sqC, es5, Ms5, L, Q, G, a0, withEps_m,
      withEps_ε, withEps_mass, cOne_withEps, cTwo_withEps, seCL_withEps, seCG_withEps,
      seMs4_withEps, seMs5_withEps]
    ring
  have hlim := tendsto_efi_sum (l := 𝓝[>] (0 : ℝ)) (c := c) (X := X)
    (c₀ := ![a0, -(2 * a0), -a0, 2 * a0, 0, 0])
    (a := ![seL2 0 L P.m (seMs4 P) (-p), seL1 (seQuadA p α β) Q P.m (seMs4 P) (-p),
      seL3 0 L P.m Ms5 (-p), seL2 (seQuadA p α β) Q P.m Ms5 (-p),
      seL1 0 G P.m (seMs4 P) (-p), seL2 0 G P.m Ms5 (-p)]) ?_ ?_ ?_
  · refine (hlim.congr fun ε => ?_).trans (le_of_eq ?_)
    · congr 1
      funext ℓ
      exact (hpt ε ℓ).symm
    · congr 1
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, sePieceLim, a0, L, Q, Ms5]
      ring
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h4 : ∀ j : Fin 4, 0 < (fun _ : Fin 4 => ε) j := fun _ => hε
    have h5 : ∀ j, 0 < es5 ε j := seEs5_pos (P := withEps P ε) hε
      (hε.trans_le (QED.TwoLoop.VPHalfAtAssembly.specEta_ge hε hx))
    intro i
    fin_cases i
    · exact goodEF4_s2' hEL (k := 0) le_rfl (by norm_num) hMs4 h4 hε
    · exact (goodEF4_s1' hEQ (k := 1) le_rfl (by norm_num) hMs4 h4 hε).1
    · exact goodEF4_s3' hEL (k := 0) le_rfl (by norm_num) hMs5 h5 hε
    · exact goodEF4_s2' hEQ (k := 1) le_rfl (by norm_num) hMs5 h5 hε
    · exact (goodEF4_s1' hEG1 (k := 1) le_rfl (by norm_num) hMs4 h4 hε).1
    · exact goodEF4_s2' hEG1 (k := 1) le_rfl (by norm_num) hMs5 h5 hε
  · intro i
    fin_cases i
    · exact tendsto_efi_s2 hEL hLL (k := 0) le_rfl (by norm_num) hMs4 hes4
    · exact tendsto_efi_s1 hEQ hLQ (k := 1) le_rfl (by norm_num) hMs4 hes4
    · exact tendsto_efi_s3 hEL hLL (k := 0) le_rfl (by norm_num) hMs5 hes5
    · exact tendsto_efi_s2 hEQ hLQ (k := 1) le_rfl (by norm_num) hMs5 hes5
    · exact tendsto_efi_s1 hEG1 hLG1 (k := 1) le_rfl (by norm_num) hMs4 hes4
    · exact tendsto_efi_s2 hEG1 hLG1 (k := 1) le_rfl (by norm_num) hMs5 hes5
  · intro i
    fin_cases i
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · show Tendsto (fun ε : ℝ => (ε : ℂ) * cTwo P * (x : ℂ)) _ _
      have h : Tendsto (fun ε : ℝ => (ε : ℂ) * cTwo P * (x : ℂ)) (𝓝[>] 0)
          (𝓝 (((0 : ℝ) : ℂ) * cTwo P * (x : ℂ))) :=
        (((continuous_ofReal.tendsto 0).comp
          (tendsto_id.mono_left nhdsWithin_le_nhds)).mul_const _).mul_const _
      simpa using h
    · show Tendsto (fun ε : ℝ => -((ε : ℂ) * cTwo P * (x : ℂ))) _ _
      have h : Tendsto (fun ε : ℝ => -((ε : ℂ) * cTwo P * (x : ℂ))) (𝓝[>] 0)
          (𝓝 (-(((0 : ℝ) : ℂ) * cTwo P * (x : ℂ)))) :=
        ((((continuous_ofReal.tendsto 0).comp
          (tendsto_id.mono_left nhdsWithin_le_nhds)).mul_const _).mul_const _).neg
      simpa using h

end Piece

/-! ### The limit of the `x`-integrand -/

@[simp] theorem seVK_withEps (P : Params) (ε : ℝ) : seVK (withEps P ε) = seVK P := rfl
@[simp] theorem withEps_loopCoeff (P : Params) (ε : ℝ) (f : Fin 3) :
    (withEps P ε).loopCoeff f = P.loopCoeff f := rfl

/-- The limit of the coefficient of one flavour: `K (Λ² - m_γ²)² c_f (1 - 2x) / M_f²`. -/
noncomputable def seCfLim (P : Params) (x : ℝ) (f : Fin 3) : ℂ :=
  seVK P * (((P.Λ ^ 2 - P.mγ ^ 2) ^ 2 : ℝ) : ℂ) * (P.loopCoeff f : ℂ) * ((1 - 2 * x : ℝ) : ℂ) *
    ((P.mass f ^ 2 : ℝ) : ℂ)⁻¹

/-- The limit of the `x`-integrand. -/
noncomputable def seGIntLim (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (x : ℝ) : ℂ :=
  ∑ f, seCfLim P x f * sePieceLim P p α β x f

theorem tendsto_seCf (P : Params) {x : ℝ} (f : Fin 3) (hMf : 0 < P.mass f) :
    Tendsto (fun ε => seCf (withEps P ε) x f) (𝓝[>] 0) (𝓝 (seCfLim P x f)) := by
  have hne : ((P.mass f ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hMf 2).ne'
  have h := (tendsto_massShift (P.mass f)
    (tendsto_id.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0)))).inv₀ hne
  exact h.const_mul _

section Integrand

variable {P : Params} {M₀ K : ℝ} (hM₀ : 0 < M₀) (hmγ : M₀ ≤ P.mγ) (hΛ : M₀ ≤ P.Λ)
  (hmass : ∀ f, M₀ ≤ P.mass f) (hK0 : 0 ≤ K) {p : Fin 4 → ℝ} {α β : Fin 4}
  (hEL : SEEngU (seAff (seCL P p α β) 3 α β) P.m M₀ (-p) K 0)
  (hEQ : SEEngU (seQuad p α β) P.m M₀ (-p) K 1)
  (hEG : SEEngU (seAff (seCG P p α β) 2 α β) P.m M₀ (-p) K 0)

include hmγ hΛ hmass hK0 hEL hEQ hEG in
theorem goodEF4_sePiece_withEps {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (f : Fin 3) (hMf : 0 < P.mass f) :
    GoodEF4 (sePiece (withEps P ε) p α β x f) (seBp (withEps P ε) K) :=
  goodEF4_sePiece (withEps P ε) hε hmγ hΛ p α β hK0 (hEL ε hε) (hEQ ε hε)
    (fun k _ hk => hEG ε hε k (Nat.zero_le k) hk) hx f (hmass f) hMf

variable (hLL : SELimU 0 (seAff (seCL P p α β) 3 α β) P.m M₀ (-p) 0)
  (hLQ : SELimU (seQuadA p α β) (seQuad p α β) P.m M₀ (-p) 1)
  (hLG : SELimU 0 (seAff (seCG P p α β) 2 α β) P.m M₀ (-p) 0)

include hM₀ hmγ hΛ hmass hK0 hEL hEQ hEG hLL hLQ hLG in
/-- **The limit of the `x`-integrand**, for `0 < x < 1`. -/
theorem tendsto_efi_seGInt {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun ε => energyFirstIntegral (seGInt (withEps P ε) p α β x)) (𝓝[>] 0)
      (𝓝 (seGIntLim P p α β x)) := by
  have hMf : ∀ f, 0 < P.mass f := fun f => hM₀.trans_le (hmass f)
  have h := tendsto_efi_sum (l := 𝓝[>] (0 : ℝ)) (c := fun f ε => seCf (withEps P ε) x f)
    (X := fun f ε => sePiece (withEps P ε) p α β x f) (c₀ := fun f => seCfLim P x f)
    (a := fun f => sePieceLim P p α β x f) ?_
    (fun f => tendsto_efi_sePiece hM₀ hmγ hΛ hEL hEQ hEG hLL hLQ hLG hx f (hmass f))
    (fun f => tendsto_seCf P f (hMf f))
  · refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    congr 1
    funext k
    exact (seGInt_eq_pieces (withEps P ε) hε p α β hx k).symm
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact fun f => (goodEF4_sePiece_withEps hmγ hΛ hmass hK0 hEL hEQ hEG hε hx f (hMf f)).1

end Integrand

/-! ### One bound for all `ε ∈ (0, 1]` and the limit under `∫₀¹` -/

theorem seBp_withEps_le (P : Params) {K : ℝ} (hK : 0 ≤ K) {ε : ℝ} (hε : 0 ≤ ε) (h1 : ε ≤ 1) :
    seBp (withEps P ε) K ≤ seBp (withEps P 1) K := by
  simp only [seBp, withEps_ε, cOne_withEps, cTwo_withEps]
  have hA : (1 + (P.mγ ^ 2 + P.Λ ^ 2 + ε)) ^ 3 * K ≤ (1 + (P.mγ ^ 2 + P.Λ ^ 2 + 1)) ^ 3 * K := by
    gcongr
  have hB : 0 ≤ (1 + (P.mγ ^ 2 + P.Λ ^ 2 + ε)) ^ 3 * K := by positivity
  have h2 := norm_nonneg (cOne P)
  have h3 := norm_nonneg (cTwo P)
  have := mul_le_mul h1 (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity) zero_le_one
  have h4 : ε * ‖cTwo P‖ * (2 * ((1 + (P.mγ ^ 2 + P.Λ ^ 2 + ε)) ^ 3 * K)) ≤
      1 * ‖cTwo P‖ * (2 * ((1 + (P.mγ ^ 2 + P.Λ ^ 2 + 1)) ^ 3 * K)) := by
    rw [mul_comm ε, mul_comm (1 : ℝ), mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left this h3
  have h5 : ‖cOne P‖ * (6 * ((1 + (P.mγ ^ 2 + P.Λ ^ 2 + ε)) ^ 3 * K)) ≤
      ‖cOne P‖ * (6 * ((1 + (P.mγ ^ 2 + P.Λ ^ 2 + 1)) ^ 3 * K)) := by gcongr
  exact add_le_add h5 h4

section Unif

variable {P : Params} {M₀ K : ℝ} (hM₀ : 0 < M₀) (hmγ : M₀ ≤ P.mγ) (hΛ : M₀ ≤ P.Λ)
  (hmass : ∀ f, M₀ ≤ P.mass f) (hK0 : 0 ≤ K) {p : Fin 4 → ℝ} {α β : Fin 4}
  (hEL : SEEngU (seAff (seCL P p α β) 3 α β) P.m M₀ (-p) K 0)
  (hEQ : SEEngU (seQuad p α β) P.m M₀ (-p) K 1)
  (hEG : SEEngU (seAff (seCG P p α β) 2 α β) P.m M₀ (-p) K 0)

include hM₀ hmγ hΛ hmass hK0 hEL hEQ hEG in
/-- **One `GoodEF4` constant for the `x`-integrand for all `ε ∈ (0, 1]` and `x ∈ (0, 1)`.** -/
theorem exists_goodEF4_seGInt_unif :
    ∃ C : ℝ, ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ x ∈ Ioo (0 : ℝ) 1,
      GoodEF4 (seGInt (withEps P ε) p α β x) C := by
  set Bcf := ‖seVK P‖ * ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2) * seCc P * (M₀ ^ 2)⁻¹
  have hc0 : 0 ≤ seCc P := by unfold seCc; positivity
  have hB0 : 0 ≤ Bcf :=
    mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) hc0) (by positivity)
  refine ⟨3 * (Bcf * seBp (withEps P 1) K), fun ε hε x hx => ?_⟩
  have hxI : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have hMf : ∀ f, 0 < P.mass f := fun f => hM₀.trans_le (hmass f)
  have hpiece := fun f => goodEF4_sePiece_withEps hmγ hΛ hmass hK0 hEL hEQ hEG hε.1 hx f (hMf f)
  have hcf : ∀ f, ‖seCf (withEps P ε) x f‖ ≤ Bcf := fun f =>
    norm_seCf_le (withEps P ε) hM₀ hmass hxI f
  have hsum : ∀ ℓ, seGInt (withEps P ε) p α β x ℓ =
      seCf (withEps P ε) x 0 * sePiece (withEps P ε) p α β x 0 ℓ +
      seCf (withEps P ε) x 1 * sePiece (withEps P ε) p α β x 1 ℓ +
      seCf (withEps P ε) x 2 * sePiece (withEps P ε) p α β x 2 ℓ := fun ℓ => by
    rw [seGInt_eq_pieces (withEps P ε) hε.1 p α β hx, Fin.sum_univ_three]
  have Z := ((SEgoodEF4_const_mul_le (hpiece 0) _ (hcf 0)).add
    (SEgoodEF4_const_mul_le (hpiece 1) _ (hcf 1))).add
    (SEgoodEF4_const_mul_le (hpiece 2) _ (hcf 2))
  have hle := mul_le_mul_of_nonneg_left (seBp_withEps_le P hK0 hε.1.le hε.2) hB0
  exact (Z.congr fun ℓ => (hsum ℓ).symm).mono' (by linarith)

variable (hLL : SELimU 0 (seAff (seCL P p α β) 3 α β) P.m M₀ (-p) 0)
  (hLQ : SELimU (seQuadA p α β) (seQuad p α β) P.m M₀ (-p) 1)
  (hLG : SELimU 0 (seAff (seCG P p α β) 2 α β) P.m M₀ (-p) 0)

include hM₀ hmγ hΛ hmass hK0 hEL hEQ hEG hLL hLQ hLG in
/-- **The limit under the Feynman-parameter integral**:
`∫₀¹ efi (seGInt_ε x) dx → ∫₀¹ seGIntLim x dx` as `ε → 0⁺`. -/
theorem tendsto_integral_efi_seGInt :
    Tendsto (fun ε => ∫ x in (0 : ℝ)..1, energyFirstIntegral (seGInt (withEps P ε) p α β x))
      (𝓝[>] 0) (𝓝 (∫ x in (0 : ℝ)..1, seGIntLim P p α β x)) := by
  obtain ⟨C, hC⟩ := exists_goodEF4_seGInt_unif hM₀ hmγ hΛ hmass hK0 hEL hEQ hEG
  have hI : ∀ g : ℝ → ℂ, ∫ x in (0 : ℝ)..1, g x = ∫ x in Ioo (0 : ℝ) 1, g x := fun g => by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  simp_rw [hI]
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  have hae : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT zero_lt_one
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ => C * ∫ v : Fin 3 → ℝ, (1 + ‖v‖) ^ (-(4 : ℝ))) ?_ ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun ε => ?_
    have hm := (measurable_seGInt (withEps P ε) p α β).stronglyMeasurable
    exact (hm.integral_prod_right' (ν := (volume : Measure ℝ))).integral_prod_left'
      (μ := (volume : Measure (Fin 3 → ℝ))) |>.aestronglyMeasurable
  · filter_upwards [hev] with ε hε
    exact hae.mono fun x hx => (hC ε hε x hx).norm_efi_le
  · exact hae.mono fun x hx =>
      tendsto_efi_seGInt hM₀ hmγ hΛ hmass hK0 hEL hEQ hEG hLL hLQ hLG hx

/-! ### The constant part and the class `V` -/

@[simp] theorem logSum_withEps (P : Params) (ε : ℝ) : logSum (withEps P ε) = logSum P := rfl

/-- The limit of the constant part `seConst`. -/
noncomputable def seConstLim (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  seVK P * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2 * (I * cOne P * (1 / 6) * logSum P 0) *
    (seL1 0 (seAff (seCL P p α β) 3 α β) P.m (seMs4 P) (-p) -
      2 * seProdLim (seQuadA p α β) (seQuad p α β) P.m (seMs4 P) (-p))

include hM₀ hmγ hΛ hmass hEL hEQ hEG hLL hLQ hLG in
/-- **The limit of the constant part.** -/
theorem tendsto_efi_seConst :
    Tendsto (fun ε => energyFirstIntegral (seConst (withEps P ε) p α β)) (𝓝[>] 0)
      (𝓝 (seConstLim P p α β)) := by
  have hMf : ∀ f, 0 < P.mass f := fun f => hM₀.trans_le (hmass f)
  have hMs4 : ∀ j, M₀ ≤ seMs4 P j := seMs4_ge hmγ hΛ
  have hes4 : ∀ j : Fin 4, Tendsto (fun ε : ℝ => (fun _ : Fin 4 => ε) j) (𝓝[>] 0) (𝓝[>] 0) :=
    fun _ => tendsto_id
  set L := seAff (seCL P p α β) 3 α β
  set Q := seQuad p α β
  set G := seAff (seCG P p α β) 2 α β
  set κ : ℂ := seVK P * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) ^ 2
  set X : Fin 3 → ℝ → (Fin 4 → ℝ) → ℂ := ![
    fun ε ℓ => sqC ℓ * seProd L P.m (seMs4 P) (fun _ => ε) ε (-p) ℓ,
    fun ε ℓ => seProd Q P.m (seMs4 P) (fun _ => ε) ε (-p) ℓ,
    fun ε ℓ => seProd G P.m (seMs4 P) (fun _ => ε) ε (-p) ℓ] with hX
  set c : Fin 3 → ℝ → ℂ := ![fun ε => κ * (I * cOne P * (1 / 6) * logSum P ε),
    fun ε => -(2 * (κ * (I * cOne P * (1 / 6) * logSum P ε))),
    fun ε => κ * ((ε : ℂ) * cTwo P * logSum P ε)] with hc
  have hpt : ∀ ε, 0 < ε → ∀ ℓ, seConst (withEps P ε) p α β ℓ = ∑ i, c i ε * X i ε ℓ := by
    intro ε hε ℓ
    rw [seConst, withEps_ε, photonScalar_eq_mul _ _ _ hε, seChainGK_apply, seChainG_apply,
      seDen_eq_denom]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hX, hc, Matrix.cons_val_zero,
      Matrix.cons_val_succ, sqC, L, Q, G, κ, withEps_m, withEps_ε, cOne_withEps, cTwo_withEps,
      seCL_withEps, seCG_withEps, seVK_withEps, logSum_withEps, seProd, seMs4,
      Fin.prod_univ_succ, Fin.prod_univ_zero]
    simp only [withEps]
    ring
  have hlim := tendsto_efi_sum (l := 𝓝[>] (0 : ℝ)) (c := c) (X := X)
    (c₀ := ![κ * (I * cOne P * (1 / 6) * logSum P 0),
      -(2 * (κ * (I * cOne P * (1 / 6) * logSum P 0))), 0])
    (a := ![seL1 0 L P.m (seMs4 P) (-p), seProdLim (seQuadA p α β) Q P.m (seMs4 P) (-p),
      seProdLim 0 G P.m (seMs4 P) (-p)]) ?_ ?_ ?_
  · refine (hlim.congr' ?_).trans (le_of_eq ?_)
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      congr 1
      funext ℓ
      exact (hpt ε hε ℓ).symm
    · congr 1
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, seConstLim, κ, L, Q]
      ring
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h4 : ∀ j : Fin 4, 0 < (fun _ : Fin 4 => ε) j := fun _ => hε
    intro i
    fin_cases i
    · exact (goodEF4_s1' hEL (k := 1) (Nat.zero_le 1) (by norm_num) hMs4 h4 hε).1
    · exact efInt_s0 hEQ (k := 2) (by norm_num) (by norm_num) hMs4 h4 hε
    · exact efInt_s0 hEG (k := 2) (by norm_num) (by norm_num) hMs4 h4 hε
  · intro i
    fin_cases i
    · exact tendsto_efi_s1 hEL hLL (k := 1) (Nat.zero_le 1) (by norm_num) hMs4 hes4
    · exact hLQ 2 (by norm_num) (by norm_num) _ hMs4 _ hes4
    · exact hLG 2 (by norm_num) (by norm_num) _ hMs4 _ hes4
  · have hlog := QED.TwoLoop.VPHalfAtAssembly.tendsto_logSum P fun f => (hMf f).ne'
    intro i
    fin_cases i
    · exact (((tendsto_const_nhds.mul hlog)).const_mul _)
    · exact ((tendsto_const_nhds.mul hlog).const_mul _).const_mul _ |>.neg
    · show Tendsto (fun ε : ℝ => κ * ((ε : ℂ) * cTwo P * logSum P ε)) _ _
      have h0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 ((0 : ℝ) : ℂ)) :=
        (continuous_ofReal.tendsto 0).comp (tendsto_id.mono_left nhdsWithin_le_nhds)
      have h := ((h0.mul_const (cTwo P)).mul hlog).const_mul κ
      simpa using h

end Unif

theorem SEEngU.mono {N : (Fin 4 → ℝ) → ℂ} {m M₀ : ℝ} {Pv : Fin 4 → ℝ} {K₁ K : ℝ} {k₀ : ℕ}
    (h : SEEngU N m M₀ Pv K₁ k₀) (hle : K₁ ≤ K) : SEEngU N m M₀ Pv K k₀ :=
  fun ε hε k h0 h3 Ms es hMs hes => (h ε hε k h0 h3 Ms es hMs hes).mono' hle

/-- **The limit under the Feynman-parameter integral, below threshold**: for `M₀ > 0` below
`m_γ`, `Λ` and every loop mass, and `-(m + M₀)² < p²`,
`∫₀¹ efi (seGInt_ε x) dx → ∫₀¹ seGIntLim x dx` as `ε → 0⁺`. -/
theorem tendsto_integral_efi_seGInt_of_lt {P : Params} {M₀ : ℝ} (hM₀ : 0 < M₀)
    (hmγ : M₀ ≤ P.mγ) (hΛ : M₀ ≤ P.Λ) (hmass : ∀ f, M₀ ≤ P.mass f) {p : Fin 4 → ℝ}
    (hp : -(P.m + M₀) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    Tendsto (fun ε => ∫ x in (0 : ℝ)..1, energyFirstIntegral (seGInt (withEps P ε) p α β x))
      (𝓝[>] 0) (𝓝 (∫ x in (0 : ℝ)..1, seGIntLim P p α β x)) := by
  have hm : 0 < P.m := hM₀.trans_le (hmass 0)
  have hpp : Minkowski.dot (-p) (-p) = Minkowski.dot p p := by
    simp only [Minkowski.dot, Pi.neg_apply]; ring_nf
  obtain ⟨c₀, hc₀, hPc⟩ := exists_pos_le_selfEnergyFeynmanMass hm hM₀ (hpp ▸ hp)
  obtain ⟨KL, hKL, hL⟩ := exists_seEngU_seAff hM₀.le hc₀ hPc (seCL P p α β) 3 α β
  obtain ⟨KG, hKG, hG⟩ := exists_seEngU_seAff hM₀.le hc₀ hPc (seCG P p α β) 2 α β
  obtain ⟨KQ, hKQ, hQ⟩ := exists_seEngU_seQuad hM₀.le hc₀ hPc p α β
  exact tendsto_integral_efi_seGInt hM₀ hmγ hΛ hmass (K := KL + KG + KQ) (by positivity)
    (hL.mono (by linarith)) (hQ.mono (by linarith)) (hG.mono (by linarith))
    (seLimU_seAff hM₀.le hc₀ hPc _ _ α β) (seLimU_seQuad hM₀.le hc₀ hPc p α β)
    (seLimU_seAff hM₀.le hc₀ hPc _ _ α β)

open QED.GradedProof.SE2 in
/-- **The limit of the self-energy class `V`, below threshold**: for admissible parameters with
`m < M₁, M₂`, `M₀ > 0` below `m_γ`, `Λ` and every loop mass, and `-(m + M₀)² < p²`, the value of
`repV` at the self-energy kinematics tends, as `ε → 0⁺`, to
`seConstLim - ∫₀¹ seGIntLim x dx`. -/
theorem tendsto_contractionValue₂_repV {P : Params} (hP : Adm P) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) {M₀ : ℝ} (hM₀ : 0 < M₀) (hmγ : M₀ ≤ P.mγ) (hΛ : M₀ ≤ P.Λ)
    (hmass : ∀ f, M₀ ≤ P.mass f) {p : Fin 4 → ℝ} (hp : -(P.m + M₀) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    Tendsto (fun ε => contractionValue₂ (withEps P ε) repV ![p] ![p] ![] ![α] ![β] ![])
      (𝓝[>] 0) (𝓝 (seConstLim P p α β - ∫ x in (0 : ℝ)..1, seGIntLim P p α β x)) := by
  have hm : 0 < P.m := hM₀.trans_le (hmass 0)
  have hpp : Minkowski.dot (-p) (-p) = Minkowski.dot p p := by
    simp only [Minkowski.dot, Pi.neg_apply]; ring_nf
  obtain ⟨c₀, hc₀, hPc⟩ := exists_pos_le_selfEnergyFeynmanMass hm hM₀ (hpp ▸ hp)
  obtain ⟨KL, hKL, hL⟩ := exists_seEngU_seAff hM₀.le hc₀ hPc (seCL P p α β) 3 α β
  obtain ⟨KG, hKG, hG⟩ := exists_seEngU_seAff hM₀.le hc₀ hPc (seCG P p α β) 2 α β
  obtain ⟨KQ, hKQ, hQ⟩ := exists_seEngU_seQuad hM₀.le hc₀ hPc p α β
  have hL' := hL.mono (K := KL + KG + KQ) (by linarith)
  have hQ' := hQ.mono (K := KL + KG + KQ) (by linarith)
  have hG' := hG.mono (K := KL + KG + KQ) (by linarith)
  have lL := seLimU_seAff hM₀.le hc₀ hPc (seCL P p α β) 3 α β
  have lQ := seLimU_seQuad hM₀.le hc₀ hPc p α β
  have lG := seLimU_seAff hM₀.le hc₀ hPc (seCG P p α β) 2 α β
  have h1 := tendsto_efi_seConst hM₀ hmγ hΛ hmass hL' hQ' hG' lL lQ lG
  have h2 := tendsto_integral_efi_seGInt hM₀ hmγ hΛ hmass (by positivity) hL' hQ' hG' lL lQ lG
  refine (h1.sub h2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hA : Adm (withEps P ε) :=
    ⟨hε, hP.hm, hP.hM₁, hP.hM₂, hP.hmγ, hP.hΛ, hP.pv₁, hP.pv₂⟩
  exact (contractionValue₂_repV_eq_spectral hA hM₁ hM₂ hM₀ hmγ hΛ hmass hp α β).1.symm

end QED.ChainProof.SetCRegDisp

end
