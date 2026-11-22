/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.CubeMellin
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The meromorphic continuation of cube Mellin integrals

Let `H(z, y)` be smooth on the closed unit cube, with all `y`-derivatives jointly continuous and
holomorphic in a complex parameter `z ∈ U`, and let `s(z) ∈ ℂ^N` be holomorphic. The cube Mellin
integral `M (H z) (s z) = ∫_{(0,1]^N} ∏ₖ yₖ ^ (sₖ(z) - 1) H(z, y) dy` converges where all
`re sₖ > 0`. Partial integration in a coordinate `i` (`QED.DimReg.cubeMellin_step`),

  `M H a = (M (H|_{yᵢ = 1}) (a with aᵢ = 1) - M (∂ᵢ H) (a with aᵢ + 1)) / aᵢ`,

trades the integral for two integrals with larger exponents. Iterating it along a list `L` of
coordinates gives `QED.DimReg.cubeCont`, the continuation. The derivatives taken so far are
recorded as a word `w` in the coordinates (so the family `D w = ∂_w H` never has to commute
derivatives), and the coordinates already evaluated at `1` as a finset `E`. For `L` containing
every coordinate `K` times (`QED.DimReg.contList`) this is `QED.DimReg.cubeMellinCont K`:

* it equals the integral where all `re sₖ > 0` (`QED.DimReg.cubeMellinCont_eq`);
* it is meromorphic in `z` where all `re sₖ > -K` (`QED.DimReg.meromorphicAt_cubeMellinCont`);
* it is analytic there if moreover no `sₖ(z₀)` lies in `{0, -1, -2, …}`
  (`QED.DimReg.analyticAt_cubeMellinCont`).

This is the `N`-dimensional parametric continuation behind sector decomposition: on a leaf of a
sector decomposition the integrand is `∏ₖ yₖ ^ (ℓₖ - 1) P̃(y) ^ (-d / 2)` with `P̃ ≥ 1`, so
`H = P̃ ^ (-d / 2)` qualifies (`QED.DimReg.PowerFamily`).

## Main definitions

* `QED.DimReg.CubeDerivFamily D U`: `D (w ++ [i]) = ∂ᵢ D w`, continuity and holomorphy.
* `QED.DimReg.cubeCont`, `QED.DimReg.cubeMellinCont`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.DimReg

variable {N : ℕ}

/-! ### Evaluation of coordinates at `1` -/

/-- The point `y` with the coordinates in `E` set to `1`. -/
def evalOne (E : Finset (Fin N)) (y : Fin N → ℝ) : Fin N → ℝ :=
  fun k => if k ∈ E then 1 else y k

theorem evalOne_empty (y : Fin N → ℝ) : evalOne ∅ y = y := by
  funext k; simp [evalOne]

theorem evalOne_mem_closedCube (E : Finset (Fin N)) {y : Fin N → ℝ} (hy : y ∈ closedCube N) :
    evalOne E y ∈ closedCube N := by
  rw [mem_closedCube] at hy ⊢
  intro k
  by_cases hk : k ∈ E
  · simp [evalOne, hk]
  · simpa [evalOne, hk] using hy k

theorem continuous_evalOne (E : Finset (Fin N)) : Continuous (evalOne E) :=
  continuous_pi fun k => by
    unfold evalOne
    split_ifs
    · exact continuous_const
    · exact continuous_apply k

theorem evalOne_apply_of_notMem {E : Finset (Fin N)} {i : Fin N} (hi : i ∉ E) (y : Fin N → ℝ) :
    evalOne E y i = y i := by
  simp [evalOne, hi]

theorem evalOne_insert {E : Finset (Fin N)} {i : Fin N} (hi : i ∉ E) (y : Fin N → ℝ) :
    evalOne (insert i E) y = evalOne E (Function.update y i 1) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [evalOne, hi]
  · simp [evalOne, hk]

theorem evalOne_update {E : Finset (Fin N)} {i : Fin N} (hi : i ∉ E) (y : Fin N → ℝ) (t : ℝ) :
    evalOne E (Function.update y i t) = Function.update (evalOne E y) i t := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [evalOne, hi]
  · simp [evalOne, Function.update_of_ne hk]

/-! ### Families of derivatives -/

/-- A family `D w` of iterated `y`-derivatives along words `w` in the coordinates, depending on a
complex parameter `z ∈ U`: `D (w ++ [i]) = ∂ᵢ D w` at the points of the closed cube with
`0 < yᵢ < 1`, each `D w` jointly continuous on `U × [0, 1]^N` and holomorphic in `z`. -/
structure CubeDerivFamily (D : List (Fin N) → ℂ → (Fin N → ℝ) → ℂ) (U : Set ℂ) : Prop where
  hasDerivAt : ∀ w i, ∀ z ∈ U, ∀ y ∈ closedCube N, y i ∈ Ioo (0 : ℝ) 1 →
    HasDerivAt (fun t => D w z (Function.update y i t)) (D (w ++ [i]) z y) (y i)
  continuousOn : ∀ w,
    ContinuousOn (fun p : ℂ × (Fin N → ℝ) => D w p.1 p.2) (U ×ˢ closedCube N)
  differentiableOn : ∀ w, ∀ y ∈ closedCube N, DifferentiableOn ℂ (fun z => D w z y) U

/-! ### The continuation -/

/-- The exponents after the partial integrations recorded by `w` and `E`: `1` on `E`, and
`sₖ + #{k in w}` elsewhere. -/
def contExp (s : ℂ → Fin N → ℂ) (w : List (Fin N)) (E : Finset (Fin N)) (z : ℂ) (k : Fin N) :
    ℂ :=
  if k ∈ E then 1 else s z k + w.count k

/-- The continuation of the cube Mellin integral by partial integration along the list `L` of
coordinates, from the state `(w, E)`. -/
noncomputable def cubeCont (D : List (Fin N) → ℂ → (Fin N → ℝ) → ℂ) (s : ℂ → Fin N → ℂ) :
    List (Fin N) → List (Fin N) → Finset (Fin N) → ℂ → ℂ
  | [], w, E, z => cubeMellin (fun y => D w z (evalOne E y)) (contExp s w E z)
  | i :: L, w, E, z => if i ∈ E then cubeCont D s L w E z else
      (cubeCont D s L w (insert i E) z - cubeCont D s L (w ++ [i]) E z) / (s z i + w.count i)

variable {D : List (Fin N) → ℂ → (Fin N → ℝ) → ℂ} {s : ℂ → Fin N → ℂ} {U : Set ℂ}

theorem count_cons_of_ne {i k : Fin N} (h : k ≠ i) (L : List (Fin N)) :
    (i :: L).count k = L.count k := by
  simp [Ne.symm h]

theorem count_cons_self (k : Fin N) (L : List (Fin N)) : (k :: L).count k = L.count k + 1 := by
  simp

theorem count_append_of_ne {i k : Fin N} (h : k ≠ i) (w : List (Fin N)) :
    (w ++ [i]).count k = w.count k := by
  simp [List.count_append, Ne.symm h]

theorem count_append_self (k : Fin N) (w : List (Fin N)) : (w ++ [k]).count k = w.count k + 1 := by
  simp [List.count_append]

theorem contExp_insert {w : List (Fin N)} {E : Finset (Fin N)} {i : Fin N} (z : ℂ) :
    contExp s w (insert i E) z = Function.update (contExp s w E z) i 1 := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [contExp]
  · simp [contExp, hk]

theorem contExp_append {w : List (Fin N)} {E : Finset (Fin N)} {i : Fin N} (hi : i ∉ E)
    (z : ℂ) :
    contExp s (w ++ [i]) E z = Function.update (contExp s w E z) i (contExp s w E z i + 1) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp only [contExp, hi, ite_false, count_append_self, Function.update_self]
    push_cast; ring
  · simp only [contExp, Function.update_of_ne hk, count_append_of_ne hk]

theorem count_append_singleton (w : List (Fin N)) (i k : Fin N) :
    ((w ++ [i]).count k : ℝ) = w.count k + if k = i then 1 else 0 := by
  by_cases hk : k = i
  · subst hk; simp
  · simp [count_append_of_ne hk, hk]

/-- **The continuation agrees with the integral.** Where all exponents of the state have
positive real part, `cubeCont` is the cube Mellin integral of the state. -/
theorem cubeCont_eq (hD : CubeDerivFamily D U) {z : ℂ} (hz : z ∈ U) :
    ∀ (L w : List (Fin N)) (E : Finset (Fin N)), (∀ k ∉ E, 0 < (s z k + w.count k).re) →
      cubeCont D s L w E z = cubeCont D s [] w E z
  | [], w, E, _ => rfl
  | i :: L, w, E, h => by
    by_cases hi : i ∈ E
    · simp only [cubeCont, hi, ite_true]
      exact cubeCont_eq hD hz L w E h
    have h1 : ∀ k ∉ insert i E, 0 < (s z k + w.count k).re := fun k hk =>
      h k fun h' => hk (Finset.mem_insert_of_mem h')
    have h2 : ∀ k ∉ E, 0 < (s z k + (w ++ [i]).count k).re := by
      intro k hk
      have := h k hk
      simp only [add_re, natCast_re] at this ⊢
      rw [count_append_singleton]
      split_ifs <;> linarith
    simp only [cubeCont, hi, ite_false]
    rw [cubeCont_eq hD hz L w (insert i E) h1, cubeCont_eq hD hz L (w ++ [i]) E h2]
    simp only [cubeCont]
    have ha : ∀ k, 0 < (contExp s w E z k).re := by
      intro k
      by_cases hk : k ∈ E
      · simp [contExp, hk]
      · simpa [contExp, hk] using h k hk
    have hai : contExp s w E z i = s z i + w.count i := by simp [contExp, hi]
    have hne : s z i + w.count i ≠ 0 := by
      intro h0; have := ha i; rw [hai, h0] at this; simp at this
    have hc : ∀ w', ContinuousOn (fun y => D w' z (evalOne E y)) (closedCube N) := fun w' =>
      (hD.continuousOn w').comp (continuousOn_const.prodMk (continuous_evalOne E).continuousOn)
        fun y hy => ⟨hz, evalOne_mem_closedCube E hy⟩
    have hstep := cubeMellin_step (i := i) (hc w) (hc (w ++ [i])) (fun y hy hyi => by
      have := hD.hasDerivAt w i z hz (evalOne E y) (evalOne_mem_closedCube E hy)
        (by rwa [evalOne_apply_of_notMem hi])
      rw [evalOne_apply_of_notMem hi] at this
      simpa only [evalOne_update hi] using this) ha
    rw [← contExp_insert, ← contExp_append hi, hai] at hstep
    simp only [← evalOne_insert hi] at hstep
    rw [div_eq_iff hne, ← hstep]
    ring

/-- **Meromorphy of the continuation.** Where every coordinate `k ∉ E` satisfies
`re sₖ(z₀) + #{k in w} > -#{k in L}`, `cubeCont D s L w E` is meromorphic at `z₀`. -/
theorem meromorphicAt_cubeCont (hU : IsOpen U) (hD : CubeDerivFamily D U)
    (hs : ∀ k, DifferentiableOn ℂ (fun z => s z k) U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∀ (L w : List (Fin N)) (E : Finset (Fin N)),
      (∀ k ∉ E, -(L.count k : ℝ) < (s z₀ k).re + w.count k) →
      MeromorphicAt (cubeCont D s L w E) z₀
  | [], w, E, h => by
    refine (analyticAt_cubeMellin_param (H := fun z y => D w z (evalOne E y))
      (a := fun z => contExp s w E z) hU ?_ ?_ ?_ hz₀ ?_).meromorphicAt
    · exact (hD.continuousOn w).comp (continuous_fst.prodMk
        ((continuous_evalOne E).comp continuous_snd)).continuousOn
        fun p hp => ⟨hp.1, evalOne_mem_closedCube E hp.2⟩
    · exact fun y hy => hD.differentiableOn w _ (evalOne_mem_closedCube E hy)
    · intro k
      unfold contExp
      split_ifs
      · exact differentiableOn_const _
      · exact (hs k).add_const _
    · intro k
      by_cases hk : k ∈ E
      · simp [contExp, hk]
      · have := h k hk
        simp only [List.count_nil, CharP.cast_eq_zero, neg_zero] at this
        simpa [contExp, hk] using this
  | i :: L, w, E, h => by
    by_cases hi : i ∈ E
    · have he : cubeCont D s (i :: L) w E = cubeCont D s L w E := by
        funext z; simp [cubeCont, hi]
      rw [he]
      refine meromorphicAt_cubeCont hU hD hs hz₀ L w E fun k hk => ?_
      have := h k hk
      have hki : k ≠ i := fun e => hk (e ▸ hi)
      rwa [count_cons_of_ne hki] at this
    have he : cubeCont D s (i :: L) w E = fun z =>
        (cubeCont D s L w (insert i E) z - cubeCont D s L (w ++ [i]) E z) /
          (s z i + w.count i) := by
      funext z; simp [cubeCont, hi]
    rw [he]
    have h1 := meromorphicAt_cubeCont hU hD hs hz₀ L w (insert i E) fun k hk => by
      have := h k fun h' => hk (Finset.mem_insert_of_mem h')
      have hki : k ≠ i := fun e => hk (e ▸ Finset.mem_insert_self i E)
      rwa [count_cons_of_ne hki] at this
    have h2 := meromorphicAt_cubeCont hU hD hs hz₀ L (w ++ [i]) E fun k hk => by
      have := h k hk
      rw [count_append_singleton]
      by_cases hki : k = i
      · subst hki; rw [count_cons_self] at this; push_cast at this
        simp only [ite_true]; linarith
      · rw [count_cons_of_ne hki] at this; simp only [hki, ite_false]; linarith
    have hden : AnalyticAt ℂ (fun z => s z i + (w.count i : ℂ)) z₀ :=
      ((hs i).analyticAt (hU.mem_nhds hz₀)).add analyticAt_const
    exact (h1.sub h2).div hden.meromorphicAt

/-- **Analyticity of the continuation** where moreover no exponent of the state lies in
`{0, -1, -2, …}`. -/
theorem analyticAt_cubeCont (hU : IsOpen U) (hD : CubeDerivFamily D U)
    (hs : ∀ k, DifferentiableOn ℂ (fun z => s z k) U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∀ (L w : List (Fin N)) (E : Finset (Fin N)),
      (∀ k ∉ E, -(L.count k : ℝ) < (s z₀ k).re + w.count k) →
      (∀ k ∉ E, ∀ j : ℕ, s z₀ k + w.count k + j ≠ 0) →
      AnalyticAt ℂ (cubeCont D s L w E) z₀
  | [], w, E, h, _ => by
    refine analyticAt_cubeMellin_param (H := fun z y => D w z (evalOne E y))
      (a := fun z => contExp s w E z) hU ?_ ?_ ?_ hz₀ ?_
    · exact (hD.continuousOn w).comp (continuous_fst.prodMk
        ((continuous_evalOne E).comp continuous_snd)).continuousOn
        fun p hp => ⟨hp.1, evalOne_mem_closedCube E hp.2⟩
    · exact fun y hy => hD.differentiableOn w _ (evalOne_mem_closedCube E hy)
    · intro k
      unfold contExp
      split_ifs
      · exact differentiableOn_const _
      · exact (hs k).add_const _
    · intro k
      by_cases hk : k ∈ E
      · simp [contExp, hk]
      · have := h k hk
        simp only [List.count_nil, CharP.cast_eq_zero, neg_zero] at this
        simpa [contExp, hk] using this
  | i :: L, w, E, h, hp => by
    by_cases hi : i ∈ E
    · have he : cubeCont D s (i :: L) w E = cubeCont D s L w E := by
        funext z; simp [cubeCont, hi]
      rw [he]
      refine analyticAt_cubeCont hU hD hs hz₀ L w E (fun k hk => ?_) hp
      have := h k hk
      have hki : k ≠ i := fun e => hk (e ▸ hi)
      rwa [count_cons_of_ne hki] at this
    have he : cubeCont D s (i :: L) w E = fun z =>
        (cubeCont D s L w (insert i E) z - cubeCont D s L (w ++ [i]) E z) /
          (s z i + w.count i) := by
      funext z; simp [cubeCont, hi]
    rw [he]
    have h1 := analyticAt_cubeCont hU hD hs hz₀ L w (insert i E) (fun k hk => by
      have := h k fun h' => hk (Finset.mem_insert_of_mem h')
      have hki : k ≠ i := fun e => hk (e ▸ Finset.mem_insert_self i E)
      rwa [count_cons_of_ne hki] at this)
      fun k hk => hp k fun h' => hk (Finset.mem_insert_of_mem h')
    have h2 := analyticAt_cubeCont hU hD hs hz₀ L (w ++ [i]) E (fun k hk => by
      have := h k hk
      rw [count_append_singleton]
      by_cases hki : k = i
      · subst hki; rw [count_cons_self] at this; push_cast at this
        simp only [ite_true]; linarith
      · rw [count_cons_of_ne hki] at this; simp only [hki, ite_false]; linarith)
      fun k hk j => by
        by_cases hki : k = i
        · subst hki
          have := hp k hk (j + 1)
          rw [count_append_self]; push_cast at this ⊢
          convert this using 1; ring
        · rw [count_append_of_ne hki]; exact hp k hk j
    have hden : AnalyticAt ℂ (fun z => s z i + (w.count i : ℂ)) z₀ :=
      ((hs i).analyticAt (hU.mem_nhds hz₀)).add analyticAt_const
    have hne : s z₀ i + (w.count i : ℂ) ≠ 0 := by simpa using hp i hi 0
    exact (h1.sub h2).div hden hne

/-! ### Every coordinate `K` times -/

/-- The list containing every coordinate `K` times. -/
def contList (N K : ℕ) : List (Fin N) := (List.finRange N).flatMap fun k => List.replicate K k

theorem count_contList (K : ℕ) (k : Fin N) : (contList N K).count k = K := by
  rw [contList, List.count_flatMap, ← Fin.sum_univ_def]
  simp [List.count_replicate]

/-- The `K`-fold continuation of the cube Mellin integral `M (D [] z) (s z)`. -/
noncomputable def cubeMellinCont (K : ℕ) (D : List (Fin N) → ℂ → (Fin N → ℝ) → ℂ)
    (s : ℂ → Fin N → ℂ) (z : ℂ) : ℂ :=
  cubeCont D s (contList N K) [] ∅ z

/-- **The continuation is the integral** where all `re sₖ > 0`. -/
theorem cubeMellinCont_eq (K : ℕ) (hD : CubeDerivFamily D U) {z : ℂ} (hz : z ∈ U)
    (hre : ∀ k, 0 < (s z k).re) : cubeMellinCont K D s z = cubeMellin (D [] z) (s z) := by
  rw [cubeMellinCont, cubeCont_eq hD hz _ _ _ (fun k _ => by simpa using hre k)]
  simp only [cubeCont, evalOne_empty]
  congr 1
  funext k
  simp [contExp]

/-- **Meromorphy** where all `re sₖ > -K`. -/
theorem meromorphicAt_cubeMellinCont (K : ℕ) (hU : IsOpen U) (hD : CubeDerivFamily D U)
    (hs : ∀ k, DifferentiableOn ℂ (fun z => s z k) U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hre : ∀ k, -(K : ℝ) < (s z₀ k).re) : MeromorphicAt (cubeMellinCont K D s) z₀ :=
  meromorphicAt_cubeCont hU hD hs hz₀ _ _ _ fun k _ => by
    simpa [count_contList] using hre k

/-- **Analyticity** where all `re sₖ > -K` and no `sₖ(z₀)` lies in `{0, -1, -2, …}`. -/
theorem analyticAt_cubeMellinCont (K : ℕ) (hU : IsOpen U) (hD : CubeDerivFamily D U)
    (hs : ∀ k, DifferentiableOn ℂ (fun z => s z k) U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hre : ∀ k, -(K : ℝ) < (s z₀ k).re) (hpole : ∀ k, ∀ j : ℕ, s z₀ k + j ≠ 0) :
    AnalyticAt ℂ (cubeMellinCont K D s) z₀ :=
  analyticAt_cubeCont hU hD hs hz₀ _ _ _ (fun k _ => by simpa [count_contList] using hre k)
    fun k _ j => by simpa using hpole k j

end QED.DimReg
