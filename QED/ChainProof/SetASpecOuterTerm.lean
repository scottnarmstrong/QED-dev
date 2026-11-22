/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecOuterAlg

/-!
# Set (a): the outer numerator reduction as uniform spectral terms of the limit engine

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`,
obligation (O) of `QED.ChainProof.SetASpec.SetAOuterSpec`. A *uniform spectral photon term*
(`SAOuterTerm`) is one term `t(k) (k²)ʲ ∫_Δ w_ε(x) fDen(√A(x), ε, ξ(x), k)^{-r}` of an
`ε`-uniform spectral form of the two-loop vacuum polarization, with `SAOuterTerm.Good`: the
tensor shape `j + [t = k k] ≤ 2`, measurable masses `√A ≥ M_lo` and parameters `ξ ∈ (0, 1)`
a.e., weights with one integrable majorant on `ε ∈ (0, 1]` converging almost everywhere. Nothing
else about the spectral form is assumed.

* `SAOuterForm`: an outer integrand `f ε` whose energy-first integral is, at every
  `ε ∈ (0, 1]`, integrable in both stages and a finite `ε`-independent combination of the values
  `QED.ChainProof.SetASpec.SALimTerm.val` of uniform spectral terms of the engine satisfying
  `SALimTerm.Hyp 2 M_lo` over `(m_γ, Λ, m_γ, Λ)`; closed under sums, constant multiples and
  list sums.
* **`SAOuterTerm.outerForm`**: the outer integrand `saOuterInt` of one good term, every entry,
  is `SAOuterForm`. The numerators are `numG` for `t = g` and `numS`, `numL`, `numQ` for
  `t = k k` (`QED.ChainProof.HCBB2.QuadN`), the powers of `k²` are `j` resp. `j + 1, j + 1, j`,
  all at most `2` (`saOuterInt_false`, `saOuterInt_true`).
* `saOuterPhoton_list`, `vertexChain_list_photon`: the sandwich of a list of terms is the list
  of sandwiches, and the vertex chain with it is the list of outer integrands.
* **`saOuterForm_list`**: for a list of good terms with constant coefficients, the vertex chain
  entry with the sandwiched sum is `SAOuterForm`.
* **`SAOuterForm.exists_finset`**: the form in the shape of the entries of `SetAOuterSpec`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.OneLoop QED.Integration.Feynman QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPUnitNested
open QED.TwoLoop.VPHalfAtAssembly QED.TwoLoop.VPHalfAtGen QED.TwoLoop.Insertion
open QED.ChainProof.HCBB2

/-! ### Integrability of a uniform engine term -/

/-- **A term satisfying `Hyp` is integrable in both stages** at every `ε ∈ (0, 1]`. -/
theorem SALimTerm.efInt_val {m M₀ Mlo : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) (hMlo : M₀ ≤ Mlo)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {k : ℕ} {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i)
    {τ : SALimTerm} (hτ : τ.Hyp k Mlo) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    EFInt (saLimTermInt τ.N m τ.j Ms τ.r τ.A τ.ξ (τ.w ε) ε p' p) := by
  obtain ⟨hNc, hNq, ⟨CN, hNb⟩, hjk, hA, hξ, hAlo, hξ01, ⟨h, hh, hw⟩, hwl⟩ := hτ
  exact ((saLim_tendsto_term hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMlo hjk Ms hMs τ.r hA hξ hAlo
    hξ01 τ.w τ.w₀ h hh (fun ε h0 h1 => (hw ε h0 h1).1) (fun ε h0 h1 => (hw ε h0 h1).2)
    hwl).1 ε hε hε1).1

/-! ### Outer forms -/

/-- **The outer form of an integrand**: at every `ε ∈ (0, 1]`, `f ε` is integrable in both stages
and its energy-first integral is a finite combination, with `ε`-independent coefficients, of
uniform spectral terms of the engine satisfying `Hyp 2 M_lo`, over the masses `Ms`. -/
def SAOuterForm (m Mlo : ℝ) (Ms : Fin (2 + 2) → ℝ) (p' p : Fin 4 → ℝ)
    (f : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ l : List (ℂ × SALimTerm), (∀ q ∈ l, q.2.Hyp 2 Mlo) ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    EFInt (f ε) ∧ energyFirstIntegral (f ε) = (l.map fun q => q.1 * q.2.val m Ms p' p ε).sum

namespace SAOuterForm

variable {m Mlo : ℝ} {Ms : Fin (2 + 2) → ℝ} {p' p : Fin 4 → ℝ} {f g : ℝ → (Fin 4 → ℝ) → ℂ}

theorem zero : SAOuterForm m Mlo Ms p' p fun _ _ => 0 := by
  refine ⟨[], by simp, fun ε _ _ => ⟨⟨fun _ => integrable_zero _ _ _, ?_⟩, ?_⟩⟩
  · simp
  · simp [energyFirstIntegral]

theorem add (hf : SAOuterForm m Mlo Ms p' p f) (hg : SAOuterForm m Mlo Ms p' p g) :
    SAOuterForm m Mlo Ms p' p fun ε ℓ => f ε ℓ + g ε ℓ := by
  obtain ⟨l, hl, hf⟩ := hf
  obtain ⟨l', hl', hg⟩ := hg
  refine ⟨l ++ l', fun q hq => ?_, fun ε hε hε1 => ?_⟩
  · rcases List.mem_append.mp hq with h | h
    exacts [hl q h, hl' q h]
  obtain ⟨h1, e1⟩ := hf ε hε hε1
  obtain ⟨h2, e2⟩ := hg ε hε hε1
  refine ⟨h1.add h2, ?_⟩
  rw [efi_add h1 h2, e1, e2, List.map_append, List.sum_append]

theorem const_mul (c : ℂ) (hf : SAOuterForm m Mlo Ms p' p f) :
    SAOuterForm m Mlo Ms p' p fun ε ℓ => c * f ε ℓ := by
  obtain ⟨l, hl, hf⟩ := hf
  refine ⟨l.map fun q => (c * q.1, q.2), fun q hq => ?_, fun ε hε hε1 => ?_⟩
  · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact hl q' hq'
  obtain ⟨h1, e1⟩ := hf ε hε hε1
  refine ⟨h1.const_mul c, ?_⟩
  rw [efi_const_mul, e1, List.map_map, ← List.sum_map_mul_left]
  congr 1
  exact List.map_congr_left fun q _ => by simp only [Function.comp_apply]; ring

theorem congr (hf : SAOuterForm m Mlo Ms p' p f)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → f ε = g ε) : SAOuterForm m Mlo Ms p' p g := by
  obtain ⟨l, hl, hf⟩ := hf
  exact ⟨l, hl, fun ε hε hε1 => h ε hε hε1 ▸ hf ε hε hε1⟩

theorem list_sum {ι : Type*} (L : List ι) (F : ι → ℝ → (Fin 4 → ℝ) → ℂ)
    (hF : ∀ i ∈ L, SAOuterForm m Mlo Ms p' p (F i)) :
    SAOuterForm m Mlo Ms p' p fun ε ℓ => (L.map fun i => F i ε ℓ).sum := by
  induction L with
  | nil => simpa using zero
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF i List.mem_cons_self).add (ih fun i hi => hF i (List.mem_cons_of_mem _ hi))

/-- **One engine term** satisfying `Hyp` is an outer form. -/
theorem single {M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) (hMlo : M₀ ≤ Mlo)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hMs : ∀ i, M₀ ≤ Ms i) {τ : SALimTerm} (hτ : τ.Hyp 2 Mlo) :
    SAOuterForm m Mlo Ms p' p fun ε => saLimTermInt τ.N m τ.j Ms τ.r τ.A τ.ξ (τ.w ε) ε p' p :=
  ⟨[(1, τ)], by simpa using hτ, fun ε hε hε1 =>
    ⟨SALimTerm.efInt_val hm hM₀ hMlo hp' hp hp0' hp0 hMs hτ hε hε1, by
      simp [SALimTerm.val]⟩⟩

/-- A default term (used only outside the index set). -/
noncomputable def defaultTerm : SALimTerm :=
  ⟨fun _ => 0, 0, 0, 0, 0, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ => 0⟩

/-- **The outer form in the shape of the entries of `SetAOuterSpec`.** -/
theorem exists_finset (hf : SAOuterForm m Mlo Ms p' p f) :
    ∃ (s : Finset ℕ) (c : ℕ → ℂ) (τ : ℕ → SALimTerm), (∀ i ∈ s, (τ i).Hyp 2 Mlo) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → EFInt (f ε) ∧
        energyFirstIntegral (f ε) = ∑ i ∈ s, c i * (τ i).val m Ms p' p ε := by
  obtain ⟨l, hl, hf⟩ := hf
  refine ⟨Finset.range l.length, fun i => (l.getD i (0, defaultTerm)).1,
    fun i => (l.getD i (0, defaultTerm)).2, fun i hi => ?_, fun ε hε hε1 => ?_⟩
  · have h := Finset.mem_range.mp hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    exact hl _ (List.getElem_mem _)
  obtain ⟨h1, e1⟩ := hf ε hε hε1
  refine ⟨h1, ?_⟩
  rw [e1, Finset.sum_range, ← Fin.sum_univ_fun_getElem]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2, Option.getD_some]

end SAOuterForm

/-! ### Uniform spectral photon terms -/

/-- **A uniform spectral photon term**: `t(k) (k²)ʲ ∫_Δ w_ε(x) fDen(√A(x), ε, ξ(x), k)^{-r}` on
the simplex of dimension `n`, with limit weight `w₀`. -/
structure SAOuterTerm where
  /-- The tensor structure (`saTens`). -/
  t : Bool
  /-- The power of `k²`. -/
  j : ℕ
  /-- The power of the spectral factor. -/
  r : ℕ
  /-- The simplex dimension. -/
  n : ℕ
  /-- The mass square of the spectral factor. -/
  A : (Fin n → ℝ) → ℝ
  /-- The Feynman parameter of the spectral factor. -/
  ξ : (Fin n → ℝ) → ℝ
  /-- The weight at `ε`. -/
  w : ℝ → (Fin n → ℝ) → ℂ
  /-- The limit weight. -/
  w₀ : (Fin n → ℝ) → ℂ

namespace SAOuterTerm

/-- The hypotheses on a term: the tensor shape `j + [t = k k] ≤ 2` and the hypotheses of the
engine on the masses, parameters and weights. -/
def Good (Mlo : ℝ) (τ : SAOuterTerm) : Prop :=
  τ.j + (if τ.t then 1 else 0) ≤ 2 ∧ Measurable τ.A ∧ Measurable τ.ξ ∧ (∀ x, Mlo ^ 2 ≤ τ.A x) ∧
    (∀ᵐ x ∂(volume.restrict (simplexSet τ.n)), τ.ξ x ∈ Ioo (0 : ℝ) 1) ∧
    (∃ h : (Fin τ.n → ℝ) → ℝ, IntegrableOn h (simplexSet τ.n) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        AEStronglyMeasurable (τ.w ε) (volume.restrict (simplexSet τ.n)) ∧
        ∀ᵐ x ∂(volume.restrict (simplexSet τ.n)), ‖τ.w ε x‖ ≤ h x) ∧
    ∀ᵐ x ∂(volume.restrict (simplexSet τ.n)),
      Tendsto (fun ε => τ.w ε x) (𝓝[>] 0) (𝓝 (τ.w₀ x))

/-- The value of the term at `ε`, `k`, `(a, b)`. -/
noncomputable def val (τ : SAOuterTerm) (ε : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) : ℂ :=
  saTens τ.t k a b * saSpecScalar τ.j τ.r τ.A τ.ξ (τ.w ε) ε k

/-- The engine term with numerator `N`, leading coefficient `α` and power `j'`. -/
def engine (τ : SAOuterTerm) (N : (Fin 4 → ℝ) → ℂ) (α : ℂ) (j' : ℕ) : SALimTerm :=
  ⟨N, α, j', τ.r, τ.n, τ.A, τ.ξ, τ.w, τ.w₀⟩

theorem engine_hyp {Mlo : ℝ} {τ : SAOuterTerm} (hτ : τ.Good Mlo) {N : (Fin 4 → ℝ) → ℂ}
    (hN : QuadN N) {j' : ℕ} (hj' : j' ≤ 2) : (τ.engine N hN.quad.choose j').Hyp 2 Mlo := by
  obtain ⟨-, hA, hξ, hAlo, hξ01, hw, hwl⟩ := hτ
  exact ⟨hN.cont, hN.quad.choose_spec, hN.bound, hj', hA, hξ, hAlo, hξ01, hw, hwl⟩

/-- The outer integrand of the term, entry `(i, j)`. -/
noncomputable def outer (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (τ : SAOuterTerm)
    (ε : ℝ) (ℓ : Fin 4 → ℝ) : ℂ :=
  saOuterInt e m mγ Λ p' p μ i j τ.t τ.j τ.r τ.A τ.ξ (τ.w ε) ε ℓ

/-- The engine terms of the outer integrand, with their coefficients. -/
noncomputable def pieces (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (τ : SAOuterTerm) :
    List (ℂ × SALimTerm) :=
  let c : ℂ := kap e * (((Λ ^ 2 - mγ ^ 2) ^ 2 : ℝ) : ℂ)
  if τ.t then
    [(c, τ.engine (numS μ i j) (quadN_numS μ i j).quad.choose (τ.j + 1)),
      (c, τ.engine (numL m p' p μ i j) (quadN_numL m p' p μ i j).quad.choose (τ.j + 1)),
      (c, τ.engine (numQ m p' p μ i j) (quadN_numQ m p' p μ i j).quad.choose τ.j)]
  else [(c, τ.engine (numG m p' p μ i j) (quadN_numG m p' p μ i j).quad.choose τ.j)]

theorem pieces_hyp {Mlo : ℝ} {τ : SAOuterTerm} (hτ : τ.Good Mlo) (e m mγ Λ : ℝ)
    (p' p : Fin 4 → ℝ) (μ i j : Fin 4) : ∀ q ∈ τ.pieces e m mγ Λ p' p μ i j, q.2.Hyp 2 Mlo := by
  have hj := hτ.1
  intro q hq
  unfold pieces at hq
  cases ht : τ.t <;> simp only [ht, ite_true, ite_false, Bool.false_eq_true] at hq hj
  · simp only [List.mem_singleton] at hq
    subst hq
    exact engine_hyp hτ (quadN_numG _ _ _ _ _ _) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact engine_hyp hτ (quadN_numS _ _ _) (by omega)
    · exact engine_hyp hτ (quadN_numL _ _ _ _ _ _) (by omega)
    · exact engine_hyp hτ (quadN_numQ _ _ _ _ _ _) (by omega)

/-- **The outer integrand of a term as engine terms**, pointwise at `ε > 0`. -/
theorem outer_eq (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (τ : SAOuterTerm) {ε : ℝ}
    (hε : 0 < ε) (ℓ : Fin 4 → ℝ) :
    τ.outer e m mγ Λ p' p μ i j ε ℓ = ((τ.pieces e m mγ Λ p' p μ i j).map fun q =>
      q.1 * saLimTermInt q.2.N m q.2.j (saMs4 mγ Λ) q.2.r q.2.A q.2.ξ (q.2.w ε) ε p' p ℓ).sum := by
  unfold outer pieces
  cases ht : τ.t
  · simp only [Bool.false_eq_true, ite_false, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, engine]
    exact saOuterInt_false e m mγ Λ p' p μ i j _ _ _ _ _ hε ℓ
  · simp only [ite_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      engine]
    rw [saOuterInt_true e m mγ Λ p' p μ i j _ _ _ _ _ hε ℓ]
    ring

/-- **(O) for one term**: for a good term and an on-shell positive-energy pair, every entry of
the outer integrand has an outer form over `(m_γ, Λ, m_γ, Λ)`, with the engine terms `pieces`. -/
theorem outerForm {m M₀ Mlo mγ Λ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) (hMlo : M₀ ≤ Mlo)
    (hmγ : M₀ ≤ mγ) (hΛ : M₀ ≤ Λ) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (e : ℝ)
    {τ : SAOuterTerm} (hτ : τ.Good Mlo) (μ i j : Fin 4) :
    SAOuterForm m Mlo (saMs4 mγ Λ) p' p (τ.outer e m mγ Λ p' p μ i j) := by
  have hMs : ∀ i, M₀ ≤ saMs4 mγ Λ i := fun i => by
    fin_cases i <;> simp [saMs4, hmγ, hΛ]
  have hP := pieces_hyp hτ e m mγ Λ p' p μ i j
  refine (SAOuterForm.list_sum (τ.pieces e m mγ Λ p' p μ i j) (fun q ε ℓ => q.1 *
    saLimTermInt q.2.N m q.2.j (saMs4 mγ Λ) q.2.r q.2.A q.2.ξ (q.2.w ε) ε p' p ℓ)
    fun q hq => (SAOuterForm.single hm hM₀ hMlo hp' hp hp0' hp0 hMs (hP q hq)).const_mul q.1
    ).congr fun ε hε _ => ?_
  funext ℓ
  exact (outer_eq e m mγ Λ p' p μ i j τ hε ℓ).symm

end SAOuterTerm

/-! ### Lists of terms -/

/-- The photon tensor of a list of terms with constant coefficients at `ε`. -/
noncomputable def saOuterTensor (L : List (ℂ × SAOuterTerm)) (ε : ℝ) (k : Fin 4 → ℝ)
    (a b : Fin 4) : ℂ :=
  (L.map fun q => q.1 * q.2.val ε k a b).sum

/-- **The sandwich of a list of terms is the list of sandwiches.** -/
theorem saOuterPhoton_list (mγ Λ : ℝ) (L : List (ℂ × SAOuterTerm)) (ε : ℝ) (k : Fin 4 → ℝ)
    (ν ρ : Fin 4) :
    ∑ a, ∑ b, photonPropagator mγ Λ ε k ν a * saOuterTensor L ε k a b *
        photonPropagator mγ Λ ε (-k) ρ b =
      (L.map fun q => q.1 * saOuterPhoton mγ Λ q.2.t q.2.j q.2.r q.2.A q.2.ξ (q.2.w ε) ε k ν ρ).sum
    := by
  induction L with
  | nil => simp [saOuterTensor]
  | cons q L ih =>
    simp only [saOuterTensor, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih, saOuterPhoton, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [SAOuterTerm.val]
    ring

/-- **The vertex chain with the sandwich of a list of terms is the list of outer integrands.** -/
theorem saOuterList_eq (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (L : List (ℂ × SAOuterTerm)) (ε : ℝ) (ℓ : Fin 4 → ℝ) :
    vertexChain e μ (electronPropagator m ε (p' + ℓ)) (electronPropagator m ε (p + ℓ))
        (fun ν ρ => ∑ a, ∑ b, photonPropagator mγ Λ ε ℓ ν a * saOuterTensor L ε ℓ a b *
          photonPropagator mγ Λ ε (-ℓ) ρ b) i j =
      (L.map fun q => q.1 * q.2.outer e m mγ Λ p' p μ i j ε ℓ).sum := by
  simp only [saOuterPhoton_list]
  induction L with
  | nil => simp [vertexChain]
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [vertexChain_add_photon, vertexChain_smul_photon, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, ih]
    rfl

/-- **(O) for a list of terms**: for good terms with constant coefficients and an on-shell
positive-energy pair, every entry of the vertex chain with the sandwich of their sum has an outer
form over `(m_γ, Λ, m_γ, Λ)`. -/
theorem saOuterForm_list {m M₀ Mlo mγ Λ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) (hMlo : M₀ ≤ Mlo)
    (hmγ : M₀ ≤ mγ) (hΛ : M₀ ≤ Λ) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (e : ℝ)
    (L : List (ℂ × SAOuterTerm)) (hL : ∀ q ∈ L, q.2.Good Mlo) (μ i j : Fin 4) :
    SAOuterForm m Mlo (saMs4 mγ Λ) p' p fun ε ℓ =>
      vertexChain e μ (electronPropagator m ε (p' + ℓ)) (electronPropagator m ε (p + ℓ))
        (fun ν ρ => ∑ a, ∑ b, photonPropagator mγ Λ ε ℓ ν a * saOuterTensor L ε ℓ a b *
          photonPropagator mγ Λ ε (-ℓ) ρ b) i j := by
  refine (SAOuterForm.list_sum L (fun q ε ℓ => q.1 * q.2.outer e m mγ Λ p' p μ i j ε ℓ)
    fun q hq => (SAOuterTerm.outerForm hm hM₀ hMlo hmγ hΛ hp' hp hp0' hp0 e (hL q hq) μ i j
      ).const_mul q.1).congr fun ε _ _ => ?_
  funext ℓ
  exact (saOuterList_eq e m mγ Λ p' p μ i j L ε ℓ).symm

end QED.ChainProof.SetASpec

end
