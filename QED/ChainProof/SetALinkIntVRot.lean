/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkIntVCx

/-!
# (T₉′) at three loops for products of line factors

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58), classes `VA`, `VB`, `VC`. Lines `i : ι` carry the momenta
`kᵢ = ∑ₛ aᵢₛ ℓₛ + qᵢ` (`rowMom3`, integer rows), the masses `msᵢ` of their denominators and an
`AffPoly dᵢ` numerator `Nᵢ` with `dᵢ ≤ 2|msᵢ|`. Rows that agree up to sign are merged
(`cls`, rows `a'`). **`jef_lines3`**: if the merged exponents `eᵢ = 2|msᵢ| - dᵢ` pass the
basis criterion with threshold `5` (`BasisCrit`, `QED/ChainProof/SetALinkIntVMaj.lean`), then
`z ∏ᵢ Nᵢ(kᵢ) ∏_{M ∈ msᵢ} D_M(kᵢ)⁻¹` satisfies (T₉′) at three loops for every `ε > 0`, at any
masses and shifts.

## Proof

As for the bubble–bubble integrand of set (b) (`QED.ChainProof.RepsIntBB`): extend to complex
momenta (`AffPoly.exists_cx`, `dProdC`) and multiply the three loop energies by `z`
(`QED.ChainProof.RepsIntBB.rl`). On the rectangle `rotRect h`, `h` small against the energy
shifts, each factor is `≤ K (1 + |tᵢ|)^{-eᵢ}` at fixed spatial momenta (`norm_factor_rect`),
and the product is a multiple of the majorant on the energies, integrable by the criterion
with threshold `2` (`integrable_majF_real`): stage 1, and the domination of
`QED.Integration.ThreeLoop.integral_eq_rotate`. At `z = 1 + s i` each factor is
`≤ K ν(Lᵢ ℓ)^{-eᵢ}` in all momenta (`norm_factor_rot`), so the rotated integrand is integrable
on `(ℝ⁴)³` (`integrable_majF_four`), and stage 2 follows by
`QED.ChainProof.RepsIntBB.integrable_integral_join`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetALinkV

open QED.ChainProof.RepsIntBB QED.GradedProof.X0 QED.Integration.ThreeLoop
open QED.TwoLoop.JointIntegralInvariance

/-! ### Line momenta -/

/-- The momentum of a line at three loops. -/
noncomputable def rowMom3 (r : Fin 3 → ℤ) (q : Fin 4 → ℝ) (ℓ : Fin 3 → Fin 4 → ℝ) :
    Fin 4 → ℝ :=
  ∑ s, (r s : ℝ) • ℓ s + q

/-- The momentum of a line at complex loop momenta. -/
noncomputable def lc (r : Fin 3 → ℤ) (q : Fin 4 → ℝ) (w : Fin 3 → Fin 4 → ℂ) : Fin 4 → ℂ :=
  ∑ s, ((r s : ℤ) : ℂ) • w s + cv q

theorem lc_cv (r : Fin 3 → ℤ) (q : Fin 4 → ℝ) (ℓ : Fin 3 → Fin 4 → ℝ) :
    lc r q (fun s => cv (ℓ s)) = cv (rowMom3 r q ℓ) := by
  funext μ
  simp [lc, rowMom3, cv, Finset.sum_apply]

theorem lc_rl (r : Fin 3 → ℤ) (q : Fin 4 → ℝ) (z : ℂ) (τ : Fin 3 → ℝ)
    (v : Fin 3 → Fin 3 → ℝ) :
    lc r q (rl z τ v) =
      mk (z * ((∑ s, (r s : ℝ) * τ s : ℝ) : ℂ) + ((q 0 : ℝ) : ℂ))
        (∑ s, (r s : ℝ) • v s + Fin.tail q) := by
  funext μ
  refine Fin.cases ?_ (fun j => ?_) μ
  · simp only [lc, rl, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, mk_zero, cv, smul_eq_mul]
    push_cast
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  · simp [lc, rl, RepsIntBB.mk, cv, Finset.sum_apply, Fin.tail]

theorem differentiable_lc (r : Fin 3 → ℤ) (q : Fin 4 → ℝ) : Differentiable ℂ (lc r q) := by
  unfold lc
  refine (Differentiable.fun_sum fun s _ => ?_).add (differentiable_const _)
  exact (differentiable_apply (𝕜 := ℂ) (F' := fun _ : Fin 3 => Fin 4 → ℂ) s).const_smul
    (((r s : ℤ) : ℂ))

theorem linF_real (r : Fin 3 → ℤ) (τ : Fin 3 → ℝ) : linF r τ = ∑ s, (r s : ℝ) * τ s := by
  simp [linF]

theorem linF_cons (r : Fin 3 → ℤ) (ℓ : Fin 3 → Fin 4 → ℝ) :
    linF r ℓ = Fin.cons (∑ s, (r s : ℝ) * ℓ s 0) (∑ s, (r s : ℝ) • Fin.tail (ℓ s)) := by
  funext μ
  refine Fin.cases ?_ (fun j => ?_) μ <;> simp [linF, Finset.sum_apply, Fin.tail]

/-- Rows agreeing up to sign: the product of the line weights is the merged majorant. -/
theorem prod_nu_eq_majF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    [Fintype ι] (a : ι → Fin 3 → ℤ) {m' : ℕ} (a' : Fin m' → Fin 3 → ℤ) (cls : ι → Fin m')
    (hs : ∀ i, a i = a' (cls i) ∨ a i = -a' (cls i)) (e : ι → ℕ) (ℓ : Fin 3 → E) :
    ∏ i, (nu (linF (a i) ℓ) ^ e i)⁻¹ =
      majF a' (fun c => ∑ i ∈ Finset.univ.filter (fun i => cls i = c), e i) ℓ := by
  classical
  have h1 : ∀ i, nu (linF (a i) ℓ) = nu (linF (a' (cls i)) ℓ) := fun i => by
    rcases hs i with h | h <;> rw [h]
    simp [nu, linF_neg]
  unfold majF
  simp only [h1]
  rw [← Finset.prod_fiberwise (s := Finset.univ) (g := cls)
    (f := fun i => (nu (linF (a' (cls i)) ℓ) ^ e i)⁻¹)]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum, Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.mp hx).2]

/-! ### Regularity of the rotated loop momenta -/

theorem differentiableAt_rl (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => rl w τ v) z := by
  refine differentiableAt_pi.2 fun s => ?_
  change DifferentiableAt ℂ (fun w : ℂ => (Fin.cons (w * (τ s : ℂ))
    (fun i => ((v s i : ℝ) : ℂ)) : Fin 4 → ℂ)) z
  exact differentiableAt_cons (differentiableAt_id.mul_const _) (differentiableAt_const _)

theorem continuous_rl (z : ℂ) :
    Continuous fun ℓ : Fin 3 → Fin 4 → ℝ => rl z (fun s => ℓ s 0) (fun s => Fin.tail (ℓ s)) := by
  refine continuous_pi fun s => continuous_pi fun μ => ?_
  refine Fin.cases ?_ (fun j => ?_) μ
  · simp only [rl, mk_zero]
    exact continuous_const.mul (continuous_ofReal.comp
      ((continuous_apply 0).comp (continuous_apply s)))
  · simp only [rl, RepsIntBB.mk, Fin.cons_succ, Fin.tail]
    exact continuous_ofReal.comp ((continuous_apply j.succ).comp (continuous_apply s))

theorem continuous_rl_tau (z : ℂ) (v : Fin 3 → Fin 3 → ℝ) :
    Continuous fun τ : Fin 3 → ℝ => rl z τ v := by
  refine continuous_pi fun s => continuous_pi fun μ => ?_
  refine Fin.cases ?_ (fun j => ?_) μ
  · simp only [rl, mk_zero]
    exact continuous_const.mul (continuous_ofReal.comp (continuous_apply s))
  · simp only [rl, RepsIntBB.mk, Fin.cons_succ]
    exact continuous_const

/-! ### The rotation skeleton -/

/-- **(T₉′) at three loops from the rotation**: a complex integrand holomorphic in the rotated
energies on `rotRect h`, dominated there by an integrable function of the energies at each
spatial momentum, and integrable on `(ℝ⁴)³` at `z = 1 + s i`. -/
theorem jef_of_rot (G : (Fin 3 → Fin 4 → ℂ) → ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (hsh : s < h)
    (hd : ∀ v τ, ∀ z ∈ rotRect h, DifferentiableAt ℂ G (rl z τ v))
    {g : (Fin 3 → ℝ) → ℝ} (hg : Integrable g)
    (hb : ∀ v, ∃ K, ∀ z ∈ rotRect h, ∀ τ, ‖G (rl z τ v)‖ ≤ K * g τ)
    {g₄ : (Fin 3 → Fin 4 → ℝ) → ℝ} (hg₄ : Integrable g₄)
    (hb₄ : ∀ ℓ : Fin 3 → Fin 4 → ℝ,
      ‖G (rl (1 + s * I) (fun s => ℓ s 0) (fun s => Fin.tail (ℓ s)))‖ ≤ g₄ ℓ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 3 fun ℓ => G fun s => cv (ℓ s) := by
  have hreal : ∀ (τ : Fin 3 → ℝ) (v : Fin 3 → Fin 3 → ℝ),
      (G fun s => cv (Fin.cons (τ s) (v s) : Fin 4 → ℝ)) = G (rl 1 τ v) := fun τ v => by
    rw [rl_one]
  have hcont : ∀ z ∈ rotRect h, ∀ v, Continuous fun τ => G (rl z τ v) := fun z hz v =>
    continuous_iff_continuousAt.2 fun τ => ContinuousAt.comp (f := fun τ => rl z τ v)
      (hd v τ z hz).continuousAt (continuous_rl_tau z v).continuousAt
  have hrot : ∀ v, ∫ τ, G (rl 1 τ v) = (1 + s * I) ^ 3 * ∫ τ, G (rl (1 + s * I) τ v) := by
    intro v
    obtain ⟨K, hK'⟩ := hb v
    exact integral_eq_rotate (f := fun z' τ => G (rl z' τ v))
      (fun z' τ r _ => by simp only [rl_smul]) hh (hg.const_mul K) hK'
      (fun τ z' hz => DifferentiableAt.comp (g := G) (f := fun w => rl w τ v) z'
        (hd v τ z' hz) (differentiableAt_rl τ v z'))
      (fun z' hz => (hcont z' hz v).aestronglyMeasurable) hs hsh
  have hK : Integrable fun ℓ : Fin 3 → Fin 4 → ℝ =>
      G (rl (1 + s * I) (fun s => ℓ s 0) (fun s => Fin.tail (ℓ s))) := by
    have hz : (1 + (s : ℂ) * I) ∈ rotRect h := one_add_mem_rotRect hs.le hsh.le
    refine hg₄.mono' ?_ (Filter.Eventually.of_forall hb₄)
    refine (continuous_iff_continuousAt.2 fun ℓ => ContinuousAt.comp (g := G)
      (f := fun ℓ : Fin 3 → Fin 4 → ℝ => rl (1 + s * I) (fun s => ℓ s 0)
        (fun s => Fin.tail (ℓ s))) ?_ (continuous_rl _).continuousAt).aestronglyMeasurable
    exact (hd _ _ _ hz).continuousAt
  have hjoin : ∀ v, (fun τ => G (rl (1 + s * I) (fun s => joinMomenta τ v s 0)
      (fun s => Fin.tail (joinMomenta τ v s)))) = fun τ => G (rl (1 + s * I) τ v) := by
    intro v
    funext τ
    simp [joinMomenta]
  refine ⟨fun v => ?_, ?_⟩
  · simp only [hreal]
    obtain ⟨K, hK'⟩ := hb v
    exact (hg.const_mul K).mono' (hcont 1 (one_mem_rotRect hh.le) v).aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => hK' 1 (one_mem_rotRect hh.le) τ)
  · simp only [hreal, hrot]
    refine Integrable.const_mul ?_ _
    have := integrable_integral_join hK
    simpa only [hjoin] using this

/-! ### The line integrand -/

variable {ι : Type*} [Fintype ι]

/-- The complex line integrand. -/
noncomputable def lineG (Nc : ι → (Fin 4 → ℂ) → ℂ) (a : ι → Fin 3 → ℤ) (q : ι → Fin 4 → ℝ)
    (ms : ι → List ℝ) (ε : ℝ) (z : ℂ) (w : Fin 3 → Fin 4 → ℂ) : ℂ :=
  z * ∏ i, (Nc i (lc (a i) (q i) w) * dProdC ε (ms i) (lc (a i) (q i) w))

theorem differentiableAt_lineG {Nc : ι → (Fin 4 → ℂ) → ℂ} (hNc : ∀ i, Differentiable ℂ (Nc i))
    (a : ι → Fin 3 → ℤ) (q : ι → Fin 4 → ℝ) (ms : ι → List ℝ) (ε : ℝ) (z : ℂ)
    {w : Fin 3 → Fin 4 → ℂ} (hw : ∀ i M, denC M ε (lc (a i) (q i) w) ≠ 0) :
    DifferentiableAt ℂ (lineG Nc a q ms ε z) w := by
  classical
  unfold lineG
  refine DifferentiableAt.const_mul ?_ z
  have hi : ∀ i ∈ (Finset.univ : Finset ι), DifferentiableAt ℂ
      (fun w => Nc i (lc (a i) (q i) w) * dProdC ε (ms i) (lc (a i) (q i) w)) w :=
    fun i _ => (((hNc i) _).comp w (differentiable_lc _ _ w)).mul
      ((differentiableAt_dProdC ε (ms i) (hw i)).comp w (differentiable_lc _ _ w))
  exact (HasFDerivAt.finsetProd fun i hu => (hi i hu).hasFDerivAt).differentiableAt

theorem lineG_cv {N : ι → (Fin 4 → ℝ) → ℂ} {Nc : ι → (Fin 4 → ℂ) → ℂ}
    (hNc : ∀ i k, Nc i (cv k) = N i k) (a : ι → Fin 3 → ℤ) (q : ι → Fin 4 → ℝ)
    (ms : ι → List ℝ) (ε : ℝ) (z : ℂ) (ℓ : Fin 3 → Fin 4 → ℝ) :
    lineG Nc a q ms ε z (fun s => cv (ℓ s)) =
      z * ∏ i, (N i (rowMom3 (a i) (q i) ℓ) * dProd ε (ms i) (rowMom3 (a i) (q i) ℓ)) := by
  simp only [lineG, lc_cv, hNc, dProdC_cv]

/-- Bounding `lineG` factor by factor. -/
theorem norm_lineG_le {Nc : ι → (Fin 4 → ℂ) → ℂ} (a : ι → Fin 3 → ℤ) (q : ι → Fin 4 → ℝ)
    (ms : ι → List ℝ) (ε : ℝ) (z : ℂ) (w : Fin 3 → Fin 4 → ℂ) (K u : ι → ℝ)
    (hb : ∀ i, ‖Nc i (lc (a i) (q i) w) * dProdC ε (ms i) (lc (a i) (q i) w)‖ ≤ K i * u i) :
    ‖lineG Nc a q ms ε z w‖ ≤ (‖z‖ * ∏ i, K i) * ∏ i, u i := by
  unfold lineG
  rw [norm_mul, norm_prod, mul_assoc, ← Finset.prod_mul_distrib]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
    fun i _ => hb i) (norm_nonneg _)

/-! ### The three-loop line theorem -/

theorem sq_le_shift (q : ι → Fin 4 → ℝ) {ε x : ℝ} (hε : 0 < ε)
    (hx : x ≤ min 1 (ε / (4 * (1 + ∑ i, (q i 0) ^ 2)))) (i : ι) :
    x * (q i 0) ^ 2 ≤ ε / 4 := by
  have hA : 0 < 1 + ∑ i, (q i 0) ^ 2 := by positivity
  have hqi : (q i 0) ^ 2 ≤ 1 + ∑ i, (q i 0) ^ 2 := by
    have := Finset.single_le_sum (f := fun i => (q i 0) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i)
    linarith
  calc x * (q i 0) ^ 2 ≤ (ε / (4 * (1 + ∑ i, (q i 0) ^ 2))) * (1 + ∑ i, (q i 0) ^ 2) :=
        mul_le_mul (hx.trans (min_le_right _ _)) hqi (sq_nonneg _) (by positivity)
    _ = ε / 4 := by field_simp

/-- **(T₉′) at three loops for a product of line factors** under the basis criterion. -/
theorem jef_lines3 (a : ι → Fin 3 → ℤ) (q : ι → Fin 4 → ℝ) (ms : ι → List ℝ) (d : ι → ℕ)
    (N : ι → (Fin 4 → ℝ) → ℂ) (hN : ∀ i, AffPoly (d i) (N i))
    (hd : ∀ i, d i ≤ 2 * (ms i).length) {m' : ℕ} (a' : Fin m' → Fin 3 → ℤ)
    (cls : ι → Fin m') (hs : ∀ i, a i = a' (cls i) ∨ a i = -a' (cls i))
    (hc : BasisCrit a' (fun c => ∑ i ∈ Finset.univ.filter (fun i => cls i = c),
      (2 * (ms i).length - d i)) 5)
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 3 fun ℓ =>
      z * ∏ i, (N i (rowMom3 (a i) (q i) ℓ) * dProd ε (ms i) (rowMom3 (a i) (q i) ℓ)) := by
  classical
  choose Nc hNc using fun i => SetALinkV.AffPoly.exists_cx (hN i)
  choose C hC0 hCb using fun i => (hNc i).2.2
  have e1 : (fun ℓ : Fin 3 → Fin 4 → ℝ =>
      z * ∏ i, (N i (rowMom3 (a i) (q i) ℓ) * dProd ε (ms i) (rowMom3 (a i) (q i) ℓ))) =
      fun ℓ => lineG Nc a q ms ε z fun s => cv (ℓ s) := by
    funext ℓ
    rw [lineG_cv (fun i => (hNc i).1)]
  rw [e1]
  obtain ⟨h, hh0, hh1, hq⟩ : ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
      ∀ x, x ≤ h → ∀ i, x * (q i 0) ^ 2 ≤ ε / 4 :=
    ⟨_, lt_min one_pos (by positivity), min_le_left _ _, fun x hx i => sq_le_shift q hε hx i⟩
  have hfac : ∀ i z' τ v, lc (a i) (q i) (rl z' τ v) =
      mk (z' * ((∑ s, (a i s : ℝ) * τ s : ℝ) : ℂ) + ((q i 0 : ℝ) : ℂ))
        (∑ s, (a i s : ℝ) • v s + Fin.tail (q i)) := fun i z' τ v => lc_rl _ _ _ _ _
  have hs0 : 0 < h / 2 := by positivity
  have hsh : h / 2 ≤ h := by linarith
  choose K hK0 hK using fun i => norm_factor_rot (hC0 i) (hCb i) (ms i) (hd i) hs0
    (by linarith) hε (hq _ hsh i) (Fin.tail (q i))
  refine jef_of_rot (lineG Nc a q ms ε z) hh0 hs0 (by linarith)
    (fun v τ z' hz => differentiableAt_lineG (fun i => (hNc i).2.1) a q ms ε z fun i M => by
      rw [hfac]
      exact nz_rect hz hε (hq h le_rfl i) _ _ rfl M)
    (integrable_majF_real a' _ hc (by norm_num)) (fun v => ?_)
    ((integrable_majF_four a' _ hc).const_mul (‖z‖ * ∏ i, K i)) (fun ℓ => ?_)
  · choose K hK0 hK using fun i => norm_factor_rect (hC0 i) (hCb i) (ms i) (hd i) hh1 hε
      (hq h le_rfl i) (∑ s, (a i s : ℝ) • v s + Fin.tail (q i))
    refine ⟨‖z‖ * ∏ i, K i, fun z' hz τ => ?_⟩
    rw [← prod_nu_eq_majF a a' cls hs _ τ]
    refine norm_lineG_le a q ms ε z _ K _ fun i => ?_
    rw [hfac]
    refine (hK i z' hz _).trans (le_of_eq ?_)
    simp only [nu, linF_real, Real.norm_eq_abs]
  · rw [← prod_nu_eq_majF a a' cls hs _ ℓ]
    refine norm_lineG_le a q ms ε z _ K _ fun i => ?_
    rw [hfac]
    refine (hK i _ (∑ s, (a i s : ℝ) • Fin.tail (ℓ s))).trans (le_of_eq ?_)
    simp only [nu, linF_cons]

end QED.ChainProof.SetALinkV

end
