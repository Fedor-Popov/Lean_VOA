/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesArakawaBottom

/-!
# The slice Arakawa property, unconditionally

With the positive-mode lifts `Q₀, Q₁, Q₂` (`TwoSeriesArakawaIntertwine`) no description of the
maximal ideal of `V^k(sl₂)` by generators is needed.  Let `I = maxIdeal(V^k)` and
`S = W₁(I) ⊆ Vir^{c}`, `c = c_DS(k)`.

* `S` is stable under every Virasoro mode: `L_{n≤-1}` by the Sugawara transport, `L₁, L₂` by
  `W₁ ∘ Q_i = L_i ∘ W₁` (and `Q_i I ⊆ I` since `I` is an ideal), hence all `L_{n≥1}`.
* No vector of `S` has a vacuum component: `(𝟙 | W₁ y) = 0` for `y ∈ I` (`eps_maxIdeal`).  On the
  `(f,h,e)`-ordered PBW basis the vacuum functional only sees the words of Drinfeld–Sokolov weight
  zero, which are the powers `f_{-1}^N |0⟩`; their coefficients in an element of `I` vanish
  because a polynomial projector in the commuting diagonal operators `L₀, h₀` keeps us in `I`, and
  `e_1^N f_{-1}^N |0⟩ = N! k(k-1)⋯(k-N+1) |0⟩ ≠ 0` for `k ∉ ℕ` while `|0⟩ ∉ I`.
* Hence, moving creation modes across the invariant form, `S` lies in the radical of the
  Shapovalov form of `Vir^c`, which is its maximal ideal (Li's theorem, in the repository).

The graded components of the slice map are reached by a Lagrange projector in `h₀`.

## Results

* `W1_maxIdeal` — `W₁(maxIdeal V^k) ⊆ maxIdeal(Vir^{c_DS(k)})` for every non-critical `k ∉ ℕ`;
* `sliceArakawa_unconditional` — `SliceArakawa (dsSliceMap (cDS L.kA) L)` for `L.kA ∉ ℕ`;
* `twoSeries_sliceArakawa` — `SliceArakawa (dsSliceMap (twoSeriesLevels m).c
  (twoSeriesLevels (m+1)))` for every `m`, **with no hypothesis**;
* `twoSeries_gradedUnitary_of_affine` — **Affine GU ⇒ GU of `M(2, 2m+5)`**, conditional only
  on `hA` and the jet-ideal Poincaré input `JetPoincareCoreT0 (m+1)`.

Everything here is proved; no new axiom.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA VOA.AffineVOA.SugawaraCov VOA.AffineVOA.Strong MvPolynomial
open VOA.VirModule VOA.TwoSeries.DSSlice VOA.VirSimple VOA.LeeYangCharacter
open VOA.TwoSeries.StrictModel VOA.SymbolModel VOA.AffineVOA.Inst
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete
open VOA.AffineSl2BoundaryMaximalIdeal
open scoped BigOperators

noncomputable section

variable (c k : ℂ) (hk : k + 2 ≠ 0)

/-! ## §1  The maximal ideal is stable under the modes and the lifts -/

/-- The maximal ideal of `V^k(sl₂)`. -/
abbrev Imax : Submodule ℂ (WakModule k) := QuotVOA.maxGradedIdeal (affineSl2VOA_closed k hk)

theorem J_mem_Imax (a : Fin 3) (m : ℤ) {y : WakModule k} (hy : y ∈ Imax k hk) :
    J k a m y ∈ Imax k hk := by
  rw [← smul_currentState_eq_J k hk]
  exact QuotVOA.maxGradedIdeal_isIdeal _ _ _ _ hy

theorem Lm_mem_Imax (n : ℤ) {y : WakModule k} (hy : y ∈ Imax k hk) : Lm k hk n y ∈ Imax k hk := by
  have h : Lm k hk n y = (affineSl2VOA_closed k hk).L n y := by
    rw [closed_L, Lm, YA_omega_eq, Lsug_def]
  rw [h]
  exact LiRadical.L_mem_of_isIdeal (QuotVOA.maxGradedIdeal_isIdeal _) n hy

theorem Q1_mem_Imax {y : WakModule k} (hy : y ∈ Imax k hk) : Q1 k hk y ∈ Imax k hk := by
  simp only [Q1]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Lm_mem_Imax k hk 1 hy)
    (J_mem_Imax k hk _ _ hy)) (Submodule.smul_mem _ _ (J_mem_Imax k hk _ _ hy)))
    (Submodule.smul_mem _ _ (J_mem_Imax k hk _ _ (J_mem_Imax k hk _ _ hy)))

theorem Q2_mem_Imax {y : WakModule k} (hy : y ∈ Imax k hk) : Q2 k hk y ∈ Imax k hk := by
  have hJ := fun a m {z : WakModule k} (hz : z ∈ Imax k hk) => J_mem_Imax k hk a m hz
  simp only [Q2]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ (Lm_mem_Imax k hk 2 hy)
    (Submodule.smul_mem _ _ (hJ _ _ hy))) (Submodule.smul_mem _ _ (hJ _ _ hy)))
    (Submodule.smul_mem _ _ (hJ _ _ (hJ _ _ hy)))) (Submodule.smul_mem _ _ (hJ _ _ (hJ _ _ hy))))
    (hJ _ _ (hJ _ _ hy))) (Submodule.smul_mem _ _ (hJ _ _ (hJ _ _ (hJ _ _ hy))))

theorem aeval_mem {I : Submodule ℂ (WakModule k)} (T : Module.End ℂ (WakModule k))
    (hT : ∀ y ∈ I, T y ∈ I) (p : Polynomial ℂ) : ∀ y ∈ I, Polynomial.aeval T p y ∈ I := by
  induction p using Polynomial.induction_on with
  | C a =>
      intro y hy
      rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
        Module.End.one_apply]
      exact I.smul_mem a hy
  | add p q hp hq =>
      intro y hy
      rw [map_add, LinearMap.add_apply]
      exact I.add_mem (hp y hy) (hq y hy)
  | monomial n a ih =>
      intro y hy
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
      exact ih _ (hT y hy)

/-! ## §2  The PBW basis diagonalises `L₀` and `h₀` -/

/-- The Sugawara weight of a rank word. -/
def wtR (l : List RLetter) : ℕ := (l.map fun q => dep q + 1).sum

theorem Lm0_rword (l : List RLetter) : Lm k hk 0 (rword k l) = (wtR l : ℂ) • rword k l := by
  induction l with
  | nil => simp [wtR, Lm_vac k hk (by norm_num : (-1 : ℤ) ≤ 0)]
  | cons q l ih =>
      rw [rword_cons, Lm_J, ih, map_smul, zero_add]
      simp only [wtR, List.map_cons, List.sum_cons]
      push_cast
      module

theorem wtR_cons (q : RLetter) (l : List RLetter) : wtR (q :: l) = dep q + 1 + wtR l := by
  simp [wtR]

theorem chl_le_wtR (l : List RLetter) : chl l ≤ (wtR l : ℤ) := by
  induction l with
  | nil => simp [wtR]
  | cons q l ih =>
      rw [chl_cons, wtR_cons]
      push_cast
      omega

/-- A word of Drinfeld–Sokolov weight zero is a power of `f_{-1}`. -/
theorem rword_of_wtR_eq_chl (l : List RLetter) (h : (wtR l : ℤ) = chl l) :
    rword k l = (J k 1 (-1) ^ wtR l) (vacuumA k) := by
  induction l with
  | nil => simp [wtR]
  | cons q l ih =>
      have hl := chl_le_wtR l
      rw [chl_cons, wtR_cons] at h
      push_cast at h
      have hrk : (rk q : ℤ) = 0 := by omega
      have hdep : dep q = 0 := by omega
      have hl' : (wtR l : ℤ) = chl l := by omega
      have hcol : col q = 1 := by
        have : (ofLex q).1 = 0 := by
          have h0 : rk q = 0 := by exact_mod_cast hrk
          exact Fin.ext h0
        simp [col, this, rankColor]
      rw [rword_cons, hcol, hdep, ih hl', wtR_cons, hdep, zero_add, add_comm 1, pow_succ',
        Module.End.mul_apply]
      norm_num

/-- Coordinates of a polynomial in a diagonal operator. -/
theorem repr_aeval_of_diag (T : Module.End ℂ (WakModule k)) (lam : (RLetter →₀ ℕ) → ℂ)
    (hT : ∀ μ, T (Fbasis k hk μ) = lam μ • Fbasis k hk μ) (p : Polynomial ℂ)
    (y : WakModule k) (μ : RLetter →₀ ℕ) :
    (Fbasis k hk).repr (Polynomial.aeval T p y) μ = p.eval (lam μ) * (Fbasis k hk).repr y μ := by
  have h : (Finsupp.lapply μ).comp ((Fbasis k hk).repr.toLinearMap.comp (Polynomial.aeval T p)) =
      (p.eval (lam μ)) • (Finsupp.lapply μ).comp (Fbasis k hk).repr.toLinearMap := by
    refine (Fbasis k hk).ext fun ν => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lapply_apply,
      LinearEquiv.coe_coe]
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hT ν), map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, smul_eq_mul]
    split_ifs with he
    · subst he; ring
    · ring
  have := LinearMap.congr_fun h y
  simpa using this

theorem Lm0_Fbasis (μ : RLetter →₀ ℕ) :
    Lm k hk 0 (Fbasis k hk μ) = (wtR (expWord μ) : ℂ) • Fbasis k hk μ := by
  rw [Fbasis_apply, Fvec, Lm0_rword]

theorem h0_Fbasis (μ : RLetter →₀ ℕ) :
    J k 2 0 (Fbasis k hk μ) = (-2 * (chl (expWord μ) : ℂ)) • Fbasis k hk μ := by
  rw [Fbasis_apply, Fvec, h0_rword]

/-! ## §3  `e₁^N f₋₁^N |0⟩` -/

theorem h0_fpow_vac (N : ℕ) :
    J k 2 0 ((J k 1 (-1) ^ N) (vacuumA k)) = (-2 * (N : ℂ)) • (J k 1 (-1) ^ N) (vacuumA k) := by
  induction N with
  | zero => simp [J_vacuum_nonneg k 2 le_rfl]
  | succ N ih =>
      rw [pow_succ', Module.End.mul_apply, h_f_comm, ih, map_smul, zero_add]
      push_cast; module

theorem e1_fpow_vac (N : ℕ) :
    J k 0 1 ((J k 1 (-1) ^ (N + 1)) (vacuumA k)) =
      (((N : ℂ) + 1) * (k - N)) • (J k 1 (-1) ^ N) (vacuumA k) := by
  induction N with
  | zero =>
      rw [pow_one, pow_zero, Module.End.one_apply, J_comm_apply,
        J_vacuum_nonneg k 0 (by norm_num : (0 : ℤ) ≤ 1), map_zero, zero_add, if_pos (by norm_num),
        Fin.sum_univ_three, show (1 : ℤ) + -1 = 0 by norm_num]
      simp [fabc, kappa, J_vacuum_nonneg k _ (le_refl (0 : ℤ))]
  | succ N ih =>
      rw [pow_succ' _ (N + 1), Module.End.mul_apply, J_comm_apply, ih, map_smul,
        if_pos (by norm_num), Fin.sum_univ_three]
      simp only [fabc, zero_smul, zero_add, one_smul, add_zero]
      rw [show (1 : ℤ) + -1 = 0 by norm_num, h0_fpow_vac]
      rw [← Module.End.mul_apply, ← pow_succ']
      push_cast
      simp only [kappa]
      module

/-- The normalisation `n_N = ∏_{i<N} (i+1)(k-i)`. -/
def nN (N : ℕ) : ℂ := ∏ i ∈ Finset.range N, (((i : ℂ) + 1) * (k - i))

theorem e1pow_fpow_vac (N : ℕ) :
    (J k 0 1 ^ N) ((J k 1 (-1) ^ N) (vacuumA k)) = nN k N • vacuumA k := by
  induction N with
  | zero => simp [nN]
  | succ N ih =>
      rw [pow_succ, Module.End.mul_apply, e1_fpow_vac, map_smul, ih, smul_smul, nN, nN,
        Finset.prod_range_succ, mul_comm]

theorem nN_ne_zero (hkN : ∀ i : ℕ, k ≠ i) (N : ℕ) : nN k N ≠ 0 := by
  rw [nN, Finset.prod_ne_zero_iff]
  intro i _
  exact mul_ne_zero (Nat.cast_add_one_ne_zero i) (sub_ne_zero.mpr (hkN i))

/-! ## §4  The vacuum functional vanishes on the maximal ideal -/

/-- The vacuum row of the slice map. -/
def eps (y : WakModule k) : ℂ := (VirGram4.canB c).form (vacVec c) (W1 c k hk y)

theorem eps_Q0 (y : WakModule k) : eps c k hk (Q0 k hk y) = 0 := by
  rw [eps, W1_Q0]
  have h := VirFormSym.adjLop (VirGram4.canB c) 0 (vacVec c) (W1 c k hk y)
  rw [Lop_vacuum c (by norm_num), map_zero, LinearMap.zero_apply, neg_zero] at h
  exact h.symm

theorem eps_Fbasis_of_ne (μ : RLetter →₀ ℕ) (h : (wtR (expWord μ) : ℤ) ≠ chl (expWord μ)) :
    eps c k hk (Fbasis k hk μ) = 0 := by
  have hQ : Q0 k hk (Fbasis k hk μ) =
      ((wtR (expWord μ) : ℂ) - chl (expWord μ)) • Fbasis k hk μ := by
    simp only [Q0]
    rw [Lm0_Fbasis, h0_Fbasis]
    module
  have h0 := eps_Q0 c k hk (Fbasis k hk μ)
  rw [hQ, eps, map_smul, map_smul, ← eps] at h0
  refine (smul_eq_zero.mp h0).resolve_left ?_
  intro he
  apply h
  have : ((wtR (expWord μ) : ℤ) : ℂ) = ((chl (expWord μ) : ℤ) : ℂ) := by
    push_cast; linear_combination he
  exact_mod_cast this

theorem eps_eq_sum (y : WakModule k) :
    eps c k hk y = ∑ μ ∈ ((Fbasis k hk).repr y).support,
      (Fbasis k hk).repr y μ * eps c k hk (Fbasis k hk μ) := by
  conv_lhs => rw [← (Fbasis k hk).linearCombination_repr y]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hl : ∀ z : WakModule k, eps c k hk z = ((VirGram4.canB c).form (vacVec c)).comp
      (W1 c k hk) z := fun z => rfl
  rw [hl, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- **The coefficient of `f₋₁^N |0⟩`-type words in an element of the maximal ideal vanishes.** -/
theorem sumN_eq_zero (hkN : ∀ i : ℕ, k ≠ i) {y : WakModule k} (hy : y ∈ Imax k hk) (N : ℕ) :
    ∑ μ ∈ ((Fbasis k hk).repr y).support.filter
        (fun μ => wtR (expWord μ) = N ∧ chl (expWord μ) = N),
      (Fbasis k hk).repr y μ = 0 := by
  classical
  set b := Fbasis k hk
  set s := (b.repr y).support
  set D := s.image fun μ => wtR (expWord μ)
  set C := s.image fun μ => chl (expWord μ)
  set p : Polynomial ℂ := ∏ d ∈ D.erase N, (Polynomial.X - Polynomial.C (d : ℂ))
  set q : Polynomial ℂ := ∏ e ∈ C.erase (N : ℤ), (Polynomial.X - Polynomial.C (-2 * (e : ℂ)))
  set z := Polynomial.aeval (J k 2 0) q (Polynomial.aeval (Lm k hk 0) p y)
  have hz : z ∈ Imax k hk :=
    aeval_mem k _ (fun x hx => J_mem_Imax k hk 2 0 hx) q _
      (aeval_mem k _ (fun x hx => Lm_mem_Imax k hk 0 hx) p y hy)
  have hrepr : ∀ μ, b.repr z μ = q.eval (-2 * (chl (expWord μ) : ℂ)) *
      (p.eval (wtR (expWord μ) : ℂ) * b.repr y μ) := by
    intro μ
    rw [repr_aeval_of_diag k hk (J k 2 0) _ (h0_Fbasis k hk),
      repr_aeval_of_diag k hk (Lm k hk 0) _ (Lm0_Fbasis k hk)]
  set κ := q.eval (-2 * ((N : ℤ) : ℂ)) * p.eval (N : ℂ) with hκdef
  have hκ : κ ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
      intro e he
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      intro h0
      have : ((e : ℤ) : ℂ) = ((N : ℤ) : ℂ) := by linear_combination h0 / 2
      exact (Finset.mem_erase.mp he).1 (by exact_mod_cast this)
    · rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
      intro d hd
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      intro h0
      have : (N : ℂ) = (d : ℂ) := by linear_combination h0
      exact (Finset.mem_erase.mp hd).1 (by exact_mod_cast this.symm)
  -- the projected vector is a multiple of `f₋₁^N |0⟩`
  set S := ∑ μ ∈ s.filter (fun μ => wtR (expWord μ) = N ∧ chl (expWord μ) = N), b.repr y μ
  have hzS : z = (κ * S) • (J k 1 (-1) ^ N) (vacuumA k) := by
    conv_lhs => rw [← b.linearCombination_repr z]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    have hsupp : (b.repr z).support ⊆ s.filter (fun μ => wtR (expWord μ) = N ∧
        chl (expWord μ) = N) := by
      intro μ hμ
      rw [Finsupp.mem_support_iff, hrepr] at hμ
      have hμs : μ ∈ s := by
        rw [Finsupp.mem_support_iff]; intro h0; apply hμ; rw [h0]; ring
      refine Finset.mem_filter.mpr ⟨hμs, ?_, ?_⟩
      · by_contra hne
        apply hμ
        have : p.eval (wtR (expWord μ) : ℂ) = 0 := by
          rw [Polynomial.eval_prod]
          exact Finset.prod_eq_zero (i := wtR (expWord μ))
            (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem _ hμs⟩) (by simp)
        rw [this]; ring
      · by_contra hne
        apply hμ
        have : q.eval (-2 * (chl (expWord μ) : ℂ)) = 0 := by
          rw [Polynomial.eval_prod]
          exact Finset.prod_eq_zero (i := chl (expWord μ))
            (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem _ hμs⟩) (by simp)
        rw [this]; ring
    rw [Finset.sum_subset hsupp (fun μ _ hμ => by
      rw [Finsupp.notMem_support_iff.mp hμ, zero_smul])]
    rw [Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    obtain ⟨_, hw, hc⟩ := Finset.mem_filter.mp hμ
    rw [hrepr, Fbasis_apply, Fvec, rword_of_wtR_eq_chl k (expWord μ) (by rw [hw, hc]), hw, hc,
      hκdef]
    push_cast
    congr 1
    ring
  -- apply `e₁^N`
  have he : (J k 0 1 ^ N) z ∈ Imax k hk := by
    have := aeval_mem k _ (fun x hx => J_mem_Imax k hk 0 1 hx) (Polynomial.X ^ N) z hz
    simpa using this
  rw [hzS, map_smul, e1pow_fpow_vac, smul_smul] at he
  by_contra hS
  have hcoef : κ * S * nN k N ≠ 0 := mul_ne_zero (mul_ne_zero hκ hS) (nN_ne_zero k hkN N)
  apply QuotVOA.vacuum_not_mem_maxGradedIdeal (affineSl2VOA_closed k hk)
    (affineSl2_vacuum_ne_zero k hk)
  have := Submodule.smul_mem _ (κ * S * nN k N)⁻¹ he
  rwa [smul_smul, inv_mul_cancel₀ hcoef, one_smul] at this

/-- **The vacuum row of the slice map vanishes on the maximal ideal.** -/
theorem eps_maxIdeal (hkN : ∀ i : ℕ, k ≠ i) {y : WakModule k} (hy : y ∈ Imax k hk) :
    eps c k hk y = 0 := by
  classical
  rw [eps_eq_sum]
  set b := Fbasis k hk
  set s := (b.repr y).support
  -- only Drinfeld–Sokolov weight zero contributes
  rw [← Finset.sum_filter_add_sum_filter_not s (fun μ => (wtR (expWord μ) : ℤ) = chl (expWord μ))]
  rw [Finset.sum_eq_zero (s := s.filter (fun μ => ¬ ((wtR (expWord μ) : ℤ) = chl (expWord μ))))
    (fun μ hμ => by rw [eps_Fbasis_of_ne c k hk μ (Finset.mem_filter.mp hμ).2, mul_zero]),
    add_zero]
  -- group by the weight
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun μ => wtR (expWord μ))
    (t := s.image fun μ => wtR (expWord μ)) (fun μ hμ => Finset.mem_image_of_mem _
      (Finset.mem_filter.mp hμ).1)]
  refine Finset.sum_eq_zero fun N _ => ?_
  have hfib : ∀ μ ∈ (s.filter fun μ => (wtR (expWord μ) : ℤ) = chl (expWord μ)).filter
      (fun μ => wtR (expWord μ) = N),
      b.repr y μ * eps c k hk (b μ) = b.repr y μ * eps c k hk ((J k 1 (-1) ^ N) (vacuumA k)) := by
    intro μ hμ
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hμ
    obtain ⟨_, h3⟩ := Finset.mem_filter.mp h1
    rw [Fbasis_apply, Fvec, rword_of_wtR_eq_chl k _ h3, h2]
  rw [Finset.sum_congr rfl hfib, ← Finset.sum_mul]
  have hset : (s.filter fun μ => (wtR (expWord μ) : ℤ) = chl (expWord μ)).filter
      (fun μ => wtR (expWord μ) = N) =
      s.filter (fun μ => wtR (expWord μ) = N ∧ chl (expWord μ) = N) := by
    ext μ
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hμ, h3⟩, h2⟩; exact ⟨hμ, h2, by rw [← h3, h2]⟩
    · rintro ⟨hμ, h2, h3⟩; exact ⟨⟨hμ, by rw [h2, h3]⟩, h2⟩
  rw [hset, sumN_eq_zero k hk hkN hy N, zero_mul]

/-! ## §5  `W₁(I)` is in the maximal ideal of `Vir^{c_DS}` -/

theorem Lop_pos_lift (n : ℕ) :
    ∀ y ∈ Imax k hk, ∃ y' ∈ Imax k hk,
      Lop (cDS k) ((n : ℤ) + 1) (W1 (cDS k) k hk y) = W1 (cDS k) k hk y' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy
    rcases n with _ | _ | n
    · exact ⟨Q1 k hk y, Q1_mem_Imax k hk hy, by
        rw [show ((0 : ℕ) : ℤ) + 1 = 1 by norm_num]; exact (W1_Q1 _ k hk y).symm⟩
    · exact ⟨Q2 k hk y, Q2_mem_Imax k hk hy, by
        rw [show ((0 + 1 : ℕ) : ℤ) + 1 = 2 by norm_num]; exact (W1_Q2 k hk y).symm⟩
    · -- `L_{n+3} = (L₁ L_{n+2} - L_{n+2} L₁)/(1 - (n+2))`
      obtain ⟨y₁, hy₁, e₁⟩ := ih (n + 1) (by omega) y hy
      obtain ⟨y₂, hy₂, e₂⟩ := ih (n + 1) (by omega) (Q1 k hk y) (Q1_mem_Imax k hk hy)
      have hc := LeeYang.Lop_apply_comm (cDS k) 1 ((((n + 1 : ℕ) : ℤ)) + 1) (W1 (cDS k) k hk y)
      rw [if_neg (by omega), zero_smul, add_zero, e₁, ← W1_Q1, ← W1_Q1, e₂] at hc
      have hne : ((1 : ℤ) : ℂ) - ((((n + 1 : ℕ) : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := by
        push_cast; intro h0
        have : (n : ℂ) + 1 = 0 := by linear_combination -h0
        exact Nat.cast_add_one_ne_zero n this
      refine ⟨(((1 : ℤ) : ℂ) - ((((n + 1 : ℕ) : ℤ) + 1 : ℤ) : ℂ))⁻¹ • (Q1 k hk y₁ - y₂),
        Submodule.smul_mem _ _ (Submodule.sub_mem _ (Q1_mem_Imax k hk hy₁) hy₂), ?_⟩
      rw [map_smul, map_sub, hc]
      rw [show (1 : ℤ) + ((((n + 1 : ℕ) : ℤ)) + 1) = (((n + 2 : ℕ) : ℤ)) + 1 by push_cast; ring]
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- **`W₁(maxIdeal V^k) ⊆ maxIdeal(Vir^{c_DS(k)})`** for every non-critical `k ∉ ℕ`. -/
theorem W1_maxIdeal (hkN : ∀ i : ℕ, k ≠ i) {y : WakModule k} (hy : y ∈ Imax k hk) :
    W1 (cDS k) k hk y ∈ maxIdealVir (cDS k) := by
  have hrow : ∀ w : List ℕ, ∀ y ∈ Imax k hk,
      (VirGram4.canB (cDS k)).form (negWordVir (cDS k) w) (W1 (cDS k) k hk y) = 0 := by
    intro w
    induction w with
    | nil => intro y hy; rw [negWordVir_nil]; exact eps_maxIdeal (cDS k) k hk hkN hy
    | cons i w ih =>
        intro y hy
        rw [VirFormSym.negWord_cons_left]
        obtain ⟨y', hy', e⟩ := Lop_pos_lift k hk (i + 1) y hy
        rw [show ((i : ℤ) + 2) = (((i + 1 : ℕ) : ℤ)) + 1 by push_cast; ring, e]
        exact ih y' hy'
  have hr : W1 (cDS k) k hk y ∈ SingVec.rightRadical (VirGram4.canB (cDS k)) := by
    rw [SingVec.mem_rightRadical]
    intro x
    have hx : x ∈ Submodule.span ℂ (Set.range (negWordVir (cDS k))) := by
      have := negSpanVir_eq_top (cDS k)
      rw [negSpanVir] at this
      rw [this]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨w, rfl⟩ := hx; exact hrow w y hy
    | zero => simp
    | add x z _ _ hx hz => simp [map_add, hx, hz]
    | smul a x _ hx => simp [map_smul, hx]
  rw [LiRadical.rightRadical_eq_maxGradedIdeal (VirGram4.canB_isFullyInvariant _)
    (VirGram4.canB_normalized _)] at hr
  exact hr

/-! ## §6  The graded components -/

theorem Wslice_h0_pow (n : ℕ) (y : WakModule k) (a : ℤ) :
    Wslice c k hk ((J k 2 0 ^ n) y) a = (-2 * (a : ℂ)) ^ n • Wslice c k hk y a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, Wslice_h0, ih, smul_smul, pow_succ']

theorem Wslice_aeval_h0 (p : Polynomial ℂ) (y : WakModule k) (a : ℤ) :
    Wslice c k hk (Polynomial.aeval (J k 2 0) p y) a =
      p.eval (-2 * (a : ℂ)) • Wslice c k hk y a := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.eval_eq_sum_range, LinearMap.sum_apply, map_sum,
    Finsupp.finsetSum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, Wslice_h0_pow, smul_smul]

/-- **The slice Arakawa property, unconditionally**: for every non-critical level datum with
`L.kA ∉ ℕ`, the slice map sends the maximal ideal of `V^{kA}(sl₂)` into the maximal ideal of
`Vir^{c_DS(kA)}`. -/
theorem sliceArakawa_unconditional (L : CosetLevels) (hkN : ∀ i : ℕ, L.kA ≠ i) :
    SliceArakawa (dsSliceMap (cDS L.kA) L) := by
  classical
  intro y hy a
  change Wslice (cDS L.kA) L.kA L.aNoncritical y a ∈ maxIdealVir (cDS L.kA)
  have hy' : y ∈ Imax L.kA L.aNoncritical := hy
  set C := cDS L.kA
  set T := (Wslice C L.kA L.aNoncritical y).support
  by_cases ha : a ∈ T
  · set P : Polynomial ℂ := ∏ b ∈ T.erase a, (Polynomial.X - Polynomial.C (-2 * (b : ℂ)))
    set z := Polynomial.aeval (J L.kA 2 0) P y
    have hz : z ∈ Imax L.kA L.aNoncritical :=
      aeval_mem L.kA _ (fun x hx => J_mem_Imax L.kA L.aNoncritical 2 0 hx) P y hy'
    have hW := W1_maxIdeal L.kA L.aNoncritical hkN hz
    have hP0 : ∀ b ∈ T, b ≠ a → P.eval (-2 * (b : ℂ)) = 0 := by
      intro b hb hba
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hba, hb⟩) (by simp)
    have hPa : P.eval (-2 * (a : ℂ)) ≠ 0 := by
      rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
      intro b hb
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      intro h0
      have : (a : ℂ) = b := by linear_combination -h0 / 2
      exact (Finset.mem_erase.mp hb).1 (by exact_mod_cast this.symm)
    have hsum := Wslice_sum C L.kA L.aNoncritical z
    have hzs : Wslice C L.kA L.aNoncritical z =
        Finsupp.single a (P.eval (-2 * (a : ℂ)) • Wslice C L.kA L.aNoncritical y a) := by
      ext b
      rw [Wslice_aeval_h0, Finsupp.single_apply]
      split_ifs with hab
      · subst hab; rfl
      · by_cases hb : b ∈ T
        · rw [hP0 b hb (Ne.symm hab), zero_smul]
        · rw [Finsupp.notMem_support_iff.mp hb, smul_zero]
    rw [hzs, Finsupp.sum_single_index (by simp)] at hsum
    have hmem : P.eval (-2 * (a : ℂ)) • Wslice C L.kA L.aNoncritical y a ∈ maxIdealVir C := by
      rw [hsum]; exact hW
    have := Submodule.smul_mem _ (P.eval (-2 * (a : ℂ)))⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hPa, one_smul] at this
  · rw [Finsupp.notMem_support_iff.mp ha]
    exact Submodule.zero_mem _

theorem twoSeries_kA_not_nat (m : ℕ) (i : ℕ) : (twoSeriesLevels (m + 1)).kA ≠ i := by
  rw [twoSeriesLevels_kA, level_eq]
  intro h
  have h1 : ((2 * (m + 1) + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * (m + 1))
  have h2 : (2 : ℂ) = ((i : ℂ) + 2) * ((2 * (m + 1) + 1 : ℕ) : ℂ) := by
    field_simp at h
    linear_combination h
  have h3 : (2 : ℕ) = (i + 2) * (2 * (m + 1) + 1) := by exact_mod_cast h2
  nlinarith

/-- **`SliceArakawa` for the two series, with no hypothesis.** -/
theorem twoSeries_sliceArakawa (m : ℕ) :
    SliceArakawa (dsSliceMap (twoSeriesLevels m).c (twoSeriesLevels (m + 1))) := by
  rw [twoSeries_c_eq_cDS]
  exact sliceArakawa_unconditional _ (twoSeries_kA_not_nat m)

/-- **Affine GU ⇒ GU of `M(2, 2m+5)`**, `#print axioms`-clean, conditional only on `hA` and
the jet-ideal Poincaré input `JetPoincareCoreT0 (m+1)`. -/
theorem twoSeries_gradedUnitary_of_affine (m : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels (m + 1)))
      (affineRealStructure (twoSeriesLevels (m + 1))) (affineFlag (twoSeriesLevels (m + 1))))
    (h : PoincareZero.JetPoincareCoreT0 (m + 1)) :
    VirGradedUnitary (twoSeriesLevels (m + 1)).c (targetRealStructure (twoSeriesLevels (m + 1))) :=
  twoSeries_gradedUnitary_of_sliceArakawa m hA (twoSeries_sliceArakawa m) h

end

end VOA.TwoSeries.SliceMap
