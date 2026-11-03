/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusUnitaryZhu
import VOA.Modularity.ZhuRecursionProof
import VOA.Modularity.LiFiltration
import VOA.Modules.Rationality
import VOA.Core.BilinearForm

/-!
# A top vector with the vacuum character generates a copy of `V`

Let `V` be a simple VOA and `N` an irreducible ordinary `V`-module with lowest weight `0`.  If a
nonzero `x ∈ N_0` is annihilated by every zero mode `o(a)`, `a ∈ V_{≥1}`, then `N ≅ V`.

## Proof
* `cycSpan A w = span{u₍ₙ₎w}` is closed under all modes (`mode_mem_cycSpan_of_mem`): the module
  Jacobi identity with `ℓ = p − T`, `m = T` (`T` a truncation bound of `b` on `w`) expresses
  `b₍ₚ₎a₍ₙ₎w` through `(b₍ⱼ₎a)₍ₖ₎w` and `b₍ₚ₋ᵢ₎a₍ₙ₊ᵢ₎w`, `i ≥ 1` (downward induction on `n`).
* `L(−1)x = 0`: every `u₍ₙ₎L(−1)x` has no weight-`0` component (the weight-`0` one is
  `u₍ₖ₎L(−1)x = L(−1)u₍ₖ₎x + k·o(u)x = 0`), so the cyclic submodule of `L(−1)x` misses `x`.
* hence `u₍ₙ₎x = 0` for all `n ≥ 0` (`[L(−1), u₍ₙ₎] = −n u₍ₙ₋₁₎`), and `a ↦ a₍₋₁₎x` is a module
  map `V → N` (the Borcherds iterate), injective by simplicity and onto by irreducibility.

## Main result
* `nonempty_moduleEquiv_adjoint_of_vacuumTop`.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne.PlusUnitary

open VOA

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-! ## Cyclic spans are submodules -/

section Cyclic

variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- `span{u₍ₙ₎w : u ∈ V, n ∈ ℤ}`. -/
def cycSpan (A : WeakModule V M) (w : M) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (a : 𝒱) (n : ℤ), y = mode (A.YM a) n w}

theorem mode_mem_cycSpan (A : WeakModule V M) (w : M) (a : 𝒱) (n : ℤ) :
    mode (A.YM a) n w ∈ cycSpan A w :=
  Submodule.subset_span ⟨a, n, rfl⟩

/-- The key step: `b₍ₚ₎a₍ₙ₎w ∈ span{u₍ₖ₎w}`. -/
theorem mode_mode_mem_cycSpan (A : WeakModule V M) (w : M) (b a : 𝒱) (n p : ℤ) :
    mode (A.YM b) p (mode (A.YM a) n w) ∈ cycSpan A w := by
  obtain ⟨Ta, hTa⟩ := A.truncation a w
  obtain ⟨Tb, hTb⟩ := A.truncation b w
  suffices H : ∀ k : ℕ, ∀ n : ℤ, Ta - n ≤ k → ∀ p : ℤ,
      mode (A.YM b) p (mode (A.YM a) n w) ∈ cycSpan A w from
    H (Ta - n).toNat n (by omega) p
  intro k
  induction k with
  | zero =>
    intro n hn p
    rw [hTa n (by omega), map_zero]; exact Submodule.zero_mem _
  | succ k ih =>
    intro n hn p
    by_cases hn' : Ta ≤ n
    · rw [hTa n hn', map_zero]; exact Submodule.zero_mem _
    push Not at hn'
    have hjac := A.jacobi b a w (p - Tb) Tb n
    set F : ℤ → M := fun i => (negOnePow i * cbz (p - Tb) i) •
      (mode (A.YM b) (p - Tb + Tb - i) (mode (A.YM a) (n + i) w)
        - negOnePow (p - Tb) • mode (A.YM a) (p - Tb + n - i) (mode (A.YM b) (Tb + i) w)) with hFdef
    have hR : (∑ᶠ i : ℤ, F i) ∈ cycSpan A w := by
      rw [hjac]
      exact finsum_mem_submodule_lf _ _ fun i => Submodule.smul_mem _ _ (mode_mem_cycSpan A w _ _)
    -- the support of `F` lies in `[0, Ta - n]`
    have hFneg : ∀ i : ℤ, i < 0 → F i = 0 := by
      intro i hi; simp [hFdef, cbz_apply_neg _ hi]
    have hFb : ∀ i : ℤ, 0 ≤ i → mode (A.YM b) (Tb + i) w = 0 := fun i hi => hTb _ (by omega)
    have hFbig : ∀ i : ℤ, Ta - n ≤ i → F i = 0 := by
      intro i hi
      simp only [hFdef, hTa (n + i) (by omega), map_zero, hFb i (by omega), smul_zero, sub_zero]
    have hFmem : ∀ i : ℤ, i ≠ 0 → F i ∈ cycSpan A w := by
      intro i hi
      rcases lt_or_gt_of_ne hi with hi | hi
      · rw [hFneg i hi]; exact Submodule.zero_mem _
      · simp only [hFdef, hFb i hi.le, map_zero, smul_zero, sub_zero]
        exact Submodule.smul_mem _ _ (ih (n + i) (by omega) _)
    have hF0 : F 0 = mode (A.YM b) p (mode (A.YM a) n w) := by
      have hb0 : mode (A.YM b) Tb w = 0 := hTb Tb le_rfl
      simp only [hFdef, add_zero, hb0, map_zero, smul_zero, sub_zero, sub_add_cancel]
      rw [cbz_apply_nonneg _ le_rfl, show negOnePow 0 = 1 by simp [negOnePow]]
      simp [gBinom]
    -- split the finite sum
    have hsupp : Function.support F ⊆ (Finset.Icc (0 : ℤ) (Ta - n) : Set ℤ) := by
      intro i hi
      simp only [Function.mem_support] at hi
      simp only [Finset.coe_Icc, Set.mem_Icc]
      by_contra h
      push Not at h
      by_cases h0 : 0 ≤ i
      · exact hi (hFbig i (by have := h h0; omega))
      · exact hi (hFneg i (by omega))
    rw [finsum_eq_sum_of_support_subset F hsupp] at hR
    have hsplit := Finset.add_sum_erase (Finset.Icc (0 : ℤ) (Ta - n)) F
      (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    rw [← hsplit, hF0] at hR
    have hrest : ∑ i ∈ (Finset.Icc (0 : ℤ) (Ta - n)).erase 0, F i ∈ cycSpan A w :=
      Submodule.sum_mem _ fun i hi => hFmem i (Finset.ne_of_mem_erase hi)
    simpa using Submodule.sub_mem _ hR hrest

/-- **`span{u₍ₙ₎w}` is closed under every mode.** -/
theorem mode_mem_cycSpan_of_mem (A : WeakModule V M) (w : M) (b : 𝒱) (p : ℤ) {y : M}
    (hy : y ∈ cycSpan A w) : mode (A.YM b) p y ∈ cycSpan A w := by
  refine Submodule.span_induction (p := fun y _ => mode (A.YM b) p y ∈ cycSpan A w) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨a, n, rfl⟩; exact mode_mode_mem_cycSpan A w b a n p
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; simp only [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; simp only [map_smul]; exact Submodule.smul_mem _ c hx

/-- The cyclic span as a weak submodule. -/
def cycSub (A : WeakModule V M) (w : M) : WeakModule.Submodule' A where
  carrier := cycSpan A w
  act_mem u n _ hx := by rw [WeakModule.act_def]; exact mode_mem_cycSpan_of_mem A w u n hx

end Cyclic

/-! ## The vacuum-like top vector -/

section Vacuum

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- `[L(−1), u₍ₙ₎] = −n u₍ₙ₋₁₎` on a module. -/
theorem L_neg_one_comm (A : WeakModule V M) (a : 𝒱) (n : ℤ) (x : M) :
    mode (A.YM V.conformalVector) 0 (mode (A.YM a) n x) - mode (A.YM a) n (mode (A.YM V.conformalVector) 0 x)
      = (-(n : ℂ)) • mode (A.YM a) (n - 1) x := by
  rw [mode_commutator A V.conformalVector a x 0 n]
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
  rw [cbz_zero_left, if_pos rfl, one_smul, zero_add, sub_zero]
  have hT := act_T_covariance A a n x
  simp only [WeakModule.act_def] at hT
  rw [← hT, VertexOperatorAlgebra.L_def]
  rfl

/-- **A top vector with the vacuum character generates a copy of `V`.** -/
theorem nonempty_moduleEquiv_adjoint_of_vacuumTop (hV : V.IsSimple) (N : OrdVModule V M)
    (hirr : N.IsIrreducible) {x : M} (hlow : IsLowestWeight N 0) (hx : x ∈ N.weight 0)
    (hx0 : x ≠ 0) (hzero : ∀ k : ℤ, 1 ≤ k → ∀ a ∈ V.grading k, oMod N a x = 0) :
    Nonempty (ModuleEquiv V N (adjointModule V)) := by
  set ω := V.conformalVector
  set w1 := mode (N.YM ω) 0 x with hw1
  -- (1) the weight-`0`-free subspace
  set K : Submodule ℂ M := ⨆ (γ : ℂ) (_ : γ ≠ 0), N.weight γ with hK
  have hKdisj : ∀ y ∈ N.weight 0, y ∈ K → y = 0 := fun y h0 hk =>
    (Submodule.disjoint_def.mp (N.isInternal.submodule_iSupIndep 0)) y h0 hk
  have hmemK : ∀ {γ : ℂ} {y : M}, γ ≠ 0 → y ∈ N.weight γ → y ∈ K := fun hγ hy =>
    (le_iSup₂_of_le _ hγ le_rfl : N.weight _ ≤ K) hy
  have hw1mem : w1 ∈ N.weight 1 := by
    have := mode_mem_weight N V.conformal_mem hx 0
    rwa [show (0 : ℂ) + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 = 1 by norm_num] at this
  -- (2) every `u₍ₙ₎w1` lies in `K`
  have hgen : ∀ (a : 𝒱) (n : ℤ), mode (N.YM a) n w1 ∈ K := by
    intro a n
    have hatop : a ∈ ⨆ i, V.grading i := by
      rw [V.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction V.grading (motive := fun a => mode (N.YM a) n w1 ∈ K) hatop
      ?_ (by simp only [map_zero, LinearMap.zero_apply]; exact K.zero_mem)
      (fun a b ha hb => by simp only [map_add, LinearMap.add_apply]; exact K.add_mem ha hb)
    intro k a ha
    have hmem := mode_mem_weight N ha hw1mem n
    by_cases hkn : (1 : ℂ) + k - n - 1 = 0
    · -- `n = k`: compute
      have hnk : n = k := by
        have : ((n : ℤ) : ℂ) = (k : ℂ) := by linear_combination -hkn
        exact_mod_cast this
      subst hnk
      have hcomm := L_neg_one_comm N.toWeakModule a n x
      have hlowv : mode (N.YM a) n x = 0 := by
        have h := mode_mem_weight N ha hx n
        have hbot : N.weight ((0 : ℂ) + n - n - 1) = ⊥ := by
          by_contra hne
          obtain ⟨j, hj⟩ := hlow _ hne
          have : ((-1 : ℤ) : ℂ) = (j : ℂ) := by push_cast at hj ⊢; linear_combination hj
          have : (-1 : ℤ) = j := by exact_mod_cast this
          omega
        rw [hbot, Submodule.mem_bot] at h; exact h
      rw [hlowv, map_zero, zero_sub] at hcomm
      have hval : mode (N.YM a) n w1 = (n : ℂ) • mode (N.YM a) (n - 1) x := by
        rw [hw1]; rw [neg_smul] at hcomm; exact neg_injective hcomm
      rw [hval]
      rcases lt_trichotomy n 0 with hn | hn | hn
      · have ha0 : a = 0 := by rw [V.positivity n hn, Submodule.mem_bot] at ha; exact ha
        rw [ha0]
        have h00 : mode (N.YM (0 : 𝒱)) (n - 1) x = 0 := by rw [map_zero]; rfl
        rw [h00, smul_zero]; exact K.zero_mem
      · subst hn; simp
      · have ho := hzero n hn a ha
        rw [oMod_homogeneous N ha] at ho
        rw [ho, smul_zero]; exact K.zero_mem
    · exact hmemK hkn hmem
  -- (3) the cyclic submodule of `w1` is zero, so `L(−1)x = 0`
  have hcyc : cycSpan N.toWeakModule w1 ≤ K := by
    rw [cycSpan, Submodule.span_le]; rintro _ ⟨a, n, rfl⟩; exact hgen a n
  have hw10 : w1 = 0 := by
    rcases hirr.2 (cycSub N.toWeakModule w1) with h | h
    · have : w1 ∈ cycSpan N.toWeakModule w1 := by
        have := mode_mem_cycSpan N.toWeakModule w1 V.vacuum (-1)
        rwa [N.vacuum_YM, show mode (1 : FormalDist (Module.End ℂ M)) (-1) = 1 from by
          simp [mode_one]] at this
      have h' : cycSpan N.toWeakModule w1 = ⊥ := h
      rw [h', Submodule.mem_bot] at this; exact this
    · exfalso
      have h' : cycSpan N.toWeakModule w1 = ⊤ := h
      exact hx0 (hKdisj x hx (hcyc (h' ▸ Submodule.mem_top)))
  -- (4) all non-negative modes kill `x`
  have hnonneg : ∀ (a : 𝒱) (n : ℤ), 0 ≤ n → mode (N.YM a) n x = 0 := by
    intro a
    obtain ⟨T, hT⟩ := N.truncation a x
    suffices H : ∀ k : ℕ, ∀ n : ℤ, 0 ≤ n → T - n ≤ k → mode (N.YM a) n x = 0 from
      fun n hn => H (T - n).toNat n hn (by omega)
    intro k
    induction k with
    | zero => intro n _ hn; exact hT n (by omega)
    | succ k ih =>
      intro n hn0 hn
      have h := ih (n + 1) (by omega) (by omega)
      have hcomm := L_neg_one_comm N.toWeakModule a (n + 1) x
      rw [h, map_zero, ← hw1, hw10, map_zero, sub_zero] at hcomm
      have hne : (-(((n + 1 : ℤ)) : ℂ)) ≠ 0 := by
        have : ((n + 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
        exact neg_ne_zero.mpr this
      have := (smul_eq_zero.mp hcomm.symm).resolve_left hne
      simpa using this
  -- (5) the module map `a ↦ a₍₋₁₎x`
  let f : 𝒱 →ₗ[ℂ] M := (modeLinear (-1)).comp N.YM |>.flip x
  have hf : ∀ a, f a = mode (N.YM a) (-1) x := fun a => rfl
  have hfint : ∀ (b : 𝒱) (p : ℤ) (a : 𝒱), f (V.smul b p a) = mode (N.YM b) p (f a) := by
    intro b p a
    rw [hf, hf, mode_iterate N.toWeakModule b a x p (-1)]
    rw [finsum_eq_single _ (0 : ℤ)]
    · rw [cbz_apply_nonneg _ le_rfl, hnonneg b 0 le_rfl, map_zero, smul_zero, sub_zero]
      simp [negOnePow, gBinom]
    · intro i hi
      rcases lt_or_gt_of_ne hi with hi | hi
      · rw [cbz_apply_neg _ hi, mul_zero, zero_smul]
      · rw [hnonneg a (-1 + i) (by omega), map_zero, hnonneg b i hi.le, map_zero, smul_zero,
          sub_zero, smul_zero]
  have hf1 : f V.vacuum = x := by
    rw [hf, N.vacuum_YM]; simp [mode_one]
  -- (6) injective: the kernel is an ideal
  have hinj : Function.Injective f := by
    have hideal : V.IsIdeal (LinearMap.ker f) := by
      intro u v n hv
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hfint, hv, map_zero]
    rcases hV.2 _ hideal with h | h
    · exact LinearMap.ker_eq_bot.mp h
    · exfalso
      have : V.vacuum ∈ LinearMap.ker f := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, hf1] at this
      exact hx0 this
  -- (7) surjective: the range is a submodule containing `x`
  have hsurj : Function.Surjective f := by
    let R : WeakModule.Submodule' N.toWeakModule :=
      { carrier := LinearMap.range f
        act_mem := by
          rintro u n _ ⟨a, rfl⟩
          rw [WeakModule.act_def, ← hfint]; exact ⟨_, rfl⟩ }
    rcases hirr.2 R with h | h
    · exfalso
      have : x ∈ LinearMap.range f := ⟨V.vacuum, hf1⟩
      have h' : LinearMap.range f = ⊥ := h
      rw [h', Submodule.mem_bot] at this; exact hx0 this
    · intro y
      have h' : LinearMap.range f = ⊤ := h
      have hy : y ∈ LinearMap.range f := by rw [h']; trivial
      exact hy
  -- (8) the isomorphism
  let e : 𝒱 ≃ₗ[ℂ] M := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨{ toLinearEquiv := e.symm, map_act := fun u n y => ?_ }⟩
  apply e.injective
  rw [LinearEquiv.apply_symm_apply]
  change mode (N.YM u) n y = f (V.smul u n (e.symm y))
  rw [hfint]
  congr 1
  exact (e.apply_symm_apply y).symm

end Vacuum

end VOA.Classification.COne.PlusUnitary
