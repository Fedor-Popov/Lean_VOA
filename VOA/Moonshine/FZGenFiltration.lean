/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.ZhuGenFiltration
import VOA.Modules.Translation

/-!
# A filtered criterion for Frenkel–Zhu bimodule generation (module-generic)

Let `W` be a VOA and `N` an ordinary `W`-module (`OrdVModule W M`).  For homogeneous `a ∈ W_p`
(`p : ℕ`) and `x ∈ M`, the three Frenkel–Zhu residues are

* `fzCirc N p a x = Res z⁻²(1+z)^p Y(a,z)x = ∑_{i ≤ p} C(p,i) a₍ᵢ₋₂₎x` (the generators of
  `O(M)`);
* `fzLeft N p a x = Res z⁻¹(1+z)^p Y(a,z)x = ∑_{i ≤ p} C(p,i) a₍ᵢ₋₁₎x` (`a ∗ x`);
* `fzRight N p a x = Res z⁻¹(1+z)^{p-1} Y(a,z)x = ∑_{i < p} C(p-1,i) a₍ᵢ₋₁₎x` (`x ∗ a`, `p ≥ 1`).

These are **minimal local definitions**: any construction of the FZ bimodule `A(M) = M/O(M)`
whose `O(M)`, `a ∗ x`, `x ∗ a` agree with these on homogeneous `a` (they are the standard
formulas) satisfies the hypotheses of the criterion below.

Write `F_{<n}M = ⊕_{k<n} M_k` (integer weights).  If `F_{<n}M ≤ S`, then `S` contains every
`a₍ⱼ₎x` with `a ∈ W_p`, `x ∈ M_q`, `q < n`, `j ≤ 0`, `p + q − j − 1 = n` (`lowerProdM_subset`):

* `j = -1`: `a ∗ x − a₍₋₁₎x ∈ F_{<n}M`;
* `j ≤ -2`: the module higher-pole residue `PresM` lies in the span of the `fzCirc`
  (`PresM_mem`, the module form of Frenkel–Zhu Lemma 2.1.2, from `act_T_covariance`) and has
  leading term `a₍ⱼ₎x`;
* `j = 0`: `a ∗ x − x ∗ a − a₍₀₎x ∈ F_{<n}M` (exact; no skew-symmetry and no `O(M)` needed).

Induction on the weight gives `eq_top_of_lowerSpanM`.

## Main results
* `fzCirc`, `fzLeft`, `fzRight`, `PresM`, `PresM_mem`.
* `FlM`, `lowerProdM`, `lowerProdM_subset`, `weight_le_of_lowerSpanM`,
  `eq_top_of_lowerSpanM`.

## Status
`sorry`-free; no project axiom (no `VOA.pbw`).  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.FZGen

open VOA VertexOperatorAlgebra WeakModule
open Submodule

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## §1  The Frenkel–Zhu residues -/

/-- `O(M)` generator: `Res z⁻²(1+z)^p Y(a,z)x` for `a ∈ W_p`. -/
noncomputable def fzCirc (N : OrdVModule W M) (p : ℕ) (a : 𝒱) (x : M) : M :=
  ∑ i ∈ Finset.range (p + 1), cbz (p : ℤ) (i : ℤ) • N.act a ((i : ℤ) - 2) x

/-- The left action `a ∗ x = Res z⁻¹(1+z)^p Y(a,z)x` for `a ∈ W_p`. -/
noncomputable def fzLeft (N : OrdVModule W M) (p : ℕ) (a : 𝒱) (x : M) : M :=
  ∑ i ∈ Finset.range (p + 1), cbz (p : ℤ) (i : ℤ) • N.act a ((i : ℤ) - 1) x

/-- The right action `x ∗ a = Res z⁻¹(1+z)^{p-1} Y(a,z)x` for `a ∈ W_p`, `p ≥ 1`. -/
noncomputable def fzRight (N : OrdVModule W M) (p : ℕ) (a : 𝒱) (x : M) : M :=
  ∑ i ∈ Finset.range p, cbz ((p : ℤ) - 1) (i : ℤ) • N.act a ((i : ℤ) - 1) x

/-- The depth-`k` module residue `Res z^{-2-k}(1+z)^{p+k} Y(a,z)x`. -/
noncomputable def PresM (N : OrdVModule W M) (p : ℕ) (a : 𝒱) (x : M) (k : ℕ) : M :=
  ∑ i ∈ Finset.range (p + k + 1), cbz ((p : ℤ) + k) (i : ℤ) • N.act a ((i : ℤ) - 2 - k) x

theorem PresM_zero (N : OrdVModule W M) (p : ℕ) (a : 𝒱) (x : M) :
    PresM N p a x 0 = fzCirc N p a x := by
  unfold PresM fzCirc
  refine Finset.sum_congr rfl fun i _ => ?_
  norm_num

theorem act_L_neg_one (N : OrdVModule W M) (a : 𝒱) (n : ℤ) (x : M) :
    N.act (W.L (-1) a) n x = (-(n : ℂ)) • N.act a (n - 1) x :=
  act_T_covariance N.toWeakModule a n x

/-- **Module higher-pole residues** (Frenkel–Zhu Lemma 2.1.2 for modules): if `X` contains
every `fzCirc N p a x` (fixed `x`, all homogeneous `a`), it contains every `PresM N p a x k`. -/
theorem PresM_mem (N : OrdVModule W M) (x : M) (X : Submodule ℂ M)
    (hbase : ∀ (p : ℕ) (a : 𝒱), a ∈ W.grading (p : ℤ) → fzCirc N p a x ∈ X) (k : ℕ) :
    ∀ (p : ℕ) (a : 𝒱), a ∈ W.grading (p : ℤ) → PresM N p a x k ∈ X := by
  induction k with
  | zero => intro p a ha; rw [PresM_zero]; exact hbase p a ha
  | succ n ih =>
    intro P a ha
    have haL : W.L (-1) a ∈ W.grading ((P + 1 : ℕ) : ℤ) := by
      have := L_neg_one_mem_grading_succ W ha
      rwa [show ((P : ℤ) + 1) = ((P + 1 : ℕ) : ℤ) by push_cast; ring] at this
    have hG : PresM N (P + 1) (W.L (-1) a) x n ∈ X := ih (P + 1) _ haL
    have hP : PresM N P a x n ∈ X := ih P a ha
    have hGeq : PresM N (P + 1) (W.L (-1) a) x n
        = ∑ i ∈ Finset.range (P + n + 2),
            (cbz ((P : ℤ) + n + 1) (i : ℤ) * (-((i : ℂ) - 2 - n))) • N.act a ((i : ℤ) - 3 - n) x := by
      unfold PresM
      rw [show P + 1 + n + 1 = P + n + 2 from by ring]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [act_L_neg_one, smul_smul,
        show ((i : ℤ) - 2 - n - 1) = (i : ℤ) - 3 - n from by ring]
      congr 1
      push_cast; ring_nf
    have hLHS : ((n : ℂ) + 2) • PresM N P a x (n + 1)
        = ∑ i ∈ Finset.range (P + n + 2),
            (((n : ℂ) + 2) * cbz ((P : ℤ) + n + 1) (i : ℤ)) • N.act a ((i : ℤ) - 3 - n) x := by
      unfold PresM
      rw [show P + (n + 1) + 1 = P + n + 2 from by ring, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_smul]
      congr 2
      push_cast; ring
    have hPn : ((P : ℂ) + n + 1) • PresM N P a x n
        = ∑ i ∈ Finset.range (P + n + 2),
            (((P : ℂ) + n + 1) * cbz ((P : ℤ) + n) ((i : ℤ) - 1)) • N.act a ((i : ℤ) - 3 - n) x := by
      unfold PresM
      rw [Finset.smul_sum]
      rw [Finset.sum_range_succ' (fun i => (((P : ℂ) + n + 1) * cbz ((P : ℤ) + n) ((i : ℤ) - 1))
          • N.act a ((i : ℤ) - 3 - n) x) (P + n + 1)]
      rw [show cbz ((P : ℤ) + n) ((0 : ℕ) - 1 : ℤ) = 0 from cbz_apply_neg _ (by norm_num),
        mul_zero, zero_smul, add_zero]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [smul_smul]
      congr 2
      · push_cast; ring_nf
      · push_cast; ring_nf
    have hsum : ((n : ℂ) + 2) • PresM N P a x (n + 1)
        = PresM N (P + 1) (W.L (-1) a) x n + ((P : ℂ) + n + 1) • PresM N P a x n := by
      rw [hGeq, hLHS, hPn, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← add_smul]
      congr 1
      have := pres_coeff_identity P n (i : ℤ)
      push_cast at this ⊢
      linear_combination this
    have hne : ((n : ℂ) + 2) ≠ 0 := by
      have : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast Nat.succ_ne_zero (n + 1)
    have : PresM N P a x (n + 1)
        = (((n : ℂ) + 2)⁻¹) • (PresM N (P + 1) (W.L (-1) a) x n + ((P : ℂ) + n + 1) • PresM N P a x n) := by
      rw [← hsum, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact smul_mem _ _ (add_mem hG (smul_mem _ _ hP))

/-! ## §2  The weight filtration of `M` -/

/-- `F_{<n}M = ⊕_{k<n} M_k` (integer weights). -/
noncomputable def FlM (N : OrdVModule W M) (n : ℤ) : Submodule ℂ M :=
  ⨆ (k : ℤ) (_ : k < n), N.weight (k : ℂ)

theorem mem_FlM_of_mem {N : OrdVModule W M} {k n : ℤ} (h : k < n) {x : M}
    (hx : x ∈ N.weight (k : ℂ)) : x ∈ FlM N n :=
  le_iSup₂_of_le (f := fun (k : ℤ) (_ : k < n) => N.weight (k : ℂ)) k h le_rfl hx

theorem FlM_le_of {N : OrdVModule W M} {n : ℤ} {S : Submodule ℂ M}
    (h : ∀ k < n, N.weight (k : ℂ) ≤ S) : FlM N n ≤ S :=
  iSup₂_le fun k hk => h k hk

/-- Mode grading on `M`: `a ∈ W_p`, `x ∈ M_q ⇒ a₍ⱼ₎x ∈ M_{p+q-j-1}`. -/
theorem act_mem_weight (N : OrdVModule W M) {p q : ℤ} {a : 𝒱} (ha : a ∈ W.grading p) {x : M}
    (hx : x ∈ N.weight (q : ℂ)) (j : ℤ) : N.act a j x ∈ N.weight ((p + q - j - 1 : ℤ) : ℂ) := by
  have h := mode_mem_weight N ha hx j
  rw [act_def]
  convert h using 2
  push_cast; ring

theorem act_mem_FlM (N : OrdVModule W M) {p q j n : ℤ} {a : 𝒱} (ha : a ∈ W.grading p) {x : M}
    (hx : x ∈ N.weight (q : ℂ)) (h : p + q - j - 1 < n) : N.act a j x ∈ FlM N n :=
  mem_FlM_of_mem h (act_mem_weight N ha hx j)

theorem act_zero_left' (N : OrdVModule W M) (j : ℤ) (x : M) : N.act (0 : 𝒱) j x = 0 := by
  rw [act_def, map_zero]; rfl

/-! ## §3  The three leading-term identities -/

/-- `a ∗ x − a₍₋₁₎x ∈ F_{<p+q}`. -/
theorem fzLeft_sub_mem (N : OrdVModule W M) {p : ℕ} {q : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading (p : ℤ)) {x : M} (hx : x ∈ N.weight (q : ℂ)) :
    fzLeft N p a x - N.act a (-1) x ∈ FlM N ((p : ℤ) + q) := by
  unfold fzLeft
  rw [Finset.sum_range_succ', Nat.cast_zero, cbz_zero, one_smul, zero_sub, add_sub_cancel_right]
  refine sum_mem fun i _ => smul_mem _ _ (act_mem_FlM N ha hx ?_)
  push_cast; omega

/-- `a₍₋₂₋ₖ₎x − PresM ∈ F_{<p+q+1+k}`. -/
theorem act_sub_PresM_mem (N : OrdVModule W M) {p : ℕ} {q : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading (p : ℤ)) {x : M} (hx : x ∈ N.weight (q : ℂ)) (k : ℕ) :
    N.act a (-2 - k) x - PresM N p a x k ∈ FlM N ((p : ℤ) + q + 1 + k) := by
  unfold PresM
  rw [Finset.sum_range_succ', Nat.cast_zero, cbz_zero, one_smul, zero_sub]
  rw [show N.act a (-2 - k) x - (∑ i ∈ Finset.range (p + k), cbz ((p : ℤ) + k) ((i + 1 : ℕ) : ℤ) •
      N.act a (((i + 1 : ℕ) : ℤ) - 2 - k) x + N.act a (-2 - k) x)
      = -(∑ i ∈ Finset.range (p + k), cbz ((p : ℤ) + k) ((i + 1 : ℕ) : ℤ) •
      N.act a (((i + 1 : ℕ) : ℤ) - 2 - k) x) by abel]
  refine neg_mem (sum_mem fun i _ => smul_mem _ _ (act_mem_FlM N ha hx ?_))
  push_cast; omega

omit [Module ℂ M] in
theorem sum_range_two_sub (f : ℕ → M) (K : ℕ) :
    ∑ i ∈ Finset.range (K + 2), f i = f 0 + f 1 + ∑ i ∈ Finset.range K, f (i + 2) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  abel

/-- **The exact commutator, at leading order**: `a ∗ x − x ∗ a − a₍₀₎x ∈ F_{<p+q-1}`
(`a ∈ W_p`, `p ≥ 2`). -/
theorem fzLeft_sub_fzRight_mem (N : OrdVModule W M) {P : ℕ} {q : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading ((P + 2 : ℕ) : ℤ)) {x : M} (hx : x ∈ N.weight (q : ℂ)) :
    fzLeft N (P + 2) a x - fzRight N (P + 2) a x - N.act a 0 x
      ∈ FlM N (((P + 2 : ℕ) : ℤ) + q - 1) := by
  unfold fzLeft fzRight
  rw [show P + 2 + 1 = (P + 1) + 2 by ring, sum_range_two_sub, sum_range_two_sub]
  have c1 : cbz (((P + 2 : ℕ) : ℤ)) (1 : ℤ) = ((P + 2 : ℕ) : ℂ) := by
    rw [cbz_apply_nonneg _ (by norm_num)]; simp [gBinom]
  have c2 : cbz (((P + 2 : ℕ) : ℤ) - 1) (1 : ℤ) = ((P + 1 : ℕ) : ℂ) := by
    rw [show (((P + 2 : ℕ) : ℤ) - 1) = ((P + 1 : ℕ) : ℤ) by push_cast; ring,
      cbz_apply_nonneg _ (by norm_num)]; simp [gBinom]
  simp only [Nat.cast_zero, cbz_zero, one_smul, Nat.cast_one, sub_self]
  rw [c1, c2]
  have hS1 : (∑ i ∈ Finset.range (P + 1), cbz (((P + 2 : ℕ) : ℤ)) (((i + 2 : ℕ) : ℤ)) •
      N.act a (((i + 2 : ℕ) : ℤ) - 1) x) ∈ FlM N (((P + 2 : ℕ) : ℤ) + q - 1) :=
    sum_mem fun i _ => smul_mem _ _ (act_mem_FlM N ha hx (by push_cast; omega))
  have hS2 : (∑ i ∈ Finset.range P, cbz (((P + 2 : ℕ) : ℤ) - 1) (((i + 2 : ℕ) : ℤ)) •
      N.act a (((i + 2 : ℕ) : ℤ) - 1) x) ∈ FlM N (((P + 2 : ℕ) : ℤ) + q - 1) :=
    sum_mem fun i _ => smul_mem _ _ (act_mem_FlM N ha hx (by push_cast; omega))
  have key : N.act a (0 - 1) x + ((P + 2 : ℕ) : ℂ) • N.act a 0 x
        + (∑ i ∈ Finset.range (P + 1), cbz (((P + 2 : ℕ) : ℤ)) (((i + 2 : ℕ) : ℤ)) •
          N.act a (((i + 2 : ℕ) : ℤ) - 1) x)
      - (N.act a (0 - 1) x + ((P + 1 : ℕ) : ℂ) • N.act a 0 x
        + ∑ i ∈ Finset.range P, cbz (((P + 2 : ℕ) : ℤ) - 1) (((i + 2 : ℕ) : ℤ)) •
          N.act a (((i + 2 : ℕ) : ℤ) - 1) x) - N.act a 0 x
      = (∑ i ∈ Finset.range (P + 1), cbz (((P + 2 : ℕ) : ℤ)) (((i + 2 : ℕ) : ℤ)) •
          N.act a (((i + 2 : ℕ) : ℤ) - 1) x)
        - ∑ i ∈ Finset.range P, cbz (((P + 2 : ℕ) : ℤ) - 1) (((i + 2 : ℕ) : ℤ)) •
          N.act a (((i + 2 : ℕ) : ℤ) - 1) x := by
    push_cast; module
  rw [key]
  exact sub_mem hS1 hS2

/-! ## §4  The criterion -/

/-- The **weight-raising products of lower-weight states** of `M` of weight `n`:
`a₍ⱼ₎x` with `a ∈ W_p`, `x ∈ M_q`, `q < n`, `j ≤ 0`, `p + q − j − 1 = n`. -/
def lowerProdM (N : OrdVModule W M) (n : ℤ) : Set M :=
  {y | ∃ p q j : ℤ, q < n ∧ j ≤ 0 ∧ p + q - j - 1 = n ∧
    ∃ a ∈ W.grading p, ∃ x ∈ N.weight (q : ℂ), y = N.act a j x}

theorem mem_grading_neg_eq_zero' {k : ℤ} (hk : k < 0) {a : 𝒱} (ha : a ∈ W.grading k) : a = 0 := by
  rw [W.positivity k hk] at ha; exact (mem_bot ℂ).mp ha

/-- If `S` contains `F_{<n}M`, the `fzCirc`, and is closed under `a ∗ ·` and `· ∗ a`, it
contains `lowerProdM N n`. -/
theorem lowerProdM_subset (N : OrdVModule W M) {S : Submodule ℂ M}
    (hO : ∀ (p : ℕ) (a : 𝒱), a ∈ W.grading (p : ℤ) → ∀ x : M, fzCirc N p a x ∈ S)
    (hL : ∀ (p : ℕ) (a : 𝒱), a ∈ W.grading (p : ℤ) → ∀ x ∈ S, fzLeft N p a x ∈ S)
    (hR : ∀ (p : ℕ) (a : 𝒱), 1 ≤ p → a ∈ W.grading (p : ℤ) → ∀ x ∈ S, fzRight N p a x ∈ S)
    {n : ℤ} (hF : FlM N n ≤ S) : lowerProdM N n ⊆ S := by
  rintro y ⟨p, q, j, hq, hj, hw, a, ha, x, hx, rfl⟩
  have hxS : x ∈ S := hF (mem_FlM_of_mem hq hx)
  rcases lt_or_ge p 0 with hp0 | hp0
  · rw [mem_grading_neg_eq_zero' hp0 ha, act_zero_left']; exact zero_mem _
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, p = (P : ℤ) := ⟨p.toNat, by omega⟩
  rcases lt_trichotomy j (-1) with hlt | heq | hgt
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = -2 - k := ⟨(-2 - j).toNat, by omega⟩
    have h1 := act_sub_PresM_mem N ha hx k
    rw [show (P : ℤ) + q + 1 + k = n by omega] at h1
    have h2 : PresM N P a x k ∈ S := PresM_mem N x S (fun p a ha => hO p a ha x) k P a ha
    have := add_mem (hF h1) h2
    rwa [sub_add_cancel] at this
  · subst heq
    have h1 := fzLeft_sub_mem N ha hx
    rw [show (P : ℤ) + q = n by omega] at h1
    have := sub_mem (hL P a ha x hxS) (hF h1)
    rwa [sub_sub_cancel] at this
  · have hj0 : j = 0 := by omega
    subst hj0
    obtain ⟨P', rfl⟩ : ∃ P' : ℕ, P = P' + 2 := ⟨P - 2, by omega⟩
    have h1 := fzLeft_sub_fzRight_mem N ha hx
    rw [show ((P' + 2 : ℕ) : ℤ) + q - 1 = n by push_cast at hw ⊢; omega] at h1
    have h2 := sub_mem (hL _ a ha x hxS) (hR _ a (by omega) ha x hxS)
    have := sub_mem h2 (hF h1)
    rwa [sub_sub_cancel] at this

/-- **The filtered FZ-bimodule generation criterion (graded form).**  Suppose the integer
weights of `M` are bounded below by `n₀`, and every `M_n` is spanned by `G` and
`lowerProdM N n`.  Then every subspace `S` containing `G` and all `fzCirc` (i.e. `O(M)`), and
closed under `a ∗ ·`, `· ∗ a`, contains every integer-weight space `M_k`. -/
theorem weight_le_of_lowerSpanM (N : OrdVModule W M) (G : Set M) (n₀ : ℤ)
    (hbot : ∀ k : ℤ, k < n₀ → N.weight (k : ℂ) = ⊥)
    (hG : ∀ n : ℤ, N.weight (n : ℂ) ≤ span ℂ (G ∪ lowerProdM N n))
    (S : Submodule ℂ M)
    (hO : ∀ (p : ℕ) (a : 𝒱), a ∈ W.grading (p : ℤ) → ∀ x : M, fzCirc N p a x ∈ S)
    (hL : ∀ (p : ℕ) (a : 𝒱), a ∈ W.grading (p : ℤ) → ∀ x ∈ S, fzLeft N p a x ∈ S)
    (hR : ∀ (p : ℕ) (a : 𝒱), 1 ≤ p → a ∈ W.grading (p : ℤ) → ∀ x ∈ S, fzRight N p a x ∈ S)
    (hGS : G ⊆ S) : ∀ k : ℤ, N.weight (k : ℂ) ≤ S := by
  have key : ∀ m : ℕ, ∀ k : ℤ, k < n₀ + m → N.weight (k : ℂ) ≤ S := by
    intro m
    induction m with
    | zero =>
      intro k hk
      rw [hbot k (by simpa using hk)]; exact bot_le
    | succ m ih =>
      intro k hk
      rcases lt_or_eq_of_le (show k ≤ n₀ + m by push_cast at hk; omega) with hlt | heq
      · exact ih k hlt
      subst heq
      refine (hG _).trans (span_le.mpr ?_)
      rintro x (hx | hx)
      · exact hGS hx
      · exact lowerProdM_subset N hO hL hR (FlM_le_of ih) hx
  intro k
  exact key (k - n₀ + 1).toNat k (by omega)

/-- **The filtered FZ-bimodule generation criterion.**  As `weight_le_of_lowerSpanM`, when
moreover every nonzero weight space has integer weight: then `S = ⊤`. -/
theorem eq_top_of_lowerSpanM (N : OrdVModule W M) (G : Set M) (n₀ : ℤ)
    (hint : ∀ α : ℂ, N.weight α ≠ ⊥ → ∃ k : ℤ, α = k)
    (hbot : ∀ k : ℤ, k < n₀ → N.weight (k : ℂ) = ⊥)
    (hG : ∀ n : ℤ, N.weight (n : ℂ) ≤ span ℂ (G ∪ lowerProdM N n))
    (S : Submodule ℂ M)
    (hO : ∀ (p : ℕ) (a : 𝒱), a ∈ W.grading (p : ℤ) → ∀ x : M, fzCirc N p a x ∈ S)
    (hL : ∀ (p : ℕ) (a : 𝒱), a ∈ W.grading (p : ℤ) → ∀ x ∈ S, fzLeft N p a x ∈ S)
    (hR : ∀ (p : ℕ) (a : 𝒱), 1 ≤ p → a ∈ W.grading (p : ℤ) → ∀ x ∈ S, fzRight N p a x ∈ S)
    (hGS : G ⊆ S) : S = ⊤ := by
  have hk := weight_le_of_lowerSpanM N G n₀ hbot hG S hO hL hR hGS
  rw [eq_top_iff, ← N.isInternal.submodule_iSup_eq_top, iSup_le_iff]
  intro α
  by_cases h : N.weight α = ⊥
  · rw [h]; exact bot_le
  · obtain ⟨k, rfl⟩ := hint α h
    exact hk k

end VOA.Moonshine.FZGen
