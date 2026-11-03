import VOA.Huang.LiConverseResidue
import VOA.Huang.LiFusionZhuLaws

/-! # The Frenkel–Zhu bimodule laws for an arbitrary weak module

Frenkel–Zhu (Duke 1992, Thm 1.5.1): for any module `M`, `M / O(M)` is an `A(V)`-bimodule
under `a ∗ w = Res z⁻¹(1+z)^{wt a} Y(a,z)w` and `w ∗ a = Res z⁻¹(1+z)^{wt a - 1} Y(a,z)w`.
Using the residue calculus of `LiConverseResidue`, each law is one instance of the module
Jacobi identity with explicit Laurent-polynomial test functions, followed by membership of
the higher-pole residues `Res z^{-2-m}(1+z)^{wt c + n} Y(c,z)` (`n ≤ m`) in `O(M)`.

The final theorem `rawZhuBimoduleLaws` discharges the seven identities named in
`VOA.Huang.LiFusion.RawZhuBimoduleLaws` for every ordinary module, unconditionally.

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiConverse

open VOA VOA.FZ LaurentPolynomial
open scoped BigOperators

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type v} [AddCommGroup M] [Module ℂ M]

/-! ## Test functions whose residues land in `O(M)` -/

section Good

variable (A : WeakModule W M)

/-- The test functions `φ` with `Res φ(z) Y(c,z) x ∈ O(M)` for every weight-`k` state `c`. -/
def good (k : ℤ) : Submodule ℂ ℂ[T;T⁻¹] where
  carrier := {φ | ∀ c ∈ W.grading k, ∀ x : M, res A c x φ ∈ fzO A}
  add_mem' {φ ψ} hφ hψ c hc x := by rw [map_add]; exact Submodule.add_mem _ (hφ c hc x) (hψ c hc x)
  zero_mem' c _ x := by rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' r φ hφ c hc x := by rw [map_smul]; exact Submodule.smul_mem _ r (hφ c hc x)

theorem res_mem_of_good {k : ℤ} {c : V} (hc : c ∈ W.grading k) (x : M) {φ : ℂ[T;T⁻¹]}
    (hφ : φ ∈ good A k) : res A c x φ ∈ fzO A := hφ c hc x

theorem good_of_neg {k : ℤ} (hk : k < 0) (φ : ℂ[T;T⁻¹]) : φ ∈ good A k := by
  intro c hc x
  rw [W.positivity k hk, Submodule.mem_bot] at hc
  subst hc
  rw [res_zero_a]; exact Submodule.zero_mem _

theorem T_neg_two_sub_succ (m : ℕ) :
    z * T (-2 - ((m + 1 : ℕ) : ℤ)) = T (-2 - (m : ℤ)) := by
  rw [z_mul_T]; congr 1; push_cast; ring

/-- **Higher-pole residues** (Frenkel–Zhu Lemma 2.1.2, module form):
`Res z^{-2-m}(1+z)^{r+n} Y(c,z) x ∈ O(M)` for `c` of weight `r` and `n ≤ m`. -/
theorem gen_mem_good (r : ℕ) : ∀ (d n : ℕ),
    (1 + z) ^ (r + n) * T (-2 - ((n + d : ℕ) : ℤ)) ∈ good A (r : ℤ)
  | 0, n => by
    intro c hc x
    rw [Nat.add_zero, ← fzRes_eq_res]
    exact fzRes_mem_fzO A n hc x
  | d + 1, n => by
    have h1 := gen_mem_good r d (n + 1)
    have h2 := gen_mem_good r d n
    have he : (1 + z) ^ (r + n) * T (-2 - ((n + (d + 1) : ℕ) : ℤ))
        = (1 + z) ^ (r + (n + 1)) * T (-2 - ((n + 1 + d : ℕ) : ℤ))
          - (1 + z) ^ (r + n) * T (-2 - ((n + d : ℕ) : ℤ)) := by
      rw [show n + 1 + d = n + (d + 1) by ring, ← T_neg_two_sub_succ (n + d),
        show n + d + 1 = n + (d + 1) by ring, show r + (n + 1) = r + n + 1 by ring, pow_succ]
      ring
    rw [he]
    exact Submodule.sub_mem _ h1 h2

/-- The general generator, in the form used by the law computations. -/
theorem gen_mem_good' {k : ℤ} {e n m : ℕ} (he : (e : ℤ) = k + n) (hnm : n ≤ m) (c : ℂ) :
    LC c * ((1 + z) ^ e * T (-2 - (m : ℤ))) ∈ good A k := by
  rw [← smul_eq_C_mul]
  apply Submodule.smul_mem
  rcases lt_or_ge k 0 with hk | hk
  · exact good_of_neg A hk _
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, k = r := ⟨k.toNat, by omega⟩
    have hr : e = r + n := by omega
    obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
    rw [hr]
    exact gen_mem_good A r d n

end Good

/-! ## Finite sums in a submodule -/

theorem finsum_mem_submodule {N : Type*} [AddCommGroup N] [Module ℂ N] (S : Submodule ℂ N)
    {ι : Type*} (f : ι → N) (hf : ∀ i, f i ∈ S) : (∑ᶠ i, f i) ∈ S := by
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum f h]
    exact Submodule.sum_mem _ fun i _ => hf i
  · rw [finsum_of_infinite_support h]; exact S.zero_mem

/-- If every summand differs from the `0`-th "main term" only by an element of `S`, the
whole finite sum differs from that main term by an element of `S`. -/
theorem finsum_sub_main_mem {N : Type*} [AddCommGroup N] [Module ℂ N] (S : Submodule ℂ N)
    (f : ℤ → N) (hf : (Function.support f).Finite) (x : N)
    (h : ∀ j, f j - (if j = 0 then x else 0) ∈ S) : (∑ᶠ j, f j) - x ∈ S := by
  have hfin : (Function.support fun j : ℤ => if j = 0 then x else 0).Finite :=
    (Set.finite_singleton (0 : ℤ)).subset fun j hj => by
      by_contra h'
      exact hj (if_neg h')
  have : (∑ᶠ j, f j) - x = ∑ᶠ j, (f j - if j = 0 then x else 0) := by
    rw [finsum_sub_distrib hf hfin, finsum_eq_single _ 0 (fun j hj => if_neg hj), if_pos rfl]
  rw [this]
  exact finsum_mem_submodule S _ h

/-! ## Collapsing the Jacobi sums -/

section Collapse

variable (A : WeakModule W M)

theorem negOnePow_neg_one : negOnePow (-1) = -1 := by
  simp [negOnePow]

theorem negOnePow_mul_cbz_neg_one (t : ℕ) : negOnePow (t : ℤ) * cbz (-1) (t : ℤ) = 1 := by
  rw [ZhuRes.cbz_neg_one, negOnePow_natCast, ← mul_pow]; norm_num

/-- At `l = 0` the left side of `res_jacobi` is a commutator. -/
theorem jacL_zero_sum (a b : V) (w : M) (f g : ℂ[T;T⁻¹]) :
    (∑ᶠ j : ℤ, jacL A a b w 0 f g j) = res A a (res A b w g) f - res A b (res A a w f) g := by
  rw [finsum_eq_single _ 0 (fun j hj => by
    rw [jacL, cbz_zero_left, if_neg hj, mul_zero, zero_smul])]
  simp [jacL, negOnePow, T_zero]

/-- At `l = -1`, the `j`-th left term is a sum of two ordered products. -/
theorem jacL_neg_one_nat (a b : V) (w : M) (f g : ℂ[T;T⁻¹]) (t : ℕ) :
    jacL A a b w (-1) f g (t : ℤ)
      = res A a (res A b w (T t * g)) (T (-1 - t) * f)
        + res A b (res A a w (T t * f)) (T (-1 - t) * g) := by
  rw [jacL, negOnePow_mul_cbz_neg_one, one_smul, negOnePow_neg_one, neg_one_smul, sub_neg_eq_add]

theorem jacL_neg_one_neg (a b : V) (w : M) (l : ℤ) (f g : ℂ[T;T⁻¹]) {j : ℤ} (hj : j < 0) :
    jacL A a b w l f g j = 0 := by
  rw [jacL, cbz_apply_neg l hj, mul_zero, zero_smul]

/-- Divided derivatives of `(1+z)^K z^s`. -/
theorem dd_pow_mul_T (K : ℕ) (s : ℤ) (t : ℕ) :
    dd t ((1 + z) ^ K * T s) = ∑ σ ∈ Finset.range (t + 1),
      LC (cbz K σ * cbz s ((t : ℤ) - σ)) * ((1 + z) ^ (K - σ) * T (s - ((t : ℤ) - σ))) := by
  rw [dd_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [dd_one_add_z_pow, dd_T, map_mul]
  ring

/-- A single test-function term of the shape produced by the law computations. -/
theorem term_mem_good {k : ℤ} (c : ℂ) (e₁ e₂ : ℕ) (s₁ s₂ : ℤ) (n m : ℕ)
    (he : ((e₁ + e₂ : ℕ) : ℤ) = k + n) (hs : s₁ + s₂ = -2 - (m : ℤ)) (hnm : n ≤ m) :
    LC c * ((1 + z) ^ e₁ * T s₁) * ((1 + z) ^ e₂ * T s₂) ∈ good A k := by
  have : LC c * ((1 + z) ^ e₁ * T s₁) * ((1 + z) ^ e₂ * T s₂)
      = LC c * ((1 + z) ^ (e₁ + e₂) * T (-2 - (m : ℤ))) := by
    rw [← hs, T_add, pow_add]; ring
  rw [this]
  exact gen_mem_good' A he hnm c

end Collapse

/-! ## The left action -/

section Left

variable (A : WeakModule W M)

/-- **`O(M)` is stable under the left action** (generators). -/
theorem fzLeft_fzRes_mem {K p : ℕ} {u a : V} (hu : u ∈ W.grading (K : ℤ))
    (ha : a ∈ W.grading (p : ℤ)) (k : ℕ) (m : M) :
    fzLeft A K u (fzRes A p k a m) ∈ fzO A := by
  set f : ℂ[T;T⁻¹] := (1 + z) ^ K * T (-1)
  set g : ℂ[T;T⁻¹] := (1 + z) ^ (p + k) * T (-2 - k)
  have hj := res_jacobi A u a m 0 f g
  rw [jacL_zero_sum] at hj
  rw [fzRes_eq_res, fzLeft_eq_res, show res A u (res A a m g) f
      = res A a (res A u m f) g + ∑ᶠ i : ℤ, jacR A u a m 0 f g i by rw [← hj]; abel]
  refine Submodule.add_mem _ ?_ (finsum_mem_submodule _ _ fun i => ?_)
  · rw [← fzRes_eq_res]; exact fzRes_mem_fzO A k ha _
  · rcases lt_or_ge i 0 with hi | hi
    · rw [jacR, dd_neg hi, zero_mul, map_zero]; exact Submodule.zero_mem _
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, i = t := ⟨i.toNat, by omega⟩
    refine res_mem_of_good A (W.smul_mem_grading hu ha _) m ?_
    rw [dd_pow_mul_T, Finset.sum_mul]
    refine Submodule.sum_mem _ fun σ hσ => ?_
    rw [Finset.mem_range] at hσ
    rcases le_or_gt σ K with hσK | hσK
    · exact term_mem_good A _ _ _ _ _ (k + (t - σ) + 1) (k + (t - σ) + 1)
        (by push_cast [Nat.cast_sub hσK, Nat.cast_sub (show σ ≤ t by omega)]; ring)
        (by push_cast [Nat.cast_sub (show σ ≤ t by omega)]; ring) le_rfl
    · rw [cbz_lt (p := (K : ℤ)) (c := (σ : ℤ)) (by positivity) (by omega), zero_mul, map_zero,
        zero_mul, zero_mul]
      exact Submodule.zero_mem _

/-- Shifting `T(-1-t) * (1+z)^p` into generator form. -/
theorem left_tail_mem {p : ℕ} (t : ℕ) (ht : 1 ≤ t) (c : ℂ) :
    LC c * (T (-1 - (t : ℤ)) * (1 + z) ^ p) ∈ good A (p : ℤ) := by
  have := gen_mem_good' A (k := (p : ℤ)) (e := p) (n := 0) (m := t - 1) (by simp) (by omega) c
  convert this using 2
  rw [mul_comm]; congr 2; push_cast [Nat.cast_sub ht]; ring

/-- **Left associativity mod `O(M)`** (Zhu's argument, module form), for homogeneous
`a ∈ V_p`, `b ∈ V_q`: `(a ∗ b) ∗ w − a ∗ (b ∗ w) ∈ O(M)`, with `a ∗ b` written out as
`∑ₜ C(p,t) a₍ₜ₋₁₎b` (each summand of weight `p + q - t`). -/
theorem left_mul_mem {p q : ℕ} {a b : V} (ha : a ∈ W.grading (p : ℤ))
    (hb : b ∈ W.grading (q : ℤ)) (w : M) :
    (∑ t ∈ Finset.range (p + 1), cbz (p : ℤ) (t : ℤ) •
        fzLeft A (p + q - t) (W.smul a ((t : ℤ) - 1) b) w)
      - fzLeft A p a (fzLeft A q b w) ∈ fzO A := by
  set f : ℂ[T;T⁻¹] := (1 + z) ^ p
  set g : ℂ[T;T⁻¹] := (1 + z) ^ q * T (-1)
  have hj := res_jacobi A a b w (-1) f g
  have hR : (∑ᶠ i : ℤ, jacR A a b w (-1) f g i) = ∑ t ∈ Finset.range (p + 1),
      cbz (p : ℤ) (t : ℤ) • fzLeft A (p + q - t) (W.smul a ((t : ℤ) - 1) b) w := by
    rw [FusionTop.finsum_int_eq_range _ p (fun i hi => by
      rcases hi with hi | hi
      · rw [jacR, dd_neg hi, zero_mul, map_zero]
      · obtain ⟨t, rfl⟩ : ∃ t : ℕ, i = t := ⟨i.toNat, by omega⟩
        rw [jacR, dd_one_add_z_pow, cbz_lt (p := (p : ℤ)) (c := (t : ℤ)) (by positivity) hi,
          map_zero, zero_mul, zero_mul, map_zero])]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rw [jacR, dd_one_add_z_pow, fzLeft_eq_res, show (-1 : ℤ) + t = (t : ℤ) - 1 by ring,
      show LC (cbz (p : ℤ) (t : ℤ)) * (1 + z) ^ (p - t) * ((1 + z) ^ q * T (-1))
        = LC (cbz (p : ℤ) (t : ℤ)) * ((1 + z) ^ (p + q - t) * T (-1)) by
          rw [show p + q - t = (p - t) + q by omega, pow_add]; ring,
      ← smul_eq_C_mul, map_smul]
  rw [← hR, ← hj]
  refine finsum_sub_main_mem _ _ (jacL_support_finite A a b w (-1) f g) _ fun j => ?_
  rcases lt_or_ge j 0 with hj0 | hj0
  · rw [jacL_neg_one_neg A a b w (-1) f g hj0, if_neg (by omega), sub_zero]
    exact Submodule.zero_mem _
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, j = t := ⟨j.toNat, by omega⟩
  rw [jacL_neg_one_nat]
  have hG : res A b (res A a w (T t * f)) (T (-1 - t) * g) ∈ fzO A := by
    refine res_mem_of_good A hb _ ?_
    have := gen_mem_good' A (k := (q : ℤ)) (e := q) (n := 0) (m := t) (by simp) (by omega) 1
    rw [map_one, one_mul] at this
    convert this using 1
    rw [show g = (1 + z) ^ q * T (-1) from rfl, show (-2 : ℤ) - t = (-1 - t) + -1 by ring, T_add]
    ring
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have e1 : res A a (res A b w (T ((0 : ℕ) : ℤ) * g)) (T (-1 - ((0 : ℕ) : ℤ)) * f)
        = fzLeft A p a (fzLeft A q b w) := by
      rw [fzLeft_eq_res, fzLeft_eq_res, Nat.cast_zero, T_zero, one_mul, sub_zero, mul_comm]
    rw [if_pos (by simp), e1, add_sub_cancel_left]; exact hG
  · rw [if_neg (by omega), sub_zero]
    refine Submodule.add_mem _ (res_mem_of_good A ha _ ?_) hG
    simpa using left_tail_mem A (p := p) t ht 1

theorem cbz_int_one (n : ℤ) : cbz n 1 = (n : ℂ) := by
  rw [cbz_apply_nonneg _ (by norm_num)]; simp [gBinom]

/-- The derivative `dd 1` is a derivation. -/
theorem dd_one_mul (f g : ℂ[T;T⁻¹]) : dd 1 (f * g) = f * dd 1 g + dd 1 f * g := by
  have := dd_mul 1 f g
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.cast_zero, Nat.cast_one, sub_zero, sub_self, dd_zero] at this
  exact this

theorem dd_one_pow (K : ℕ) : dd 1 ((1 + z) ^ (K + 1)) = LC ((K : ℂ) + 1) * (1 + z) ^ K := by
  have := dd_one_add_z_pow (K + 1) 1
  rw [Nat.cast_one, cbz_int_one, Nat.add_sub_cancel] at this
  rw [this]; push_cast; rfl

theorem dd_one_T (s : ℤ) : dd 1 (T s) = LC (s : ℂ) * T (s - 1) := by
  rw [dd_T, cbz_int_one]

theorem z_mul_T_neg_two : z * T (-2) = T (-1) := by rw [z_mul_T]; norm_num

/-- The translation generators: `(L₋₁u + L₀u) ∗ y = Res z⁻²(1+z)^p Y(u,z) y`. -/
theorem fzLeft_L_eq_fzRes (p : ℕ) (u : V) (y : M) :
    fzLeft A (p + 1) (W.L (-1) u) y + (p : ℂ) • fzLeft A p u y = fzRes A p 0 u y := by
  rw [fzLeft_eq_res, fzLeft_eq_res, fzRes_eq_res, res_L_neg_one, dd_one_mul, dd_one_pow,
    dd_one_T, ← map_smul, ← map_neg, ← map_add]
  congr 1
  rw [smul_eq_C_mul, Nat.cast_zero, Nat.add_zero, show (-2 : ℤ) - 0 = -2 by norm_num,
    show (-1 : ℤ) - 1 = -2 by norm_num, ← z_mul_T_neg_two]
  simp only [map_add, map_one, map_natCast, map_intCast]
  push_cast
  ring

end Left

/-! ## The difference operator `D(a) = a ∗ · − · ∗ a` and the right action -/

section Right

variable (A : WeakModule W M)

/-- `D(a) = Res (1+z)^{p-1} Y(a,z)` preserves `O(M)` (generators). -/
theorem resD_fzRes_mem {P q : ℕ} {a b : V} (ha : a ∈ W.grading ((P + 1 : ℕ) : ℤ))
    (hb : b ∈ W.grading (q : ℤ)) (k : ℕ) (m : M) :
    res A a (fzRes A q k b m) ((1 + z) ^ P) ∈ fzO A := by
  set f : ℂ[T;T⁻¹] := (1 + z) ^ P
  set g : ℂ[T;T⁻¹] := (1 + z) ^ (q + k) * T (-2 - k)
  have hj := res_jacobi A a b m 0 f g
  rw [jacL_zero_sum] at hj
  rw [fzRes_eq_res, show res A a (res A b m g) f
      = res A b (res A a m f) g + ∑ᶠ i : ℤ, jacR A a b m 0 f g i by rw [← hj]; abel]
  refine Submodule.add_mem _ ?_ (finsum_mem_submodule _ _ fun i => ?_)
  · rw [← fzRes_eq_res]; exact fzRes_mem_fzO A k hb _
  · rcases lt_or_ge i 0 with hi | hi
    · rw [jacR, dd_neg hi, zero_mul, map_zero]; exact Submodule.zero_mem _
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, i = t := ⟨i.toNat, by omega⟩
    refine res_mem_of_good A (W.smul_mem_grading ha hb _) m ?_
    rw [dd_one_add_z_pow]
    rcases le_or_gt t P with htP | htP
    · have := term_mem_good A (k := ((P + 1 : ℕ) : ℤ) + q - (0 + t) - 1) (cbz P t) (P - t) (q + k)
        0 (-2 - k) k k (by push_cast [Nat.cast_sub htP]; ring) (by ring) le_rfl
      rw [T_zero, mul_one] at this
      exact this
    · rw [cbz_lt (p := (P : ℤ)) (c := (t : ℤ)) (by positivity) (by omega), map_zero, zero_mul,
        zero_mul]
      exact Submodule.zero_mem _

/-- **Left and right actions commute mod `O(M)`** (homogeneous, `wt b ≥ 1`). -/
theorem commute_mem {p Q : ℕ} {a b : V} (ha : a ∈ W.grading (p : ℤ))
    (hb : b ∈ W.grading ((Q + 1 : ℕ) : ℤ)) (w : M) :
    fzLeft A p a (fzRight A (Q + 1) b w) - fzRight A (Q + 1) b (fzLeft A p a w) ∈ fzO A := by
  set f : ℂ[T;T⁻¹] := (1 + z) ^ p * T (-1)
  set g : ℂ[T;T⁻¹] := (1 + z) ^ Q * T (-1)
  have hj := res_jacobi A a b w 0 f g
  rw [jacL_zero_sum] at hj
  rw [fzRight_eq_res A (by omega), fzRight_eq_res A (by omega), fzLeft_eq_res, fzLeft_eq_res,
    Nat.add_sub_cancel, hj]
  refine finsum_mem_submodule _ _ fun i => ?_
  rcases lt_or_ge i 0 with hi | hi
  · rw [jacR, dd_neg hi, zero_mul, map_zero]; exact Submodule.zero_mem _
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, i = t := ⟨i.toNat, by omega⟩
  refine res_mem_of_good A (W.smul_mem_grading ha hb _) w ?_
  rw [dd_pow_mul_T, Finset.sum_mul]
  refine Submodule.sum_mem _ fun σ hσ => ?_
  rw [Finset.mem_range] at hσ
  rcases le_or_gt σ p with hσp | hσp
  · exact term_mem_good A _ _ _ _ _ (t - σ) (t - σ)
      (by push_cast [Nat.cast_sub hσp, Nat.cast_sub (show σ ≤ t by omega)]; ring)
      (by push_cast [Nat.cast_sub (show σ ≤ t by omega)]; ring) le_rfl
  · rw [cbz_lt (p := (p : ℤ)) (c := (σ : ℤ)) (by positivity) (by omega), zero_mul, map_zero,
      zero_mul, zero_mul]
    exact Submodule.zero_mem _

/-- The right-action tail: `Res z^{-2-j}(1+z)^{q-1} Y(b,z) y ≡ (-1)^{j+1} (y ∗ b)`. -/
theorem right_tail_mem {Q : ℕ} {b : V} (hb : b ∈ W.grading ((Q + 1 : ℕ) : ℤ)) (y : M) :
    ∀ j : ℕ, res A b y ((1 + z) ^ Q * T (-2 - (j : ℤ)))
      - ((-1 : ℂ) ^ (j + 1)) • res A b y ((1 + z) ^ Q * T (-1)) ∈ fzO A
  | 0 => by
    have h := gen_mem_good' A (k := ((Q + 1 : ℕ) : ℤ)) (e := Q + 1) (n := 0) (m := 0)
      (by push_cast; ring) le_rfl 1
    rw [map_one, one_mul] at h
    have he : (1 + z) ^ Q * T (-2 - ((0 : ℕ) : ℤ))
        = (1 + z) ^ (Q + 1) * T (-2 - ((0 : ℕ) : ℤ)) - (1 + z) ^ Q * T (-1) := by
      rw [pow_succ, Nat.cast_zero, sub_zero, ← z_mul_T_neg_two]; ring
    rw [he, map_sub]
    simpa using h b hb y
  | j + 1 => by
    have ih := right_tail_mem hb y j
    have h := gen_mem_good' A (k := ((Q + 1 : ℕ) : ℤ)) (e := Q + 1) (n := 0) (m := j + 1)
      (by push_cast; ring) (by omega) 1
    rw [map_one, one_mul] at h
    have he : (1 + z) ^ Q * T (-2 - ((j + 1 : ℕ) : ℤ))
        = (1 + z) ^ (Q + 1) * T (-2 - ((j + 1 : ℕ) : ℤ)) - (1 + z) ^ Q * T (-2 - (j : ℤ)) := by
      rw [pow_succ, ← T_neg_two_sub_succ j]; ring
    rw [he, map_sub, show ((-1 : ℂ) ^ (j + 1 + 1)) = -((-1 : ℂ) ^ (j + 1)) by ring, neg_smul,
      show ∀ x y r : M, x - y - -r = x - (y - r) by intros; abel]
    exact Submodule.sub_mem _ (h b hb y) ih

theorem alt_geom (P n : ℕ) :
    ∑ t ∈ Finset.range n, ((-1 : ℂ) ^ t) • (T (t : ℤ) * (1 + z) ^ (P + 1))
      = (1 + z) ^ P - ((-1 : ℂ) ^ n) • (T (n : ℤ) * (1 + z) ^ P) := by
  have e : ∀ (t : ℕ) (X : ℂ[T;T⁻¹]), ((-1 : ℂ) ^ t) • (T (t : ℤ) * X) = (-z) ^ t * X := by
    intro t X
    rw [smul_eq_C_mul, map_pow, map_neg, map_one, neg_pow z, z, T_pow, mul_one]; ring
  simp only [e]
  rw [← Finset.sum_mul]
  have h := geom_sum_mul_neg (-z) n
  linear_combination (1 + z) ^ P * h

/-- **Right associativity mod `O(M)`** (homogeneous, positive weights):
`w ∗ (a ∗ b) − (w ∗ a) ∗ b ∈ O(M)`, with `a ∗ b = ∑ₜ C(p,t) a₍ₜ₋₁₎b`. -/
theorem right_mul_mem {P Q : ℕ} {a b : V} (ha : a ∈ W.grading ((P + 1 : ℕ) : ℤ))
    (hb : b ∈ W.grading ((Q + 1 : ℕ) : ℤ)) (w : M) :
    (∑ t ∈ Finset.range (P + 2), cbz ((P + 1 : ℕ) : ℤ) (t : ℤ) •
        fzRight A (P + 1 + (Q + 1) - t) (W.smul a ((t : ℤ) - 1) b) w)
      - fzRight A (Q + 1) b (fzRight A (P + 1) a w) ∈ fzO A := by
  set f : ℂ[T;T⁻¹] := (1 + z) ^ (P + 1)
  set g : ℂ[T;T⁻¹] := (1 + z) ^ Q * T (-1)
  have hj := res_jacobi A a b w (-1) f g
  have hR : (∑ᶠ i : ℤ, jacR A a b w (-1) f g i) = ∑ t ∈ Finset.range (P + 2),
      cbz ((P + 1 : ℕ) : ℤ) (t : ℤ) •
        fzRight A (P + 1 + (Q + 1) - t) (W.smul a ((t : ℤ) - 1) b) w := by
    rw [FusionTop.finsum_int_eq_range _ (P + 1) (fun i hi => by
      rcases hi with hi | hi
      · rw [jacR, dd_neg hi, zero_mul, map_zero]
      · obtain ⟨t, rfl⟩ : ∃ t : ℕ, i = t := ⟨i.toNat, by omega⟩
        rw [jacR, dd_one_add_z_pow,
          cbz_lt (p := ((P + 1 : ℕ) : ℤ)) (c := (t : ℤ)) (by positivity) hi,
          map_zero, zero_mul, zero_mul, map_zero])]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rw [jacR, dd_one_add_z_pow, fzRight_eq_res A (by omega),
      show (-1 : ℤ) + t = (t : ℤ) - 1 by ring,
      show LC (cbz ((P + 1 : ℕ) : ℤ) (t : ℤ)) * (1 + z) ^ (P + 1 - t) * ((1 + z) ^ Q * T (-1))
        = LC (cbz ((P + 1 : ℕ) : ℤ) (t : ℤ)) * ((1 + z) ^ (P + 1 + (Q + 1) - t - 1) * T (-1)) by
          rw [show P + 1 + (Q + 1) - t - 1 = (P + 1 - t) + Q by omega, pow_add]; ring,
      ← smul_eq_C_mul, map_smul]
  obtain ⟨J₁, hJ₁⟩ := res_shift_eventually_zero A a w f
  obtain ⟨J₂, hJ₂⟩ := res_shift_eventually_zero A b w g
  obtain ⟨J₃, hJ₃⟩ := res_shift_eventually_zero A a w ((1 + z) ^ P)
  set J : ℕ := (max J₁ (max J₂ J₃)).toNat with hJdef
  have hJ₁' : J₁ ≤ J := by omega
  have hJ₂' : J₂ ≤ J := by omega
  have hJ₃' : J₃ ≤ J := by omega
  set F : ℕ → M := fun t => res A a (res A b w (T t * g)) (T (-1 - t) * f) with hF
  set G : ℕ → M := fun t => res A b (res A a w (T t * f)) (T (-1 - t) * g) with hG
  set y : ℕ → M := fun t => res A a w (T t * f) with hy
  set Rb : M → M := fun x => res A b x ((1 + z) ^ Q * T (-1)) with hRb
  have hL : (∑ᶠ j : ℤ, jacL A a b w (-1) f g j) = ∑ t ∈ Finset.range (J + 1), (F t + G t) := by
    rw [FusionTop.finsum_int_eq_range _ J (fun i hi => by
      rcases hi with hi | hi
      · exact jacL_neg_one_neg A a b w (-1) f g hi
      · obtain ⟨t, rfl⟩ : ∃ t : ℕ, i = t := ⟨i.toNat, by omega⟩
        rw [jacL_neg_one_nat, hJ₁ t (by omega), hJ₂ t (by omega), res_zero_w, res_zero_w,
          add_zero])]
    exact Finset.sum_congr rfl fun t _ => jacL_neg_one_nat A a b w f g t
  -- the three parts
  have part1 : (∑ t ∈ Finset.range (J + 1), F t) - F 0 ∈ fzO A := by
    rw [Finset.sum_range_succ', add_sub_cancel_right]
    refine Submodule.sum_mem _ fun t _ => res_mem_of_good A ha _ ?_
    simpa using left_tail_mem A (p := P + 1) (t + 1) (by omega) 1
  have part2 : (∑ t ∈ Finset.range (J + 1), G t)
      - ∑ t ∈ Finset.range (J + 1), ((-1 : ℂ) ^ (t + 1)) • Rb (y t) ∈ fzO A := by
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun t _ => ?_
    have := right_tail_mem A hb (y t) t
    convert this using 2
    simp only [hG, hy, g]
    congr 1
    rw [show (-2 : ℤ) - t = (-1 - t) + -1 by ring, T_add]; ring
  have hgeom : ∑ t ∈ Finset.range (J + 1), ((-1 : ℂ) ^ (t + 1)) • Rb (y t)
      = -Rb (res A a w ((1 + z) ^ P)) := by
    have h1 : ∑ t ∈ Finset.range (J + 1), ((-1 : ℂ) ^ (t + 1)) • Rb (y t)
        = -Rb (res A a w (∑ t ∈ Finset.range (J + 1), ((-1 : ℂ) ^ t) • (T (t : ℤ) * f))) := by
      simp only [hRb, hy, map_sum, map_smul, res_sum_w, res_smul_w, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [pow_succ, mul_neg_one, neg_smul]
    rw [h1, alt_geom, map_sub, map_smul, hJ₃ _ (by omega), smul_zero, sub_zero]
  have part3 : F 0 - Rb (res A a w ((1 + z) ^ P)) - Rb (fzRight A (P + 1) a w) ∈ fzO A := by
    have hc := commute_mem A ha hb w
    have hLR := fzLeft_sub_fzRight_eq_res A (p := P + 1) (by omega) a w
    rw [Nat.add_sub_cancel] at hLR
    rw [fzRight_eq_res A (show 1 ≤ Q + 1 by omega) b (fzLeft A (P + 1) a w),
      fzRight_eq_res A (show 1 ≤ Q + 1 by omega), Nat.add_sub_cancel] at hc
    have hF0 : F 0 = fzLeft A (P + 1) a (res A b w ((1 + z) ^ Q * T (-1))) := by
      simp only [hF, fzLeft_eq_res, Nat.cast_zero, T_zero, one_mul, sub_zero, g, f]
      congr 1; ring
    have hsplit : Rb (res A a w ((1 + z) ^ P)) + Rb (fzRight A (P + 1) a w)
        = res A b (fzLeft A (P + 1) a w) ((1 + z) ^ Q * T (-1)) := by
      simp only [hRb]
      rw [← res_add_w, ← hLR, sub_add_cancel]
    rw [sub_sub, hsplit, hF0]
    exact hc
  rw [← hR, ← hj, hL, Finset.sum_add_distrib, show fzRight A (Q + 1) b (fzRight A (P + 1) a w)
      = Rb (fzRight A (P + 1) a w) by
    simp only [hRb]; rw [fzRight_eq_res A (show 1 ≤ Q + 1 by omega), Nat.add_sub_cancel]]
  have key : (∑ t ∈ Finset.range (J + 1), F t) + (∑ t ∈ Finset.range (J + 1), G t)
      - Rb (fzRight A (P + 1) a w)
      = ((∑ t ∈ Finset.range (J + 1), F t) - F 0)
        + ((∑ t ∈ Finset.range (J + 1), G t)
          - ∑ t ∈ Finset.range (J + 1), ((-1 : ℂ) ^ (t + 1)) • Rb (y t))
        + (F 0 - Rb (res A a w ((1 + z) ^ P)) - Rb (fzRight A (P + 1) a w)) := by
    rw [hgeom]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ part1 part2) part3

/-- The translation generators on the right: `y ∗ (L₋₁u + L₀u) = Res z⁻²(1+z)^p Y(u,z) y`
(`wt u = p ≥ 1`). -/
theorem fzRight_L_eq_fzRes (P : ℕ) (u : V) (y : M) :
    fzRight A (P + 2) (W.L (-1) u) y + ((P + 1 : ℕ) : ℂ) • fzRight A (P + 1) u y
      = fzRes A (P + 1) 0 u y := by
  rw [fzRight_eq_res A (by omega), fzRight_eq_res A (by omega), fzRes_eq_res, res_L_neg_one,
    show P + 2 - 1 = P + 1 by omega, Nat.add_sub_cancel, dd_one_mul, dd_one_pow, dd_one_T,
    ← map_smul, ← map_neg, ← map_add]
  congr 1
  rw [smul_eq_C_mul, Nat.cast_zero, Nat.add_zero, show (-2 : ℤ) - 0 = -2 by norm_num,
    show (-1 : ℤ) - 1 = -2 by norm_num, ← z_mul_T_neg_two]
  simp only [map_add, map_one, map_natCast, map_intCast]
  push_cast
  ring

end Right

/-! ## Assembly: the seven raw Zhu bimodule laws -/

section Assembly

open VOA.Huang.LiFusion

variable {M₀ : Type u} [AddCommGroup M₀] [Module ℂ M₀] (A : OrdVModule W M₀)

theorem eq_zero_of_neg_grading {k : ℤ} (hk : k < 0) {a : V} (ha : a ∈ W.grading k) : a = 0 := by
  rwa [W.positivity k hk, Submodule.mem_bot] at ha

theorem exists_smul_vacuum {a : V} (ha : a ∈ W.grading 0) : ∃ c : ℂ, a = c • W.vacuum := by
  rw [W.vacuum_grade, Submodule.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  exact ⟨c, rfl⟩

theorem rawLeft_smul_vacuum (c : ℂ) (y : M₀) : rawLeft A (c • W.vacuum) y = c • y := by
  rw [map_smul, LinearMap.smul_apply, rawLeft_vacuum]

theorem rawRight_smul_vacuum (c : ℂ) (y : M₀) : rawRight A (c • W.vacuum) y = c • y := by
  rw [map_smul, LinearMap.smul_apply, rawRight_vacuum]

/-- Natural-number form of a nonnegative weight. -/
theorem exists_nat_of_nonneg {k : ℤ} (hk : 0 ≤ k) : ∃ p : ℕ, k = p := ⟨k.toNat, by omega⟩

/-- A linear operator maps `O(M)` into itself as soon as it maps the residue generators in. -/
theorem preserves_fzO (L : Module.End ℂ M₀)
    (h : ∀ (q k : ℕ) (b : V), b ∈ W.grading (q : ℤ) → ∀ m,
      L (fzRes A.toWeakModule q k b m) ∈ fzO A.toWeakModule) :
    ∀ w ∈ fzO A.toWeakModule, L w ∈ fzO A.toWeakModule := by
  intro w hw
  have hle : fzO A.toWeakModule ≤ (fzO A.toWeakModule).comap L :=
    Submodule.span_le.mpr (by rintro x ⟨q, k, b, hb, m, rfl⟩; exact h q k b hb m)
  exact hle hw

theorem rawLeft_stable (a : V) : ∀ w ∈ fzO A.toWeakModule,
    rawLeft A a w ∈ fzO A.toWeakModule := by
  refine ordinaryGrading_induction W (P := fun a => ∀ w ∈ fzO A.toWeakModule,
    rawLeft A a w ∈ fzO A.toWeakModule) ?_ ?_ ?_ a
  · intro k a ha
    rcases lt_or_ge k 0 with hk | hk
    · rw [eq_zero_of_neg_grading hk ha]; intro w _; simp
    obtain ⟨p, rfl⟩ := exists_nat_of_nonneg hk
    refine preserves_fzO A _ fun q k b hb m => ?_
    rw [rawLeft_homogeneous ha]
    exact fzLeft_fzRes_mem A.toWeakModule ha hb k m
  · intro w _; simp
  · intro a b ha hb w hw
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ (ha w hw) (hb w hw)

theorem rawLeft_sub_rawRight_stable (a : V) : ∀ w ∈ fzO A.toWeakModule,
    (rawLeft A a - rawRight A a) w ∈ fzO A.toWeakModule := by
  refine ordinaryGrading_induction W (P := fun a => ∀ w ∈ fzO A.toWeakModule,
    (rawLeft A a - rawRight A a) w ∈ fzO A.toWeakModule) ?_ ?_ ?_ a
  · intro k a ha
    rcases lt_or_ge k 0 with hk | hk
    · rw [eq_zero_of_neg_grading hk ha]; intro w _; simp
    obtain ⟨p, rfl⟩ := exists_nat_of_nonneg hk
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · obtain ⟨c, rfl⟩ := exists_smul_vacuum (by simpa using ha)
      intro w _
      rw [LinearMap.sub_apply, rawLeft_smul_vacuum, rawRight_smul_vacuum, sub_self]
      exact Submodule.zero_mem _
    obtain ⟨P, rfl⟩ : ∃ P, p = P + 1 := ⟨p - 1, by omega⟩
    refine preserves_fzO A _ fun q k b hb m => ?_
    rw [LinearMap.sub_apply, rawLeft_homogeneous ha, rawRight_homogeneous ha,
      fzLeft_sub_fzRight_eq_res _ (by omega), Nat.add_sub_cancel]
    exact resD_fzRes_mem A.toWeakModule ha hb k m
  · intro w _; simp
  · intro a b ha hb w hw
    rw [map_add, map_add, add_sub_add_comm, LinearMap.add_apply]
    exact Submodule.add_mem _ (ha w hw) (hb w hw)

theorem rawRight_stable (a : V) (w : M₀) (hw : w ∈ fzO A.toWeakModule) :
    rawRight A a w ∈ fzO A.toWeakModule := by
  have h1 := rawLeft_stable A a w hw
  have h2 := rawLeft_sub_rawRight_stable A a w hw
  rw [LinearMap.sub_apply] at h2
  simpa using Submodule.sub_mem _ h1 h2

/-- Homogeneous expansion of the Zhu product inside `rawLeft`. -/
theorem rawLeft_zhuMul_homogeneous {p q : ℕ} {a b : V} (ha : a ∈ W.grading (p : ℤ))
    (hb : b ∈ W.grading (q : ℤ)) (w : M₀) :
    rawLeft A (zhuMul W a b) w = ∑ t ∈ Finset.range (p + 1), cbz (p : ℤ) (t : ℤ) •
      fzLeft A.toWeakModule (p + q - t) (W.smul a ((t : ℤ) - 1) b) w := by
  rw [zhuMul_homogeneous' W ha, map_sum, LinearMap.coe_sum, Finset.sum_apply,
    show (p : ℤ).toNat = p by simp]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [map_smul, LinearMap.smul_apply, rawLeft_homogeneous]
  have := W.smul_mem_grading ha hb ((t : ℤ) - 1)
  convert this using 2
  push_cast [Nat.cast_sub (show t ≤ p + q by omega)]; ring

theorem rawRight_zhuMul_homogeneous {P Q : ℕ} {a b : V} (ha : a ∈ W.grading ((P + 1 : ℕ) : ℤ))
    (hb : b ∈ W.grading ((Q + 1 : ℕ) : ℤ)) (w : M₀) :
    rawRight A (zhuMul W a b) w = ∑ t ∈ Finset.range (P + 2), cbz ((P + 1 : ℕ) : ℤ) (t : ℤ) •
      fzRight A.toWeakModule (P + 1 + (Q + 1) - t) (W.smul a ((t : ℤ) - 1) b) w := by
  rw [zhuMul_homogeneous' W ha, map_sum, LinearMap.coe_sum, Finset.sum_apply,
    show (((P + 1 : ℕ) : ℤ)).toNat = P + 1 by simp]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [map_smul, LinearMap.smul_apply, rawRight_homogeneous]
  have := W.smul_mem_grading ha hb ((t : ℤ) - 1)
  convert this using 2
  push_cast [Nat.cast_sub (show t ≤ P + 1 + (Q + 1) by omega)]; ring

theorem rawLeft_mul (a b : V) (w : M₀) :
    rawLeft A (zhuMul W a b) w - rawLeft A a (rawLeft A b w) ∈ fzO A.toWeakModule := by
  refine ordinaryGrading_induction W (P := fun a => ∀ b w, rawLeft A (zhuMul W a b) w
    - rawLeft A a (rawLeft A b w) ∈ fzO A.toWeakModule) ?_ ?_ ?_ a b w
  · intro k a ha b
    refine ordinaryGrading_induction W (P := fun b => ∀ w, rawLeft A (zhuMul W a b) w
      - rawLeft A a (rawLeft A b w) ∈ fzO A.toWeakModule) ?_ ?_ ?_ b
    · intro l b hb w
      rcases lt_or_ge k 0 with hk | hk
      · rw [eq_zero_of_neg_grading hk ha]; simp
      rcases lt_or_ge l 0 with hl | hl
      · rw [eq_zero_of_neg_grading hl hb]; simp
      obtain ⟨p, rfl⟩ := exists_nat_of_nonneg hk
      obtain ⟨q, rfl⟩ := exists_nat_of_nonneg hl
      rw [rawLeft_zhuMul_homogeneous A ha hb, rawLeft_homogeneous ha, rawLeft_homogeneous hb]
      exact left_mul_mem A.toWeakModule ha hb w
    · intro w; simp
    · intro b b' hb hb' w
      rw [zhuMul_add_right, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add,
        add_sub_add_comm]
      exact Submodule.add_mem _ (hb w) (hb' w)
  · intro b w; simp
  · intro a a' ha ha' b w
    rw [zhuMul_add_left, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      add_sub_add_comm]
    exact Submodule.add_mem _ (ha b w) (ha' b w)

theorem rawCommute (a b : V) (w : M₀) :
    rawLeft A a (rawRight A b w) - rawRight A b (rawLeft A a w) ∈ fzO A.toWeakModule := by
  refine ordinaryGrading_induction W (P := fun b => ∀ a w, rawLeft A a (rawRight A b w)
    - rawRight A b (rawLeft A a w) ∈ fzO A.toWeakModule) ?_ ?_ ?_ b a w
  · intro l b hb a
    refine ordinaryGrading_induction W (P := fun a => ∀ w, rawLeft A a (rawRight A b w)
      - rawRight A b (rawLeft A a w) ∈ fzO A.toWeakModule) ?_ ?_ ?_ a
    · intro k a ha w
      rcases lt_or_ge k 0 with hk | hk
      · rw [eq_zero_of_neg_grading hk ha]; simp
      rcases lt_or_ge l 0 with hl | hl
      · rw [eq_zero_of_neg_grading hl hb]; simp
      obtain ⟨p, rfl⟩ := exists_nat_of_nonneg hk
      obtain ⟨q, rfl⟩ := exists_nat_of_nonneg hl
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · obtain ⟨d, rfl⟩ := exists_smul_vacuum (by simpa using hb)
        rw [rawRight_smul_vacuum, rawRight_smul_vacuum, map_smul, sub_self]
        exact Submodule.zero_mem _
      obtain ⟨Q, rfl⟩ : ∃ Q, q = Q + 1 := ⟨q - 1, by omega⟩
      rw [rawLeft_homogeneous ha, rawLeft_homogeneous ha, rawRight_homogeneous hb,
        rawRight_homogeneous hb]
      exact commute_mem A.toWeakModule ha hb w
    · intro w; simp
    · intro a a' ha ha' w
      rw [map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, add_sub_add_comm]
      exact Submodule.add_mem _ (ha w) (ha' w)
  · intro a w; simp
  · intro b b' hb hb' a w
    rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, add_sub_add_comm]
    exact Submodule.add_mem _ (hb a w) (hb' a w)

theorem rawRight_mul (a b : V) (w : M₀) :
    rawRight A (zhuMul W a b) w - rawRight A b (rawRight A a w) ∈ fzO A.toWeakModule := by
  refine ordinaryGrading_induction W (P := fun a => ∀ b w, rawRight A (zhuMul W a b) w
    - rawRight A b (rawRight A a w) ∈ fzO A.toWeakModule) ?_ ?_ ?_ a b w
  · intro k a ha b
    refine ordinaryGrading_induction W (P := fun b => ∀ w, rawRight A (zhuMul W a b) w
      - rawRight A b (rawRight A a w) ∈ fzO A.toWeakModule) ?_ ?_ ?_ b
    · intro l b hb w
      rcases lt_or_ge k 0 with hk | hk
      · rw [eq_zero_of_neg_grading hk ha]; simp
      rcases lt_or_ge l 0 with hl | hl
      · rw [eq_zero_of_neg_grading hl hb]; simp
      obtain ⟨p, rfl⟩ := exists_nat_of_nonneg hk
      obtain ⟨q, rfl⟩ := exists_nat_of_nonneg hl
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · obtain ⟨c, rfl⟩ := exists_smul_vacuum (by simpa using ha)
        rw [zhuMul_smul_left, zhuMul_vacuum_left, rawRight_smul_vacuum, map_smul,
          LinearMap.smul_apply, map_smul, sub_self]
        exact Submodule.zero_mem _
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · obtain ⟨d, rfl⟩ := exists_smul_vacuum (by simpa using hb)
        rw [zhuMul_smul_right, zhuMul_vacuum_right, rawRight_smul_vacuum, map_smul,
          LinearMap.smul_apply, sub_self]
        exact Submodule.zero_mem _
      obtain ⟨P, rfl⟩ : ∃ P, p = P + 1 := ⟨p - 1, by omega⟩
      obtain ⟨Q, rfl⟩ : ∃ Q, q = Q + 1 := ⟨q - 1, by omega⟩
      rw [rawRight_zhuMul_homogeneous A ha hb, rawRight_homogeneous ha, rawRight_homogeneous hb]
      exact right_mul_mem A.toWeakModule ha hb w
    · intro w; simp
    · intro b b' hb hb' w
      have := Submodule.add_mem _ (hb w) (hb' w)
      convert this using 1
      simp only [zhuMul_add_right, map_add, LinearMap.add_apply]; abel
  · intro b w; simp
  · intro a a' ha ha' b w
    have := Submodule.add_mem _ (ha b w) (ha' b w)
    convert this using 1
    simp only [zhuMul_add_left, map_add, LinearMap.add_apply]; abel

theorem rawLeft_translation (u : V) (y : M₀) :
    rawLeft A (W.L (-1) u + W.L 0 u) y ∈ fzO A.toWeakModule := by
  refine ordinaryGrading_induction W (P := fun u => ∀ y,
    rawLeft A (W.L (-1) u + W.L 0 u) y ∈ fzO A.toWeakModule) ?_ ?_ ?_ u y
  · intro k u hu y
    rcases lt_or_ge k 0 with hk | hk
    · rw [eq_zero_of_neg_grading hk hu]; simp
    obtain ⟨p, rfl⟩ := exists_nat_of_nonneg hk
    have hL1 : W.L (-1) u ∈ W.grading ((p + 1 : ℕ) : ℤ) := by
      have := L_neg_one_mem_grading_succ W hu; push_cast; exact this
    rw [VertexOperatorAlgebra.L_zero_grading W u hu, map_add, LinearMap.add_apply,
      rawLeft_homogeneous hL1, map_smul, LinearMap.smul_apply, rawLeft_homogeneous hu,
      show (((p : ℤ) : ℂ)) = (p : ℂ) by simp, fzLeft_L_eq_fzRes]
    exact fzRes_mem_fzO _ 0 hu y
  · intro y; simp
  · intro u u' hu hu' y
    have := Submodule.add_mem _ (hu y) (hu' y)
    convert this using 1
    simp only [map_add, LinearMap.add_apply]; abel

theorem rawRight_translation (u : V) (y : M₀) :
    rawRight A (W.L (-1) u + W.L 0 u) y ∈ fzO A.toWeakModule := by
  refine ordinaryGrading_induction W (P := fun u => ∀ y,
    rawRight A (W.L (-1) u + W.L 0 u) y ∈ fzO A.toWeakModule) ?_ ?_ ?_ u y
  · intro k u hu y
    rcases lt_or_ge k 0 with hk | hk
    · rw [eq_zero_of_neg_grading hk hu]; simp
    obtain ⟨p, rfl⟩ := exists_nat_of_nonneg hk
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · obtain ⟨c, rfl⟩ := exists_smul_vacuum (by simpa using hu)
      rw [map_smul, map_smul, VertexOperatorAlgebra.L_neg_one_vacuum,
        VertexOperatorAlgebra.L_zero_grading W W.vacuum W.vacuum_mem_grading_zero]
      simp
    obtain ⟨P, rfl⟩ : ∃ P, p = P + 1 := ⟨p - 1, by omega⟩
    have hL1 : W.L (-1) u ∈ W.grading ((P + 2 : ℕ) : ℤ) := by
      have := L_neg_one_mem_grading_succ W hu; push_cast at this ⊢
      rwa [show (P : ℤ) + 2 = P + 1 + 1 by ring]
    rw [VertexOperatorAlgebra.L_zero_grading W u hu, map_add, LinearMap.add_apply,
      rawRight_homogeneous hL1, map_smul, LinearMap.smul_apply, rawRight_homogeneous hu,
      show (((((P + 1 : ℕ)) : ℤ) : ℂ)) = (((P + 1 : ℕ)) : ℂ) by simp, fzRight_L_eq_fzRes]
    exact fzRes_mem_fzO _ 0 hu y
  · intro y; simp
  · intro u u' hu hu' y
    have := Submodule.add_mem _ (hu y) (hu' y)
    convert this using 1
    simp only [map_add, LinearMap.add_apply]; abel

theorem rawLeft_O (a : V) (ha : a ∈ O W) (w : M₀) : rawLeft A a w ∈ fzO A.toWeakModule := by
  induction ha using Submodule.span_induction generalizing w with
  | mem x hx =>
    obtain ⟨u, v, rfl⟩ := hx
    have h1 := rawLeft_mul A (W.L (-1) u + W.L 0 u) v w
    have h2 := rawLeft_translation A u (rawLeft A v w)
    simpa using Submodule.add_mem _ h1 h2
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ (hx w) (hy w)
  | smul c x _ hx =>
    rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ c (hx w)

theorem rawRight_O (a : V) (ha : a ∈ O W) (w : M₀) : rawRight A a w ∈ fzO A.toWeakModule := by
  induction ha using Submodule.span_induction generalizing w with
  | mem x hx =>
    obtain ⟨u, v, rfl⟩ := hx
    have h1 := rawRight_mul A (W.L (-1) u + W.L 0 u) v w
    have h2 := rawRight_stable A v _ (rawRight_translation A u w)
    simpa using Submodule.add_mem _ h1 h2
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ (hx w) (hy w)
  | smul c x _ hx =>
    rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ c (hx w)

/-- **The Frenkel–Zhu bimodule theorem** (Frenkel–Zhu 1992, Thm 1.5.1), in the
form of the seven raw identities of `LiFusion.RawZhuBimoduleLaws`, for **every** ordinary
module. Unconditional. -/
theorem rawZhuBimoduleLaws : RawZhuBimoduleLaws A where
  left_stable a w hw := rawLeft_stable A a w hw
  right_stable a w hw := rawRight_stable A a w hw
  left_O a ha w := rawLeft_O A a ha w
  right_O a ha w := rawRight_O A a ha w
  left_mul a b w := rawLeft_mul A a b w
  right_mul a b w := rawRight_mul A a b w
  commute a b w := rawCommute A a b w

end Assembly

end VOA.Huang.LiConverse
