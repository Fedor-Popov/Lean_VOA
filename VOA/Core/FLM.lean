import VOA.Core.Skew
import VOA.Foundations.IotaZExpansion

/-!
# The FLM weak-associativity identity `flm` (all `a`)  (FLM §8.8–8.10)

The boundary residual `FLMBoundaryResidual`, proved without hypotheses, hence the full `flm`
(all `a`).

This self-contained file develops the finite-difference / substitution calculus of
the singular regime `a < N` and the normal-regime reduction
(`a ≥ N`, modulo `FLMBoundaryResidual`), then proves `FLMBoundaryResidual`
and assembles the full FLM weak-associativity identity `flm` for all `a`.

## The boundary residual, proved.
`FLMBoundaryResidual` says `subst2 ((z₁-z₂)ᴺ·Yprod) a b = subst2 ((z₁-z₂)ᴺ·Zhyb(a-N)) a b`.
Both sides reduce (hypothesis-free `subst2_antidiag_gen` + `antidiag_mulBySubPow`) to a 1-D
substitution `subst1 (Δᴺ (antidiag ·)) a`.  The two antidiagonals differ exactly by a CUT at
threshold `s = a-N`:
  `antidiag Yprod δ − antidiag (Zhyb s) δ = cutLt s (antidiag (Yprod−Yswap) δ)`.
Write `gD = antidiag (Yprod−Yswap) δ`; the locality bridge gives `Δᴺ gD = 0`.  Then
  `subst1 (Δᴺ (cutLt s gD)) a = subst1 (Δᴺ (cutLt 0 gD)) a + subst1 (Δᴺ (cutLt s gD − cutLt 0 gD)) a`.
The first term vanishes by the unified reproducing identity (normal regime `a ≥ N`).  The second
term is `subst1 (window) (a−N)` where the finite window is supported on `0 ≤ p < s = a−N`; there
the binomial `cbz(p, a−N) = 0` (a smaller-over-larger binomial), so it vanishes termwise.

## Status
Complete & `sorry`-free / axiom-free (FLM §8.8–8.10).  The
unconditional `FLMBoundaryResidual` and the full weak-associativity identity `flm` (all `a`),
with the supporting finite-difference / `subst2` calculus, are all proved
(`#print axioms = [propext, Classical.choice, Quot.sound]`); consumed by `Core.WeakAssoc`.
-/

namespace VOA

open scoped BigOperators
open Module (End)

universe u

/-! ## §0. The combinatorial kernel (copied from f1/f2). -/

def asgn (N r : ℕ) : ℤ := (-1 : ℤ) ^ (N - r) * (N.choose r : ℤ)

theorem asgn_pascal (N r : ℕ) (hr : r ≤ N) :
    asgn (N + 1) (r + 1) = asgn N r - asgn N (r + 1) := by
  unfold asgn
  rw [Nat.choose_succ_succ' N r]
  push_cast
  rw [mul_add]
  congr 1
  rcases Nat.lt_or_ge r N with hlt | hge
  · rw [show N - r = (N - (r + 1)) + 1 by omega, pow_succ]
    ring
  · rw [show r + 1 = N + 1 by omega, Nat.choose_succ_self]
    simp

theorem mulBySubPow_apply_asgn {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲]
    (N : ℕ) (f : FormalDist₂ 𝒲) (m n : ℤ) :
    mulBySubPow N f m n
      = ∑ r ∈ Finset.range (N + 1), asgn N r • f (m - (r : ℤ)) (n - ((N - r : ℕ) : ℤ)) := by
  rw [mulBySubPow_apply_sum]
  rfl

theorem fd_step (N : ℕ) {M : Type*} [AddCommGroup M] (g : ℕ → M) :
    (∑ r ∈ Finset.range (N + 2), asgn (N + 1) r • g r)
      = (∑ r ∈ Finset.range (N + 1), asgn N r • g (r + 1))
        - (∑ r ∈ Finset.range (N + 1), asgn N r • g r) := by
  rw [Finset.sum_range_succ' (fun r => asgn (N + 1) r • g r) (N + 1)]
  have hsplit : ∀ r ∈ Finset.range (N + 1),
      asgn (N + 1) (r + 1) • g (r + 1) = asgn N r • g (r + 1) - asgn N (r + 1) • g (r + 1) := by
    intro r hr
    rw [Finset.mem_range] at hr
    rw [asgn_pascal N r (by omega), sub_smul]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  have hreindex : (∑ r ∈ Finset.range (N + 1), asgn N (r + 1) • g (r + 1))
      = (∑ s ∈ Finset.range (N + 1), asgn N s • g s) - asgn N 0 • g 0 := by
    have h2 : (∑ s ∈ Finset.range (N + 2), asgn N s • g s)
        = (∑ r ∈ Finset.range (N + 1), asgn N (r + 1) • g (r + 1)) + asgn N 0 • g 0 :=
      Finset.sum_range_succ' (fun r => asgn N r • g r) (N + 1)
    have h3 : (∑ s ∈ Finset.range (N + 2), asgn N s • g s)
        = (∑ s ∈ Finset.range (N + 1), asgn N s • g s) + asgn N (N + 1) • g (N + 1) :=
      Finset.sum_range_succ (fun s => asgn N s • g s) (N + 1)
    have h4 : asgn N (N + 1) = 0 := by
      unfold asgn; rw [Nat.choose_succ_self]; simp
    rw [h4, zero_smul, add_zero] at h3
    rw [h3] at h2
    rw [h2]; abel
  rw [hreindex]
  have hsign : asgn (N + 1) 0 • g 0 + asgn N 0 • g 0 = (0 : M) := by
    rw [asgn, asgn, Nat.sub_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.choose_zero_right]
    push_cast
    rw [← add_smul]
    rw [show ((-1:ℤ)^(N+1) * 1 + (-1:ℤ)^N * 1) = 0 by rw [pow_succ]; ring, zero_smul]
  have hZ : asgn (N + 1) 0 • g 0 = - (asgn N 0 • g 0) := by
    rw [eq_neg_iff_add_eq_zero]; exact hsign
  rw [hZ]
  abel

theorem cbz_fd (N : ℕ) (j a : ℤ) :
    (∑ r ∈ Finset.range (N + 1), asgn N r • cbz (j + r) a) = cbz j (a - N) := by
  induction N generalizing j with
  | zero =>
      rw [Finset.sum_range_one]
      simp [asgn]
  | succ k ih =>
      rw [fd_step k (fun r => cbz (j + r) a)]
      have hshift : (∑ r ∈ Finset.range (k + 1), asgn k r • cbz (j + ((r : ℕ) + 1 : ℕ)) a)
          = (∑ r ∈ Finset.range (k + 1), asgn k r • cbz ((j + 1) + r) a) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [show ((((r : ℕ) + 1 : ℕ)) : ℤ) = (r : ℤ) + 1 by push_cast; ring,
          show j + ((r : ℤ) + 1) = (j + 1) + (r : ℤ) by ring]
      rw [hshift, ih (j + 1), ih j]
      have hp := cbz_pascal (j + 1) (a - (k : ℤ))
      rw [show (j + 1) - 1 = j by ring] at hp
      rw [hp]
      rw [show a - (k : ℤ) - 1 = a - ((k : ℤ) + 1) by ring]
      rw [show a - ((k : ℕ) + 1 : ℕ) = a - ((k : ℤ) + 1) by push_cast; ring]
      ring

/-! ## §1. `cbz` smaller-over-larger vanishing. -/

/-- A generalized binomial of a small nonnegative top over a strictly larger bottom vanishes:
`gBinom p k = 0` whenever `0 ≤ p < k` (the factor `(p − p) = 0` sits in the product). -/
theorem gBinom_lt {p : ℤ} (hp : 0 ≤ p) {k : ℕ} (hk : p < (k : ℤ)) : gBinom p k = 0 := by
  rw [gBinom]
  rw [Finset.prod_eq_zero (i := p.toNat) (Finset.mem_range.mpr (by omega)) (by
        have : ((p.toNat : ℤ) : ℂ) = (p : ℂ) := by rw [Int.toNat_of_nonneg hp]
        push_cast at this ⊢
        rw [this, sub_self]), zero_div]

/-- `cbz p c = 0` for `0 ≤ p < c` (smaller top, larger bottom). -/
theorem cbz_lt {p c : ℤ} (hp : 0 ≤ p) (hpc : p < c) : cbz p c = 0 := by
  rw [cbz_apply_nonneg p (by omega)]
  exact gBinom_lt hp (by omega)

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §2. Copied `a < 0` / column forms (from f1/f2). -/

theorem subst2_neg_a (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (N : ℕ)
    {a : ℤ} (ha : a < 0) (b : ℤ) :
    subst2 (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) a b = 0 := by
  rw [subst2_apply]
  rw [finsum_congr (g := fun _ : ℤ => (0 : 𝒱)) fun k => by
      rw [cbz_apply_neg _ (show a < 0 from ha), zero_smul]]
  exact finsum_zero

theorem smul_eq_zero_of_locality (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱)
    {N : ℕ} (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0)
    {n : ℕ} (hn : N ≤ n) : W.smul u (n : ℤ) v = 0 := by
  have hY : W.Y (W.smul u (n : ℤ) v) = 0 := by
    rw [← nth_product]
    ext m
    rw [cCoeff_apply, mulBySubPow_eq_zero_mono hn hN]
    rfl
  set w := W.smul u (n : ℤ) v with hw
  have e1 : w = W.smul w (-1) W.vacuum := (W.toPreVertexAlgebra.smul_vacuum_neg_one w).symm
  have e2 : W.smul w (-1) W.vacuum = (W.Y w) 0 W.vacuum := by
    rw [PreVertexAlgebra.smul_def, mode_apply, show (-(-1)-1 : ℤ) = 0 by ring]
  rw [e1, e2, hY]
  rfl

theorem comp_eq_zero_of_locality (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱)
    {N : ℕ} (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0)
    {a : ℤ} (ha : a ≤ -(N : ℤ) - 1) (b : ℤ) :
    comp W u v x a b = 0 := by
  rw [comp_apply']
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -a - 1 = (n : ℤ) := ⟨(-a - 1).toNat, by omega⟩
  rw [show W.smul u (-a - 1) v = W.smul u (n : ℤ) v from by rw [hn]]
  rw [smul_eq_zero_of_locality W u v hN (n := n) (by omega), map_zero]; rfl

theorem comp_singular_form (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {N : ℕ}
    {a : ℤ} (haN : a ≤ (N : ℤ) - 1) (b : ℤ) :
    comp W u v x (a - N) b
      = mulBySubPow (N - 1 - a).toNat
          (W.toPreVertexAlgebra.Yprod u v x - Yswap W u v x) (-1) b := by
  rw [comp_nonneg_col W u v x (show a - N ≤ -1 by omega) b]
  have hidx : (-(a - (N:ℤ)) - 1).toNat = (N - 1 - a).toNat := by
    congr 1; omega
  rw [hidx]
  rw [show mulBySubPow (N - 1 - a).toNat (bracketDist (W.Y u) (W.Y v)) (-1) b x
        = applyVec x (mulBySubPow (N - 1 - a).toNat (bracketDist (W.Y u) (W.Y v))) (-1) b from rfl,
    applyVec_mulBySubPow, applyVec_bracketDist_Y]

theorem comp_normal_form (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {N : ℕ}
    {a : ℤ} (haN : (N : ℤ) ≤ a) (b : ℤ) :
    comp W u v x (a - N) b
      = negProd (W.isField_Y u) (W.isField_Y v) (a - N).toNat b x :=
  comp_neg_col W u v x (show 0 ≤ a - N by omega) b

theorem flm_neg_a (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {N : ℕ}
    (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0)
    {a : ℤ} (ha : a < 0) (b : ℤ) :
    subst2 (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) a b = comp W u v x (a - N) b := by
  rw [subst2_neg_a W u v x N ha b,
    (comp_eq_zero_of_locality W u v x hN (show a - N ≤ -(N:ℤ) - 1 by omega) b).symm]

/-! ## §3. The hypothesis-free `subst2 → 1-D antidiagonal finsum` reduction. -/

/-- The general antidiagonal reduction: for ANY `F`, the `subst2` of `(z₁-z₂)ᴺ·F` at `(a,b)`
is the 1-D finsum `∑ᶠ_m cbz(m,a)·((z₁-z₂)ᴺ·F)(m, a+b-m)` (no hypotheses). -/
theorem subst2_antidiag_gen (F : FormalDist₂ 𝒱) (N : ℕ) (a b : ℤ) :
    subst2 (mulBySubPow N F) a b
      = ∑ᶠ m : ℤ, cbz m a • mulBySubPow N F m (a + b - m) := by
  rw [subst2_apply]
  rw [← finsum_comp_equiv (Equiv.subRight a)]
  refine finsum_congr fun m => ?_
  simp only [Equiv.subRight_apply]
  rw [show a + (m - a) = m by ring, show b - (m - a) = a + b - m by ring]

end VertexOperatorAlgebra

/-! ## §4. The 1-D difference operator `dPow` and its `asgn` expansion (copied from f1). -/

variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲]

def fdiff1 (g : ℤ → 𝒲) : ℤ → 𝒲 := fun m => g (m - 1) - g m

def dPow : ℕ → (ℤ → 𝒲) → (ℤ → 𝒲)
  | 0, g => g
  | (N + 1), g => fdiff1 (dPow N g)

@[simp] theorem dPow_zero (g : ℤ → 𝒲) : dPow 0 g = g := rfl

theorem dPow_succ (N : ℕ) (g : ℤ → 𝒲) : dPow (N + 1) g = fdiff1 (dPow N g) := rfl

theorem dPow_succ' (N : ℕ) (g : ℤ → 𝒲) : dPow (N + 1) g = dPow N (fdiff1 g) := by
  induction N generalizing g with
  | zero => rfl
  | succ k ih => rw [dPow_succ, ih g, dPow_succ]

theorem fdiff1_add (g h : ℤ → 𝒲) : fdiff1 (g + h) = fdiff1 g + fdiff1 h := by
  funext m; simp only [fdiff1, Pi.add_apply]; abel

theorem fdiff1_sub (g h : ℤ → 𝒲) : fdiff1 (g - h) = fdiff1 g - fdiff1 h := by
  funext m; simp only [fdiff1, Pi.sub_apply]; abel

theorem dPow_add (N : ℕ) (g h : ℤ → 𝒲) : dPow N (g + h) = dPow N g + dPow N h := by
  induction N with
  | zero => rfl
  | succ k ih => rw [dPow_succ, dPow_succ, dPow_succ, ih, fdiff1_add]

theorem dPow_sub (N : ℕ) (g h : ℤ → 𝒲) : dPow N (g - h) = dPow N g - dPow N h := by
  induction N with
  | zero => rfl
  | succ k ih => rw [dPow_succ, dPow_succ, dPow_succ, ih, fdiff1_sub]

theorem dPow_apply_asgn (N : ℕ) (g : ℤ → 𝒲) (m : ℤ) :
    dPow N g m = ∑ r ∈ Finset.range (N + 1), asgn N r • g (m - (r : ℤ)) := by
  induction N generalizing m with
  | zero => simp [asgn]
  | succ k ih =>
      rw [dPow_succ]
      show dPow k g (m - 1) - dPow k g m = _
      rw [ih (m - 1), ih m]
      rw [fd_step k (fun r : ℕ => g (m - (r : ℤ)))]
      congr 1
      refine Finset.sum_congr rfl (fun r _ => ?_)
      congr 2
      push_cast; ring

def antidiag (F : FormalDist₂ 𝒲) (δ : ℤ) : ℤ → 𝒲 := fun p => F p (δ - p)

@[simp] theorem antidiag_apply (F : FormalDist₂ 𝒲) (δ p : ℤ) :
    antidiag F δ p = F p (δ - p) := rfl

theorem antidiag_mulBySubPow (N : ℕ) (F : FormalDist₂ 𝒲) (δ : ℤ) :
    antidiag (mulBySubPow N F) δ = dPow N (antidiag F (δ - N)) := by
  funext m
  rw [antidiag_apply, mulBySubPow_apply_asgn, dPow_apply_asgn]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [antidiag_apply]
  congr 2
  rw [Finset.mem_range] at hr
  push_cast [Nat.cast_sub (by omega : r ≤ N)]
  ring

/-! ## §5. The 1-D substitution `subst1` and its finite-support keystone (copied from f1). -/

noncomputable def subst1 (g : ℤ → 𝒲) (c : ℤ) : 𝒲 := ∑ᶠ m : ℤ, cbz m c • g m

theorem subst1_apply (g : ℤ → 𝒲) (c : ℤ) : subst1 g c = ∑ᶠ m : ℤ, cbz m c • g m := rfl

theorem subst1_summand_finite {g : ℤ → 𝒲} (hg : (Function.support g).Finite) (c : ℤ) :
    (Function.support (fun m : ℤ => cbz m c • g m)).Finite := by
  refine hg.subset (fun m hm => ?_)
  rw [Function.mem_support] at hm ⊢
  exact fun h => hm (by rw [h, smul_zero])

theorem subst1_add {g h : ℤ → 𝒲} (hg : (Function.support g).Finite)
    (hh : (Function.support h).Finite) (c : ℤ) :
    subst1 (g + h) c = subst1 g c + subst1 h c := by
  rw [subst1_apply, subst1_apply, subst1_apply,
    ← finsum_add_distrib (subst1_summand_finite hg c) (subst1_summand_finite hh c)]
  refine finsum_congr fun m => ?_
  rw [Pi.add_apply, smul_add]

theorem subst1_sub {g h : ℤ → 𝒲} (hg : (Function.support g).Finite)
    (hh : (Function.support h).Finite) (c : ℤ) :
    subst1 (g - h) c = subst1 g c - subst1 h c := by
  rw [subst1_apply, subst1_apply, subst1_apply,
    ← finsum_sub_distrib (subst1_summand_finite hg c) (subst1_summand_finite hh c)]
  refine finsum_congr fun m => ?_
  rw [Pi.sub_apply, smul_sub]

theorem support_shift_finite {g : ℤ → 𝒲} (hg : (Function.support g).Finite) :
    (Function.support (fun m : ℤ => g (m - 1))).Finite := by
  apply (hg.image (· + 1)).subset
  intro m hm
  rw [Function.mem_support] at hm
  exact ⟨m - 1, hm, by ring⟩

theorem support_fdiff1_finite {g : ℤ → 𝒲} (hg : (Function.support g).Finite) :
    (Function.support (fdiff1 g)).Finite := by
  apply ((support_shift_finite hg).union hg).subset
  intro m hm
  rw [Function.mem_support] at hm
  by_contra hmem
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hmem
  exact hm (by simp only [fdiff1]; rw [hmem.1, hmem.2, sub_zero])

theorem support_dPow_finite (N : ℕ) {g : ℤ → 𝒲} (hg : (Function.support g).Finite) :
    (Function.support (dPow N g)).Finite := by
  induction N with
  | zero => simpa using hg
  | succ k ih => rw [dPow_succ]; exact support_fdiff1_finite ih

theorem subst1_fdiff1 {g : ℤ → 𝒲} (hg : (Function.support g).Finite) (c : ℤ) :
    subst1 (fdiff1 g) c = subst1 g (c - 1) := by
  rw [subst1_apply, subst1_apply]
  have hshift : (Function.support (fun m : ℤ => g (m - 1))).Finite := support_shift_finite hg
  have hsplit : (∑ᶠ m : ℤ, cbz m c • fdiff1 g m)
      = (∑ᶠ m : ℤ, cbz m c • g (m - 1)) - (∑ᶠ m : ℤ, cbz m c • g m) := by
    rw [← finsum_sub_distrib (subst1_summand_finite hshift c) (subst1_summand_finite hg c)]
    refine finsum_congr fun m => ?_
    simp only [fdiff1]; rw [smul_sub]
  rw [hsplit]
  have hre : (∑ᶠ m : ℤ, cbz m c • g (m - 1)) = ∑ᶠ m : ℤ, cbz (m + 1) c • g m := by
    rw [← finsum_int_succ_shift (fun m : ℤ => cbz m c • g (m - 1))]
    refine finsum_congr fun m => ?_
    rw [show m + 1 - 1 = m by ring]
  have hfin1 : (Function.support (fun m : ℤ => cbz (m + 1) c • g m)).Finite := by
    refine hg.subset (fun m hm => ?_)
    rw [Function.mem_support] at hm ⊢
    exact fun h => hm (by rw [h, smul_zero])
  rw [hre, ← finsum_sub_distrib hfin1 (subst1_summand_finite hg c)]
  refine finsum_congr fun m => ?_
  rw [← sub_smul]
  congr 1
  have hp := cbz_pascal (m + 1) c
  rw [show m + 1 - 1 = m by ring] at hp
  rw [hp]; abel

theorem subst1_dPow (N : ℕ) {g : ℤ → 𝒲} (hg : (Function.support g).Finite) (c : ℤ) :
    subst1 (dPow N g) c = subst1 g (c - (N : ℤ)) := by
  induction N generalizing c with
  | zero => simp
  | succ k ih =>
      rw [dPow_succ, subst1_fdiff1 (support_dPow_finite k hg), ih (c - 1)]
      congr 1; push_cast; ring

theorem subst1_neg (g : ℤ → 𝒲) {c : ℤ} (hc : c < 0) : subst1 g c = 0 := by
  rw [subst1_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  rw [cbz_apply_neg m hc, zero_smul]

theorem subst1_dPow_eq_zero (N : ℕ) {g : ℤ → 𝒲} (hg : (Function.support g).Finite)
    {c : ℤ} (hc : c < (N : ℤ)) : subst1 (dPow N g) c = 0 := by
  rw [subst1_dPow N hg, subst1_neg g (by omega)]

/-! ## §6. Indicator cuts (copied from f1). -/

def cutLt (t : ℤ) (g : ℤ → 𝒲) : ℤ → 𝒲 := fun p => if p < t then g p else 0

@[simp] theorem cutLt_apply (t : ℤ) (g : ℤ → 𝒲) (p : ℤ) :
    cutLt t g p = if p < t then g p else 0 := rfl

theorem support_cutLt_sub_finite (s t : ℤ) (g : ℤ → 𝒲) :
    (Function.support (cutLt s g - cutLt t g)).Finite := by
  apply (Set.finite_Icc (min s t) (max s t - 1)).subset
  intro p hp
  rw [Function.mem_support, Pi.sub_apply, cutLt_apply, cutLt_apply] at hp
  rw [Set.mem_Icc]
  constructor
  · by_contra hlo
    push_neg at hlo
    rw [if_pos (by omega : p < s), if_pos (by omega : p < t), sub_self] at hp
    exact hp rfl
  · by_contra hhi
    push_neg at hhi
    rw [if_neg (by omega : ¬ p < s), if_neg (by omega : ¬ p < t), sub_self] at hp
    exact hp rfl

theorem subst1_dPow_sub (N : ℕ) {f₁ f₂ : ℤ → 𝒲}
    (h1 : (Function.support (dPow N f₁)).Finite) (h2 : (Function.support (dPow N f₂)).Finite)
    (a : ℤ) :
    subst1 (dPow N f₁) a - subst1 (dPow N f₂) a = subst1 (dPow N (f₁ - f₂)) a := by
  rw [dPow_sub, subst1_sub h1 h2]

/-! ## §7. The 1-D unified reproducing identity (copied from f1). -/

def pointMass (t : ℤ) (w : 𝒲) : ℤ → 𝒲 := fun p => if p = t then w else 0

@[simp] theorem pointMass_apply (t : ℤ) (w : 𝒲) (p : ℤ) :
    pointMass t w p = if p = t then w else 0 := rfl

theorem support_pointMass_finite (t : ℤ) (w : 𝒲) :
    (Function.support (pointMass t w)).Finite := by
  apply (Set.finite_singleton t).subset
  intro p hp
  rw [Function.mem_support, pointMass_apply] at hp
  by_contra hne
  exact hp (if_neg hne)

theorem subst1_pointMass (t : ℤ) (w : 𝒲) (c : ℤ) :
    subst1 (pointMass t w) c = cbz t c • w := by
  rw [subst1_apply, finsum_eq_single _ t (fun m hm => by
        rw [pointMass_apply, if_neg hm, smul_zero])]
  rw [pointMass_apply, if_pos rfl]

-- `cbz_zero_left` (`cbz 0 c = if c = 0 then 1 else 0`) is the foundational copy from
-- `Foundations/IotaZExpansion`; reused here rather than re-proved.

theorem dPow_pointMass_zero_neg (N : ℕ) (w : 𝒲) : dPow N (pointMass 0 w) (-1) = 0 := by
  rw [dPow_apply_asgn]
  refine Finset.sum_eq_zero (fun r hr => ?_)
  rw [pointMass_apply, if_neg (by push_cast; omega), smul_zero]

theorem subst1_dPow_unified (N : ℕ) (s : ℤ → 𝒲)
    (hsupp : ∀ p : ℤ, 0 ≤ p → s p = 0)
    (hfin : (Function.support (dPow N s)).Finite)
    (hge : ∀ m : ℤ, m < 0 → dPow N s m = 0)
    {a : ℤ} (ha : 0 ≤ a) :
    subst1 (dPow N s) a = if a < (N : ℤ) then dPow (N - 1 - a).toNat s (-1) else 0 := by
  induction N generalizing s a with
  | zero =>
      have hs0 : s = 0 := by
        funext p
        rcases le_or_gt 0 p with hp | hp
        · exact hsupp p hp
        · have := hge p hp; simpa using this
      rw [hs0]
      simp only [dPow_zero, Nat.cast_zero]
      rw [subst1_apply, finsum_eq_zero_of_forall_eq_zero (fun m => by simp)]
      rw [if_neg (by omega)]
  | succ k ih =>
      set s₁ : ℤ → 𝒲 := cutLt 0 (fdiff1 s) with hs₁def
      have hfdiff1 : fdiff1 s = s₁ + pointMass 0 (s (-1)) := by
        funext p
        simp only [hs₁def, cutLt_apply, pointMass_apply, Pi.add_apply, fdiff1]
        rcases lt_trichotomy p 0 with hp | hp | hp
        · rw [if_pos hp, if_neg (by omega), add_zero]
        · subst hp
          rw [if_neg (by omega), if_pos rfl, zero_add, hsupp 0 le_rfl, sub_zero,
            show (0 : ℤ) - 1 = -1 by ring]
        · rw [if_neg (by omega), if_neg (by omega), add_zero,
            hsupp (p - 1) (by omega), hsupp p (by omega), sub_zero]
      have hs₁supp : ∀ p : ℤ, 0 ≤ p → s₁ p = 0 := by
        intro p hp
        simp only [hs₁def, cutLt_apply, if_neg (by omega : ¬ p < 0)]
      have hsplit : dPow (k + 1) s = dPow k s₁ + dPow k (pointMass 0 (s (-1))) := by
        rw [dPow_succ', hfdiff1, dPow_add]
      have hpm_fin : (Function.support (dPow k (pointMass 0 (s (-1))))).Finite :=
        support_dPow_finite k (support_pointMass_finite 0 (s (-1)))
      have hs₁fin : (Function.support (dPow k s₁)).Finite := by
        have : dPow k s₁ = dPow (k + 1) s - dPow k (pointMass 0 (s (-1))) := by
          rw [hsplit]; abel
        rw [this]
        exact (hfin.union hpm_fin).subset (fun p hp => by
          rw [Function.mem_support, Pi.sub_apply] at hp
          by_contra hmem
          simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hmem
          exact hp (by rw [hmem.1, hmem.2, sub_zero]))
      have hs₁ge : ∀ m : ℤ, m < 0 → dPow k s₁ m = 0 := by
        intro m hm
        have hpm0 : dPow k (pointMass 0 (s (-1))) m = 0 := by
          rw [dPow_apply_asgn]
          refine Finset.sum_eq_zero (fun r hr => ?_)
          rw [pointMass_apply, if_neg (by omega), smul_zero]
        have : dPow k s₁ m = dPow (k + 1) s m - dPow k (pointMass 0 (s (-1))) m := by
          rw [hsplit, Pi.add_apply, add_sub_cancel_right]
        rw [this, hge m (by omega), hpm0, sub_zero]
      rw [hsplit, subst1_add hs₁fin hpm_fin]
      have hpm : subst1 (dPow k (pointMass 0 (s (-1)))) a = cbz (0 : ℤ) (a - k) • s (-1) := by
        rw [subst1_dPow k (support_pointMass_finite 0 (s (-1))), subst1_pointMass]
      rw [hpm, ih s₁ hs₁supp hs₁fin hs₁ge ha]
      rw [Nat.cast_succ]
      rcases lt_trichotomy a (k : ℤ) with hak | hak | hak
      · rw [if_pos (by omega : a < (k : ℤ)),
          if_pos (by omega : a < ((k : ℤ) + 1)),
          cbz_zero_left, if_neg (by omega : ¬ (a - (k : ℤ)) = 0), zero_smul, add_zero]
        have htoNat : ((k : ℤ) + 1 - 1 - a).toNat = ((k : ℤ) - 1 - a).toNat + 1 := by omega
        rw [htoNat, dPow_succ', hfdiff1, dPow_add]
        show _ = (dPow ((k : ℤ) - 1 - a).toNat s₁
          + dPow ((k : ℤ) - 1 - a).toNat (pointMass 0 (s (-1)))) (-1)
        rw [Pi.add_apply, dPow_pointMass_zero_neg, add_zero]
      · subst hak
        rw [if_neg (by omega : ¬ (k : ℤ) < (k : ℤ)),
          if_pos (by omega : (k : ℤ) < ((k : ℤ) + 1)),
          cbz_zero_left, if_pos (by omega : (k : ℤ) - (k : ℤ) = 0), one_smul, zero_add]
        rw [show ((k : ℤ) + 1 - 1 - (k : ℤ)).toNat = 0 by omega, dPow_zero]
      · rw [if_neg (by omega : ¬ a < (k : ℤ)),
          if_neg (by omega : ¬ a < ((k : ℤ) + 1)),
          cbz_zero_left, if_neg (by omega : ¬ (a - (k : ℤ)) = 0), zero_smul, add_zero]

/-! ## §8. Auxiliary cut facts (copied from f1). -/

theorem dPow_cutLt_zero_neg (N : ℕ) (g : ℤ → 𝒲) :
    dPow N (cutLt 0 g) (-1) = dPow N g (-1) := by
  rw [dPow_apply_asgn, dPow_apply_asgn]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [cutLt_apply, if_pos (by omega : (-1 : ℤ) - (r : ℤ) < 0)]

theorem dPow_cutLt_zero_ge (N : ℕ) {e : ℤ → 𝒲} (he : dPow N e = 0) (m : ℤ) (hm : m < 0) :
    dPow N (cutLt 0 e) m = 0 := by
  have hsplit : e = cutLt 0 e + (fun p => if 0 ≤ p then e p else 0) := by
    funext p; simp only [cutLt_apply, Pi.add_apply]
    rcases lt_or_ge p 0 with hp | hp
    · rw [if_pos hp, if_neg (by omega), add_zero]
    · rw [if_neg (by omega), if_pos hp, zero_add]
  have : dPow N (cutLt 0 e) m = - dPow N (fun p => if 0 ≤ p then e p else 0) m := by
    have h2 : dPow N (cutLt 0 e) m
        + dPow N (fun p => if 0 ≤ p then e p else 0) m = 0 := by
      have h3 : dPow N e m = dPow N (cutLt 0 e) m
          + dPow N (fun p => if 0 ≤ p then e p else 0) m := by
        conv_lhs => rw [hsplit]
        rw [dPow_add, Pi.add_apply]
      rw [he] at h3
      simp only [Pi.zero_apply] at h3
      exact h3.symm
    rw [eq_neg_iff_add_eq_zero]; exact h2
  rw [this, dPow_apply_asgn]
  rw [show (∑ r ∈ Finset.range (N + 1), asgn N r • (fun p => if 0 ≤ p then e p else 0) (m - (r : ℤ)))
        = 0 from Finset.sum_eq_zero (fun r hr => by
      simp only []
      rw [if_neg (by omega : ¬ (0 : ℤ) ≤ m - (r : ℤ)), smul_zero]), neg_zero]

theorem support_antidiag_finite {F : FormalDist₂ 𝒲} (h1 : IsBddBelow₁ F) (h2 : IsBddBelow₂ F)
    (δ : ℤ) : (Function.support (antidiag F δ)).Finite := by
  obtain ⟨B₁, hB₁⟩ := h1
  obtain ⟨B₂, hB₂⟩ := h2
  apply (Set.finite_Icc B₁ (δ - B₂)).subset
  intro p hp
  rw [Function.mem_support, antidiag_apply] at hp
  rw [Set.mem_Icc]
  exact ⟨not_lt.mp fun h => hp (hB₁ p (δ - p) h),
         not_lt.mp fun h => hp (hB₂ p (δ - p) (by omega))⟩

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §9. The locality bridge in antidiagonal form (copied from f1). -/

theorem dPow_antidiag_bridge (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {N : ℕ}
    (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0) (δ : ℤ) :
    dPow N (antidiag (W.toPreVertexAlgebra.Yprod u v x - Yswap W u v x) (δ - N)) = 0 := by
  have hb : mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x - Yswap W u v x) = 0 := by
    rw [map_sub, sub_eq_zero, Yprod_swap_bridge W u v x hN]
  rw [← antidiag_mulBySubPow, hb]
  funext m; rw [antidiag_apply]; rfl

theorem support_gY_sub_cut_finite (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (δ : ℤ) :
    (Function.support (antidiag (W.toPreVertexAlgebra.Yprod u v x) δ
      - cutLt 0 (antidiag (W.toPreVertexAlgebra.Yprod u v x - Yswap W u v x) δ))).Finite := by
  obtain ⟨B₂, hB₂⟩ := W.toPreVertexAlgebra.Yprod_bddBelow u v x
  obtain ⟨B₁, hB₁⟩ := Yswap_bddBelow₁ W u v x
  apply (Set.finite_Icc (min 0 B₁) (max (-1) (δ - B₂))).subset
  intro p hp
  rw [Function.mem_support, Pi.sub_apply, antidiag_apply, cutLt_apply] at hp
  rw [Set.mem_Icc]
  rcases lt_or_ge p 0 with hlt | hge
  · rw [if_pos hlt, antidiag_apply] at hp
    have hval : W.toPreVertexAlgebra.Yprod u v x p (δ - p)
        - (W.toPreVertexAlgebra.Yprod u v x - Yswap W u v x) p (δ - p)
        = Yswap W u v x p (δ - p) := by
      show _ - (W.toPreVertexAlgebra.Yprod u v x p (δ - p) - Yswap W u v x p (δ - p)) = _
      abel
    rw [hval] at hp
    refine ⟨?_, by omega⟩
    by_contra hlo
    exact hp (hB₁ p (δ - p) (by omega))
  · rw [if_neg (by omega), sub_zero] at hp
    refine ⟨by omega, ?_⟩
    by_contra hhi
    exact hp (hB₂ p (δ - p) (by omega))

/-! ## §10. The SINGULAR case of `flm`, assembled (copied from f1). -/

theorem flm_singular (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {N : ℕ}
    (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0)
    {a : ℤ} (ha0 : 0 ≤ a) (haN : a < (N : ℤ)) (b : ℤ) :
    subst2 (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) a b
      = mulBySubPow (N - 1 - a).toNat
          (W.toPreVertexAlgebra.Yprod u v x - Yswap W u v x) (-1) b := by
  set Y := W.toPreVertexAlgebra.Yprod u v x with hY
  set D := W.toPreVertexAlgebra.Yprod u v x - Yswap W u v x with hD
  set e := antidiag D (a + b - N) with he
  obtain ⟨h1, h2⟩ := mulBySubPow_Yprod_doublyBdd W u v x hN
  have hgY_fin : (Function.support (dPow N (antidiag Y (a + b - N)))).Finite := by
    rw [← antidiag_mulBySubPow]
    exact support_antidiag_finite h1 h2 (a + b)
  have hbridge : dPow N e = 0 := by
    rw [he, hD]; exact dPow_antidiag_bridge W u v x hN (a + b)
  have hdiff_fin : (Function.support (antidiag Y (a + b - N) - cutLt 0 e)).Finite := by
    have hrw : antidiag Y (a + b - N) - cutLt 0 e
        = antidiag Y (a + b - N) - cutLt 0 (antidiag D (a + b - N)) := by rw [he]
    rw [hrw]; exact support_gY_sub_cut_finite W u v x (a + b - N)
  have hcut_fin : (Function.support (dPow N (cutLt 0 e))).Finite := by
    have hsub : cutLt 0 e = antidiag Y (a + b - N)
        - (antidiag Y (a + b - N) - cutLt 0 e) := by abel
    rw [hsub, dPow_sub]
    refine (hgY_fin.union (support_dPow_finite N hdiff_fin)).subset (fun p hp => ?_)
    rw [Function.mem_support, Pi.sub_apply] at hp
    by_contra hmem
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hmem
    exact hp (by rw [hmem.1, hmem.2, sub_zero])
  rw [subst2_antidiag_gen Y N a b]
  rw [show (∑ᶠ m : ℤ, cbz m a • mulBySubPow N Y m (a + b - m))
        = subst1 (dPow N (antidiag Y (a + b - N))) a from by
      rw [subst1_apply, ← antidiag_mulBySubPow]
      refine finsum_congr fun m => ?_
      rw [antidiag_apply]]
  rw [show subst1 (dPow N (antidiag Y (a + b - N))) a
        = subst1 (dPow N (cutLt 0 e)) a from by
      have hkey := subst1_dPow_sub N hgY_fin hcut_fin a
      rw [subst1_dPow_eq_zero N hdiff_fin haN] at hkey
      exact sub_eq_zero.mp hkey]
  rw [subst1_dPow_unified N (cutLt 0 e)
      (fun p hp => by rw [cutLt_apply, if_neg (by omega)])
      hcut_fin
      (fun m hm => dPow_cutLt_zero_ge N hbridge m hm) ha0]
  rw [if_pos haN]
  rw [dPow_cutLt_zero_neg]
  rw [he]
  have hindex : a + b - N = (b - 1) - ((N - 1 - a).toNat : ℤ) := by omega
  rw [hindex, ← antidiag_mulBySubPow, antidiag_apply,
    show (b - 1) - (-1 : ℤ) = b by ring]

theorem flm_singular_comp (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {N : ℕ}
    (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0)
    {a : ℤ} (ha0 : 0 ≤ a) (haN : a < (N : ℤ)) (b : ℤ) :
    subst2 (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) a b = comp W u v x (a - N) b := by
  rw [flm_singular W u v x hN ha0 haN b, comp_singular_form W u v x (by omega) b]

theorem flm_lt (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {N : ℕ}
    (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0)
    {a : ℤ} (haN : a < (N : ℤ)) (b : ℤ) :
    subst2 (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) a b = comp W u v x (a - N) b := by
  rcases lt_or_ge a 0 with ha | ha
  · exact flm_neg_a W u v x hN ha b
  · exact flm_singular_comp W u v x hN ha haN b

/-! ## §11. The NORMAL regime: RHS as `Phi` finsum + the hybrid `Zhyb` (copied from f2). -/

noncomputable def Phi (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (a : ℤ) (N : ℕ) (b j : ℤ) : 𝒱 :=
  cbz j (a - N) • (if 0 ≤ j - (a - N) then (W.Y u) j ((W.Y v) (b - j + (a - N)) x)
                   else (W.Y v) (b - j + (a - N)) ((W.Y u) j x))

theorem prod_rising_eq_falling (p : ℕ) (m : ℤ) :
    (∏ i ∈ Finset.range p, ((m : ℂ) + 1 + (i : ℤ)))
      = ∏ i ∈ Finset.range p, (((m + (p : ℤ) : ℤ) : ℂ) - (i : ℂ)) := by
  rw [← Finset.prod_range_reflect (fun i => (((m + (p : ℤ) : ℤ) : ℂ) - (i : ℂ))) p]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [show p - 1 - i = p - (i + 1) by omega, Nat.cast_sub (show i + 1 ≤ p by omega)]
  push_cast
  ring

theorem deriv_scalar_eq_gBinom (p : ℕ) (m : ℤ) :
    ((p.factorial : ℂ)⁻¹) * ((∏ i ∈ Finset.range p, (m + 1 + (i : ℤ)) : ℤ) : ℂ)
      = gBinom (m + (p : ℤ)) p := by
  have hfac : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hcast : ((∏ i ∈ Finset.range p, (m + 1 + (i : ℤ)) : ℤ) : ℂ)
      = ∏ i ∈ Finset.range p, ((m : ℂ) + 1 + (i : ℤ)) := by push_cast; rfl
  rw [hcast, prod_rising_eq_falling p m, ← gBinom_mul_factorial (m + (p : ℤ)) p,
    ← mul_assoc, inv_mul_cancel₀ hfac, one_mul]

theorem nprod_summand_eq_phi (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (p : ℕ) (b m : ℤ) :
    ((p.factorial : ℂ)⁻¹) •
        (normalOrdered ((deriv)^[p] (W.Y u)) (W.Y v) m (b - m)) x
      = cbz (m + (p : ℤ)) (p : ℤ) •
          (if 0 ≤ m then (W.Y u) (m + (p:ℤ)) ((W.Y v) (b - m) x)
           else (W.Y v) (b - m) ((W.Y u) (m + (p:ℤ)) x)) := by
  rw [normalOrdered_apply, cbz_apply_nonneg _ (by positivity), Int.toNat_natCast]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, if_pos hm, Module.End.mul_apply, deriv_pow_apply,
      LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℂ, smul_smul,
      ← deriv_scalar_eq_gBinom p m]
  · rw [if_neg hm, if_neg hm, Module.End.mul_apply, deriv_pow_apply,
      LinearMap.smul_apply, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul,
      ← deriv_scalar_eq_gBinom p m]

theorem rhs_eq_phi_finsum (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {N : ℕ}
    {a : ℤ} (haN : (N : ℤ) ≤ a) (b : ℤ) :
    negProd (W.isField_Y u) (W.isField_Y v) (a - N).toNat b x
      = ∑ᶠ j : ℤ, Phi W u v x a N b j := by
  set p := (a - N).toNat with hp
  have hpZ : (p : ℤ) = a - (N : ℤ) := by omega
  rw [negProd_apply, nprod_apply,
    smul_finsum' _ (normalOrdered_diag_support_finite
      ((W.isField_Y u).deriv_iterate p) (W.isField_Y v) b x)]
  rw [← finsum_comp_equiv (Equiv.addRight (p : ℤ))
        (f := fun j => Phi W u v x a N b j)]
  refine finsum_congr (fun m => ?_)
  rw [Equiv.coe_addRight]
  rw [nprod_summand_eq_phi W u v x p b m]
  show _ = Phi W u v x a N b (m + (p : ℤ))
  rw [Phi]
  rw [show m + (p : ℤ) - (a - (N : ℤ)) = m by omega,
    show b - (m + (p : ℤ)) + (a - (N : ℤ)) = b - m by omega,
    show m + (p : ℤ) = m + (p : ℤ) from rfl]
  congr 1
  rw [hpZ]

noncomputable def Zhyb (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (s : ℤ) : FormalDist₂ 𝒱 :=
  fun m n => if s ≤ m then (W.Y u) m ((W.Y v) n x) else (W.Y v) n ((W.Y u) m x)

@[simp] theorem Zhyb_apply (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (s m n : ℤ) :
    Zhyb W u v x s m n
      = if s ≤ m then (W.Y u) m ((W.Y v) n x) else (W.Y v) n ((W.Y u) m x) := rfl

theorem Zhyb_bddBelow₁ (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (s : ℤ) :
    IsBddBelow₁ (Zhyb W u v x s) := by
  obtain ⟨Nx, hNx⟩ := W.toPreVertexAlgebra.regularity u x
  refine ⟨min (-Nx) s, fun m n hm => ?_⟩
  rw [Zhyb_apply]
  have hu : (W.Y u) m x = 0 := by
    have h := hNx (-m - 1) (by omega)
    rwa [mode_apply, show (-(-m - 1) - 1 : ℤ) = m by ring] at h
  rw [if_neg (by omega), hu, map_zero]

theorem Zhyb_bddBelow₂ (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (s : ℤ) :
    IsBddBelow₂ (Zhyb W u v x s) := by
  classical
  obtain ⟨B₁, hB₁⟩ := Zhyb_bddBelow₁ W u v x s
  obtain ⟨Bv, hBv⟩ := W.toPreVertexAlgebra.regularity v x
  have hg : ∀ m : ℤ, ∃ C : ℤ, ∀ n : ℤ, n < C → (W.Y v) n ((W.Y u) m x) = 0 := by
    intro m
    obtain ⟨C, hC⟩ := W.toPreVertexAlgebra.regularity v ((W.Y u) m x)
    refine ⟨-C, fun n hn => ?_⟩
    have h := hC (-n - 1) (by omega)
    rwa [mode_apply, show (-(-n - 1) - 1 : ℤ) = n by ring] at h
  choose g hg using hg
  set Wndw : Finset ℤ := Finset.Icc B₁ (s - 1) with hWndw
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℤ, ∀ m ∈ Wndw, C₀ ≤ g m := by
    obtain ⟨c, hc⟩ := Finset.exists_le (α := ℤᵒᵈ) (Wndw.image g)
    exact ⟨c, fun m hm => hc (g m) (Finset.mem_image_of_mem g hm)⟩
  refine ⟨min C₀ (-Bv), fun m n hn => ?_⟩
  rw [Zhyb_apply]
  by_cases hsm : s ≤ m
  · rw [if_pos hsm]
    have hvz : (W.Y v) n x = 0 := by
      have h := hBv (-n - 1) (by omega)
      rwa [mode_apply, show (-(-n - 1) - 1 : ℤ) = n by ring] at h
    rw [hvz, map_zero]
  · rw [if_neg hsm]
    by_cases hmlo : m < B₁
    · have := hB₁ m n hmlo
      rw [Zhyb_apply, if_neg (by omega)] at this
      exact this
    · have hmem : m ∈ Wndw := by rw [hWndw, Finset.mem_Icc]; omega
      exact hg m n (by have := hC₀ m hmem; omega)

theorem subst2_Zhyb_eq_phi (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (N : ℕ) (a b : ℤ) :
    subst2 (Zhyb W u v x (a - N)) (a - N) b = ∑ᶠ j : ℤ, Phi W u v x a N b j := by
  rw [subst2_apply]
  rw [← finsum_comp_equiv (Equiv.addLeft (a - (N : ℤ)))
        (f := fun j => Phi W u v x a N b j)]
  refine finsum_congr (fun k => ?_)
  rw [Equiv.coe_addLeft]
  rw [Phi, Zhyb_apply]
  rw [show (a - (N : ℤ)) + k - (a - (N : ℤ)) = k by ring,
    show b - ((a - (N : ℤ)) + k) + (a - (N : ℤ)) = b - k by ring]
  congr 1
  by_cases hk : 0 ≤ k
  · rw [if_pos (by omega), if_pos hk]
  · rw [if_neg (by omega), if_neg hk]

/-! ## §12. The boundary residual, unconditionally.

The two distributions `Yprod` and `Zhyb (a-N)` agree for `m ≥ a-N` and differ by the commutator
`D = Yprod - Yswap` for `m < a-N`.  At the antidiagonal level this is exactly a CUT at threshold
`s = a-N` of `gD = antidiag D δ`, whose `Δᴺ` is killed by the locality bridge.  Moving the cut from
`s` to `0` costs only the finite window `0 ≤ p < s`, on which the binomial `cbz(p, a-N)` vanishes;
the `cutLt 0 gD` piece vanishes by the unified reproducing identity in the normal regime `a ≥ N`. -/

/-- The antidiagonal of `Yprod` minus that of `Zhyb s` is the threshold-`s` cut of the commutator
antidiagonal: `antidiag Yprod δ − antidiag (Zhyb s) δ = cutLt s (antidiag (Yprod−Yswap) δ)`. -/
theorem antidiag_Yprod_sub_Zhyb (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) (s δ : ℤ) :
    antidiag (W.toPreVertexAlgebra.Yprod u v x) δ - antidiag (Zhyb W u v x s) δ
      = cutLt s (antidiag (W.toPreVertexAlgebra.Yprod u v x - Yswap W u v x) δ) := by
  funext p
  rw [Pi.sub_apply, antidiag_apply, antidiag_apply, cutLt_apply, antidiag_apply, Zhyb_apply,
    PreVertexAlgebra.Yprod_apply]
  by_cases hp : s ≤ p
  · rw [if_pos hp, if_neg (by omega), sub_self]
  · rw [if_neg hp, if_pos (by omega)]
    show _ - _ = (W.toPreVertexAlgebra.Yprod u v x p (δ - p) - Yswap W u v x p (δ - p))
    rw [PreVertexAlgebra.Yprod_apply, Yswap_apply]

/-- The substitution of the threshold-`s` cut of the commutator antidiagonal vanishes at `a` when
`s = a − N` and `a ≥ N`.  Splitting the cut at `0`: the `cutLt 0` piece vanishes by the unified
reproducing identity (normal regime), and the finite window `0 ≤ p < s` vanishes because there
`cbz(p, a−N) = 0`. -/
theorem subst1_dPow_cutLt_boundary (N : ℕ) {gD : ℤ → 𝒲} (hbridge : dPow N gD = 0)
    {a : ℤ} (haN : (N : ℤ) ≤ a)
    (hcut_fin : (Function.support (dPow N (cutLt (a - N) gD))).Finite) :
    subst1 (dPow N (cutLt (a - N) gD)) a = 0 := by
  set s := a - (N : ℤ) with hs
  -- Finiteness of `Δᴺ (cutLt 0 gD)` from the finite window.
  have hwin_fin : (Function.support (cutLt s gD - cutLt 0 gD)).Finite :=
    support_cutLt_sub_finite s 0 gD
  have hcut0_fin : (Function.support (dPow N (cutLt 0 gD))).Finite := by
    have hsub : cutLt 0 gD = cutLt s gD - (cutLt s gD - cutLt 0 gD) := by abel
    rw [hsub, dPow_sub]
    refine (hcut_fin.union (support_dPow_finite N hwin_fin)).subset (fun p hp => ?_)
    rw [Function.mem_support, Pi.sub_apply] at hp
    by_contra hmem
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hmem
    exact hp (by rw [hmem.1, hmem.2, sub_zero])
  -- Term 1: cutLt 0 gD piece vanishes by the unified identity (a ≥ N).
  have hterm0 : subst1 (dPow N (cutLt 0 gD)) a = 0 := by
    rw [subst1_dPow_unified N (cutLt 0 gD)
        (fun p hp => by rw [cutLt_apply, if_neg (by omega)])
        hcut0_fin
        (fun m hm => dPow_cutLt_zero_ge N hbridge m hm) (by omega)]
    rw [if_neg (by omega : ¬ a < (N : ℤ))]
  -- Term 2: the finite window `0 ≤ p < s` vanishes since `cbz(p, a-N) = 0` there.
  have hterm_win : subst1 (dPow N (cutLt s gD - cutLt 0 gD)) a = 0 := by
    rw [subst1_dPow N hwin_fin, subst1_apply]
    refine finsum_eq_zero_of_forall_eq_zero (fun p => ?_)
    rw [Pi.sub_apply, cutLt_apply, cutLt_apply]
    rcases lt_or_ge p 0 with hp | hp
    · -- p < 0: both cuts equal gD p, cancel.
      rw [if_pos (by omega : p < s), if_pos hp, sub_self, smul_zero]
    · -- 0 ≤ p: second cut is 0; first cut is gD p only when p < s = a-N, where cbz vanishes.
      rw [if_neg (by omega : ¬ p < 0), sub_zero]
      by_cases hps : p < s
      · rw [if_pos hps, cbz_lt hp (by omega : p < a - N), zero_smul]
      · rw [if_neg hps, smul_zero]
  -- Assemble: subst1 (cutLt s) a = subst1 (cutLt 0) a + subst1 (window) a = 0 + 0.
  have hsplit : subst1 (dPow N (cutLt s gD)) a
      = subst1 (dPow N (cutLt 0 gD)) a + subst1 (dPow N (cutLt s gD - cutLt 0 gD)) a := by
    have heq : dPow N (cutLt s gD)
        = dPow N (cutLt 0 gD) + dPow N (cutLt s gD - cutLt 0 gD) := by
      rw [← dPow_add]
      congr 1
      abel
    rw [heq, subst1_add hcut0_fin (support_dPow_finite N hwin_fin)]
  rw [hsplit, hterm0, hterm_win, add_zero]

/-- **The FLM boundary-cancellation residual.** After `(z₁−z₂)ᴺ`, the iterated product
`Yprod` and the `(a−N)`-shifted normal-ordered hybrid `Zhyb (a−N)` give the SAME `subst2` value
at `(a,b)` (for `a ≥ N`, `N` ≥ the `(u,v)`-locality bound). -/
theorem FLMBoundaryResidual (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {N : ℕ}
    (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0)
    {a : ℤ} (haN : (N : ℤ) ≤ a) (b : ℤ) :
    subst2 (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) a b
      = subst2 (mulBySubPow N (Zhyb W u v x (a - N))) a b := by
  set Y := W.toPreVertexAlgebra.Yprod u v x with hY
  set D := W.toPreVertexAlgebra.Yprod u v x - Yswap W u v x with hD
  set s := a - (N : ℤ) with hs
  set δ := a + b - (N : ℤ) with hδ
  set gD := antidiag D δ with hgD
  -- Finiteness of the two `Δᴺ`-antidiagonals.
  obtain ⟨hY1, hY2⟩ := mulBySubPow_Yprod_doublyBdd W u v x hN
  have hgYp_fin : (Function.support (dPow N (antidiag Y δ))).Finite := by
    rw [← antidiag_mulBySubPow]
    exact support_antidiag_finite hY1 hY2 (a + b)
  have hgZh_fin : (Function.support (dPow N (antidiag (Zhyb W u v x s) δ))).Finite := by
    rw [← antidiag_mulBySubPow]
    exact support_antidiag_finite ((Zhyb_bddBelow₁ W u v x s).mulBySubPow N)
      ((Zhyb_bddBelow₂ W u v x s).mulBySubPow N) (a + b)
  -- Bridge: Δᴺ gD = 0.
  have hbridge : dPow N gD = 0 := by
    rw [hgD, hδ, hD]
    exact dPow_antidiag_bridge W u v x hN (a + b)
  -- Reduce both subst2 to subst1 of Δᴺ-antidiagonals.
  rw [subst2_antidiag_gen Y N a b, subst2_antidiag_gen (Zhyb W u v x s) N a b]
  rw [show (∑ᶠ m : ℤ, cbz m a • mulBySubPow N Y m (a + b - m))
        = subst1 (dPow N (antidiag Y δ)) a from by
      rw [subst1_apply,
        show dPow N (antidiag Y δ) = antidiag (mulBySubPow N Y) (a + b) from by
          rw [antidiag_mulBySubPow, hδ, show a + b - (N : ℤ) = δ from hδ.symm]]
      refine finsum_congr fun m => ?_
      rw [antidiag_apply]]
  rw [show (∑ᶠ m : ℤ, cbz m a • mulBySubPow N (Zhyb W u v x s) m (a + b - m))
        = subst1 (dPow N (antidiag (Zhyb W u v x s) δ)) a from by
      rw [subst1_apply,
        show dPow N (antidiag (Zhyb W u v x s) δ)
            = antidiag (mulBySubPow N (Zhyb W u v x s)) (a + b) from by
          rw [antidiag_mulBySubPow, hδ, show a + b - (N : ℤ) = δ from hδ.symm]]
      refine finsum_congr fun m => ?_
      rw [antidiag_apply]]
  -- The two subst1 differ by the cut of gD at threshold s; show that difference is 0.
  have hcut_fin : (Function.support (dPow N (cutLt s gD))).Finite := by
    have hdiff : cutLt s gD = antidiag Y δ - antidiag (Zhyb W u v x s) δ := by
      rw [hgD, antidiag_Yprod_sub_Zhyb W u v x s δ]
    rw [hdiff, dPow_sub]
    refine (hgYp_fin.union hgZh_fin).subset (fun p hp => ?_)
    rw [Function.mem_support, Pi.sub_apply] at hp
    by_contra hmem
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hmem
    exact hp (by rw [hmem.1, hmem.2, sub_zero])
  have hdifference : subst1 (dPow N (antidiag Y δ)) a
      - subst1 (dPow N (antidiag (Zhyb W u v x s) δ)) a = 0 := by
    rw [subst1_dPow_sub N hgYp_fin hgZh_fin a]
    rw [show antidiag Y δ - antidiag (Zhyb W u v x s) δ = cutLt s gD from by
      rw [hgD, antidiag_Yprod_sub_Zhyb W u v x s δ]]
    exact subst1_dPow_cutLt_boundary N hbridge haN hcut_fin
  exact sub_eq_zero.mp hdifference

/-! ## §13. The normal case `flm` (a ≥ N), unconditionally. -/

theorem flm_normal (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {N : ℕ}
    (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0)
    {a : ℤ} (haN : (N : ℤ) ≤ a) (b : ℤ) :
    subst2 (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) a b
      = negProd (W.isField_Y u) (W.isField_Y v) (a - N).toNat b x := by
  rw [rhs_eq_phi_finsum W u v x haN b, ← subst2_Zhyb_eq_phi W u v x N a b]
  rw [FLMBoundaryResidual W u v x hN haN b,
    subst2_mulBySubPow (Zhyb_bddBelow₁ W u v x (a - N)) (Zhyb_bddBelow₂ W u v x (a - N)) N,
    shiftZ₁_iterate_apply]

theorem flm_normal_comp (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {N : ℕ}
    (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0)
    {a : ℤ} (haN : (N : ℤ) ≤ a) (b : ℤ) :
    subst2 (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) a b = comp W u v x (a - N) b := by
  rw [flm_normal W u v x hN haN b, comp_normal_form W u v x haN b]

/-! ## §14. THE FULL FLM WEAK-ASSOCIATIVITY IDENTITY (all `a`). -/

/-- **FLM weak associativity, unconditional in `a`.**  For `N` ≥ the `(u,v)`-locality bound,
the `z₂`-dominant substitution `z₁ ↦ z₀+z₂` of `(z₁−z₂)ᴺ·Y(u,z₁)Y(v,z₂)x` equals the `z₀`-shifted
composite coefficient `comp W u v x (a−N) b`, for every integer column index `a`. -/
theorem flm (W : VertexOperatorAlgebra 𝒱) (u v x : 𝒱) {N : ℕ}
    (hN : mulBySubPow N (bracketDist (W.Y u) (W.Y v)) = 0) (a b : ℤ) :
    subst2 (mulBySubPow N (W.toPreVertexAlgebra.Yprod u v x)) a b = comp W u v x (a - N) b := by
  rcases lt_or_ge a (N : ℤ) with haN | haN
  · exact flm_lt W u v x hN haN b
  · exact flm_normal_comp W u v x hN haN b

end VertexOperatorAlgebra

end VOA
