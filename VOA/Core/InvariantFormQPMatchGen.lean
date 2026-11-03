/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
/-
General-weight quasi-primary matching `canBilin_qp_qp_adj`, all weights w ≥ 0.
Strategy: strong induction on `w.toNat`, base `w=1 = qpmatch_holds`, `w≤0 = canBilin_qp_qp_adj_w_le_zero`.
-/
import VOA.Core.InvariantFormQPMatch
import Mathlib.Algebra.Group.ForwardDiff

set_option linter.style.longLine false
set_option maxHeartbeats 1600000

open VOA VOA.VertexOperatorAlgebra
open scoped BigOperators fwdDiff
open Classical
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace VOA

/-! ## General-weight infrastructure (re-stated and re-proved here). -/

theorem L1_smul_qp_w {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0)
    {a : V} (hqpa : W.L 1 a = 0) (m : ℤ) :
    W.L 1 (W.smul u m a) = (2 * (w : ℂ) - m - 2) • W.smul u (m + 1) a := by
  have hbr := W.L1_bracket_smul hu m a
  rw [hqpu, PreVertexAlgebra.smul_zero_left, add_zero, hqpa, PreVertexAlgebra.smul_zero_right,
    sub_zero] at hbr
  exact hbr

theorem L1pow_smul_qp_w {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0)
    {a : V} (hqpa : W.L 1 a = 0) (n : ℤ) (k : ℕ) :
    (W.L 1 ^ k) (W.smul u n a)
      = (∏ l ∈ Finset.range k, (2 * (w : ℂ) - ((n : ℂ) + (l : ℤ)) - 2)) • W.smul u (n + k) a := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, L1_smul_qp_w hu hqpu hqpa,
      Finset.prod_range_succ, smul_smul,
      show (n + (m : ℤ) + 1) = (n + ((m : ℕ) + 1 : ℕ)) by push_cast; ring]
    congr 2
    push_cast; ring

theorem qp_match_lhs_expand_w (hne : W.vacuum ≠ 0)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0)
    {a : V} {p : ℤ} (ha : a ∈ W.grading p) (hqpa : W.L 1 a = 0)
    {b : V} {q : ℤ} (_hb : b ∈ W.grading q) :
    canBilin W hne (W.smul u (w + p - q - 1) a) b
      = -((-1:ℂ)^q • ∑ k ∈ Finset.range (q.toNat + 1), ((k.factorial:ℂ)⁻¹) •
          ((∏ l ∈ Finset.range k, (2 * (w : ℂ) - (((w + p - q - 1 : ℤ)):ℂ) - (l:ℤ) - 2)) •
            vacCoord W hne (W.smul (W.smul u ((w + p - q - 1) + k) a) (2*q - 1 - (k:ℤ)) b))) := by
  have huna : W.smul u (w + p - q - 1) a ∈ W.grading q := by
    have h := W.smul_mem_grading hu ha (w + p - q - 1)
    rwa [show (w + p - (w + p - q - 1) - 1 : ℤ) = q by ring] at h
  rw [canBilin_homog W hne huna b, adjPair]
  congr 2
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [L1pow_smul_qp_w hu hqpu hqpa (w + p - q - 1) k, PreVertexAlgebra.smul_smul_left, map_smul]
  congr 2
  refine Finset.prod_congr rfl (fun l _ => ?_)
  push_cast; ring

theorem qp_match_rhs_expand_w (hne : W.vacuum ≠ 0)
    {a : V} {p : ℤ} (ha : a ∈ W.grading p) (hqpa : W.L 1 a = 0) (X : V) :
    - canBilin W hne a X
      = (-1:ℂ)^p • vacCoord W hne (W.smul a (2*p - 1) X) := by
  rw [canBilin_homog W hne ha, adjPair]
  rw [Finset.sum_eq_single 0]
  · rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      Nat.cast_zero, sub_zero, neg_neg]
  · intro j _ hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [pow_succ, Module.End.mul_apply, hqpa, map_zero, PreVertexAlgebra.smul_zero_left, map_zero,
      smul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem comm_rel_w (u a b : V) (w p q : ℤ) (j : ℕ) :
    ∃ N : ℕ, (∀ t : ℕ, N ≤ t → W.smul u t a = 0)
      ∧ W.smul u (-(j:ℤ)) (W.smul a (w + p + q - 2 + j) b)
        - W.smul a (w + p + q - 2 + j) (W.smul u (-(j:ℤ)) b)
      = ∑ t ∈ Finset.range N, gBinom (-(j:ℤ)) t •
          W.smul (W.smul u t a) (w + p + q - 2 - (t:ℤ)) b := by
  obtain ⟨N, hzero, hN⟩ := commBound W u a (-(j:ℤ)) (w + p + q - 2 + j)
  refine ⟨N, hzero, ?_⟩
  have happ := congrArg (fun (f : Module.End ℂ V) => f b) hN
  simp only at happ
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply] at happ
  rw [LinearMap.sum_apply] at happ
  rw [show W.smul u (-(j:ℤ)) (W.smul a (w + p + q - 2 + j) b)
        = mode (W.Y u) (-(j:ℤ)) (mode (W.Y a) (w + p + q - 2 + j) b) from rfl,
      show W.smul a (w + p + q - 2 + j) (W.smul u (-(j:ℤ)) b)
        = mode (W.Y a) (w + p + q - 2 + j) (mode (W.Y u) (-(j:ℤ)) b) from rfl]
  rw [happ, ← Fin.sum_univ_eq_sum_range
    (fun t => gBinom (-(j:ℤ)) t • W.smul (W.smul u t a) (w + p + q - 2 - (t:ℤ)) b) N]
  apply Finset.sum_congr rfl
  intro t _
  rw [LinearMap.smul_apply]
  congr 1
  rw [show mode (W.Y (W.smul u (t:ℕ) a)) (-(j:ℤ) + (w + p + q - 2 + j) - (t:ℕ)) b
        = W.smul (W.smul u (t:ℕ) a) (-(j:ℤ) + (w + p + q - 2 + j) - (t:ℕ)) b from rfl]
  congr 1
  ring

theorem canBilin_qp_qp_adj_w_le_zero (hne : W.vacuum ≠ 0)
    {w : ℤ} (hw : w ≤ 0) {u : V} (hu : u ∈ W.grading w) (n : ℤ) (a b : V) :
    canBilin W hne (W.smul u n a) b = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - n - 2) b) := by
  rcases lt_or_eq_of_le hw with hwneg | hw0
  · rw [eq_zero_of_mem_neg_grading W hwneg hu]
    simp [PreVertexAlgebra.smul_zero_left]
  · subst hw0
    rw [canBilin_fullyInvariant_wt_le_zero hne (le_refl 0) u hu n a b]
    rw [show ((0:ℤ).toNat + 1) = 1 from rfl, Finset.sum_range_one]
    simp only [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      Nat.cast_zero, sub_zero]

/-! ## Off-diagonal vanishing at general weight (pure grading). -/

/-- For homogeneous `a ∈ 𝒱_p`, `b ∈ 𝒱_q`, and a mode `n ≠ w+p-q-1` (the matching mode), both
sides of the target vanish by grading. -/
theorem target_offdiag_w (hne : W.vacuum ≠ 0)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) {a : V} {p : ℤ} (ha : a ∈ W.grading p)
    {b : V} {q : ℤ} (hb : b ∈ W.grading q) (n : ℤ) (hn : n ≠ w + p - q - 1) :
    canBilin W hne (W.smul u n a) b = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - n - 2) b) := by
  have hmemL : W.smul u n a ∈ W.grading (w + p - n - 1) := W.smul_mem_grading hu ha n
  have hmemR : W.smul u (2*w - n - 2) b ∈ W.grading (w + q - (2*w - n - 2) - 1) :=
    W.smul_mem_grading hu hb (2*w - n - 2)
  rw [canBilin_offdiag hne hmemL hb (by omega : w + p - n - 1 ≠ q),
      canBilin_offdiag hne ha hmemR (by omega : p ≠ w + q - (2*w - n - 2) - 1), smul_zero]

/-! ## The matching-mode diagonal (the crux) and the main reduction. -/

/-- The matching-mode diagonal identity at general weight `w ≥ 1`, homogeneous `b ∈ 𝒱_q`. -/
def QPDiagW (hne : W.vacuum ≠ 0) (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {w : ℤ} {u : V} (_hu : u ∈ W.grading w) (_hqpu : W.L 1 u = 0) : Prop :=
  ∀ {p : ℤ} {a : V}, a ∈ W.grading p → W.L 1 a = 0 → ∀ {q : ℤ} {b : V}, b ∈ W.grading q →
    canBilin W hne (W.smul u (w + p - q - 1) a) b
      = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - (w + p - q - 1) - 2) b)

/-- From the matching-mode diagonal (for homogeneous `b`), deduce the target for all `n`, all `b`. -/
theorem qp_qp_adj_of_diag (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0)
    (hdiag : QPDiagW hne hqp hu hqpu)
    {p : ℤ} {a : V} (ha : a ∈ W.grading p) (hqpa : W.L 1 a = 0)
    (n : ℤ) (b : V) :
    canBilin W hne (W.smul u n a) b = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - n - 2) b) := by
  -- reduce `b` to homogeneous via the internal direct sum
  have hbtop : b ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun b =>
      canBilin W hne (W.smul u n a) b = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - n - 2) b))
      hbtop ?_ ?_ ?_
  · intro q b hb
    rcases eq_or_ne n (w + p - q - 1) with hn | hn
    · subst hn
      exact hdiag ha hqpa hb
    · exact target_offdiag_w hne hu ha hb n hn
  · show canBilin W hne (W.smul u n a) 0 = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - n - 2) 0)
    rw [PreVertexAlgebra.smul_zero_right, map_zero, map_zero, smul_zero]
  · intro b₁ b₂ h₁ h₂
    show canBilin W hne (W.smul u n a) (b₁ + b₂)
        = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - n - 2) (b₁ + b₂))
    rw [PreVertexAlgebra.smul_add_right, map_add, map_add, h₁, h₂, smul_add]

/-! ## Combinatorial cores for the two regimes.

`s := 2w − n − 2 = w − p + q − 1`.  Regime A is `s ≥ 0`; regime B is `s ≤ −1` (set `m := −s ≥ 1`). -/

/-- **KIDw** (regime A `s ≥ 0`, the `a`-first collapse). For `i ≤ s`:
`∑_{k=0}^{s} (−1)^k gBinom(s,k) · gBinom(n+k, i) = (−1)^s · [i = s]`.
Proof: `gBinom_iter_diff_eval` + `fwdDiff_iter_eq_sum_shift`, exactly as `KID`. -/
theorem KIDw (n : ℤ) (s : ℕ) (i : ℕ) (hi : i ≤ s) :
    (∑ k ∈ Finset.range (s + 1), (-1:ℂ)^k * gBinom (s:ℤ) k * gBinom (n + (k:ℤ)) i)
      = if i = s then ((-1:ℂ)^s) else 0 := by
  -- rewrite gBinom (s:ℤ) k = C(s,k)
  have step1 : (∑ k ∈ Finset.range (s + 1), (-1:ℂ)^k * gBinom (s:ℤ) k * gBinom (n + (k:ℤ)) i)
      = ∑ k ∈ Finset.range (s + 1), (-1:ℂ)^k * (s.choose k : ℂ) * gBinom (n + (k:ℤ)) i := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [gBinom_natCast_eq_choose hk]
  rw [step1]
  have hshift := fwdDiff_iter_eq_sum_shift (h := (1:ℤ)) (G := ℂ) (M := ℤ)
    (fun x : ℤ => gBinom (x + n) i) s 0
  have hdiff : (Δ_[(1:ℤ)]^[s] (fun x : ℤ => gBinom (x + n) i)) 0 = if i = s then (1:ℂ) else 0 :=
    gBinom_iter_diff_eval n s i hi
  have hshift2 : (Δ_[(1:ℤ)]^[s] (fun x : ℤ => gBinom (x + n) i)) 0
      = ∑ k ∈ Finset.range (s + 1),
          ((-1 : ℤ) ^ (s - k) * (s.choose k : ℤ) : ℤ) • gBinom (n + (k:ℤ)) i := by
    rw [hshift]
    apply Finset.sum_congr rfl
    intro k _
    have hidx : (0:ℤ) + k • (1:ℤ) + n = n + (k:ℤ) := by rw [nsmul_eq_mul]; ring
    simp only [hidx]
  rw [show (if i = s then ((-1:ℂ)^s) else 0)
        = (-1:ℂ)^s * (if i = s then (1:ℂ) else 0) by by_cases h : i = s <;> simp [h],
      ← hdiff, hshift2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [zsmul_eq_mul]
  push_cast
  have hms : (-1:ℂ)^s * (-1:ℂ)^(s-k) = (-1:ℂ)^k := by
    have hmk : s + (s - k) = k + 2 * (s - k) := by omega
    rw [← pow_add, hmk, pow_add, pow_mul]; norm_num
  rw [show (-1:ℂ)^s * ((-1:ℂ)^(s-k) * (s.choose k : ℂ) * gBinom (n + (k:ℤ)) i)
        = ((-1:ℂ)^s * (-1:ℂ)^(s-k)) * ((s.choose k : ℂ) * gBinom (n + (k:ℤ)) i) by ring, hms]
  ring

/-- **General `Δ`-evaluation** (generalizes `gBinom_iter_diff_eval` to a threshold/shift):
`Δ_[1]^[N] (x ↦ gBinom (x + c) t) 0 = if N ≤ t then gBinom c (t − N) else 0`. -/
theorem gBinom_iter_diff_eval_gen (c : ℤ) (N t : ℕ) :
    Δ_[(1:ℤ)]^[N] (fun x : ℤ => gBinom (x + c) t) 0 = if N ≤ t then gBinom c (t - N) else 0 := by
  rcases le_or_gt N t with hNt | hNt
  · rw [if_pos hNt]
    have h := gBinom_fwdDiff_iter c N (t - N)
    rw [show N + (t - N) = t by omega] at h
    have happ := congrArg (fun f => f (0:ℤ)) h
    simp only at happ
    rw [happ]; congr 1; simp
  · rw [if_neg (by omega)]
    -- N > t : do t+1 differences to reach a constant then 0
    have hsplit : N = (N - (t + 1)) + (t + 1) := by omega
    rw [hsplit, Function.iterate_add_apply]
    have hinner : Δ_[(1:ℤ)]^[t + 1] (fun x : ℤ => gBinom (x + c) t) = (fun _ : ℤ => (0:ℂ)) := by
      rw [Function.iterate_succ_apply']
      have h := gBinom_fwdDiff_iter c t 0
      rw [show t + 0 = t by ring] at h
      have hc : (Δ_[(1:ℤ)]^[t] fun x : ℤ => gBinom (x + c) t) = (fun x : ℤ => gBinom (x + c) 0) := by
        rw [h]
      rw [hc]; funext x; simp [fwdDiff, gBinom_zero]
    rw [hinner]
    have : (Δ_[(1:ℤ)]^[N - (t + 1)] (fun _ : ℤ => (0:ℂ))) = (fun _ : ℤ => (0:ℂ)) :=
      Function.iterate_fixed (by funext x; simp [fwdDiff]) (N - (t + 1))
    rw [this]

/-- **FDIDw** (regime B `s ≤ −1`, the shifted finite-difference identity). With `m ≤ n` (so the
shift `d := n − m ≥ 0`) and `t ≥ n − m + 1` (i.e. `n < t + m`):
`∑_{j=1}^{m} (−1)^{n+m−j} C(n, m−j) · gBinom(−j, t) = if n ≤ t then gBinom(−m, t−n) else 0`.
Proof: extend the `j`-sum to an `n`-fold forward difference of `x ↦ gBinom(x−m, t)` (the extra terms
`gBinom(i−m, t)` for `m ≤ i ≤ n` vanish since `i − m ≤ d < t`); then `gBinom_iter_diff_eval_gen`. -/
theorem FDIDw (m n : ℕ) (hmn : m ≤ n) (t : ℕ) (ht : n < t + m) :
    (∑ j ∈ Finset.range m, (-1:ℂ)^(n + m - (j+1)) * (n.choose (m - (j+1)) : ℂ) * gBinom (-((j:ℤ)+1)) t)
      = if n ≤ t then gBinom (-(m:ℤ)) (t - n) else 0 := by
  -- Step 1: reindex j ↦ i = m-(j+1), and extend to i = 0..n.  Target: ∑_{i=0}^{n} term(i).
  -- term(i) := (-1)^(n+i) C(n,i) gBinom((i:ℤ)-m, t).
  have key : (∑ j ∈ Finset.range m,
        (-1:ℂ)^(n + m - (j+1)) * (n.choose (m - (j+1)) : ℂ) * gBinom (-((j:ℤ)+1)) t)
      = ∑ i ∈ Finset.range (n + 1), (-1:ℂ)^(n + i) * (n.choose i : ℂ) * gBinom ((i:ℤ) - m) t := by
    -- RHS = LHS-part (i in [0,m-1]) + tail (i in [m,n]); the tail vanishes.
    rw [show n + 1 = m + (n + 1 - m) by omega, Finset.sum_range_add]
    have htail : (∑ i ∈ Finset.range (n + 1 - m),
          (-1:ℂ)^(n + (m + i)) * (n.choose (m + i) : ℂ) * gBinom (((m + i : ℕ):ℤ) - m) t) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show (((m + i : ℕ):ℤ) - m) = ((i:ℕ):ℤ) by push_cast; ring,
        gBinom_natCast_eq_zero (by omega : i < t), mul_zero]
    rw [htail, add_zero]
    -- match the i in [0,m-1] part with the j-sum: reflect the RHS (i ↦ m-1-i).
    rw [← Finset.sum_range_reflect (fun i => (-1:ℂ)^(n + i) * (n.choose i : ℂ) * gBinom ((i:ℤ) - m) t) m]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    -- RHS summand at reflected index (m-1-j):
    have him : (m - 1 - j) = m - (j + 1) := by omega
    simp only [him]
    have hcast : ((m - (j+1) : ℕ):ℤ) - m = -((j:ℤ)+1) := by
      push_cast [Nat.cast_sub (by omega : j + 1 ≤ m)]; ring
    rw [hcast, show (n + (m - (j+1))) = (n + m - (j+1)) by omega]
  rw [key]
  -- Step 2: identify with (-1)^? times Δ^[n] f 0 via fwdDiff_iter_eq_sum_shift.
  have hshift := fwdDiff_iter_eq_sum_shift (h := (1:ℤ)) (G := ℂ) (M := ℤ)
    (fun x : ℤ => gBinom (x + (-(m:ℤ))) t) n 0
  have heval : (Δ_[(1:ℤ)]^[n] (fun x : ℤ => gBinom (x + (-(m:ℤ))) t)) 0
      = if n ≤ t then gBinom (-(m:ℤ)) (t - n) else 0 := gBinom_iter_diff_eval_gen (-(m:ℤ)) n t
  rw [← heval, hshift]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  have hidx : (0:ℤ) + i • (1:ℤ) + (-(m:ℤ)) = (i:ℤ) - m := by rw [nsmul_eq_mul]; ring
  simp only [hidx]
  rw [zsmul_eq_mul]
  have hms : (-1:ℂ)^(n + i) = (-1:ℂ)^(n - i) := by
    have : n + i = (n - i) + 2 * i := by omega
    rw [this, pow_add, pow_mul]; norm_num
  rw [hms]
  push_cast
  ring

/-! ## VOA-side facts about the diagonal atom `h t := vacCoord((u₍t₎a)₍w+p+q−2−t₎b)`. -/

/-- The atom vanishes for high `t`: `u₍t₎a ∈ 𝒱_{w+p−t−1}` is in negative grade for `t ≥ w+p`. -/
theorem qpdiag_h_high (hne : W.vacuum ≠ 0)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) {a : V} {p : ℤ} (ha : a ∈ W.grading p)
    {b : V} {q : ℤ} (_hb : b ∈ W.grading q) {t : ℤ} (ht : w + p - 1 < t) :
    vacCoord W hne (W.smul (W.smul u t a) (w + p + q - 2 - t) b) = 0 := by
  have huta : W.smul u t a = 0 := by
    have hmem := W.smul_mem_grading hu ha t
    exact eq_zero_of_mem_neg_grading W (by omega : (w + p - t - 1 : ℤ) < 0) hmem
  rw [huta, PreVertexAlgebra.smul_zero_left, map_zero]

/-- **Regime B low-mode vanishing.** For quasi-primary `u ∈ 𝒱_w`, `a ∈ 𝒱_p`, and `s ≤ −1`
(i.e. `w + q ≤ p`), the atom `h t = 0` for `t ≤ 2w − 2`: in the two-point iterate the `u`-first
family dies by `vacCoord_a_low_mode_zero` on `u` (u-mode `t−i ≤ 2w−2`) and the `a`-first family dies
by `vacCoord_a_low_mode_zero` on `a` (a-mode `w+p+q−2−i ≤ 2p−2` since `i ≥ 0 ≥ s+1`). -/
theorem qpdiag_h_low (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0)
    {a : V} {p : ℤ} (ha : a ∈ W.grading p) (hqpa : W.L 1 a = 0)
    {b : V} {q : ℤ} (_hb : b ∈ W.grading q) (hs : w + q ≤ p) {t : ℤ} (ht : t ≤ 2 * w - 2) :
    vacCoord W hne (W.smul (W.smul u t a) (w + p + q - 2 - t) b) = 0 := by
  rw [vacCoord_iterate hne u a b t (w + p + q - 2 - t)]
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro i
  have hU : vacCoord W hne (W.smul u (t - i) (W.smul a (w + p + q - 2 - t + i) b)) = 0 :=
    vacCoord_a_low_mode_zero hne hqp hu hqpu (by omega : t - (i:ℤ) ≤ 2 * w - 2) _
  have hA : vacCoord W hne (W.smul a (t + (w + p + q - 2 - t) - i) (W.smul u i b)) = 0 :=
    vacCoord_a_low_mode_zero hne hqp ha hqpa (by omega : t + (w + p + q - 2 - t) - (i:ℤ) ≤ 2 * p - 2) _
  rw [hU, hA]
  simp

/-- **Weighted commutator relation** (analog of `comm_rel_P`). For `w ≥ 1`, `j ≥ 1`, and any range
bound `R` with `w + p ≤ R` (so the high atoms `h t = 0`, `t ≥ w+p`, are absorbed):
`∑_{t ∈ range R} gBinom(−j,t)·h(t) = − vacCoord(a₍w+p+q−2+j₎(u₍−j₎b))`. -/
theorem comm_rel_P_w (hne : W.vacuum ≠ 0)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hw : 1 ≤ w)
    {a : V} {p : ℤ} (ha : a ∈ W.grading p)
    {b : V} {q : ℤ} (hb : b ∈ W.grading q) (R : ℕ) (hR : w + p ≤ (R:ℤ))
    {j : ℕ} (hj : 1 ≤ j) :
    (∑ t ∈ Finset.range R, gBinom (-(j:ℤ)) t *
        vacCoord W hne (W.smul (W.smul u t a) (w + p + q - 2 - (t:ℤ)) b))
      = - vacCoord W hne (W.smul a (w + p + q - 2 + j) (W.smul u (-(j:ℤ)) b)) := by
  obtain ⟨N, hzero, hrel⟩ := comm_rel_w (W := W) u a b w p q j
  have hvac := congrArg (vacCoord W hne) hrel
  rw [map_sub, map_sum] at hvac
  -- first LHS term vanishes: a₍w+p+q-2+j₎b ∈ 𝒱_{1-w-j} negative grade
  have hzero1 : vacCoord W hne (W.smul u (-(j:ℤ)) (W.smul a (w + p + q - 2 + j) b)) = 0 := by
    have hmem := W.smul_mem_grading ha hb (w + p + q - 2 + j)
    rw [eq_zero_of_mem_neg_grading W (by omega : (p + q - (w + p + q - 2 + j) - 1 : ℤ) < 0) hmem,
      PreVertexAlgebra.smul_zero_right, map_zero]
  rw [hzero1, zero_sub] at hvac
  -- convert the comm-sum (over range N) of vacCoord(gBinom • ...) into ∑ gBinom·h(t)
  rw [show (∑ t ∈ Finset.range N, vacCoord W hne (gBinom (-(j:ℤ)) t •
          W.smul (W.smul u t a) (w + p + q - 2 - (t:ℤ)) b))
        = ∑ t ∈ Finset.range N, gBinom (-(j:ℤ)) t *
            vacCoord W hne (W.smul (W.smul u t a) (w + p + q - 2 - (t:ℤ)) b) from
      Finset.sum_congr rfl (fun t _ => by rw [map_smul, smul_eq_mul])] at hvac
  -- the term function vanishes for t ≥ N (u₍t₎a=0) and for t ≥ w+p (h high); equate ranges via max.
  have hfzeroN : ∀ t : ℕ, N ≤ t → gBinom (-(j:ℤ)) t *
      vacCoord W hne (W.smul (W.smul u t a) (w + p + q - 2 - (t:ℤ)) b) = 0 := by
    intro t ht
    rw [hzero t ht, PreVertexAlgebra.smul_zero_left, map_zero, mul_zero]
  have hfzeroR : ∀ t : ℕ, R ≤ t → gBinom (-(j:ℤ)) t *
      vacCoord W hne (W.smul (W.smul u t a) (w + p + q - 2 - (t:ℤ)) b) = 0 := by
    intro t ht
    rw [qpdiag_h_high hne hu ha hb (by omega : w + p - 1 < (t:ℤ)), mul_zero]
  set S : ℕ := max N R with hS_def
  have eN : (∑ t ∈ Finset.range N, gBinom (-(j:ℤ)) t *
        vacCoord W hne (W.smul (W.smul u t a) (w + p + q - 2 - (t:ℤ)) b))
      = ∑ t ∈ Finset.range S, gBinom (-(j:ℤ)) t *
        vacCoord W hne (W.smul (W.smul u t a) (w + p + q - 2 - (t:ℤ)) b) := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left N R))
    intro t _ htn; rw [Finset.mem_range, not_lt] at htn; exact hfzeroN t htn
  have eR : (∑ t ∈ Finset.range R, gBinom (-(j:ℤ)) t *
        vacCoord W hne (W.smul (W.smul u t a) (w + p + q - 2 - (t:ℤ)) b))
      = ∑ t ∈ Finset.range S, gBinom (-(j:ℤ)) t *
        vacCoord W hne (W.smul (W.smul u t a) (w + p + q - 2 - (t:ℤ)) b) := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right N R))
    intro t _ htn; rw [Finset.mem_range, not_lt] at htn; exact hfzeroR t htn
  rw [eR, ← eN, ← hvac]

/-- **Regime A `a`-first collapse.** For quasi-primary `u ∈ 𝒱_w`, and `t ≤ 2w − 2` (so the `u`-first
family dies by `vacCoord_a_low_mode_zero` on `u`), the atom is a pure `a`-first finsum:
`h t = −(−1)^t · ∑ᶠ i, (−1)^i gBinom(t,i)·vacCoord(a₍w+p+q−2−i₎(u₍i₎b))`. -/
theorem qpdiag_h_aFirst (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0)
    {a : V} {p : ℤ} (_ha : a ∈ W.grading p) {b : V} {q : ℤ} (_hb : b ∈ W.grading q)
    {t : ℤ} (ht : t ≤ 2 * w - 2) :
    vacCoord W hne (W.smul (W.smul u t a) (w + p + q - 2 - t) b)
      = (- (-1:ℂ)^t) * ∑ᶠ i : ℕ, ((-1:ℂ)^i * gBinom t i)
          * vacCoord W hne (W.smul a (w + p + q - 2 - (i:ℤ)) (W.smul u i b)) := by
  rw [vacCoord_iterate hne u a b t (w + p + q - 2 - t), mul_finsum]
  apply finsum_congr
  intro i
  rw [vacCoord_a_low_mode_zero hne hqp hu hqpu (by omega : t - (i:ℤ) ≤ 2 * w - 2)
    (W.smul a (w + p + q - 2 - t + i) b)]
  rw [show (t + (w + p + q - 2 - t) - (i:ℤ)) = (w + p + q - 2 - (i:ℤ)) by ring]
  simp only [smul_eq_mul, zero_sub, mul_neg]
  ring

/-! ## Regime A (`s ≥ 0`): the matching-mode diagonal via `KIDw`. -/

/-- The matching-mode diagonal identity in regime A (`p ≤ w + q − 1`, i.e. `s = w−p+q−1 ≥ 0`): every
LHS atom `h(n+k)` (`k ≤ s`) has its `u`-first family killed by low-mode-on-`u` (since `n+k ≤ 2w−2`),
so it is pure `a`-first; collapse by `KIDw`. -/
theorem qpdiag_regimeA (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0) (_hw : 1 ≤ w)
    {p : ℤ} {a : V} (ha : a ∈ W.grading p) (hqpa : W.L 1 a = 0)
    {q : ℤ} {b : V} (hb : b ∈ W.grading q) (hsA : p ≤ w + q - 1) :
    canBilin W hne (W.smul u (w + p - q - 1) a) b
      = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - (w + p - q - 1) - 2) b) := by
  -- edge: q < 0 ⟹ b = 0
  rcases lt_or_ge q 0 with hqneg | hq0
  · rw [eq_zero_of_mem_neg_grading W hqneg hb]
    simp [PreVertexAlgebra.smul_zero_right]
  rcases lt_or_ge p 0 with hpneg | hp0
  · rw [eq_zero_of_mem_neg_grading W hpneg ha]
    simp
  -- normalise the RHS mode
  rw [show (2*w - (w + p - q - 1) - 2 : ℤ) = w - p + q - 1 by ring]
  -- s := (w - p + q - 1).toNat ≥ 0
  set s : ℕ := (w - p + q - 1).toNat with hs_def
  have hs : (w - p + q - 1 : ℤ) = (s : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  -- expansions: rewrite RHS canBilin via rhs_expand, LHS via lhs_expand
  have hrhs : canBilin W hne a (W.smul u (w - p + q - 1) b)
      = -((-1:ℂ)^p • vacCoord W hne (W.smul a (2*p - 1) (W.smul u (w - p + q - 1) b))) := by
    have h := qp_match_rhs_expand_w (W := W) hne ha hqpa (W.smul u (w - p + q - 1) b)
    rw [eq_comm, ← neg_eq_iff_eq_neg] at h
    rw [← h]
  rw [hrhs, qp_match_lhs_expand_w hne hu hqpu ha hqpa hb]
  -- atom A
  set A : ℂ := vacCoord W hne (W.smul a (2*p - 1) (W.smul u (w - p + q - 1) b)) with hA_def
  -- the a-first atom function AF i := vacCoord(a₍w+p+q-2-i₎(u₍i₎b))
  set AF : ℕ → ℂ := fun i => vacCoord W hne (W.smul a (w + p + q - 2 - (i:ℤ)) (W.smul u i b))
    with hAF_def
  clear_value AF
  -- AF vanishes for i > s (a-mode w+p+q-2-i ≤ 2p-2)
  have hAF_zero : ∀ i : ℕ, s < i → AF i = 0 := by
    intro i hi
    rw [hAF_def]
    exact vacCoord_a_low_mode_zero hne hqp ha hqpa (by omega : w + p + q - 2 - (i:ℤ) ≤ 2 * p - 2)
      (W.smul u i b)
  -- a range bound R with u₍i₎b = 0 for i ≥ R (to express the a-first finsum as a finite sum)
  obtain ⟨Rub, hRub⟩ := W.toPreVertexAlgebra.smul_eventually_zero u b
  set R : ℕ := max (Rub.toNat) (s + 1) with hR_def
  have hub_zero : ∀ i : ℕ, R ≤ i → W.smul u i b = 0 := by
    intro i hi
    apply hRub
    have hge : Rub.toNat ≤ i := le_trans (le_max_left _ _) hi
    rcases le_or_gt 0 Rub with h0 | h0
    · rw [← Int.toNat_of_nonneg h0]; exact_mod_cast hge
    · exact le_trans (le_of_lt h0) (Int.natCast_nonneg i)
  -- 1) coefficient to gBinom (same range), then extend the outer sum to range (s+1).
  have hcoeff : ∀ k : ℕ, ((k.factorial:ℂ)⁻¹) *
        (∏ l ∈ Finset.range k, (2 * (w : ℂ) - (((w + p - q - 1 : ℤ)):ℂ) - (l:ℤ) - 2))
        = gBinom (s:ℤ) k := by
    intro k
    rw [gBinom, div_eq_mul_inv, mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro l _
    have h2 : (2 * (w : ℂ) - (((w + p - q - 1 : ℤ)):ℂ) - (l:ℤ) - 2)
        = (((w - p + q - 1 : ℤ)):ℂ) - (l:ℂ) := by push_cast; ring
    rw [h2, hs]
  -- atom-zero facts for the bidirectional range conversion.
  have hatomk_zero : ∀ k : ℕ, q.toNat < k → gBinom (s:ℤ) k *
      vacCoord W hne (W.smul (W.smul u ((w + p - q - 1) + k) a) (2*q - 1 - (k:ℤ)) b) = 0 := by
    intro k hk
    rw [show (2*q - 1 - (k:ℤ)) = (w + p + q - 2 - ((w+p-q-1) + (k:ℤ))) by ring,
      qpdiag_h_high hne hu ha hb (by omega : w + p - 1 < (w+p-q-1) + (k:ℤ)), mul_zero]
  have hgbk_zero : ∀ k : ℕ, s < k → gBinom (s:ℤ) k *
      vacCoord W hne (W.smul (W.smul u ((w + p - q - 1) + k) a) (2*q - 1 - (k:ℤ)) b) = 0 := by
    intro k hk
    rw [show (s:ℤ) = ((s:ℕ):ℤ) by norm_num, gBinom_natCast_eq_zero (by omega : s < k), zero_mul]
  have hstep1 : (∑ k ∈ Finset.range ((q).toNat + 1), ((k.factorial:ℂ)⁻¹) •
        ((∏ l ∈ Finset.range k, (2 * (w : ℂ) - (((w + p - q - 1 : ℤ)):ℂ) - (l:ℤ) - 2)) •
          vacCoord W hne (W.smul (W.smul u ((w + p - q - 1) + k) a) (2*q - 1 - (k:ℤ)) b)))
      = ∑ k ∈ Finset.range (s + 1), gBinom (s:ℤ) k *
          vacCoord W hne (W.smul (W.smul u ((w + p - q - 1) + k) a) (2*q - 1 - (k:ℤ)) b) := by
    -- convert form (same range q.toNat+1), then bridge to range(s+1) through range(M+1).
    set M : ℕ := max (q.toNat) s with hM_def
    have e1 : (∑ k ∈ Finset.range ((q).toNat + 1), ((k.factorial:ℂ)⁻¹) •
          ((∏ l ∈ Finset.range k, (2 * (w : ℂ) - (((w + p - q - 1 : ℤ)):ℂ) - (l:ℤ) - 2)) •
            vacCoord W hne (W.smul (W.smul u ((w + p - q - 1) + k) a) (2*q - 1 - (k:ℤ)) b)))
        = ∑ k ∈ Finset.range (M + 1), gBinom (s:ℤ) k *
            vacCoord W hne (W.smul (W.smul u ((w + p - q - 1) + k) a) (2*q - 1 - (k:ℤ)) b) := by
      rw [Finset.sum_subset (Finset.range_subset_range.mpr (by omega : q.toNat + 1 ≤ M + 1))
        (fun k _ hknot => by
          rw [Finset.mem_range, not_lt] at hknot
          rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, hcoeff]
          exact hatomk_zero k (by omega))]
      apply Finset.sum_congr rfl
      intro k _
      rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, hcoeff]
    have e2 : (∑ k ∈ Finset.range (s + 1), gBinom (s:ℤ) k *
            vacCoord W hne (W.smul (W.smul u ((w + p - q - 1) + k) a) (2*q - 1 - (k:ℤ)) b))
        = ∑ k ∈ Finset.range (M + 1), gBinom (s:ℤ) k *
            vacCoord W hne (W.smul (W.smul u ((w + p - q - 1) + k) a) (2*q - 1 - (k:ℤ)) b) := by
      apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega : s + 1 ≤ M + 1))
      intro k _ hknot
      rw [Finset.mem_range, not_lt] at hknot
      exact hgbk_zero k (by omega)
    rw [e1, ← e2]
  rw [hstep1]
  -- 2) identify the inner atom with h(n+k) = (-(-1)^(n+k)) ∑ᶠ ... and convert to finite a-first sum
  have hatom : ∀ k ∈ Finset.range (s + 1),
      vacCoord W hne (W.smul (W.smul u ((w + p - q - 1) + k) a) (2*q - 1 - (k:ℤ)) b)
        = (- (-1:ℂ)^((w+p-q-1) + (k:ℤ))) *
            ∑ i ∈ Finset.range R, ((-1:ℂ)^i * gBinom ((w+p-q-1) + (k:ℤ)) i) * AF i := by
    intro k hk
    rw [Finset.mem_range] at hk
    -- rewrite the inner mode 2q-1-k = w+p+q-2-((w+p-q-1)+k) to match h
    rw [show (2*q - 1 - (k:ℤ)) = (w + p + q - 2 - ((w+p-q-1) + (k:ℤ))) by ring]
    rw [qpdiag_h_aFirst hne hqp hu hqpu ha hb (by omega : (w+p-q-1) + (k:ℤ) ≤ 2 * w - 2)]
    congr 1
    -- finsum body equals (-1)^i gBinom · AF i; convert finsum to finite sum over range R
    rw [show (∑ᶠ i : ℕ, ((-1:ℂ)^i * gBinom ((w+p-q-1) + (k:ℤ)) i)
            * vacCoord W hne (W.smul a (w + p + q - 2 - (i:ℤ)) (W.smul u i b)))
          = ∑ᶠ i : ℕ, ((-1:ℂ)^i * gBinom ((w+p-q-1) + (k:ℤ)) i) * AF i from
        finsum_congr (fun i => by rw [hAF_def])]
    rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range R) ?_]
    intro i hi
    rw [Function.mem_support] at hi
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    rw [not_lt] at hc
    exact hi (by rw [hAF_zero i (by omega), mul_zero])
  rw [Finset.sum_congr rfl (fun k hk => by rw [hatom k hk])]
  -- A = AF s
  have hAs : A = AF s := by
    rw [hA_def, hAF_def]
    simp only []
    rw [← hs, show (w + p + q - 2 - (w-p+q-1:ℤ)) = 2*p - 1 by ring]
  -- collapse the double sum: distribute, swap to ∑_i ∑_k, KIDw per i, keep i=s.
  -- per-i k-sum collapse via KIDw.
  have hcol : ∀ i : ℕ, i ≤ s →
      (∑ k ∈ Finset.range (s + 1),
        (gBinom (s:ℤ) k * (- (-1:ℂ)^((w+p-q-1) + (k:ℤ))) *
          ((-1:ℂ)^i * gBinom ((w+p-q-1) + (k:ℤ)) i)))
        = (-1:ℂ)^((w+p-q-1)+1) * (if i = s then (1:ℂ) else 0) := by
    intro i hi
    -- factor: = (-(-1)^n)(-1)^i · ∑_k (-1)^k gBinom(s,k) gBinom(n+k,i)
    have hk : ∀ k : ℕ, (gBinom (s:ℤ) k * (- (-1:ℂ)^((w+p-q-1) + (k:ℤ))) *
        ((-1:ℂ)^i * gBinom ((w+p-q-1) + (k:ℤ)) i))
        = ((- (-1:ℂ)^(w+p-q-1)) * (-1:ℂ)^i) *
            ((-1:ℂ)^k * gBinom (s:ℤ) k * gBinom ((w+p-q-1) + (k:ℤ)) i) := by
      intro k
      have he : (-1:ℂ)^((w+p-q-1) + (k:ℤ)) = (-1:ℂ)^(w+p-q-1) * (-1:ℂ)^k := by
        rw [zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0), zpow_natCast]
      rw [he]; ring
    rw [Finset.sum_congr rfl (fun k _ => hk k), ← Finset.mul_sum, KIDw (w+p-q-1) s i hi]
    by_cases hieq : i = s
    · rw [hieq, if_pos rfl, if_pos rfl]
      have hss : (-1:ℂ)^s * (-1:ℂ)^s = 1 := by
        rw [← pow_add, show s + s = 2*s by ring, pow_mul]; norm_num
      rw [show (-(-1:ℂ)^(w+p-q-1)) * (-1:ℂ)^s * (-1:ℂ)^s
            = (-(-1:ℂ)^(w+p-q-1)) * ((-1:ℂ)^s * (-1:ℂ)^s) by ring, hss,
          show (-1:ℂ)^((w+p-q-1)+1) = (-1:ℂ)^(w+p-q-1) * (-1) by
            rw [zpow_add₀ (by norm_num), zpow_one]]
      ring
    · rw [if_neg hieq, if_neg hieq, mul_zero, mul_zero]
  -- assemble: distribute, swap, sum_eq_single s.
  rw [show (∑ k ∈ Finset.range (s + 1), gBinom (s:ℤ) k *
          ((- (-1:ℂ)^((w+p-q-1) + (k:ℤ))) *
            ∑ i ∈ Finset.range R, ((-1:ℂ)^i * gBinom ((w+p-q-1) + (k:ℤ)) i) * AF i))
        = ∑ i ∈ Finset.range R, (∑ k ∈ Finset.range (s + 1),
            (gBinom (s:ℤ) k * (- (-1:ℂ)^((w+p-q-1) + (k:ℤ))) *
              ((-1:ℂ)^i * gBinom ((w+p-q-1) + (k:ℤ)) i))) * AF i from ?_]
  · rw [Finset.sum_eq_single s]
    · rw [hcol s (le_refl s), if_pos rfl, mul_one, hAs]
      -- final: -((-1)^q • ((-1)^(n+1) * A)) = (-1)^w • -((-1)^p • A)
      rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
      have hsgn : -((-1:ℂ)^q * ((-1:ℂ)^((w+p-q-1)+1) * AF s))
          = (-1:ℂ)^w * -((-1:ℂ)^p * AF s) := by
        have key : (-1:ℂ)^q * (-1:ℂ)^((w+p-q-1)+1) = (-1:ℂ)^w * (-1:ℂ)^p := by
          rw [← zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0),
            ← zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0) w p,
            show q + ((w+p-q-1)+1) = (w+p) by ring]
        rw [show -((-1:ℂ)^q * ((-1:ℂ)^((w+p-q-1)+1) * AF s))
              = -(((-1:ℂ)^q * (-1:ℂ)^((w+p-q-1)+1)) * AF s) by ring, key]
        ring
      rw [hsgn]
    · intro i _ hine
      rcases lt_or_gt_of_ne hine with hlt | hgt
      · rw [hcol i (by omega), if_neg hine, mul_zero, zero_mul]
      · rw [hAF_zero i hgt, mul_zero]
    · intro hcon; exact absurd (Finset.mem_range.mpr (by omega : s < R)) hcon
  · -- push each k-term into the inner ∑_i, then swap the order of summation.
    rw [show (∑ k ∈ Finset.range (s + 1), gBinom (s:ℤ) k *
            ((- (-1:ℂ)^((w+p-q-1) + (k:ℤ))) *
              ∑ i ∈ Finset.range R, ((-1:ℂ)^i * gBinom ((w+p-q-1) + (k:ℤ)) i) * AF i))
          = ∑ k ∈ Finset.range (s + 1), ∑ i ∈ Finset.range R,
              (gBinom (s:ℤ) k * (- (-1:ℂ)^((w+p-q-1) + (k:ℤ))) *
                ((-1:ℂ)^i * gBinom ((w+p-q-1) + (k:ℤ)) i)) * AF i from ?_]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul]
    · apply Finset.sum_congr rfl; intro k _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      ring

/-! ## Regime B (`s ≤ −1`, i.e. `w + q ≤ p`): the matching-mode diagonal via `FDIDw` + commutators. -/

/-- The matching-mode diagonal identity in regime B (`w + q ≤ p`, the pure `u`-first regime). -/
theorem qpdiag_regimeB (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0) (hw : 1 ≤ w)
    {p : ℤ} {a : V} (ha : a ∈ W.grading p) (hqpa : W.L 1 a = 0)
    {q : ℤ} {b : V} (hb : b ∈ W.grading q) (hsB : w + q ≤ p) :
    canBilin W hne (W.smul u (w + p - q - 1) a) b
      = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - (w + p - q - 1) - 2) b) := by
  -- edge: q < 0 ⟹ b = 0
  rcases lt_or_ge q 0 with hqneg | hq0
  · rw [eq_zero_of_mem_neg_grading W hqneg hb]
    simp [PreVertexAlgebra.smul_zero_right]
  -- now 0 ≤ q, and p ≥ w+q ≥ w+0 ≥ 1 so p ≥ 1.
  rw [show (2*w - (w + p - q - 1) - 2 : ℤ) = w - p + q - 1 by ring]
  -- m := p - q - w + 1 ≥ 1 (= -s), n := w + p - q - 1, with n = m + (2w-2).
  set m : ℕ := (p - q - w + 1).toNat with hm_def
  have hm : (p - q - w + 1 : ℤ) = (m : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  have hm1 : 1 ≤ m := by omega
  set N : ℕ := (w + p).toNat with hN_def
  have hN : (w + p : ℤ) ≤ (N : ℤ) := by rw [hN_def, Int.toNat_of_nonneg (by omega)]
  set Q : ℕ := q.toNat with hQ_def
  have hQ : (q : ℤ) = (Q : ℤ) := (Int.toNat_of_nonneg hq0).symm
  set n : ℕ := (w + p - q - 1).toNat with hn_def
  have hn : (w + p - q - 1 : ℤ) = (n : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  have hnm : n = m + (2 * w - 2).toNat := by omega
  have hNn : (N : ℤ) = (n : ℤ) + (Q : ℤ) + 1 := by omega
  -- expansions
  have hrhs : canBilin W hne a (W.smul u (w - p + q - 1) b)
      = -((-1:ℂ)^p • vacCoord W hne (W.smul a (2*p - 1) (W.smul u (w - p + q - 1) b))) := by
    have h := qp_match_rhs_expand_w (W := W) hne ha hqpa (W.smul u (w - p + q - 1) b)
    rw [eq_comm, ← neg_eq_iff_eq_neg] at h
    rw [← h]
  rw [hrhs, qp_match_lhs_expand_w hne hu hqpu ha hqpa hb]
  set A : ℂ := vacCoord W hne (W.smul a (2*p - 1) (W.smul u (w - p + q - 1) b)) with hA_def
  -- the atom h t
  set h : ℕ → ℂ := fun t => vacCoord W hne (W.smul (W.smul u (t:ℤ) a) (w + p + q - 2 - (t:ℤ)) b)
    with hh_def
  -- h low (s ≤ -1) and high
  have hh_low : ∀ t : ℕ, (t:ℤ) ≤ 2*w - 2 → h t = 0 := fun t ht => by
    rw [hh_def]; exact qpdiag_h_low hne hqp hu hqpu ha hqpa hb (by omega) ht
  have hh_high : ∀ t : ℕ, w + p - 1 < (t:ℤ) → h t = 0 := fun t ht => by
    rw [hh_def]; exact qpdiag_h_high hne hu ha hb ht
  -- commutator relations over range N
  have hcomm : ∀ j : ℕ, 1 ≤ j →
      (∑ t ∈ Finset.range N, gBinom (-(j:ℤ)) t * h t)
        = - vacCoord W hne (W.smul a (w + p + q - 2 + j) (W.smul u (-(j:ℤ)) b)) := by
    intro j hj
    rw [show (∑ t ∈ Finset.range N, gBinom (-(j:ℤ)) t * h t)
          = ∑ t ∈ Finset.range N, gBinom (-(j:ℤ)) t *
              vacCoord W hne (W.smul (W.smul u (t:ℤ) a) (w + p + q - 2 - (t:ℤ)) b) from
        Finset.sum_congr rfl (fun t _ => by rw [hh_def])]
    exact comm_rel_P_w hne hu hw ha hb N hN hj
  -- B(j) = 0 for 1 ≤ j ≤ m-1
  have hBzero : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
      (∑ t ∈ Finset.range N, gBinom (-(j:ℤ)) t * h t) = 0 := by
    intro j hj1 hjm
    rw [hcomm j hj1, vacCoord_a_low_mode_zero hne hqp ha hqpa
      (by omega : (w + p + q - 2 + (j:ℤ)) ≤ 2 * p - 2) (W.smul u (-(j:ℤ)) b), neg_zero]
  -- B(m) = -A
  have hBm : (∑ t ∈ Finset.range N, gBinom (-(m:ℤ)) t * h t) = - A := by
    rw [hcomm m hm1, hA_def,
      show (w + p + q - 2 + (m:ℤ)) = 2*p - 1 by omega, show (-(m:ℤ)) = w - p + q - 1 by omega]
  -- convert the LHS expansion to ∑_{k∈range(Q+1)} gBinom(-m,k)·h(n+k).
  have hLexp : (∑ k ∈ Finset.range ((q).toNat + 1), ((k.factorial:ℂ)⁻¹) •
        ((∏ l ∈ Finset.range k, (2 * (w : ℂ) - (((w + p - q - 1 : ℤ)):ℂ) - (l:ℤ) - 2)) •
          vacCoord W hne (W.smul (W.smul u ((w + p - q - 1) + k) a) (2*q - 1 - (k:ℤ)) b)))
      = ∑ k ∈ Finset.range (Q + 1), gBinom (-(m:ℤ)) k * h (n + k) := by
    rw [hQ_def]
    apply Finset.sum_congr rfl
    intro k _
    have hcoeff : ((k.factorial:ℂ)⁻¹) *
        (∏ l ∈ Finset.range k, (2 * (w : ℂ) - (((w + p - q - 1 : ℤ)):ℂ) - (l:ℤ) - 2))
        = gBinom (-(m:ℤ)) k := by
      rw [gBinom, div_eq_mul_inv, mul_comm]
      congr 1
      apply Finset.prod_congr rfl
      intro l _
      have h2 : (2 * (w : ℂ) - (((w + p - q - 1 : ℤ)):ℂ) - (l:ℤ) - 2)
          = ((-(m:ℤ) : ℤ):ℂ) - (l:ℂ) := by
        rw [show (-(m:ℤ)) = w - p + q - 1 by omega]; push_cast; ring
      rw [h2]
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, hcoeff, hh_def]
    have hnk : ((n + k : ℕ) : ℤ) = (w + p - q - 1) + (k:ℤ) := by push_cast [← hn]; ring
    simp only [hnk]
    rw [show (w + p + q - 2 - ((w + p - q - 1) + (k:ℤ))) = (2*q - 1 - (k:ℤ)) by ring]
  rw [hLexp]
  -- the binomial combination T := ∑_{j∈range m} β(j) · R(j+1),  β(j)=(-1)^(n+m-(j+1))C(n,m-(j+1)).
  set T : ℂ := ∑ j ∈ Finset.range m,
      ((-1:ℂ)^(n + m - (j+1)) * (n.choose (m - (j+1)) : ℂ)) *
        (∑ t ∈ Finset.range N, gBinom (-((j:ℤ)+1)) t * h t) with hT_def
  -- (i) T = Lsum, via FDIDw + swap.
  have hTL : T = ∑ k ∈ Finset.range (Q + 1), gBinom (-(m:ℤ)) k * h (n + k) := by
    rw [hT_def]
    -- distribute & swap to ∑_t [∑_j β(j) gBinom(-(j+1),t)] h t
    rw [show (∑ j ∈ Finset.range m,
            ((-1:ℂ)^(n + m - (j+1)) * (n.choose (m - (j+1)) : ℂ)) *
              (∑ t ∈ Finset.range N, gBinom (-((j:ℤ)+1)) t * h t))
          = ∑ t ∈ Finset.range N,
              (∑ j ∈ Finset.range m,
                (-1:ℂ)^(n + m - (j+1)) * (n.choose (m - (j+1)) : ℂ) * gBinom (-((j:ℤ)+1)) t) * h t from ?_]
    · -- per t: FDIDw collapses the j-sum
      have hper : ∀ t ∈ Finset.range N,
          (∑ j ∈ Finset.range m,
              (-1:ℂ)^(n + m - (j+1)) * (n.choose (m - (j+1)) : ℂ) * gBinom (-((j:ℤ)+1)) t) * h t
            = (if n ≤ t then gBinom (-(m:ℤ)) (t - n) else 0) * h t := by
        intro t _
        rcases le_or_gt t (2*w-2).toNat with htlow | hthigh
        · -- h t = 0
          rw [hh_low t (by omega), mul_zero, mul_zero]
        · -- t ≥ 2w-1, apply FDIDw (needs n < t + m, i.e. t > n - m = 2w-2)
          rw [FDIDw m n (by omega : m ≤ n) t (by omega : n < t + m)]
      rw [Finset.sum_congr rfl hper]
      -- reindex: only n ≤ t survives, t = n + k, k ∈ [0,Q]
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun t => n ≤ t)]
      rw [show (∑ t ∈ Finset.filter (fun t => ¬ n ≤ t) (Finset.range N),
              (if n ≤ t then gBinom (-(m:ℤ)) (t - n) else 0) * h t) = 0 from
          Finset.sum_eq_zero (fun t ht => by
            rw [Finset.mem_filter] at ht; rw [if_neg ht.2, zero_mul])]
      rw [add_zero]
      -- the filter {t ∈ range N | n ≤ t} ↔ map (· + n) (range (Q+1))
      rw [show Finset.filter (fun t => n ≤ t) (Finset.range N)
            = Finset.map (addLeftEmbedding n) (Finset.range (Q + 1)) from ?_]
      · rw [Finset.sum_map]
        apply Finset.sum_congr rfl
        intro k _
        simp only [addLeftEmbedding_apply]
        rw [if_pos (by omega), show (n + k - n) = k by omega, add_comm n k]
      · ext t
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, addLeftEmbedding_apply]
        constructor
        · rintro ⟨htN, hnt⟩; exact ⟨t - n, by omega, by omega⟩
        · rintro ⟨k, hk, rfl⟩
          refine ⟨?_, by omega⟩
          have : (n + k : ℤ) < (N:ℤ) := by rw [hNn]; omega
          omega
    · -- distribute β(j) into the t-sum, then swap
      rw [show (∑ j ∈ Finset.range m,
              ((-1:ℂ)^(n + m - (j+1)) * (n.choose (m - (j+1)) : ℂ)) *
                (∑ t ∈ Finset.range N, gBinom (-((j:ℤ)+1)) t * h t))
            = ∑ j ∈ Finset.range m, ∑ t ∈ Finset.range N,
                ((-1:ℂ)^(n + m - (j+1)) * (n.choose (m - (j+1)) : ℂ) * gBinom (-((j:ℤ)+1)) t) * h t from ?_]
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro t _
        rw [Finset.sum_mul]
      · apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro t _; ring
  -- (ii) T = (-1)^(n+1) · A, via comm relations (only j+1 = m survives).
  have hTA : T = (-1:ℂ)^((n:ℤ)+1) * A := by
    rw [hT_def, Finset.sum_eq_single (m - 1)]
    · -- j = m-1 term:  β(m-1) = (-1)^n,  R(m) = -A
      rw [show (n + m - (m - 1 + 1)) = n by omega, show (m - (m - 1 + 1)) = 0 by omega,
        Nat.choose_zero_right, Nat.cast_one, mul_one,
        show ((m-1:ℕ):ℤ) + 1 = (m:ℤ) by omega, hBm,
        show (-1:ℂ)^((n:ℤ)+1) = (-1:ℂ)^(n:ℤ) * (-1) by
          rw [zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0) (n:ℤ) 1, zpow_one],
        zpow_natCast]
      ring
    · -- j ≠ m-1 (j ∈ range m, so j ≤ m-1, hence j < m-1): R(j+1)=0 since j+1 ≤ m-1
      intro j hj hjne
      rw [Finset.mem_range] at hj
      rw [show (-((j:ℤ)+1)) = (-((j+1:ℕ):ℤ)) by push_cast; ring,
        hBzero (j+1) (by omega) (by omega), mul_zero]
    · intro hcon; exact absurd (Finset.mem_range.mpr (by omega : m - 1 < m)) hcon
  -- combine: Lsum = (-1)^(n+1)·A; finish with the sign.
  rw [← hTL, hTA]
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have hsgn : -((-1:ℂ)^q * ((-1:ℂ)^((n:ℤ)+1) * A)) = (-1:ℂ)^w * -((-1:ℂ)^p * A) := by
    have key : (-1:ℂ)^q * (-1:ℂ)^((n:ℤ)+1) = (-1:ℂ)^w * (-1:ℂ)^p := by
      rw [← zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0) w p,
        show q + ((n:ℤ)+1) = (w+p) by rw [← hn]; ring]
    rw [show -((-1:ℂ)^q * ((-1:ℂ)^((n:ℤ)+1) * A)) = -(((-1:ℂ)^q * (-1:ℂ)^((n:ℤ)+1)) * A) by ring,
      key]
    ring
  rw [hsgn]

/-! ## Assembly: `QPDiagW` and the main theorem `canBilin_qp_qp_adj`. -/

/-- `QPDiagW` for `w ≥ 1`: combine regime A (`p ≤ w+q−1`) and regime B (`p ≥ w+q`). -/
theorem qpdiagW_holds (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0) (hw : 1 ≤ w) :
    QPDiagW hne hqp hu hqpu := by
  intro p a ha hqpa q b hb
  rcases le_or_gt p (w + q - 1) with hcase | hcase
  · exact qpdiag_regimeA hne hqp hu hqpu hw ha hqpa hb hcase
  · exact qpdiag_regimeB hne hqp hu hqpu hw ha hqpa hb (by omega)

/-- **MAIN THEOREM.** General-weight quasi-primary skew-adjointness of the canonical invariant form:
for `u ∈ 𝒱_w` and `a ∈ 𝒱_p` both quasi-primary (`L₁ = 0`), and ALL modes `n`, all `b`,
`canBilin(u₍ₙ₎a, b) = (−1)^w • canBilin(a, u₍2w−n−2₎b)`. -/
theorem canBilin_qp_qp_adj (hne : W.vacuum ≠ 0) (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
    {w : ℤ} {u : V} (hu : u ∈ W.grading w) (hqpu : W.L 1 u = 0)
    {p : ℤ} {a : V} (ha : a ∈ W.grading p) (hqpa : W.L 1 a = 0) (n : ℤ) (b : V) :
    canBilin W hne (W.smul u n a) b = (-1:ℂ)^w • canBilin W hne a (W.smul u (2*w - n - 2) b) := by
  rcases le_or_gt w 0 with hw | hw
  · exact canBilin_qp_qp_adj_w_le_zero hne hw hu n a b
  · exact qp_qp_adj_of_diag hne hqp hu hqpu (qpdiagW_holds hne hqp hu hqpu (by omega)) ha hqpa n b


end VOA
