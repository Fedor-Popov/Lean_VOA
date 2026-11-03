import VOA.Classification.COne.OrbOddData16
import VOA.Classification.COne.OrbOddZhu
import VOA.Classification.COne.PlusRat3Iterate
import VOA.Classification.COne.OrbSpanGlue

/-!
# OrbOdd (4): the products `u₍ₖ₎v` of two Virasoro primaries, by a Virasoro-only chain

Generic: any VOA `W` of central charge `1`, primaries `u ∈ W₉`, `v ∈ W₁₆` (`L(m)u = L(m)v = 0`,
`m ≥ 1`) with `s₇ u = 0` (the level-seven singular vector of `M(1,9)`), and a submodule `S`
(the "odd sector") stable under the `L(n)`, containing `u` and all `u₍ₖ₎v`, in which
primaries of weight `≤ 25` are multiples of `u` in weight `9` and vanish otherwise.

* `L_smul_primary`: `L(n) a₍ₖ₎ y = a₍ₖ₎ L(n) y + ((h-1)(n+1) - k) a₍ₙ₊ₖ₎ y` for a primary `a ∈ W_h`.
* `chain_L1`, `chain_L2`: the certified recursion `L(1)x_k = (16-k)x_{k+1}`,
  `L(2)x_k = (24-k)x_{k+2}` for the explicit Virasoro words `x_k = xsN (15-k)` on `u`
  (`OrbOddData1` … `OrbOddData16`, kernel-checked).
* `chain_main`: `∃ c, u₍₁₅₎v = c u ∧ ∀ N ≤ 16, u₍₁₅₋N₎ v = c · x_{15-N}`.

The proof is the Virasoro recursion: `y_N = u₍₁₅₋N₎v - c x_{15-N}` satisfies
`L(1)y_N = (N+1) y_{N-1}`, `L(2) y_N = (N+9) y_{N-2}`, so by induction it is a primary of weight
`9 + N` in `S`, hence zero.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbOdd

open VOA VertexOperatorAlgebra OrbSpan

/-- The chain vectors by level `N` (`x_{15-N}`). -/
def xsN : ℕ → VVec
  | 0 => xvTop | 1 => xv1 | 2 => xv2 | 3 => xv3 | 4 => xv4 | 5 => xv5 | 6 => xv6 | 7 => xv7
  | 8 => xv8 | 9 => xv9 | 10 => xv10 | 11 => xv11 | 12 => xv12 | 13 => xv13 | 14 => xv14
  | 15 => xv15 | 16 => xv16 | _ => []

/-- Every word of `xsN N` has level `N` and positive letters. -/
def levelOK (N : ℕ) : Bool := (xsN N).all fun p => p.2.sum == N && posW p.2

set_option maxRecDepth 100000 in
theorem levelOK_all : ∀ N : Fin 17, levelOK N = true := by decide +kernel

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## Generic Virasoro facts -/

/-- `L(1) y = L(2) y = 0` forces `L(m) y = 0` for all `m ≥ 1`. -/
theorem L_pos_of_L1_L2 {y : 𝒱} (h1 : W.L 1 y = 0) (h2 : W.L 2 y = 0) :
    ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) y = 0
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simpa using h1
  | 2, _ => by simpa using h2
  | m + 3, _ => by
    have ih := L_pos_of_L1_L2 h1 h2 (m + 2) (by omega)
    have e := L_L_apply (W := W) 1 ((m + 2 : ℕ) : ℤ) y
    rw [ih, map_zero, h1, map_zero, zero_add, if_neg (by omega)] at e
    have hne : ((1 : ℤ) : ℂ) - (((m + 2 : ℕ) : ℤ) : ℂ) ≠ 0 := by
      push_cast; intro h; have : (m : ℂ) = -1 := by linear_combination -h
      exact absurd (by exact_mod_cast this : (m : ℤ) = -1) (by omega)
    have e2 : (((1 : ℤ) : ℂ) - (((m + 2 : ℕ) : ℤ) : ℂ)) • W.L (1 + ((m + 2 : ℕ) : ℤ)) y = 0 := by
      rw [add_zero] at e; exact e.symm
    rw [smul_eq_zero] at e2
    rcases e2 with h | h
    · exact absurd h hne
    · rw [show ((m + 3 : ℕ) : ℤ) = 1 + ((m + 2 : ℕ) : ℤ) by push_cast; ring]; exact h

/-- The commutator of `L(n)` with the modes of a primary `a ∈ W_h`. -/
theorem L_smul_primary {a : 𝒱} {h : ℤ} (ha : a ∈ W.grading h)
    (hp : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) a = 0) (n k : ℤ) (y : 𝒱) :
    W.L n (W.smul a k y) = W.smul a k (W.L n y) +
      (((h - 1) * (n + 1) - k : ℤ) : ℂ) • W.smul a (n + k) y := by
  let A := adjointWeakModule W
  have hm : ∀ (b : 𝒱) (p : ℤ) (z : 𝒱), mode (A.YM b) p z = W.smul b p z := fun b p z => by
    rw [PreVertexAlgebra.smul_def]; rfl
  have hc := mode_commutator A W.conformalVector a y (n + 1) k
  have hsupp : (Function.support fun i : ℤ => cbz (n + 1) i • mode (A.YM
      (W.smul W.conformalVector i a)) (n + 1 + k - i) y) ⊆ ((({0, 1} : Finset ℤ)) : Set ℤ) := by
    intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hne
    push Not at hne
    apply hi
    rcases lt_or_ge i 0 with hneg | hpos
    · rw [cbz_apply_neg _ hneg, zero_smul]
    · have h0 := hp (i - 1).toNat (by omega)
      rw [VertexOperatorAlgebra.L_def, show (((i - 1).toNat : ℕ) : ℤ) + 1 = i by omega] at h0
      rw [show W.smul W.conformalVector i a = 0 by rw [PreVertexAlgebra.smul_def]; exact h0,
        map_zero]
      simp
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair (by norm_num)] at hc
  have e0 : W.smul W.conformalVector 0 a = W.L (-1) a := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]; norm_num
  have e1 : W.smul W.conformalVector 1 a = (h : ℂ) • a := by
    have := W.L_zero_grading a ha
    rw [VertexOperatorAlgebra.L_def, zero_add, ← PreVertexAlgebra.smul_def] at this
    exact this
  rw [cbz_zero, one_smul, e0, PlusRat3.T_mode A, PlusRat3.cbz_one', e1, map_smul] at hc
  simp only [mode_smul, LinearMap.smul_apply, hm] at hc
  have hL : ∀ z : 𝒱, W.L n z = W.smul W.conformalVector (n + 1) z := fun z => by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]
  rw [hL, hL, ← sub_eq_iff_eq_add', hc, show n + 1 + k - 0 - 1 = n + k by ring,
    show n + 1 + k - 1 = n + k by ring]
  push_cast
  module

/-! ## Evaluated words: grading, lower descendants, stable submodules -/

theorem evV_mem_grading {x : 𝒱} {h : ℤ} (hx : x ∈ W.grading h) {N : ℕ} {v : VVec}
    (hv : ∀ p ∈ v, p.2.sum = N) : evV W x v ∈ W.grading (h + N) := by
  induction v with
  | nil => exact Submodule.zero_mem _
  | cons p v ih =>
    rw [evV_cons]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (ih fun q hq => hv q (by simp [hq]))
    have := evW_mem_grading W hx p.2
    rwa [hv p (by simp)] at this

theorem evV_mem_lowerDesc {x : 𝒱} {h : ℤ} (hx : x ∈ W.grading h) {N : ℕ} {v : VVec}
    (hv : ∀ p ∈ v, p.2.sum = N ∧ p.2 ≠ [] ∧ posW p.2 = true) :
    evV W x v ∈ lowerDesc W (h + N) := by
  induction v with
  | nil => exact Submodule.zero_mem _
  | cons p v ih =>
    rw [evV_cons]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (ih fun q hq => hv q (by simp [hq]))
    obtain ⟨hs, hne, hpos⟩ := hv p (by simp)
    obtain ⟨n, w, hw⟩ : ∃ n w, p.2 = n :: w := by
      cases h' : p.2 with
      | nil => exact absurd h' hne
      | cons n w => exact ⟨n, w, rfl⟩
    rw [hw] at hs hpos ⊢
    simp only [posW, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hpos
    obtain ⟨hn1, -⟩ := hpos
    simp only [List.sum_cons] at hs
    simp only [evW]
    refine Submodule.subset_span ⟨n - 1, evW W x w, ?_, ?_⟩
    · have := evW_mem_grading W hx w
      have e : h + (N : ℤ) - ((n - 1 : ℕ) : ℤ) - 1 = h + ((w.sum : ℕ) : ℤ) := by omega
      rw [e]; exact this
    · rw [show -((n - 1 : ℕ) : ℤ) - 1 = -(n : ℤ) by omega]

theorem evV_mem_stable (S : Submodule ℂ 𝒱) (hSL : ∀ (n : ℤ) (y : 𝒱), y ∈ S → W.L n y ∈ S)
    {x : 𝒱} (hx : x ∈ S) (v : VVec) : evV W x v ∈ S := by
  have hw : ∀ w : List ℕ, evW W x w ∈ S := by
    intro w; induction w with
    | nil => exact hx
    | cons n w ih => exact hSL _ _ ih
  induction v with
  | nil => exact Submodule.zero_mem _
  | cons p v ih => rw [evV_cons]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hw _)) ih

/-! ## The certified chain -/

section Chain

variable {x : 𝒱} (hc : W.centralCharge = ((1 : ℚ) : ℂ))
  (hx : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) x = 0) (hx0 : W.L 0 x = ((9 : ℚ) : ℂ) • x)
  (hs7 : evV W x s7v = 0)
include hc hx hx0 hs7

theorem chain_L1 : ∀ N : ℕ, 1 ≤ N → N ≤ 16 →
    W.L 1 (evV W x (xsN N)) = ((N + 1 : ℕ) : ℂ) • evV W x (xsN (N - 1)) := by
  intro N h1 h2
  have key : ∀ {c : Cache} {xv prev wit : VVec} {α : ℚ},
      cacheOK 9 1 64 1 c = true → chkGen c xv prev wit α = true →
      W.L 1 (evV W x xv) = (α : ℂ) • evV W x prev := fun hcok hk => by
    have := chkGen_sound hc hx hx0 hs7 (m := 1) hcok hk
    simpa using this
  interval_cases N
  · simpa [xsN] using key ca1_1_ok chkA1_ok
  · simpa [xsN] using key ca1_2_ok chkA2_ok
  · simpa [xsN] using key ca1_3_ok chkA3_ok
  · simpa [xsN] using key ca1_4_ok chkA4_ok
  · simpa [xsN] using key ca1_5_ok chkA5_ok
  · simpa [xsN] using key ca1_6_ok chkA6_ok
  · simpa [xsN] using key ca1_7_ok chkA7_ok
  · simpa [xsN] using key ca1_8_ok chkA8_ok
  · simpa [xsN] using key ca1_9_ok chkA9_ok
  · simpa [xsN] using key ca1_10_ok chkA10_ok
  · simpa [xsN] using key ca1_11_ok chkA11_ok
  · simpa [xsN] using key ca1_12_ok chkA12_ok
  · simpa [xsN] using key ca1_13_ok chkA13_ok
  · simpa [xsN] using key ca1_14_ok chkA14_ok
  · simpa [xsN] using key ca1_15_ok chkA15_ok
  · simpa [xsN] using key ca1_16_ok chkA16_ok

theorem chain_L2 : ∀ N : ℕ, 1 ≤ N → N ≤ 16 →
    W.L 2 (evV W x (xsN N)) =
      ((N + 9 : ℕ) : ℂ) • evV W x (if N = 1 then [] else xsN (N - 2)) := by
  intro N h1 h2
  have key : ∀ {c : Cache} {xv prev wit : VVec} {α : ℚ},
      cacheOK 9 1 64 2 c = true → chkGen c xv prev wit α = true →
      W.L 2 (evV W x xv) = (α : ℂ) • evV W x prev := fun hcok hk => by
    have := chkGen_sound hc hx hx0 hs7 (m := 2) hcok hk
    simpa using this
  interval_cases N
  · simpa [xsN] using key ca2_1_ok chkB1_ok
  · simpa [xsN] using key ca2_2_ok chkB2_ok
  · simpa [xsN] using key ca2_3_ok chkB3_ok
  · simpa [xsN] using key ca2_4_ok chkB4_ok
  · simpa [xsN] using key ca2_5_ok chkB5_ok
  · simpa [xsN] using key ca2_6_ok chkB6_ok
  · simpa [xsN] using key ca2_7_ok chkB7_ok
  · simpa [xsN] using key ca2_8_ok chkB8_ok
  · simpa [xsN] using key ca2_9_ok chkB9_ok
  · simpa [xsN] using key ca2_10_ok chkB10_ok
  · simpa [xsN] using key ca2_11_ok chkB11_ok
  · simpa [xsN] using key ca2_12_ok chkB12_ok
  · simpa [xsN] using key ca2_13_ok chkB13_ok
  · simpa [xsN] using key ca2_14_ok chkB14_ok
  · simpa [xsN] using key ca2_15_ok chkB15_ok
  · simpa [xsN] using key ca2_16_ok chkB16_ok

end Chain

/-! ## The main chain theorem -/

theorem levelOK_spec (N : ℕ) (hN : N ≤ 16) :
    ∀ p ∈ xsN N, p.2.sum = N ∧ posW p.2 = true := by
  have h := levelOK_all ⟨N, by omega⟩
  simp only [levelOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  exact h

/-- The products `u₍ₖ₎v`, `k ≥ -1`, are the explicit Virasoro words `c · x_k` on `u`. -/
theorem chain_main {u v : 𝒱} (hc : W.centralCharge = ((1 : ℚ) : ℂ))
    (hu : u ∈ W.grading 9) (hup : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) u = 0)
    (hv : v ∈ W.grading 16) (hvp : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) v = 0)
    (hs7 : evV W u s7v = 0) (S : Submodule ℂ 𝒱) (huS : u ∈ S)
    (hSL : ∀ (n : ℤ) (y : 𝒱), y ∈ S → W.L n y ∈ S) (hkS : ∀ k : ℤ, W.smul u k v ∈ S)
    (hP : ∀ N : ℤ, N ≤ 25 → ∀ y ∈ S, y ∈ prim W N →
      (N = 9 → ∃ c : ℂ, y = c • u) ∧ (N ≠ 9 → y = 0)) :
    ∃ c : ℂ, W.smul u 15 v = c • u ∧
      ∀ N : ℕ, N ≤ 16 → W.smul u (15 - (N : ℤ)) v = c • evV W u (xsN N) := by
  have hu0 : W.L 0 u = ((9 : ℚ) : ℂ) • u := by
    rw [W.L_zero_grading u hu]; norm_num
  -- the recursion for `u₍ₖ₎v`
  have hrec : ∀ (n k : ℤ), W.L n (W.smul u k v) = W.smul u k (W.L n v) +
      (((9 - 1) * (n + 1) - k : ℤ) : ℂ) • W.smul u (n + k) v :=
    fun n k => L_smul_primary hu hup n k v
  have hL1 : ∀ k : ℤ, W.L 1 (W.smul u k v) = ((16 - k : ℤ) : ℂ) • W.smul u (k + 1) v := by
    intro k
    rw [hrec, show W.L 1 v = 0 by simpa using hvp 1 le_rfl, PreVertexAlgebra.smul_zero_right,
      zero_add, show (1 : ℤ) + k = k + 1 by ring]
    congr 1
  have hL2 : ∀ k : ℤ, W.L 2 (W.smul u k v) = ((24 - k : ℤ) : ℂ) • W.smul u (k + 2) v := by
    intro k
    rw [hrec, show W.L 2 v = 0 by simpa using hvp 2 (by norm_num),
      PreVertexAlgebra.smul_zero_right, zero_add, show (2 : ℤ) + k = k + 2 by ring]
    congr 1
  have hgr : ∀ k : ℤ, W.smul u k v ∈ W.grading (24 - k) := by
    intro k
    have := W.grading_mode u hu v hv k
    convert this using 2; ring
  -- Step 1: `u₍ₖ₎v = 0` for `k ≥ 16`
  have step1 : ∀ i : ℕ, ∀ j : ℕ, 9 ≤ j + i → W.smul u (16 + (j : ℤ)) v = 0 := by
    intro i
    induction i with
    | zero =>
      intro j hj
      have hg := hgr (16 + j)
      rw [W.positivity _ (by omega)] at hg
      exact (Submodule.mem_bot ℂ).mp hg
    | succ i ih =>
      intro j hj
      by_cases hj' : 9 ≤ j + i
      · exact ih j hj'
      · have e1 := hL1 (16 + j)
        have e2 := hL2 (16 + j)
        rw [show (16 + (j : ℤ)) + 1 = 16 + ((j + 1 : ℕ) : ℤ) by push_cast; ring,
          ih (j + 1) (by omega), smul_zero] at e1
        rw [show (16 + (j : ℤ)) + 2 = 16 + ((j + 2 : ℕ) : ℤ) by push_cast; ring,
          ih (j + 2) (by omega), smul_zero] at e2
        have hprim : W.smul u (16 + (j : ℤ)) v ∈ prim W (24 - (16 + j)) := by
          rw [mem_prim]
          refine ⟨hgr _, fun m => ?_⟩
          have := L_pos_of_L1_L2 e1 e2 (m + 1) (by omega)
          simpa using this
        exact ((hP _ (by omega) _ (hkS _) hprim).2 (by omega))
  have hzero : ∀ k : ℤ, 16 ≤ k → W.smul u k v = 0 := by
    intro k hk
    have := step1 9 (k - 16).toNat (by omega)
    rwa [show (16 : ℤ) + ((k - 16).toNat : ℤ) = k by omega] at this
  -- Step 2: `u₍₁₅₎v = c u`
  have hprim15 : W.smul u 15 v ∈ prim W 9 := by
    rw [mem_prim]
    refine ⟨by simpa using hgr 15, fun m => ?_⟩
    have e1 := hL1 15
    have e2 := hL2 15
    rw [hzero (15 + 1) (by norm_num), smul_zero] at e1
    rw [hzero (15 + 2) (by norm_num), smul_zero] at e2
    have := L_pos_of_L1_L2 e1 e2 (m + 1) (by omega)
    simpa using this
  obtain ⟨c, hc15⟩ := (hP 9 (by norm_num) _ (hkS 15) hprim15).1 rfl
  refine ⟨c, hc15, ?_⟩
  -- Step 3: induction on the level
  have hs7' := hs7
  have hxL1 := chain_L1 hc hup hu0 hs7
  have hxL2 := chain_L2 hc hup hu0 hs7
  have hxs0 : evV W u (xsN 0) = u := by simp [xsN, xvTop, evV, evW]
  have key : ∀ N : ℕ, N ≤ 16 → ∀ M : ℕ, M ≤ N →
      W.smul u (15 - (M : ℤ)) v = c • evV W u (xsN M) := by
    intro N
    induction N with
    | zero =>
      intro _ M hM
      obtain rfl : M = 0 := by omega
      rw [hxs0]; simpa using hc15
    | succ N ih =>
      intro hN M hM
      rcases Nat.lt_or_ge M (N + 1) with hlt | hge
      · exact ih (by omega) M (by omega)
      · obtain rfl : M = N + 1 := by omega
        set y := W.smul u (15 - ((N + 1 : ℕ) : ℤ)) v - c • evV W u (xsN (N + 1)) with hy
        have hy1 : W.L 1 y = 0 := by
          rw [hy, map_sub, map_smul, hL1, hxL1 (N + 1) (by omega) hN,
            show 15 - ((N + 1 : ℕ) : ℤ) + 1 = 15 - (N : ℤ) by push_cast; ring,
            show N + 1 - 1 = N by omega, ih (by omega) N le_rfl]
          push_cast
          rw [smul_smul, smul_smul, mul_comm]
          ring_nf
          rw [sub_self]
        have hy2 : W.L 2 y = 0 := by
          rw [hy, map_sub, map_smul, hL2, hxL2 (N + 1) (by omega) hN,
            show 15 - ((N + 1 : ℕ) : ℤ) + 2 = 15 - ((N : ℤ) - 1) by push_cast; ring]
          by_cases hN0 : N = 0
          · subst hN0
            rw [hzero _ (by norm_num), smul_zero]
            simp [evV]
          · rw [if_neg (by omega), show N + 1 - 2 = N - 1 by omega]
            have := ih (by omega) (N - 1) (by omega)
            rw [show 15 - ((N - 1 : ℕ) : ℤ) = 15 - ((N : ℤ) - 1) by omega] at this
            rw [this]
            push_cast
            rw [smul_smul, smul_smul, mul_comm]
            ring_nf
            rw [sub_self]
        have hyS : y ∈ S :=
          Submodule.sub_mem _ (hkS _) (Submodule.smul_mem _ _ (evV_mem_stable S hSL huS _))
        have hspec := levelOK_spec (N + 1) hN
        have hyg : y ∈ W.grading (9 + ((N + 1 : ℕ) : ℤ)) := by
          refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)
          · convert hgr (15 - ((N + 1 : ℕ) : ℤ)) using 2; ring
          · exact evV_mem_grading hu (fun p hp => (hspec p hp).1)
        have hprim : y ∈ prim W (9 + ((N + 1 : ℕ) : ℤ)) := by
          rw [mem_prim]
          refine ⟨hyg, fun m => ?_⟩
          have := L_pos_of_L1_L2 hy1 hy2 (m + 1) (by omega)
          simpa using this
        have h0 := (hP _ (by omega) y hyS hprim).2 (by omega)
        exact sub_eq_zero.mp h0
  exact fun N hN => key N hN N le_rfl

end VOA.Classification.COne.OrbOdd
