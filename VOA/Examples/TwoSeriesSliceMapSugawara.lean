/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesSliceMapWhittaker
import VOA.Examples.AffineSl2Virasoro

/-!
# The Sugawara modes on the Whittaker coinvariants

The creation Sugawara modes `L_n` (`n ≤ -1`) of `V^k(sl₂)` normalise the Whittaker ideal
(`Lm_whitIdeal`): `[L_n, x_m] = -m x_{m+n}` and, for `x ∈ {f, h}`, `m ≤ -1`, `n ≤ -1`, the mode
`x_{m+n}` has `χ = 0`.  Hence they descend to operators `Lt n = W₀ ∘ L_n ∘ sE` on
`E = ℂ[X₀, X₁, …]` with `W₀ ∘ L_n = Lt n ∘ W₀` exactly (`W0_Lm`).

## Results

* `W0_Lm` — the exact intertwining;
* `Lt_comm` — the Virasoro relations `[Lt m, Lt n] = (m - n) Lt (m+n)` (`m, n ≤ -1`);
* `Lt_neg_one_X` — `Lt (-1)` acts on generators as the derivation `X_j ↦ (j+1) X_{j+1}`;
* `Lt_one` — `Lt (-j-2) 1 = cL · X_j` up to a constant, `cL = -2 c₀ = -1/(k+2) ≠ 0`;
* `Lt_tri` — **triangularity**: on polynomials of total degree `≤ d`,
  `Lt (-j-2) P = cL · X_j P + (total degree ≤ d)`;
* `Lm_KC` — the Sugawara modes raise the Kazhdan weight by at most `2` and preserve charge.

Everything is proved; no new axiom.
-/

namespace VOA.TwoSeries.SliceMap

open VOA.AffineVOA MvPolynomial VOA.AffineVOA.SugawaraCov

noncomputable section

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-! ## §1  The Sugawara modes -/

/-- The Sugawara mode `L_n = ω_{(n+1)}`. -/
def Lm (n : ℤ) : Module.End ℂ (WakModule k) := mode (YA k hk (omegaA k)) (n + 1)

theorem Lm_J (n : ℤ) (a : Fin 3) (ν : ℤ) (y : WakModule k) :
    Lm k hk n (J k a ν y) = J k a ν (Lm k hk n y) + ((-ν : ℤ) : ℂ) • J k a (n + ν) y :=
  Vir.Lcomm_J_apply k hk n a ν y

theorem Lm_vac {n : ℤ} (hn : -1 ≤ n) : Lm k hk n (vacuumA k) = 0 :=
  (YA_creation k hk (omegaA k)).2 (n + 1) (by omega)

theorem Lm_neg_two_vac : Lm k hk (-2) (vacuumA k) = omegaA k := by
  have h := (YA_creation k hk (omegaA k)).1
  rw [Lm, show (-2 : ℤ) + 1 = -1 by norm_num]
  exact h

theorem Lm_comm (m n : ℤ) (hmn : m + n ≠ 0) (y : WakModule k) :
    Lm k hk m (Lm k hk n y) = Lm k hk n (Lm k hk m y) + ((m : ℂ) - n) • Lm k hk (m + n) y := by
  have h := congrArg (fun T : Module.End ℂ (WakModule k) => T y) (Vir.hYA_virasoro k hk m n)
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, if_neg hmn, add_zero] at h
  rw [sub_eq_iff_eq_add] at h
  rw [Lm, Lm, Lm, h, add_comm]

/-! ## §2  The Sugawara modes normalise the Whittaker ideal -/

theorem Lm_whitIdeal {n : ℤ} (hn : n ≤ -1) {y : WakModule k} (hy : y ∈ whitIdeal k) :
    Lm k hk n y ∈ whitIdeal k := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      rcases hx with (⟨v, rfl⟩ | ⟨d, v, rfl⟩) | ⟨d, v, rfl⟩
      · rw [map_add, Lm_J]
        have he : n + -1 = -(((-n - 1).toNat : ℕ) : ℤ) - 2 := by omega
        rw [he, show J k 1 (-1) (Lm k hk n v) + ((-(-1) : ℤ) : ℂ) •
            J k 1 (-(((-n - 1).toNat : ℕ) : ℤ) - 2) v + Lm k hk n v =
            (J k 1 (-1) (Lm k hk n v) + Lm k hk n v) +
              ((-(-1) : ℤ) : ℂ) • J k 1 (-(((-n - 1).toNat : ℕ) : ℤ) - 2) v by abel]
        exact Submodule.add_mem _ (fOne_mem k _) (Submodule.smul_mem _ _ (fHigh_mem k _ _))
      · rw [Lm_J]
        have he : n + (-(d : ℤ) - 2) = -((d + (-n).toNat : ℕ) : ℤ) - 2 := by push_cast; omega
        rw [he]
        exact Submodule.add_mem _ (fHigh_mem k _ _) (Submodule.smul_mem _ _ (fHigh_mem k _ _))
      · rw [Lm_J]
        have he : n + (-(d : ℤ) - 1) = -((d + (-n).toNat : ℕ) : ℤ) - 1 := by push_cast; omega
        rw [he]
        exact Submodule.add_mem _ (h_mem k _ _) (Submodule.smul_mem _ _ (h_mem k _ _))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-! ## §3  The descended operators -/

/-- **The descended Sugawara mode** `Lt n = W₀ ∘ L_n ∘ sE` on `E`. -/
def Lt (n : ℤ) : EPoly →ₗ[ℂ] EPoly := (W0 k hk).comp ((Lm k hk n).comp (sE k))

/-- **Exact intertwining** `W₀ ∘ L_n = Lt n ∘ W₀` (`n ≤ -1`). -/
theorem W0_Lm {n : ℤ} (hn : n ≤ -1) (y : WakModule k) :
    W0 k hk (Lm k hk n y) = Lt k hk n (W0 k hk y) := by
  have h := W0_whitIdeal k hk (Lm_whitIdeal k hk hn (sub_sE_W0_mem k hk y))
  rw [map_sub, map_sub, sub_eq_zero] at h
  exact h

theorem Lt_comm {m n : ℤ} (hm : m ≤ -1) (hn : n ≤ -1) (P : EPoly) :
    Lt k hk m (Lt k hk n P) = Lt k hk n (Lt k hk m P) + ((m : ℂ) - n) • Lt k hk (m + n) P := by
  have h := congrArg (W0 k hk) (Lm_comm k hk m n (by omega) (sE k P))
  rw [map_add, map_smul] at h
  rw [W0_Lm k hk hm, W0_Lm k hk hn, W0_Lm k hk hn, W0_Lm k hk hm, W0_Lm k hk (by omega),
    W0_sE] at h
  exact h

theorem Lt_one_neg_one : Lt k hk (-1) 1 = 0 := by
  rw [Lt, LinearMap.comp_apply, LinearMap.comp_apply, sE_one, Lm_vac k hk le_rfl, map_zero]

theorem sE_X (j : ℕ) : sE k (X j) = rword k [eL j] := by
  rw [X, sE_monomial, eword, Finsupp.toMultiset_single, one_smul, Multiset.toList_singleton]
  rfl

theorem W0_rword_eL (j : ℕ) : W0 k hk (rword k [eL j]) = X j := by
  rw [W0_rword_sorted k hk _ (List.pairwise_singleton _ _), classicalW_cons, eL, letterVal_e,
    classicalW_nil, mul_one]

theorem Lt_neg_one_X (j : ℕ) : Lt k hk (-1) (X j) = ((j : ℂ) + 1) • X (j + 1) := by
  rw [Lt, LinearMap.comp_apply, LinearMap.comp_apply, sE_X, rword_cons, Lm_J, rword_nil,
    Lm_vac k hk le_rfl, map_zero, zero_add, map_smul]
  have : J k (col (eL j)) (-1 + (-(dep (eL j) : ℤ) - 1)) (vacuumA k) = rword k [eL (j + 1)] := by
    rw [rword_cons, rword_nil]
    congr 1
    simp [eL]; ring_nf
  rw [this, W0_rword_eL]
  congr 1
  simp [eL]; ring

theorem Lt_const_neg_one (a : ℂ) : Lt k hk (-1) (MvPolynomial.C a) = 0 := by
  rw [C_eq_smul_one, map_smul, Lt_one_neg_one, smul_zero]

/-! ## §4  The Kazhdan weight of Sugawara modes -/

/-- A list of creation letters as an operator. -/
def rwordOp (l : List RLetter) : Module.End ℂ (WakModule k) :=
  (l.map fun q => J k (col q) (-(dep q : ℤ) - 1)).prod

theorem rwordOp_cons (q : RLetter) (l : List RLetter) (z : WakModule k) :
    rwordOp k (q :: l) z = J k (col q) (-(dep q : ℤ) - 1) (rwordOp k l z) := rfl

theorem rwordOp_rword (l l' : List RLetter) : rwordOp k l (rword k l') = rword k (l ++ l') := by
  induction l with
  | nil => rfl
  | cons q l ih => rw [rwordOp_cons, ih, List.cons_append, rword_cons]

theorem rwordOp_vac (l : List RLetter) : rwordOp k l (vacuumA k) = rword k l := by
  simpa using rwordOp_rword k l []

theorem rwordOp_KC (l : List RLetter) {p : ℕ} {q : ℤ} {z : WakModule k} (hz : z ∈ KC k p q) :
    rwordOp k l z ∈ KC k (Kl l + p) (chl l + q) := by
  induction l with
  | nil => simpa using hz
  | cons r l ih =>
      rw [rwordOp_cons]
      have h := J_letter_KC k r ih
      rw [Kl_cons, chl_cons]
      convert h using 2 <;> ring

/-- The deeper copy of a letter. -/
def shiftL (q : RLetter) (s : ℕ) : RLetter := toLex ((ofLex q).1, dep q + s)

theorem Lm_rwordOp {n : ℤ} (hn : n ≤ -1) (l : List RLetter) {p : ℕ} {q : ℤ} {z : WakModule k}
    (hz : z ∈ KC k p q) :
    Lm k hk n (rwordOp k l z) - rwordOp k l (Lm k hk n z) ∈ KC k (Kl l + p) (chl l + q) := by
  induction l with
  | nil => simp [rwordOp]
  | cons r l ih =>
      rw [rwordOp_cons, rwordOp_cons, Lm_J]
      have hJ := J_letter_KC k r ih
      rw [map_sub] at hJ
      have hsh : J k (col r) (n + (-(dep r : ℤ) - 1)) (rwordOp k l z) =
          J k (col (shiftL r (-n).toNat)) (-(dep (shiftL r (-n).toNat) : ℤ) - 1)
            (rwordOp k l z) := by
        have hm : n + (-(dep r : ℤ) - 1) = -(dep (shiftL r (-n).toNat) : ℤ) - 1 := by
          simp only [shiftL, dep, ofLex_toLex]
          push_cast
          rw [Int.toNat_of_nonneg (by omega : 0 ≤ -n)]
          ring
        rw [hm]
        rfl
      have h2 := J_letter_KC k (shiftL r (-n).toNat) (rwordOp_KC k l hz)
      have hrk : rk (shiftL r (-n).toNat) = rk r := rfl
      rw [hrk] at h2
      rw [hsh, add_sub_right_comm]
      rw [Kl_cons, chl_cons]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
      · convert hJ using 2 <;> ring
      · convert h2 using 2 <;> ring

theorem omegaA_explicit : omegaA k = c0 k • (J k 0 (-1) (J k 1 (-1) (vacuumA k)) +
    J k 1 (-1) (J k 0 (-1) (vacuumA k)) + (1 / 2 : ℂ) • J k 2 (-1) (J k 2 (-1) (vacuumA k))) := by
  rw [Vir.omegaA_creation_form]
  simp [Fin.sum_univ_three, kappaInv]

theorem J_neg_one_eq (a : Fin 3) (y : WakModule k) :
    J k a (-1) y = J k a (-((0 : ℕ) : ℤ) - 1) y := by
  norm_num

/-- The three Sugawara words. -/
theorem word_ef : J k 0 (-1) (J k 1 (-1) (vacuumA k)) = rword k [eL 0, toLex (0, 0)] := by
  rw [J_neg_one_eq, J_neg_one_eq]; rfl

theorem word_fe : J k 1 (-1) (J k 0 (-1) (vacuumA k)) = rword k [toLex (0, 0), eL 0] := by
  rw [J_neg_one_eq, J_neg_one_eq]; rfl

theorem word_hh : J k 2 (-1) (J k 2 (-1) (vacuumA k)) = rword k [toLex (1, 0), toLex (1, 0)] := by
  rw [J_neg_one_eq, J_neg_one_eq]; rfl

theorem omegaA_mem_KC : omegaA k ∈ KC k 2 0 := by
  rw [omegaA_explicit, word_ef, word_fe, word_hh]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
    (Submodule.smul_mem _ _ ?_)) <;>
  exact rword_mem_KC k (by decide) (by decide)

theorem Lm_neg_one_KC {p : ℕ} {q : ℤ} {y : WakModule k} (hy : y ∈ KC k p q) :
    Lm k hk (-1) y ∈ KC k p q := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, hq, rfl⟩ := hx
      have h := Lm_rwordOp k hk le_rfl l (show vacuumA k ∈ KC k 0 0 from rword_mem_KC k
        (l := []) le_rfl rfl)
      rw [rwordOp_vac, Lm_vac k hk le_rfl, map_zero, sub_zero, add_zero, add_zero, hq] at h
      exact KC_mono k hl q h
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- `L_{-j-2} |0⟩` has Kazhdan weight `≤ 2` and charge `0`. -/
theorem Lm_vac_KC (j : ℕ) : Lm k hk (-(j : ℤ) - 2) (vacuumA k) ∈ KC k 2 0 := by
  induction j with
  | zero =>
      rw [show (-((0 : ℕ) : ℤ) - 2) = -2 by norm_num, Lm_neg_two_vac]
      exact omegaA_mem_KC k
  | succ j ih =>
      have h := Lm_comm k hk (-1) (-(j : ℤ) - 2) (by omega) (vacuumA k)
      rw [Lm_vac k hk le_rfl, map_zero, zero_add] at h
      have hne : ((-1 : ℤ) : ℂ) - ((-(j : ℤ) - 2 : ℤ) : ℂ) ≠ 0 := by
        push_cast
        intro h0
        have : (j : ℂ) + 1 = 0 := by linear_combination h0
        exact Nat.cast_add_one_ne_zero j this
      have h2 : Lm k hk (-((j + 1 : ℕ) : ℤ) - 2) (vacuumA k) =
          (((-1 : ℤ) : ℂ) - ((-(j : ℤ) - 2 : ℤ) : ℂ))⁻¹ •
            Lm k hk (-1) (Lm k hk (-(j : ℤ) - 2) (vacuumA k)) := by
        rw [h, smul_smul, inv_mul_cancel₀ hne, one_smul]
        congr 2
        push_cast; ring
      rw [h2]
      exact Submodule.smul_mem _ _ (Lm_neg_one_KC k hk ih)

/-- The Sugawara creation modes on Kazhdan–charge spans. -/
theorem Lm_KC (j : ℕ) {p : ℕ} {q : ℤ} {y : WakModule k} (hy : y ∈ KC k p q) :
    Lm k hk (-(j : ℤ) - 2) y ∈ KC k (p + 2) q := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, hq, rfl⟩ := hx
      have h := Lm_rwordOp k hk (by omega : -(j : ℤ) - 2 ≤ -1) l
        (show vacuumA k ∈ KC k 0 0 from rword_mem_KC k (l := []) le_rfl rfl)
      rw [rwordOp_vac, add_zero, add_zero] at h
      have h2 := rwordOp_KC k l (Lm_vac_KC k hk j)
      rw [← sub_add_cancel (Lm k hk (-(j : ℤ) - 2) (rword k l))
        (rwordOp k l (Lm k hk (-(j : ℤ) - 2) (vacuumA k))), ← hq]
      exact Submodule.add_mem _ (KC_mono k (p := Kl l) (by omega) _ h)
        (KC_mono k (p := Kl l + 2) (by omega) _ (by simpa using h2))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-! ## §5  Triangularity -/

/-- The leading coefficient `cL = -2 c₀ = -1/(k+2)`. -/
def cL : ℂ := -2 * c0 k

theorem cL_ne_zero (hk : k + 2 ≠ 0) : cL k ≠ 0 := by
  rw [cL, c0, dualCoxeter]
  have : (2 * (k + 2) : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hk
  simpa using this

theorem W0_word_sub_mem_Dg0 (l : List RLetter) (hl : Kl l ≤ 2) :
    W0 k hk (rword k l) - classicalW l ∈ Dg 0 :=
  Dg_mono (by omega) (W0_rword_sub k hk l)

theorem Lt_neg_two_one : Lt k hk (-2) 1 - cL k • X 0 ∈ Dg 0 := by
  rw [Lt, LinearMap.comp_apply, LinearMap.comp_apply, sE_one, Lm_neg_two_vac, omegaA_explicit,
    word_ef, word_fe, word_hh, map_smul, map_add, map_add, map_smul]
  have h1 := W0_word_sub_mem_Dg0 k hk [eL 0, toLex (0, 0)] (by decide)
  have h2 := W0_word_sub_mem_Dg0 k hk [toLex (0, 0), eL 0] (by decide)
  have h3 := W0_word_sub_mem_Dg0 k hk [toLex (1, 0), toLex (1, 0)] (by decide)
  have c1 : classicalW [eL 0, toLex (0, 0)] = -X 0 := by
    simp [classicalW, eL, letterVal_e, letterVal_f, chiF]
  have c2 : classicalW [toLex (0, 0), eL 0] = -X 0 := by
    simp [classicalW, eL, letterVal_e, letterVal_f, chiF]
  have c3 : classicalW [toLex (1, 0), toLex (1, 0)] = 0 := by
    simp [classicalW, letterVal_h]
  rw [c1] at h1; rw [c2] at h2; rw [c3, sub_zero] at h3
  have : c0 k • (W0 k hk (rword k [eL 0, toLex (0, 0)]) +
      W0 k hk (rword k [toLex (0, 0), eL 0]) +
        (1 / 2 : ℂ) • W0 k hk (rword k [toLex (1, 0), toLex (1, 0)])) - cL k • X 0 =
      c0 k • ((W0 k hk (rword k [eL 0, toLex (0, 0)]) - -X 0) +
        (W0 k hk (rword k [toLex (0, 0), eL 0]) - -X 0) +
          (1 / 2 : ℂ) • W0 k hk (rword k [toLex (1, 0), toLex (1, 0)])) := by
    rw [cL]; module
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _ h1 h2)
    (Submodule.smul_mem _ _ h3))

theorem eq_C_of_mem_Dg0 {P : EPoly} (hP : P ∈ Dg 0) : P = MvPolynomial.C (coeff 0 P) :=
  totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp (mem_Dg.mp hP))

/-- `Lt (-j-2) 1 = cL · X_j` up to a constant. -/
theorem Lt_one (j : ℕ) : Lt k hk (-(j : ℤ) - 2) 1 - cL k • X j ∈ Dg 0 := by
  induction j with
  | zero => simpa using Lt_neg_two_one k hk
  | succ j ih =>
      have h := Lt_comm k hk (m := -1) (n := -(j : ℤ) - 2) le_rfl (by omega) 1
      rw [Lt_one_neg_one, map_zero, zero_add] at h
      set D := Lt k hk (-(j : ℤ) - 2) 1 - cL k • X j with hD
      have hD0 := eq_C_of_mem_Dg0 ih
      have hLt : Lt k hk (-(j : ℤ) - 2) 1 = cL k • X j + MvPolynomial.C (coeff 0 D) := by
        rw [← hD0, hD]; abel
      rw [hLt, map_add, map_smul, Lt_neg_one_X, Lt_const_neg_one, add_zero, smul_smul] at h
      have hc : ((-1 : ℤ) : ℂ) - ((-(j : ℤ) - 2 : ℤ) : ℂ) = (j : ℂ) + 1 := by push_cast; ring
      rw [hc] at h
      have hj : (j : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero j
      have hval : Lt k hk (-((j + 1 : ℕ) : ℤ) - 2) 1 = cL k • X (j + 1) := by
        have h' := congrArg (fun P => ((j : ℂ) + 1)⁻¹ • P) h
        simp only [smul_smul] at h'
        rw [inv_mul_cancel₀ hj, one_smul] at h'
        rw [show (-((j + 1 : ℕ) : ℤ) - 2) = -1 + (-(j : ℤ) - 2) by push_cast; ring, ← h',
          mul_comm (cL k), ← mul_assoc, inv_mul_cancel₀ hj, one_mul]
      rw [hval, sub_self]
      exact Submodule.zero_mem _

/-- The `e`-list of a monomial. -/
def eList (ν : ℕ →₀ ℕ) : List RLetter := (Finsupp.toMultiset ν).toList.map eL

theorem Kl_eList (ν : ℕ →₀ ℕ) : Kl (eList ν) = 2 * (monomial ν (1 : ℂ)).totalDegree := by
  rw [totalDegree_monomial _ one_ne_zero]
  have hlen : (eList ν).length = ν.sum fun _ e => e := by
    rw [eList, List.length_map, Multiset.length_toList, Finsupp.card_toMultiset]
    rfl
  have : ∀ l : List RLetter, (∀ q ∈ l, rk q = 2) → Kl l = 2 * l.length := by
    intro l hl
    induction l with
    | nil => rfl
    | cons q l ih =>
        rw [Kl_cons, hl q (by simp), ih (fun q' hq' => hl q' (List.mem_cons_of_mem _ hq'))]
        simp; ring
  rw [this, hlen]
  intro q hq
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hq
  rfl

/-- The product with an `e`-word, read off by `W₀`, is multiplicative up to lower degree. -/
theorem W0_rwordOp_eList (ν : ℕ →₀ ℕ) {z : WakModule k} (hz : z ∈ KC k 2 0) :
    W0 k hk (rwordOp k (eList ν) z) - monomial ν 1 * W0 k hk z ∈
      Dg (monomial ν (1 : ℂ)).totalDegree := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, _, rfl⟩ := hx
      rw [rwordOp_rword]
      have h1 := W0_rword_sub k hk (eList ν ++ l)
      have h2 := W0_word_sub_mem_Dg0 k hk l hl
      rw [classicalW_append, Kl_append, Kl_eList] at h1
      have hcl : classicalW (eList ν) = monomial ν 1 := classicalW_eList ν
      rw [hcl] at h1
      have h3 := Dg_mul (mem_Dg.mpr (le_refl (monomial ν (1 : ℂ)).totalDegree)) h2
      rw [add_zero] at h3
      have : W0 k hk (rword k (eList ν ++ l)) - monomial ν 1 * W0 k hk (rword k l) =
          (W0 k hk (rword k (eList ν ++ l)) - monomial ν 1 * classicalW l) -
            monomial ν 1 * (W0 k hk (rword k l) - classicalW l) := by ring
      rw [this]
      exact Submodule.sub_mem _ (Dg_mono (by omega) h1) h3
  | zero => simp
  | add x y _ _ hx hy =>
      rw [map_add, map_add, map_add, mul_add]
      convert Submodule.add_mem _ hx hy using 1; ring
  | smul r x _ hx =>
      simp only [map_smul]
      rw [mul_smul_comm, ← smul_sub]
      exact Submodule.smul_mem _ _ hx

theorem rword_eList (ν : ℕ →₀ ℕ) : sE k (monomial ν 1) = rwordOp k (eList ν) (vacuumA k) := by
  rw [sE_monomial, eword, rwordOp_vac, eList]

/-- **Triangularity on monomials.** -/
theorem Lt_monomial (j : ℕ) (ν : ℕ →₀ ℕ) :
    Lt k hk (-(j : ℤ) - 2) (monomial ν 1) - cL k • (X j * monomial ν 1) ∈
      Dg (monomial ν (1 : ℂ)).totalDegree := by
  have hn : -(j : ℤ) - 2 ≤ -1 := by omega
  have hvac : vacuumA k ∈ KC k 0 0 := rword_mem_KC k (l := []) le_rfl rfl
  have hcomm := Lm_rwordOp k hk hn (eList ν) hvac
  rw [add_zero, add_zero, rwordOp_vac] at hcomm
  have hW1 := W0_KC k hk hcomm
  rw [Kl_eList, show 2 * (monomial ν (1 : ℂ)).totalDegree / 2 =
    (monomial ν (1 : ℂ)).totalDegree by omega] at hW1
  have hW2 := W0_rwordOp_eList k hk ν (Lm_vac_KC k hk j)
  have hW3 := Dg_mul (mem_Dg.mpr (le_refl (monomial ν (1 : ℂ)).totalDegree)) (Lt_one k hk j)
  rw [add_zero] at hW3
  have hLt : Lt k hk (-(j : ℤ) - 2) (monomial ν 1) =
      W0 k hk (Lm k hk (-(j : ℤ) - 2) (rword k (eList ν))) := by
    rw [Lt, LinearMap.comp_apply, LinearMap.comp_apply, rword_eList, rwordOp_vac]
  have hone : Lt k hk (-(j : ℤ) - 2) 1 = W0 k hk (Lm k hk (-(j : ℤ) - 2) (vacuumA k)) := by
    rw [Lt, LinearMap.comp_apply, LinearMap.comp_apply, sE_one]
  rw [map_sub] at hW1
  rw [← hone] at hW2
  rw [hLt]
  have : W0 k hk (Lm k hk (-(j : ℤ) - 2) (rword k (eList ν))) - cL k • (X j * monomial ν 1) =
      (W0 k hk (Lm k hk (-(j : ℤ) - 2) (rword k (eList ν))) -
          W0 k hk (rwordOp k (eList ν) (Lm k hk (-(j : ℤ) - 2) (vacuumA k)))) +
        (W0 k hk (rwordOp k (eList ν) (Lm k hk (-(j : ℤ) - 2) (vacuumA k))) -
          monomial ν 1 * Lt k hk (-(j : ℤ) - 2) 1) +
        monomial ν 1 * (Lt k hk (-(j : ℤ) - 2) 1 - cL k • X j) := by
    rw [mul_sub, mul_smul_comm, mul_comm (monomial ν 1) (X j)]; abel
  rw [this]
  exact Submodule.add_mem _ (Submodule.add_mem _ hW1 hW2) hW3

/-- **Triangularity**: `Lt (-j-2) P = cL · X_j P` up to total degree `≤ d` on `Dg d`. -/
theorem Lt_tri (j : ℕ) {d : ℕ} {P : EPoly} (hP : P ∈ Dg d) :
    Lt k hk (-(j : ℤ) - 2) P - cL k • (X j * P) ∈ Dg d := by
  rw [P.as_sum, map_sum, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun ν hν => ?_
  have hdeg : (monomial ν (1 : ℂ)).totalDegree ≤ d := by
    rw [totalDegree_monomial _ one_ne_zero]
    exact (le_totalDegree hν).trans (mem_Dg.mp hP)
  have hm : monomial ν (coeff ν P) = coeff ν P • monomial ν (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, mul_smul_comm, smul_comm, ← smul_sub]
  exact Submodule.smul_mem _ _ (Dg_mono hdeg (Lt_monomial k hk j ν))

end

end VOA.TwoSeries.SliceMap
