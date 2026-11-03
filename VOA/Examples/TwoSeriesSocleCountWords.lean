/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesSocleCountMultisum
import VOA.Examples.RRLowerReduction

/-!
# Words, contents and MacMahon's inversion identity

* `coeff_ipoch` — `[q^E] 1/(q)_s = pc s E` (partitions of `E` into parts `≤ s`).
* Content vectors `m : Fin n → ℕ` (`m b` = number of clusters of size `b + 1`), with weighted
  size `wsize`, tails `Cge m s = Σ_{b ≥ s} m b` and quadratic form `Qf m = Σ_{s<n} (C_s² + C_s)`.
  `coeff_F_one_eq` — `[x^r] F_{n,1} = Σ_{wsize m = r} q^{Qf m} ∏_b 1/(q)_{m_b}` (peeling
  off the largest letter, `Fin.snoc`).
* `Iq_mul_prod_poch` — **MacMahon**: the inversion generating function of words of content
  `m` times `∏_b (q)_{m_b}` is `(q)_N`.
* `sum_words_eq` — the word sum `Σ_w q^{Qf(content w) + inv w}/(q)_{N₁}` is the content sum.

All proved.
-/

namespace VOA.SocleCount

open PowerSeries VOA.TwoSeriesCharacter VOA.TwoSeriesCharacter.AG
open scoped BigOperators

noncomputable section

/-! ## §1  The partition series `1/(q)_s` -/

/-- `Σ_E pc s E q^E`. -/
def Pser (s : ℕ) : R := PowerSeries.mk fun E => ((VOA.RRLower.pc s (E : ℤ) : ℤ) : ℚ)

theorem Pser_zero : Pser 0 = 1 := by
  refine PowerSeries.ext fun E => ?_
  rw [Pser, coeff_mk, VOA.RRLower.pc_zero, coeff_one]
  rcases Nat.eq_zero_or_pos E with rfl | h
  · simp
  · rw [if_neg (by omega), if_neg (by omega)]; simp

theorem Pser_succ (s : ℕ) : (1 - qq ^ (s + 1)) * Pser (s + 1) = Pser s := by
  refine PowerSeries.ext fun E => ?_
  rw [sub_mul, one_mul, map_sub, qq, coeff_X_pow_mul']
  simp only [Pser, coeff_mk]
  rw [VOA.RRLower.pc_succ_eq s (E : ℤ)]
  split_ifs with h
  · push_cast [Nat.cast_sub h]
    ring_nf
  · rw [VOA.RRLower.pc_of_neg (s + 1) (by omega)]; simp

theorem Pser_mul_poch : ∀ s, Pser s * poch s = 1
  | 0 => by rw [Pser_zero, poch]; simp
  | s + 1 => by
      calc Pser (s + 1) * poch (s + 1) = ((1 - qq ^ (s + 1)) * Pser (s + 1)) * poch s := by
            rw [poch_succ]; ring
        _ = 1 := by rw [Pser_succ, Pser_mul_poch s]

theorem Pser_eq_ipoch (s : ℕ) : Pser s = ipoch s :=
  calc Pser s = Pser s * (poch s * ipoch s) := by rw [poch_mul_ipoch, mul_one]
    _ = ipoch s := by rw [← mul_assoc, Pser_mul_poch, one_mul]

/-- `[q^E] 1/(q)_s` is the number of partitions of `E` into parts `≤ s`. -/
theorem coeff_ipoch (s E : ℕ) : coeff E (ipoch s) = ((VOA.RRLower.pc s (E : ℤ) : ℤ) : ℚ) := by
  rw [← Pser_eq_ipoch, Pser, coeff_mk]

/-! ## §2  Content vectors and the content form of the multisum -/

/-- The weighted size `Σ_b (b + 1) m_b`. -/
def wsize {n : ℕ} (m : Fin n → ℕ) : ℕ := ∑ b : Fin n, ((b : ℕ) + 1) * m b

/-- The tail `Σ_{b ≥ s} m_b`. -/
def Cge {n : ℕ} (m : Fin n → ℕ) (s : ℕ) : ℕ := ∑ b : Fin n, if s ≤ (b : ℕ) then m b else 0

/-- The quadratic form `Σ_{s < n} (C_s² + C_s)`. -/
def Qf {n : ℕ} (m : Fin n → ℕ) : ℕ := ∑ s ∈ Finset.range n, (Cge m s ^ 2 + Cge m s)

/-- The content term `q^{Qf m} ∏_b 1/(q)_{m_b}`. -/
def cterm {n : ℕ} (m : Fin n → ℕ) : R := qq ^ Qf m * ∏ b, ipoch (m b)

/-- Content vectors of weighted size `r`. -/
def Mset (n r : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (r + 1)).filter fun m => wsize m = r

theorem le_wsize {n : ℕ} (m : Fin n → ℕ) (b : Fin n) : m b ≤ wsize m :=
  calc m b ≤ ((b : ℕ) + 1) * m b := Nat.le_mul_of_pos_left _ (by omega)
    _ ≤ wsize m := Finset.single_le_sum (f := fun b : Fin n => ((b : ℕ) + 1) * m b)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

theorem mem_Mset {n r : ℕ} {m : Fin n → ℕ} : m ∈ Mset n r ↔ wsize m = r := by
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun b => Finset.mem_range.mpr ?_, h⟩
    have := le_wsize m b; omega

theorem wsize_snoc {n : ℕ} (m : Fin n → ℕ) (t : ℕ) :
    wsize (Fin.snoc m t : Fin (n + 1) → ℕ) = wsize m + (n + 1) * t := by
  simp [wsize, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

theorem Cge_snoc {n : ℕ} (m : Fin n → ℕ) (t s : ℕ) (hs : s ≤ n) :
    Cge (Fin.snoc m t : Fin (n + 1) → ℕ) s = Cge m s + t := by
  simp [Cge, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hs]

theorem Cge_top {n : ℕ} (m : Fin n → ℕ) : Cge m n = 0 := by
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [if_neg (by have := b.isLt; omega)]

theorem sum_Cge {n : ℕ} (m : Fin n → ℕ) : ∑ s ∈ Finset.range n, Cge m s = wsize m := by
  unfold Cge wsize
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  congr 1
  have : (Finset.range n).filter (fun s => s ≤ (b : ℕ)) = Finset.range ((b : ℕ) + 1) := by
    ext s; simp only [Finset.mem_filter, Finset.mem_range]; have := b.isLt; omega
  rw [this, Finset.card_range]

theorem Qf_snoc {n : ℕ} (m : Fin n → ℕ) (t : ℕ) :
    Qf (Fin.snoc m t : Fin (n + 1) → ℕ) = Qf m + 2 * t * wsize m + (n + 1) * (t * t + t) := by
  unfold Qf
  rw [Finset.sum_congr rfl fun s hs => by
    rw [Cge_snoc m t s (by have := Finset.mem_range.mp hs; omega)]]
  have h : ∀ s, (Cge m s + t) ^ 2 + (Cge m s + t) =
      (Cge m s ^ 2 + Cge m s) + 2 * t * Cge m s + (t * t + t) := by intro s; ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, smul_eq_mul, Finset.sum_range_succ (fun s => Cge m s ^ 2 + Cge m s),
    Finset.sum_range_succ (fun s => Cge m s), Cge_top, sum_Cge]
  ring

theorem cterm_snoc {n : ℕ} (m : Fin n → ℕ) (t : ℕ) :
    cterm (Fin.snoc m t : Fin (n + 1) → ℕ) =
      qq ^ ((n + 1) * t * t + (n + 1) * t) * ipoch t * (qq ^ (2 * t * wsize m) * cterm m) := by
  unfold cterm
  rw [Qf_snoc, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [show Qf m + 2 * t * wsize m + (n + 1) * (t * t + t) =
    (n + 1) * t * t + (n + 1) * t + (2 * t * wsize m + Qf m) by ring]
  simp only [pow_add]
  ring

/-- Splitting off the last coordinate. -/
theorem sum_Mset_succ (n r : ℕ) (g : (Fin (n + 1) → ℕ) → R) :
    ∑ m ∈ Mset (n + 1) r, g m = ∑ t ∈ Finset.range (r + 1),
      if (n + 1) * t ≤ r then ∑ m ∈ Mset n (r - (n + 1) * t), g (Fin.snoc m t) else 0 := by
  rw [← Finset.sum_filter, Finset.sum_sigma']
  refine Finset.sum_bij' (fun m _ => ⟨m (Fin.last n), Fin.init m⟩)
    (fun p _ => Fin.snoc p.2 p.1) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    have hw := mem_Mset.mp hm
    have hs : wsize m = wsize (Fin.init m) + (n + 1) * m (Fin.last n) := by
      conv_lhs => rw [← Fin.snoc_init_self m]
      exact wsize_snoc _ _
    have hle : m (Fin.last n) ≤ (n + 1) * m (Fin.last n) := Nat.le_mul_of_pos_left _ (by omega)
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨by omega, by omega⟩, mem_Mset.mpr (by omega)⟩
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hp
    refine mem_Mset.mpr ?_
    rw [wsize_snoc, mem_Mset.mp hp.2]
    omega
  · intro m _; exact Fin.snoc_init_self m
  · intro p _
    simp only [Fin.snoc_last, Fin.init_snoc]
  · intro m _
    simp only
    rw [Fin.snoc_init_self]

theorem coeff_pterm (K e t m : ℕ) (f : PowerSeries R) :
    coeff m (pterm K e t f) = if K * t ≤ m then
      qq ^ (K * t * t + e * t) * ipoch t * (qq ^ (2 * t * (m - K * t)) * coeff (m - K * t) f)
      else 0 := by
  rw [show pterm K e t f = xx ^ (K * t) * CC (qq ^ (K * t * t + e * t) * ipoch t) *
    rs (2 * t) f by unfold pterm; ring, coeff_xmul, coeff_rs]

/-- **The content form of the multisum**:
`[x^r] F_{n,1} = Σ_{wsize m = r} q^{Qf m} ∏_b 1/(q)_{m_b}`. -/
theorem coeff_F_one_eq : ∀ (n r : ℕ), coeff r (F n 1) = ∑ m ∈ Mset n r, cterm m
  | 0, r => by
      have hF : F 0 1 = 1 := by simp [F]
      rw [hF, coeff_one]
      by_cases hr : r = 0
      · subst hr
        rw [if_pos rfl]
        have : Mset 0 0 = {default} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_Mset.mpr (by simp [wsize]), ?_⟩
          intro x _; exact Subsingleton.elim _ _
        rw [this, Finset.sum_singleton]
        simp [cterm, Qf]
      · rw [if_neg hr]
        symm
        refine Finset.sum_eq_zero fun m hm => ?_
        exact absurd (mem_Mset.mp hm) (by simp [wsize]; omega)
  | n + 1, r => by
      rw [F_succ n 1 (by omega), show n + 2 - 1 = n + 1 by omega,
        show min 1 (n + 1) = 1 by omega, peel, coeff_tsumx, sum_Mset_succ]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [coeff_pterm]
      split_ifs with h
      · rw [coeff_F_one_eq n, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [cterm_snoc, mem_Mset.mp hm]
      · rfl

/-! ## §3  Words: contents, inversions, MacMahon -/

/-- The content of a word: `ctt w b = #{j : w j = b}`. -/
def ctt {N n : ℕ} (w : Fin N → Fin n) (b : Fin n) : ℕ := ∑ j, if w j = b then 1 else 0

/-- The number of inversions `#{i < j : w j < w i}`. -/
def invs {N n : ℕ} (w : Fin N → Fin n) : ℕ := ∑ i, ∑ j, if i < j ∧ w j < w i then 1 else 0

/-- The inversion generating function of the words of content `m`. -/
def Iq (N : ℕ) {n : ℕ} (m : Fin n → ℕ) : R :=
  ∑ w : Fin N → Fin n, if ctt w = m then qq ^ invs w else 0

theorem ctt_cons {N n : ℕ} (a : Fin n) (w : Fin N → Fin n) (b : Fin n) :
    ctt (Fin.cons a w : Fin (N + 1) → Fin n) b = ctt w b + if a = b then 1 else 0 := by
  simp only [ctt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem invs_cons {N n : ℕ} (a : Fin n) (w : Fin N → Fin n) :
    invs (Fin.cons a w : Fin (N + 1) → Fin n) = (∑ j, if w j < a then 1 else 0) + invs w := by
  unfold invs
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, false_and,
    if_false, zero_add, Fin.succ_pos, true_and, Fin.succ_lt_succ_iff, Fin.not_lt_zero]

/-- The prefix sums `Σ_{b < a} m_b`. -/
def Spre {n : ℕ} (m : Fin n → ℕ) (a : Fin n) : ℕ := ∑ b, if b < a then m b else 0

theorem count_lt {N n : ℕ} (w : Fin N → Fin n) (a : Fin n) :
    (∑ j, if w j < a then 1 else 0) = Spre (ctt w) a := by
  unfold Spre ctt
  have h1 : ∀ b : Fin n, (if b < a then ∑ j, (if w j = b then 1 else 0) else 0) =
      ∑ j, (if w j = b then (if b < a then 1 else 0) else 0) := by
    intro b
    split_ifs with hb
    · rfl
    · simp
  rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem sum_ctt {N n : ℕ} (w : Fin N → Fin n) : ∑ b, ctt w b = N := by
  unfold ctt
  rw [Finset.sum_comm]
  simp

theorem wsize_ctt {N n : ℕ} (w : Fin N → Fin n) : wsize (ctt w) = ∑ j, ((w j : ℕ) + 1) := by
  unfold wsize ctt
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem ctt_le {N n : ℕ} (w : Fin N → Fin n) (b : Fin n) : ctt w b ≤ N := by
  have := Finset.single_le_sum (f := ctt w) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
  rw [sum_ctt] at this
  exact this

theorem tele : ∀ (n : ℕ) (m : Fin n → ℕ),
    ∑ a, qq ^ Spre m a * (1 - qq ^ m a) = 1 - qq ^ (∑ b, m b)
  | 0, m => by simp
  | n + 1, m => by
      have hS : ∀ a : Fin n, Spre m (Fin.castSucc a) = Spre (Fin.init m) a := by
        intro a
        simp only [Spre, Fin.sum_univ_castSucc, Fin.castSucc_lt_castSucc_iff, Fin.init]
        rw [if_neg (not_lt.mpr (Fin.castSucc_lt_last a).le), add_zero]
      have hL : Spre m (Fin.last n) = ∑ b, Fin.init m b := by
        simp only [Spre, Fin.sum_univ_castSucc, Fin.castSucc_lt_last, if_true, lt_self_iff_false,
          if_false, add_zero, Fin.init]
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [hS]
      have IH := tele n (Fin.init m)
      simp only [Fin.init] at IH hL
      rw [IH, hL]
      simp only [pow_add]
      ring

theorem Spre_update {n : ℕ} (m : Fin n → ℕ) (a : Fin n) (v : ℕ) :
    Spre (Function.update m a v) a = Spre m a := by
  unfold Spre
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [Function.update_of_ne (ne_of_lt h)]
  · rfl

theorem ctt_cons_eq_iff {N n : ℕ} (a : Fin n) (w : Fin N → Fin n) (m : Fin n → ℕ) :
    ctt (Fin.cons a w : Fin (N + 1) → Fin n) = m ↔
      1 ≤ m a ∧ ctt w = Function.update m a (m a - 1) := by
  constructor
  · intro h
    have ha := congrFun h a
    rw [ctt_cons, if_pos rfl] at ha
    refine ⟨by omega, funext fun b => ?_⟩
    have hb := congrFun h b
    rw [ctt_cons] at hb
    by_cases hab : b = a
    · subst hab; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hab, if_neg (Ne.symm hab)] at *; omega
  · rintro ⟨h1, h2⟩
    funext b
    rw [ctt_cons, h2]
    by_cases hab : b = a
    · subst hab; rw [Function.update_self, if_pos rfl]; omega
    · rw [Function.update_of_ne hab, if_neg (Ne.symm hab), add_zero]

theorem Iq_succ {n : ℕ} (N : ℕ) (m : Fin n → ℕ) :
    Iq (N + 1) m = ∑ a, if 1 ≤ m a then
      qq ^ Spre m a * Iq N (Function.update m a (m a - 1)) else 0 := by
  unfold Iq
  rw [← (Fin.consEquiv fun _ => Fin n).sum_comp, Fintype.sum_prod_type]
  have hc : ∀ p : Fin n × (Fin N → Fin n), (Fin.consEquiv fun _ => Fin n) p = Fin.cons p.1 p.2 :=
    fun p => rfl
  simp only [hc]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : ctt w = Function.update m a (m a - 1)
    · rw [if_pos ((ctt_cons_eq_iff a w m).mpr ⟨ha, hw⟩), if_pos hw, invs_cons, count_lt, hw,
        Spre_update, pow_add]
    · rw [if_neg (fun h => hw ((ctt_cons_eq_iff a w m).mp h).2), if_neg hw, mul_zero]
  · refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg (fun h => ha ((ctt_cons_eq_iff a w m).mp h).1)]

theorem Iq_zero_len {n : ℕ} (m : Fin n → ℕ) (hm : ∑ b, m b = 0) : Iq 0 m = 1 := by
  have hm0 : ∀ b, m b = 0 := fun b =>
    (Finset.sum_eq_zero_iff.mp hm) b (Finset.mem_univ b)
  unfold Iq
  rw [Fintype.sum_unique]
  rw [if_pos (funext fun b => by rw [hm0 b]; simp [ctt])]
  simp [invs]

/-- **MacMahon's identity**: `Iq N m · ∏_b (q)_{m_b} = (q)_N` for `Σ_b m_b = N`. -/
theorem Iq_mul_prod_poch {n : ℕ} : ∀ (N : ℕ) (m : Fin n → ℕ), ∑ b, m b = N →
    Iq N m * ∏ b, poch (m b) = poch N
  | 0, m, hm => by
      have hm0 : ∀ b, m b = 0 := fun b =>
        (Finset.sum_eq_zero_iff.mp hm) b (Finset.mem_univ b)
      rw [Iq_zero_len m hm]
      simp [hm0, poch]
  | N + 1, m, hm => by
      rw [Iq_succ, Finset.sum_mul]
      have key : ∀ a : Fin n, (if 1 ≤ m a then
          qq ^ Spre m a * Iq N (Function.update m a (m a - 1)) else 0) * ∏ b, poch (m b) =
          poch N * (qq ^ Spre m a * (1 - qq ^ m a)) := by
        intro a
        split_ifs with ha
        · have hsum : ∑ b, Function.update m a (m a - 1) b = N := by
            rw [Finset.sum_update_of_mem (Finset.mem_univ a)]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at hm
            rw [Finset.sdiff_singleton_eq_erase]
            omega
          have IH := Iq_mul_prod_poch N _ hsum
          have hprod : ∏ b, poch (m b) =
              (1 - qq ^ m a) * ∏ b, poch (Function.update m a (m a - 1) b) := by
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
              ← Finset.mul_prod_erase _ _ (Finset.mem_univ a), Function.update_self,
              Finset.prod_congr rfl fun b hb =>
                congrArg poch (Function.update_of_ne (Finset.ne_of_mem_erase hb) _ m)]
            conv_lhs => rw [show m a = (m a - 1) + 1 by omega, poch_succ]
            rw [show m a - 1 + 1 = m a by omega]
            ring
          rw [hprod, ← IH]
          ring
        · rw [show m a = 0 by omega]; simp
      rw [Finset.sum_congr rfl fun a _ => key a, ← Finset.mul_sum, tele, hm, poch_succ]

theorem Iq_mul_ipoch {n N : ℕ} (m : Fin n → ℕ) (hm : ∑ b, m b = N) :
    Iq N m * ipoch N = ∏ b, ipoch (m b) := by
  have h1 : (∏ b, poch (m b)) * ∏ b, ipoch (m b) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun b _ => poch_mul_ipoch _
  calc Iq N m * ipoch N = Iq N m * ipoch N * ((∏ b, poch (m b)) * ∏ b, ipoch (m b)) := by
        rw [h1, mul_one]
    _ = (Iq N m * ∏ b, poch (m b)) * ipoch N * ∏ b, ipoch (m b) := by ring
    _ = ∏ b, ipoch (m b) := by
        rw [Iq_mul_prod_poch N m hm, poch_mul_ipoch, one_mul]

theorem Iq_eq_zero {n N : ℕ} (m : Fin n → ℕ) (hm : ∑ b, m b ≠ N) : Iq N m = 0 := by
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [if_neg]
  intro h
  exact hm (by rw [← h, sum_ctt])

/-- **Words to contents**: for words of length `N₁`,
`Σ_{w, |w| = r} q^{Qf(ctt w) + inv w}/(q)_{N₁} = Σ_{m ∈ Mset n r, Σ m = N₁} cterm m`. -/
theorem sum_words_eq (n N₁ r : ℕ) :
    ∑ w : Fin N₁ → Fin n, (if ∑ j, ((w j : ℕ) + 1) = r then
      qq ^ (Qf (ctt w) + invs w) * ipoch N₁ else 0) =
      ∑ m ∈ Mset n r, if ∑ b, m b = N₁ then cterm m else 0 := by
  set T : Finset (Fin n → ℕ) := Fintype.piFinset fun _ => Finset.range (N₁ + 1) with hT
  have hmem : ∀ w : Fin N₁ → Fin n, ctt w ∈ T := fun w =>
    Fintype.mem_piFinset.mpr fun b => Finset.mem_range.mpr (by have := ctt_le w b; omega)
  have step1 : ∀ w : Fin N₁ → Fin n, (if ∑ j, ((w j : ℕ) + 1) = r then
      qq ^ (Qf (ctt w) + invs w) * ipoch N₁ else 0) =
      ∑ m ∈ T, if ctt w = m then
        (if wsize m = r then qq ^ Qf m * ipoch N₁ else 0) * qq ^ invs w else 0 := by
    intro w
    rw [Finset.sum_ite_eq T (ctt w), if_pos (hmem w), wsize_ctt]
    split_ifs
    · rw [pow_add]; ring
    · simp
  rw [Finset.sum_congr rfl fun w _ => step1 w, Finset.sum_comm]
  have step2 : ∀ m ∈ T, (∑ w : Fin N₁ → Fin n, if ctt w = m then
      (if wsize m = r then qq ^ Qf m * ipoch N₁ else 0) * qq ^ invs w else 0) =
      if wsize m = r ∧ ∑ b, m b = N₁ then cterm m else 0 := by
    intro m _
    have : (∑ w : Fin N₁ → Fin n, if ctt w = m then
        (if wsize m = r then qq ^ Qf m * ipoch N₁ else 0) * qq ^ invs w else 0) =
        (if wsize m = r then qq ^ Qf m * ipoch N₁ else 0) * Iq N₁ m := by
      rw [Iq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      split_ifs <;> simp
    rw [this]
    by_cases hs : ∑ b, m b = N₁
    · rw [show (if wsize m = r then qq ^ Qf m * ipoch N₁ else 0) * Iq N₁ m =
        if wsize m = r then qq ^ Qf m * (Iq N₁ m * ipoch N₁) else 0 by split_ifs <;> ring,
        Iq_mul_ipoch m hs]
      simp only [hs, and_true, cterm]
    · rw [Iq_eq_zero m hs, mul_zero]
      simp [hs]
  rw [Finset.sum_congr rfl step2, ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext m
  simp only [Finset.mem_filter, mem_Mset, hT, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2⟩
    refine ⟨fun b => ?_, h1, h2⟩
    have := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    omega

end

end VOA.SocleCount
