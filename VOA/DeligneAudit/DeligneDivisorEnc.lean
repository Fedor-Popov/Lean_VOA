/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorNumeric
import VOA.DeligneAudit.DeligneDivisorFast

/-!
# Zero checks by big-integer encoding

A sparse table `L : QV` with indices `< kb` is encoded as the integer `Σ_t k_t · B^(kb·c_t + d_t)`,
`B = 2^64` (`encQ`).  If the encoding vanishes and `Σ |k_t| < 2^63`, every ordered coefficient vanishes
(`qget_eq_zero_of_encCheck`): base-`B` digits are unique (`digits_zero`).  The kernel evaluates the encoding with
GMP-accelerated `Nat` arithmetic, so the check is linear in the length of `L`.
-/

namespace VOA.DeligneAudit.DeligneDivisor

open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.Sparse











theorem bpow_eq (e : ℕ) : bpow e = (2 ^ 64 : ℤ) ^ e := by
  simp [bpow, pow_mul]

theorem digits_zero (B : ℤ) (hB : 0 < B) :
    ∀ (K : ℕ) (g : ℕ → ℤ), (∀ e, 2 * |g e| < B) → (∑ e ∈ Finset.range K, g e * B ^ e) = 0 →
      ∀ e < K, g e = 0 := by
  intro K
  induction K with
  | zero => intro g _ _ e he; omega
  | succ K ih =>
    intro g hg h e he
    rw [Finset.sum_range_succ'] at h
    have h0 : g 0 = -(B * ∑ i ∈ Finset.range K, g (i + 1) * B ^ i) := by
      rw [Finset.mul_sum]
      have : ∑ i ∈ Finset.range K, g (i + 1) * B ^ (i + 1) =
          ∑ i ∈ Finset.range K, B * (g (i + 1) * B ^ i) :=
        Finset.sum_congr rfl fun i _ => by ring
      simp only [pow_zero, mul_one] at h
      linarith
    have hdvd : B ∣ g 0 := ⟨-(∑ i ∈ Finset.range K, g (i + 1) * B ^ i), by rw [h0]; ring⟩
    have hlt : |g 0| < B := by have := hg 0; have := abs_nonneg (g 0); linarith
    have hz0 : g 0 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    have hrest : (∑ i ∈ Finset.range K, g (i + 1) * B ^ i) = 0 := by
      rw [hz0] at h0
      have : B * ∑ i ∈ Finset.range K, g (i + 1) * B ^ i = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 hB.ne'
      · exact h1
    rcases e with _ | e
    · exact hz0
    · exact ih (fun i => g (i + 1)) (fun i => hg (i + 1)) hrest e (by omega)

/-- Total coefficient of key `e`. -/
def kgetE (kb : ℕ) (L : QV) (e : ℕ) : ℤ := (L.map fun t => if keyE kb t = e then t.2.2 else 0).sum

theorem encQ_eq_sum (kb : ℕ) (L : QV) (K : ℕ) (hK : ∀ t ∈ L, keyE kb t < K) :
    encQ kb L = ∑ e ∈ Finset.range K, kgetE kb L e * (2 ^ 64 : ℤ) ^ e := by
  induction L with
  | nil => simp [encQ, kgetE]
  | cons t L ih =>
    simp only [encQ, kgetE, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih fun u hu => hK u (List.mem_cons_of_mem _ hu)]
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    congr 1
    rw [Finset.sum_ite_eq (Finset.range K) (keyE kb t), if_pos (Finset.mem_range.mpr
      (hK t List.mem_cons_self)), bpow_eq]

theorem abs_kgetE_le (kb : ℕ) (L : QV) (e : ℕ) : |kgetE kb L e| ≤ (absSum L : ℤ) := by
  induction L with
  | nil => simp [kgetE, absSum]
  | cons t L ih =>
    simp only [kgetE, absSum, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    split_ifs
    · simp
    · simp

theorem qget_eq_kgetE (kb : ℕ) (L : QV) (hL : ∀ t ∈ L, t.1 < kb ∧ t.2.1 < kb) {a b : ℕ}
    (hb : b < kb) : qget L a b = kgetE kb L (a * kb + b) := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    rw [qget_cons, kgetE, List.map_cons, List.sum_cons, ← kgetE,
      ih fun u hu => hL u (List.mem_cons_of_mem _ hu)]
    congr 1
    have ht := hL t List.mem_cons_self
    have e : (keyE kb t = a * kb + b) ↔ (t.1 = a ∧ t.2.1 = b) := by
      unfold keyE
      constructor
      · intro h
        have h1 : t.1 = a := by
          have := Nat.div_add_mod' (t.1 * kb + t.2.1) kb
          have e1 : (t.1 * kb + t.2.1) / kb = t.1 := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht.2, zero_add]
          have e2 : (a * kb + b) / kb = a := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]
          rw [← e1, h, e2]
        subst h1
        exact ⟨rfl, by omega⟩
      · rintro ⟨rfl, rfl⟩; rfl
    by_cases h : t.1 = a ∧ t.2.1 = b
    · rw [if_pos h, if_pos (e.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (e.mp h'))]

theorem qget_eq_zero_of_encCheck {kb : ℕ} {L : QV} (h : encCheck kb L = true) {a b : ℕ}
    (ha : a < kb) (hb : b < kb) : qget L a b = 0 := by
  simp only [encCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hr, habs⟩, henc⟩ := h
  rw [qget_eq_kgetE kb L hr hb]
  have hK : ∀ t ∈ L, keyE kb t < kb * kb := by
    intro t ht
    have := hr t ht
    unfold keyE
    nlinarith
  rw [encQ_eq_sum kb L (kb * kb) hK] at henc
  refine digits_zero (2 ^ 64) (by norm_num) (kb * kb) (kgetE kb L) (fun e => ?_) henc _ (by nlinarith)
  have := abs_kgetE_le kb L e
  have h2 : ((absSum L : ℕ) : ℤ) < 2 ^ 63 := by exact_mod_cast habs
  linarith

theorem castQZ_eq_of_enc {S : DeligneSectorData} {kb : ℕ} (hn : S.n ≤ kb) {L M : QV}
    (h : encCheck kb (L ++ smulQ (-1) M) = true) : castQZ (S := S) L = castQZ M := by
  funext c d
  have := qget_eq_zero_of_encCheck h (lt_of_lt_of_le c.2 hn) (lt_of_lt_of_le d.2 hn)
  rw [qget_append, qget_smulQ] at this
  simp only [castQZ]; linarith

/-! ## Linear form of the encoded check -/

theorem encQ_append (kb : ℕ) (L M : QV) : encQ kb (L ++ M) = encQ kb L + encQ kb M := by
  simp [encQ]

theorem encQ_smulQ (kb : ℕ) (k : ℤ) (L : QV) : encQ kb (smulQ k L) = k * encQ kb L := by
  induction L with
  | nil => simp [encQ, smulQ]
  | cons t L ih =>
    simp only [encQ, smulQ, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; simp only [keyE]; ring

theorem absSum_append (L M : QV) : absSum (L ++ M) = absSum L + absSum M := by
  simp [absSum]

theorem absSum_smulQ (k : ℤ) (L : QV) : absSum (smulQ k L) = k.natAbs * absSum L := by
  induction L with
  | nil => simp [absSum, smulQ]
  | cons t L ih =>
    simp only [absSum, smulQ, List.map_cons, List.sum_cons, Int.natAbs_mul] at ih ⊢
    rw [ih]; ring

theorem encQ_combQ (kb : ℕ) (tab : ℕ → QV) (C : List (ℕ × ℤ)) :
    encQ kb (combQ tab C) = (C.map fun p => p.2 * encQ kb (tab p.1)).sum := by
  induction C with
  | nil => simp [combQ, encQ]
  | cons p C ih =>
    simp only [combQ, List.flatMap_cons, encQ_append, encQ_smulQ, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih]

theorem absSum_combQ (tab : ℕ → QV) (C : List (ℕ × ℤ)) :
    absSum (combQ tab C) = (C.map fun p => p.2.natAbs * absSum (tab p.1)).sum := by
  induction C with
  | nil => simp [combQ, absSum]
  | cons p C ih =>
    simp only [combQ, List.flatMap_cons, absSum_append, absSum_smulQ, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih]



theorem encCheck_of_encLin {kb : ℕ} {tab : ℕ → QV} {target : QV} {C : List (ℕ × ℤ)}
    (h : encLin kb tab target C = true) :
    encCheck kb (target ++ smulQ (-1) (combQ tab C)) = true := by
  simp only [encLin, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [encCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact h1 t ht
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      obtain ⟨p, hp, hu'⟩ := List.mem_flatMap.mp hu
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu'
      exact h2 p hp v hv
  · rw [absSum_append, absSum_smulQ, absSum_combQ]; simpa using h3
  · rw [encQ_append, encQ_smulQ, encQ_combQ, h4]; ring

end VOA.DeligneAudit.DeligneDivisor

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneDivisor.castQZ_eq_of_enc
end AxiomAudit
