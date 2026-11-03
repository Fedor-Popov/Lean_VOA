/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.JetProductRank
import VOA.Commutative.WeightedPolynomialHilbert
import VOA.Commutative.QDurfeeChain

/-!
# Counting the independent functionals: the fermionic jet series

* `cntG_eq_gaussian` — the weight generating polynomial of multisets of `k` indices `≤ l` is the
  Gaussian binomial `[l + k, k]_q`;
* `coeff_reciprocalQFactorial_eq_card` — `[q^e] 1/(q)_r` counts exponent vectors `α` with
  `Σ (i+1) α_i = e`;
* `jetSeries` — the fermionic series `Σ_r q^r (Σ_{k ≤ 2r} [2r, k]_q) / (q)_r`;
* `coeff_jetSeries` — `[q^N] jetSeries = Σ_{r ≤ N} #jetIndex r N`;
* `coeff_jetSeries_le` — hence `[q^N] jetSeries ≤ Σ_{r ≤ N} dim A_{r,N}` (proved outright).

Everything is proved outright.
-/

namespace VOA.JetProduct

open VOA.QSeries VOA.SymbolModel
open scoped BigOperators

noncomputable section

/-! ### Multisets in a box and Gaussian binomials -/

/-- The sum of the entries of a multiset of `Fin n`. -/
def symSum {n k : ℕ} (s : Sym (Fin n) k) : ℕ := ((s : Multiset (Fin n)).map Fin.val).sum

/-- The weight generating polynomial of `Sym (Fin (l + 1)) k`. -/
def cntG (l k : ℕ) : PowerSeries ℚ := ∑ s : Sym (Fin (l + 1)) k, PowerSeries.X ^ symSum s

/-- Multisets containing the maximal element, with one copy removed. -/
def eLast {n k : ℕ} : {s : Sym (Fin (n + 1)) (k + 1) // Fin.last n ∈ s} ≃ Sym (Fin (n + 1)) k where
  toFun s := s.1.erase (Fin.last n) s.2
  invFun s := ⟨Sym.cons (Fin.last n) s, Sym.mem_cons_self _ _⟩
  left_inv s := by simp
  right_inv s := by simp

/-- Multisets avoiding the maximal element live on the smaller box. -/
def eNoLast {n k : ℕ} :
    {s : Sym (Fin (n + 2)) k // Fin.last (n + 1) ∉ s} ≃ Sym (Fin (n + 1)) k where
  toFun s := Sym.map (fun x => if h : x = Fin.last (n + 1) then 0 else x.castPred h) s.1
  invFun s := ⟨Sym.map Fin.castSucc s, by
    rw [Sym.mem_map]
    rintro ⟨a, -, ha⟩
    exact Fin.castSucc_ne_last a ha⟩
  left_inv s := by
    ext1
    simp only [Sym.map_map]
    refine (Sym.map_congr fun v hv => ?_).trans (Sym.map_id' _)
    have hne : v ≠ Fin.last (n + 1) := fun h => s.2 (h ▸ hv)
    simp [hne]
  right_inv s := by
    simp only [Sym.map_map]
    refine (Sym.map_congr fun v _ => ?_).trans (Sym.map_id' _)
    simp [Fin.castSucc_ne_last]

theorem symSum_cons {n k : ℕ} (a : Fin n) (s : Sym (Fin n) k) :
    symSum (Sym.cons a s) = a + symSum s := by
  simp [symSum, Sym.coe_cons]

theorem symSum_erase {n k : ℕ} (s : Sym (Fin (n + 1)) (k + 1)) (h : Fin.last n ∈ s) :
    symSum s = n + symSum (s.erase (Fin.last n) h) := by
  conv_lhs => rw [← Sym.cons_erase h]
  rw [symSum_cons, Fin.val_last]

theorem symSum_map_castSucc {n k : ℕ} (s : Sym (Fin (n + 1)) k) :
    symSum (Sym.map Fin.castSucc s) = symSum s := by
  simp [symSum, Sym.coe_map, Multiset.map_map]

theorem cntG_succ_succ (l k : ℕ) :
    cntG (l + 1) (k + 1) = cntG l (k + 1) + PowerSeries.X ^ (l + 1) * cntG (l + 1) k := by
  classical
  rw [cntG, ← Fintype.sum_subtype_add_sum_subtype (fun s => Fin.last (l + 1) ∈ s), add_comm]
  congr 1
  · rw [cntG, ← Equiv.sum_comp eNoLast.symm]
    apply Finset.sum_congr rfl
    intro s _
    simp only [eNoLast, Equiv.coe_fn_symm_mk]
    rw [symSum_map_castSucc]
  · rw [cntG, Finset.mul_sum, ← Equiv.sum_comp eLast.symm]
    apply Finset.sum_congr rfl
    intro s _
    simp only [eLast, Equiv.coe_fn_symm_mk]
    rw [symSum_cons, Fin.val_last, pow_add]

theorem cntG_zero_right (l : ℕ) : cntG l 0 = 1 := by
  have h : ∀ s : Sym (Fin (l + 1)) 0, symSum s = 0 := fun s => by
    have hs : (s : Multiset (Fin (l + 1))) = 0 := Multiset.card_eq_zero.mp s.2
    simp [symSum, hs]
  rw [cntG, Fintype.sum_unique, h, pow_zero]

theorem cntG_zero_left (k : ℕ) : cntG 0 k = 1 := by
  rw [cntG]
  have : ∀ s : Sym (Fin 1) k, symSum s = 0 := by
    intro s
    rw [symSum]
    apply Multiset.sum_eq_zero
    intro x hx
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hx
    exact Fin.val_eq_zero y
  simp only [this, pow_zero, Finset.sum_const, Finset.card_univ]
  rw [Sym.card_sym_eq_choose, Fintype.card_fin]
  simp only [add_tsub_cancel_left, Nat.choose_self, one_smul]

/-- The weight generating polynomial of multisets in a box is a Gaussian binomial. -/
theorem cntG_eq_gaussian : ∀ k l : ℕ, cntG l k = gaussian PowerSeries.X (l + k) k
  | 0, l => by rw [cntG_zero_right, gaussian_zero_right]
  | k + 1, 0 => by rw [cntG_zero_left, zero_add, gaussian_self]
  | k + 1, l + 1 => by
    rw [cntG_succ_succ, cntG_eq_gaussian (k + 1) l, cntG_eq_gaussian k (l + 1),
      show l + 1 + (k + 1) = (l + k + 1) + 1 by ring, gaussian_succ_succ,
      show l + k + 1 - k = l + 1 by omega, show l + (k + 1) = l + k + 1 by ring,
      show l + 1 + k = l + k + 1 by ring]

/-! ### Exponent vectors and `1/(q)_r` -/

theorem coeff_reciprocalQFactorial_eq_card (r e B : ℕ) (hB : e ≤ B) :
    PowerSeries.coeff e (reciprocalQFactorial r : PowerSeries ℚ) =
      (((Fintype.piFinset fun _ : Fin r => Finset.range (B + 1)).filter
        fun α => awt α = e).card : ℚ) := by
  classical
  rw [← prod_weightedGeometric_eq_reciprocalQFactorial,
    coeff_prod_weightedGeometric (fun i : Fin r => i.val + 1) (fun _ => Nat.succ_pos _) e]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply Finset.card_bij (fun f _ => fun i => (f i).val)
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    refine ⟨Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr ?_, ?_⟩
    · show (f i).val < B + 1
      have := (f i).2; omega
    · simp only [awt]; exact hf.2
  · intro f _ g _ h
    funext i
    exact Fin.ext (congrFun h i)
  · intro α hα
    rw [Finset.mem_filter] at hα
    have hle : ∀ i, α i < e + 1 := by
      intro i
      have h1 : ((i : ℕ) + 1) * α i ≤ awt α :=
        Finset.single_le_sum (f := fun j : Fin r => ((j : ℕ) + 1) * α j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h2 : α i ≤ ((i : ℕ) + 1) * α i := Nat.le_mul_of_pos_left _ (by omega)
      omega
    refine ⟨fun i => ⟨α i, hle i⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [awt] using hα.2⟩

/-! ### The fermionic jet series -/

/-- The `r`-th term `q^r (Σ_{k ≤ 2r} [2r, k]_q) / (q)_r`. -/
def jetTerm (r : ℕ) : PowerSeries ℚ :=
  PowerSeries.X ^ r * (∑ k ∈ Finset.range (2 * r + 1), gaussian PowerSeries.X (2 * r) k) *
    reciprocalQFactorial r

/-- The fermionic jet series `Σ_r q^r (Σ_{k ≤ 2r} [2r, k]_q) / (q)_r`. -/
def jetSeries : PowerSeries ℚ := VOA.LocallyFinitePowerSeriesSum.sum jetTerm

theorem coeff_jetTerm_eq_zero (d r : ℕ) (h : d < r) : PowerSeries.coeff d (jetTerm r) = 0 := by
  rw [jetTerm, mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem sum_gaussian_eq (r : ℕ) :
    ∑ k ∈ Finset.range (2 * r + 1), gaussian PowerSeries.X (2 * r) k =
      ∑ k : Fin (2 * r + 1), cntG (2 * r - k) k := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [cntG_eq_gaussian, Nat.sub_add_cancel (Nat.lt_succ_iff.mp k.2)]

theorem symSum_eq_msOf {r k : ℕ} (s : Rows r k) : symSum s = (msOf s).sum := rfl

theorem card_fib (r N k : ℕ) (s : Rows r k) :
    ((fib r N k s).card : ℚ) = if (msOf s).sum + r ≤ N then
      PowerSeries.coeff (N - r - (msOf s).sum) (reciprocalQFactorial r : PowerSeries ℚ) else 0 := by
  split_ifs with h
  · rw [coeff_reciprocalQFactorial_eq_card r _ N (by omega), fib]
    congr 2
    ext α
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  · rw [fib, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro α _ hα
    omega

/-- The `r`-th term counts the independent functionals of weight `N`. -/
theorem coeff_jetTerm (r N : ℕ) :
    PowerSeries.coeff N (jetTerm r) = ((jetIndex r N).card : ℚ) := by
  rw [Finset.card_eq_sum_ones, sum_jetIndex, jetTerm, sum_gaussian_eq]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [cntG, Finset.mul_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_const, nsmul_one, card_fib, ← pow_add,
    PowerSeries.coeff_X_pow_mul', symSum_eq_msOf]
  split_ifs with h1 h2 h2
  · rw [Nat.sub_sub]
  · omega
  · omega
  · rfl

/-- The coefficients of the fermionic jet series count the functionals. -/
theorem coeff_jetSeries (N : ℕ) :
    PowerSeries.coeff N jetSeries = ∑ r ∈ Finset.range (N + 1), ((jetIndex r N).card : ℚ) := by
  rw [jetSeries, coeff_indexBounded_sum _ coeff_jetTerm_eq_zero N N le_rfl, map_sum]
  exact Finset.sum_congr rfl fun r _ => coeff_jetTerm r N

/-- **The fermionic jet series is a lower bound for the jet image**, proved outright. -/
theorem coeff_jetSeries_le (N : ℕ) :
    PowerSeries.coeff N jetSeries ≤
      ∑ r ∈ Finset.range (N + 1), (Module.finrank ℂ (jetDeg r (N : ℤ)) : ℚ) := by
  rw [coeff_jetSeries]
  exact Finset.sum_le_sum fun r _ => by exact_mod_cast card_jetIndex_le_finrank r N

end

end VOA.JetProduct
