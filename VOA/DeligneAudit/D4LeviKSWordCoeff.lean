import VOA.DeligneAudit.D4LeviKSSymmetricFinal

/-! Explicit finite coefficient expansions for the D4 contraction presentations. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A : Type*} [Ring A]

/-- The coefficient of a product of shifted currents, written as a finite
    sum of ordered words in their individual modes. -/
def shiftedWordCoeff (b : ℕ → A) : List ℕ → ℕ → A
  | [], s => if s = 0 then 1 else 0
  | x :: xs, s =>
      ∑ q ∈ Finset.antidiagonal s,
        b (x + q.1) * shiftedWordCoeff b xs q.2

/-- All ordered mode allocations with total added degree `s`. The list
    retains every allocation exactly once, including repeated base modes. -/
def modeAllocations : List ℕ → ℕ → List (List ℕ)
  | [], s => if s = 0 then [[]] else []
  | x :: xs, s =>
      (Finset.antidiagonal s).toList.flatMap fun q =>
        (modeAllocations xs q.2).map ((x + q.1) :: ·)

theorem shiftedWordCoeff_eq_allocations (b : ℕ → A)
    (xs : List ℕ) (s : ℕ) :
    shiftedWordCoeff b xs s =
      ((modeAllocations xs s).map fun ys => (ys.map b).prod).sum := by
  induction xs generalizing s with
  | nil =>
      by_cases hs : s = 0 <;> simp [shiftedWordCoeff, modeAllocations, hs]
  | cons x xs ih =>
      simp only [shiftedWordCoeff, modeAllocations, List.flatMap_def,
        List.map_flatten, List.sum_flatten, List.map_map]
      conv =>
        lhs
        rw [← (Finset.antidiagonal s).toList_toFinset,
          List.sum_toFinset _ (Finset.nodup_toList _)]
      congr 1
      apply List.map_congr_left
      intro q hq
      simp only [Function.comp_def, List.map_map, List.map_cons,
        List.prod_cons, List.sum_map_mul_left, ← ih]

theorem shiftedWordCoeff_eq_coeff (b : ℕ → A)
    (xs : List ℕ) (s : ℕ) :
    shiftedWordCoeff b xs s = PowerSeries.coeff s (bWord b xs) := by
  induction xs generalizing s with
  | nil =>
      simp [shiftedWordCoeff, bWord]
  | cons x xs ih =>
      simp only [shiftedWordCoeff, bWord, List.map_cons, List.prod_cons,
        PowerSeries.coeff_mul, bTail, PowerSeries.coeff_mk]
      apply Finset.sum_congr rfl
      intro q hq
      rw [ih]
      rfl

/-- The transported radical current is the same shifted current used in
    the top Wick coefficient. -/
theorem transportCurrent_eq_bTail
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (b : ℕ → Module.End ℂ V) (r : ℕ) :
    transportCurrent b r = bTail b r := rfl

theorem transport_product_coeff
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (b : ℕ → Module.End ℂ V) (rs : List ℕ) (s : ℕ) :
    PowerSeries.coeff s (rs.map (transportCurrent b)).prod =
      shiftedWordCoeff b rs s := by
  rw [shiftedWordCoeff_eq_coeff]
  congr 1

/-- `topSum` is a finite sum of products of a constant word and explicit
    shifted-mode words. The positional choices retain multiplicities. -/
theorem topSum_eq_shiftedWordCoeff (a b : ℕ → A)
    (k s : ℕ) (xs : List ℕ) :
    topSum a b k s xs =
      ((choices xs).map fun p =>
        if p.2.length = k then
          aWord a p.1 * shiftedWordCoeff b p.2 s
        else 0).sum := by
  simp only [topSum]
  congr 1
  apply List.map_congr_left
  intro p hp
  split_ifs <;> simp [shiftedWordCoeff_eq_coeff]

/-- In the mixed XZG/YZG contractions, both the Wick choices and the
    transported factors are explicit finite word sums. -/
theorem mixedTop_eq_shiftedWordCoeff
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (a b t : ℕ → Module.End ℂ V)
    (k s : ℕ) (xs rs : List ℕ) :
    mixedTop a b k s xs (rs.map (transportCurrent t)).prod =
      ∑ q ∈ Finset.antidiagonal s,
        ((choices xs).map fun p =>
          if p.2.length = k then
            aWord a p.1 * shiftedWordCoeff b p.2 q.1
          else 0).sum * shiftedWordCoeff t rs q.2 := by
  simp only [mixedTop, topSum_eq_shiftedWordCoeff,
    transport_product_coeff]

end

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.shiftedWordCoeff_eq_coeff
#print axioms VOA.DeligneAudit.D4Levi.shiftedWordCoeff_eq_allocations
#print axioms VOA.DeligneAudit.D4Levi.transportCurrent_eq_bTail
#print axioms VOA.DeligneAudit.D4Levi.transport_product_coeff
#print axioms VOA.DeligneAudit.D4Levi.topSum_eq_shiftedWordCoeff
#print axioms VOA.DeligneAudit.D4Levi.mixedTop_eq_shiftedWordCoeff
