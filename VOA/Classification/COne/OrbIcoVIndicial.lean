import VOA.Classification.COne.OrbIcoVNullRecurrence

/-! The exact indicial polynomial and its resonances for the actual scalar null equation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
namespace VOA.Classification.COne.OrbIcoV
open OrbOdd Polynomial

def pcompL : PL → PL → PL
  | [], _ => []
  | x :: xs, b => paddL [x] (pmulL b (pcompL xs b))

def pprodL : List PL → PL
  | [] => [1]
  | p :: ps => pmulL p (pprodL ps)

def psumL : List PL → PL
  | [] => []
  | p :: ps => paddL p (psumL ps)

def leadingWord : List ℕ → PL
  | [] => [1]
  | k :: ks => pmulL [35 * ((k : ℚ) - 1), 1]
      (pcompL (leadingWord ks) [-(k : ℚ), 1])

def leadingCombo (cs : List (ℚ × List ℕ)) : PL :=
  psumL (cs.map fun t => pscaleL t.1 (leadingWord t.2))

def fusionIndicial : PL :=
  pprodL ((List.range 13).map fun (j : ℕ) => [(j : ℚ)^2 - 84, 1])

set_option maxHeartbeats 12000000 in
-- A degree-thirteen coefficient list, independently certified in the kernel.
theorem s13_indicial_list : ptrim (leadingCombo OrbIcoZ.s13v) = ptrim fusionIndicial := by
  decide +kernel

noncomputable section

theorem zp_pcompL (a b : PL) : zp (pcompL a b) = (zp a).comp (zp b) := by
  induction a with
  | nil => simp [pcompL, zp]
  | cons x a ih =>
    rw [pcompL, zp_paddL, zp_pmulL, ih]
    simp [zp, Polynomial.add_comp, Polynomial.mul_comp]

theorem zp_pprodL (ps : List PL) : zp (pprodL ps) = (ps.map zp).prod := by
  induction ps with
  | nil => simp [pprodL, zp]
  | cons p ps ih => simp only [pprodL, zp_pmulL, ih, List.map_cons, List.prod_cons]

theorem zp_psumL (ps : List PL) : zp (psumL ps) = (ps.map zp).sum := by
  induction ps with
  | nil => simp [psumL, zp]
  | cons p ps ih => simp only [psumL, zp_paddL, ih, List.map_cons, List.sum_cons]

private theorem list_prod_range {R : Type*} [CommMonoid R] (n : ℕ) (f : ℕ → R) :
    ((List.range n).map f).prod = ∏ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.prod_range_succ]

theorem s13_indicial_factorization : zp (leadingCombo OrbIcoZ.s13v) =
    ∏ j ∈ Finset.range 13, (Polynomial.X - Polynomial.C (84 - (j : ℂ)^2)) := by
  rw [← zp_ptrim, s13_indicial_list, zp_ptrim, fusionIndicial, zp_pprodL,
    List.map_map, list_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp [zp]
  ring

theorem nullWord_zero_below (h m p : ℤ) (ks : List ℕ)
    (hks : ∀ k ∈ ks, 0 < k) (hp : p < m - (ks.sum : ℤ)) :
    nullWord h (fun n => if n = p then (1 : ℂ) else 0) m ks = 0 := by
  induction ks generalizing m with
  | nil =>
    have hne : m ≠ p := by simp only [List.sum_nil, Nat.cast_zero, sub_zero] at hp; omega
    simp [nullWord, hne]
  | cons k ks ih =>
    have hk := hks k (by simp)
    have ht : ∀ j ∈ ks, 0 < j := fun j hj => hks j (by simp [hj])
    simp only [List.sum_cons, Nat.cast_add] at hp
    rw [nullWord, ih m ht (by omega), ih (m - k) ht (by omega)]
    simp

theorem nullWord_leading (m : ℤ) (ks : List ℕ)
    (hks : ∀ k ∈ ks, 0 < k) :
    nullWord 36 (fun n => if n = m - (ks.sum : ℤ) then (1 : ℂ) else 0) m ks =
      Polynomial.eval (m : ℂ) (zp (leadingWord ks)) := by
  induction ks generalizing m with
  | nil => simp [nullWord, leadingWord, zp]
  | cons k ks ih =>
    have hk := hks k (by simp)
    have ht : ∀ j ∈ ks, 0 < j := fun j hj => hks j (by simp [hj])
    have hzero := nullWord_zero_below 36 m (m - ((k :: ks).sum : ℤ)) ks ht (by
      simp only [List.sum_cons, Nat.cast_add]; omega)
    rw [nullWord, hzero, mul_zero, zero_add]
    have he : m - ((k :: ks).sum : ℤ) = (m - k) - (ks.sum : ℤ) := by
      simp only [List.sum_cons, Nat.cast_add]; omega
    rw [he, ih (m - k) ht]
    rw [leadingWord, zp_pmulL, zp_pcompL]
    simp only [zp, Rat.cast_one, Rat.cast_neg, Rat.cast_natCast,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, mul_one, mul_zero, add_zero]
    push_cast
    ring_nf

/-- The leading scalar really is the coefficient in the actual null equation. -/
theorem s13_leading_coefficient (m : ℤ) :
    nullCombo 36 (fun n => if n = m - 13 then (1 : ℂ) else 0) m OrbIcoZ.s13v =
      ∏ j ∈ Finset.range 13, ((m : ℂ) - (84 - (j : ℂ)^2)) := by
  have he : nullCombo 36 (fun n => if n = m - 13 then (1 : ℂ) else 0) m OrbIcoZ.s13v =
      Polynomial.eval (m : ℂ) (zp (leadingCombo OrbIcoZ.s13v)) := by
    unfold nullCombo leadingCombo
    rw [zp_psumL, Polynomial.eval_listSum]
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro t ht
    dsimp only [Function.comp_apply]
    have hs := (OrbIcoZ.s13v_spec t ht).1
    have hp : ∀ k ∈ t.2, 0 < k := by
      simpa only [OrbOdd.posW, List.all_eq_true, decide_eq_true_eq] using
        (OrbIcoZ.s13v_spec t ht).2.2
    rw [show (13 : ℤ) = (t.2.sum : ℤ) by exact_mod_cast hs.symm,
      nullWord_leading m t.2 hp, zp_pscaleL, Polynomial.eval_mul, Polynomial.eval_C]
  rw [he, s13_indicial_factorization, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  simp

end
end VOA.Classification.COne.OrbIcoV
