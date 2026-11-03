import VOA.Classification.COne.OrbRat4Skew

/-! # Certificate interface for the skew-symmetric evaluation of `U₍N₎ x`

* `expect v` is the bucketed normal form of `v·h(-1)1`; `val_of_bucket` turns a kernel-checked
  bucket identity into the `V₈` identity `evalSt s = v • h(-1)1`.
* `hA_of_check`: all the `J E` terms of `assemble` from one Boolean check.
* `pieces`, `evalSt_EJ_pieces`: the `E J` terms split monomial by monomial, so that every
  kernel computation stays small.
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e LatMod
  OrbRat3

/-- The coefficient list of `v·h(-1)`. -/
def mon (v : ℚ) : RawPoly ℕ := if v = 0 then [] else [(v, [1])]

/-- The bucketed normal form of `v·h(-1)1`. -/
def expect (v : ℚ) : St := [(-2, []), (0, mon v), (2, [])]

theorem evalSt_expect (v : ℚ) : evalSt (expect v) = ((v : ℚ) : ℂ) • hV := by
  rw [expect, evalSt_three, mon]
  by_cases hv : v = 0
  · rw [if_pos hv, evRc_nil, map_zero, hv]; simp
  · rw [if_neg hv, sector_one]

theorem val_of_bucket (s : St) (hs : ∀ p ∈ s, p.1 ∈ [-2, 0, 2]) (v : ℚ)
    (h : bucket [-2, 0, 2] s = expect v) : evalSt s = ((v : ℚ) : ℂ) • hV := by
  rw [← evalSt_bucket _ (by decide) _ hs, h, evalSt_expect]

theorem JE_sectors (a b : ℤ) (Z : St) (hZ : ∀ p ∈ Z, p.1 ∈ [-1, 1]) :
    ∀ p ∈ actJ a (actE b Z), p.1 ∈ [-2, 0, 2] :=
  actJ_sectors _ _ _ (actE_sectors _ _ hZ)

theorem EJ_sectors (a b : ℤ) (Z : St) (hZ : ∀ p ∈ Z, p.1 ∈ [-1, 1]) :
    ∀ p ∈ actE a (actJ b Z), p.1 ∈ [-2, 0, 2] :=
  actE_sectors _ _ (actJ_sectors _ _ _ hZ)

/-- The Boolean check of all `J E` terms. -/
def checkA (N : ℤ) (B : ℕ) (Z : St) (a : ℕ → ℕ → ℚ) : Bool :=
  (List.range 6).all fun j => (List.range B).all fun i =>
    bucket [-2, 0, 2] (actJ ((j : ℤ) - 2 - i) (actE (N - j + i) Z)) == expect (a j i)

theorem hA_of_check (N : ℤ) (B : ℕ) (Z : St) (hZ : ∀ p ∈ Z, p.1 ∈ [-1, 1])
    (a : ℕ → ℕ → ℚ) (h : checkA N B Z a = true) :
    ∀ j : ℕ, j < 6 → ∀ i : ℕ, i < B →
      evalSt (actJ ((j : ℤ) - 2 - i) (actE (N - j + i) Z)) = ((a j i : ℚ) : ℂ) • hV := by
  intro j hj i hi
  simp only [checkA, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact val_of_bucket _ (JE_sectors _ _ _ hZ) _ (h j hj i hi)

/-- The Boolean check of the `E J` terms with index in `is`, on the whole state. -/
def checkT (N : ℤ) (is : List ℕ) (Z : St) (t : ℕ → ℚ) : Bool :=
  is.all fun i => bucket [-2, 0, 2] (actE (N - 2 - i) (actJ i Z)) == expect (t i)

theorem hT_of_check (N : ℤ) (is : List ℕ) (Z : St) (hZ : ∀ p ∈ Z, p.1 ∈ [-1, 1])
    (t : ℕ → ℚ) (h : checkT N is Z t = true) :
    ∀ i ∈ is, evalSt (actE (N - 2 - i) (actJ i Z)) = ((t i : ℚ) : ℂ) • hV := by
  intro i hi
  simp only [checkT, List.all_eq_true, beq_iff_eq] at h
  exact val_of_bucket _ (EJ_sectors _ _ _ hZ) _ (h i hi)

/-! ## Splitting into monomials -/

/-- One single-monomial state for every monomial of `s`. -/
def pieces (s : St) : List St := s.flatMap fun p => p.2.map fun t => [(p.1, [t])]

theorem evalSt_single (d : ℤ) (P : RawPoly ℕ) :
    evalSt [(d, P)] = ((P.map fun t => [(d, [t])]).map evalSt).sum := by
  induction P with
  | nil => simp [evalSt_cons, evRc_nil]
  | cons t P ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, ← ih]
    simp only [evalSt_cons, evalSt_nil, add_zero]
    rw [show t :: P = [t] ++ P from rfl, evRc_append, map_add]

theorem evalSt_pieces (s : St) : evalSt s = ((pieces s).map evalSt).sum := by
  induction s with
  | nil => simp [pieces]
  | cons p s ih =>
    rw [pieces, List.flatMap_cons, ← pieces, List.map_append, List.sum_append, ← ih,
      ← evalSt_single, show p :: s = [p] ++ s from rfl, evalSt_append]

/-- The linear map `x ↦ E₍ₐ₎ J₍ᵦ₎ x`. -/
noncomputable def EJmap (a b : ℤ) : LatModuleGen (latP 4) →ₗ[ℂ] LatModuleGen (latP 4) :=
  (mode ((V2m 4 four_ge_one).Y Ec) a) ∘ₗ (mode ((V2m 4 four_ge_one).Y Jc) b)

theorem EJmap_apply (a b : ℤ) (Z : St) : EJmap a b (evalSt Z) = evalSt (actE a (actJ b Z)) := by
  rw [← actE_sound, ← actJ_sound]; rfl

theorem evalSt_EJ_pieces (a b : ℤ) (Z : St) :
    evalSt (actE a (actJ b Z)) = ((pieces Z).map fun q => evalSt (actE a (actJ b q))).sum := by
  rw [← EJmap_apply, evalSt_pieces, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  exact EJmap_apply a b q

theorem pieces_sectors (Z : St) (hZ : ∀ p ∈ Z, p.1 ∈ [-1, 1]) :
    ∀ q ∈ pieces Z, ∀ p ∈ q, p.1 ∈ [-1, 1] := by
  intro q hq p hp
  simp only [pieces, List.mem_flatMap, List.mem_map] at hq
  obtain ⟨p', hp', t, -, rfl⟩ := hq
  simp only [List.mem_singleton] at hp
  rw [hp]
  exact hZ p' hp'

/-- A sum over a list of values given pointwise. -/
theorem sum_of_vals (qs : List St) (f : St → LatModuleGen (latP 4)) (vs : List ℚ)
    (h : List.Forall₂ (fun q v => f q = ((v : ℚ) : ℂ) • hV) qs vs) :
    (qs.map f).sum = ((vs.sum : ℚ) : ℂ) • hV := by
  induction h with
  | nil => simp
  | cons hqv _ ih => rw [List.map_cons, List.sum_cons, hqv, ih, List.sum_cons, Rat.cast_add,
      add_smul]

end VOA.Classification.COne.OrbRat4
