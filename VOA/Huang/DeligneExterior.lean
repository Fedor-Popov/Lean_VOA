/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneTrace

/-!
# Deligne's theorem — exterior powers in a symmetric category

Let `C` be a symmetric monoidal category and `X : C`.  On the tensor powers `X^{⊗n}` (`tpow`,
left-nested) we define the adjacent transpositions `tsw X n i` (swap strands `i, i+1`) and prove
the Coxeter relations (`tsw_comp_self`, `tsw_comm`, `tsw_braid`).  No presentation of the symmetric
group is needed: the **antisymmetrizer** is defined by the recursion

  `e₀ = 𝟙`,  `e_{k+1} = (k+1)⁻¹ Σ_{j ≤ k} (-1)^{k-j} (e_k ⊗ 1) ∘ P_j`,

where `P_j = s_{k-1} ⋯ s_j` moves the last strand to position `j` (the coset representatives of
`S_k` in `S_{k+1}`), and everything is proved from the relations:

* `antisym_comp_tsw` — `e_k ∘ s_i = -e_k` (right absorption);
* `antisym_idem` — `e_k ∘ e_k = e_k`;
* `trMor_antisym` — `tr e_k = d(d-1)⋯(d-k+1)/k!` with `d` the braided dimension of `X`
  (via the braided partial trace `ptr`, `trMor_ptr`, `ptr_lastSwap` = Reidemeister I).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.TensorCat

open CategoryTheory MonoidalCategory Limits Module

universe v u

section Transpositions

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] (X : C)

/-- The swap of the last two strands of `(B ⊗ X) ⊗ X`. -/
def lastSwap (B : C) : (B ⊗ X) ⊗ X ⟶ (B ⊗ X) ⊗ X :=
  (α_ B X X).hom ≫ B ◁ (β_ X X).hom ≫ (α_ B X X).inv

/-- The adjacent transposition of strands `i, i+1` on `X^{⊗n}` (identity if `i + 1 ≥ n`). -/
def tsw : (n : ℕ) → ℕ → (tpow X n ⟶ tpow X n)
  | 0, _ => 𝟙 _
  | 1, _ => 𝟙 _
  | n + 2, i => if i = n then lastSwap X (tpow X n) else if i < n then tsw (n + 1) i ▷ X else 𝟙 _

variable {X}

theorem tsw_last (n : ℕ) : tsw X (n + 2) n = lastSwap X (tpow X n) := by
  simp [tsw]

theorem tsw_succ_of_lt {n i : ℕ} (h : i + 1 < n) : tsw X (n + 1) i = tsw X n i ▷ X := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : i ≠ m := by omega
  have h2 : i < m := by omega
  simp [tsw, h1, h2]

theorem tsw_of_le {n i : ℕ} (h : n ≤ i + 1) : tsw X n i = 𝟙 _ := by
  match n, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | m + 2, h =>
    have h1 : i ≠ m := by omega
    have h2 : ¬ i < m := by omega
    simp [tsw, h1, h2]

theorem lastSwap_comp_self (B : C) : lastSwap X B ≫ lastSwap X B = 𝟙 _ := by
  simp [lastSwap, ← whiskerLeft_comp_assoc]

/-- `s_i ∘ s_i = 𝟙`. -/
theorem tsw_comp_self (n i : ℕ) : tsw X n i ≫ tsw X n i = 𝟙 _ := by
  induction n with
  | zero => simp [tsw]
  | succ n ih =>
    rcases Nat.lt_or_ge (i + 1) n with h | h
    · rw [tsw_succ_of_lt h]; erw [← comp_whiskerRight, ih, id_whiskerRight]
    · rcases Nat.lt_or_ge (i + 1) (n + 1) with h' | h'
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        obtain rfl : i = m := by omega
        rw [tsw_last]; exact lastSwap_comp_self _
      · rw [tsw_of_le h', Category.comp_id]

theorem lastSwap_comm {B : C} (b : B ⟶ B) :
    ((b ▷ X) ▷ X) ≫ lastSwap X B = lastSwap X B ≫ ((b ▷ X) ▷ X) := by
  simp only [lastSwap, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc]
  simp

/-- Far transpositions commute. -/
theorem tsw_comm (n : ℕ) {i j : ℕ} (hij : i + 2 ≤ j) :
    tsw X n i ≫ tsw X n j = tsw X n j ≫ tsw X n i := by
  induction n with
  | zero => simp [tsw]
  | succ n ih =>
    rcases Nat.lt_or_ge (j + 1) n with h | h
    · rw [tsw_succ_of_lt h, tsw_succ_of_lt (by omega : i + 1 < n)]
      erw [← comp_whiskerRight, ih, comp_whiskerRight]
    · rcases Nat.lt_or_ge (j + 1) (n + 1) with h' | h'
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        obtain rfl : j = m := by omega
        obtain ⟨p, rfl⟩ : ∃ p, j = p + 1 := ⟨j - 1, by omega⟩
        rw [tsw_last, tsw_succ_of_lt (by omega : i + 1 < p + 1 + 1),
          tsw_succ_of_lt (by omega : i + 1 < p + 1)]
        exact lastSwap_comm _
      · rw [tsw_of_le h', Category.comp_id, Category.id_comp]

/-- Yang–Baxter for the last three strands. -/
theorem lastSwap_braid (B : C) :
    (lastSwap X B ▷ X) ≫ lastSwap X (B ⊗ X) ≫ (lastSwap X B ▷ X) =
      lastSwap X (B ⊗ X) ≫ (lastSwap X B ▷ X) ≫ lastSwap X (B ⊗ X) := by
  have yb := BraidedCategory.yang_baxter' X X X
  simp only [lastSwap]
  calc
    _ = 𝟙 _ ⊗≫ B ◁ ((β_ X X).hom ▷ X ⊗≫ X ◁ (β_ X X).hom ⊗≫ (β_ X X).hom ▷ X) ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ B ◁ (X ◁ (β_ X X).hom ⊗≫ (β_ X X).hom ▷ X ⊗≫ X ◁ (β_ X X).hom) ⊗≫ 𝟙 _ := by
      rw [yb]; monoidal
    _ = _ := by monoidal

/-- The braid relation `s_i s_{i+1} s_i = s_{i+1} s_i s_{i+1}` (for `i + 2 < n`). -/
theorem tsw_braid {n i : ℕ} (h : i + 2 < n) :
    tsw X n i ≫ tsw X n (i + 1) ≫ tsw X n i = tsw X n (i + 1) ≫ tsw X n i ≫ tsw X n (i + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge (i + 2) n with h' | h'
    · rw [tsw_succ_of_lt (by omega : i + 1 < n), tsw_succ_of_lt (by omega : i + 1 + 1 < n)]
      erw [← comp_whiskerRight, ← comp_whiskerRight, ih h', comp_whiskerRight, comp_whiskerRight]
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
      obtain rfl : p = i := by omega
      rw [show p + 1 = p + 1 from rfl, tsw_last (p + 1), tsw_succ_of_lt (by omega : p + 1 < p + 2),
        tsw_last p]
      exact lastSwap_braid _

/-! ### The cycles `P` -/

/-- `cyc n j m = s_{j+m-1} ≫ ⋯ ≫ s_{j+1} ≫ s_j` (diagrammatic order): moves strand `j + m` to
position `j`. -/
def cyc (n j : ℕ) : ℕ → (tpow X n ⟶ tpow X n)
  | 0 => 𝟙 _
  | m + 1 => cyc n (j + 1) m ≫ tsw X n j

theorem cyc_zero (n j : ℕ) : cyc (X := X) n j 0 = 𝟙 _ := rfl

theorem cyc_succ (n j m : ℕ) : cyc (X := X) n j (m + 1) = cyc n (j + 1) m ≫ tsw X n j := rfl

/-- (a) `cyc j m` commutes with `s_i` for `i + 2 ≤ j`. -/
theorem cyc_comm_tsw (n : ℕ) {i j : ℕ} (m : ℕ) (h : i + 2 ≤ j) :
    cyc (X := X) n j m ≫ tsw X n i = tsw X n i ≫ cyc n j m := by
  induction m generalizing j with
  | zero => simp [cyc_zero]
  | succ m ih =>
    rw [cyc_succ, Category.assoc, ← tsw_comm n h, ← Category.assoc, ih (by omega), Category.assoc]

/-- (c) `cyc j (m+1) ≫ s_j = cyc (j+1) m`. -/
theorem cyc_succ_comp_tsw (n j m : ℕ) :
    cyc (X := X) n j (m + 1) ≫ tsw X n j = cyc n (j + 1) m := by
  rw [cyc_succ, Category.assoc, tsw_comp_self, Category.comp_id]

/-- (d) `cyc j m ≫ s_i = s_{i-1} ≫ cyc j m` for `j + 1 ≤ i < j + m`, `j + m < n`. -/
theorem cyc_comp_tsw_shift {n : ℕ} {j m i : ℕ} (hn : j + m < n) (h1 : j + 1 ≤ i)
    (h2 : i < j + m) :
    cyc (X := X) n j m ≫ tsw X n i = tsw X n (i - 1) ≫ cyc n j m := by
  induction m generalizing j with
  | zero => omega
  | succ m ih =>
    rw [cyc_succ, Category.assoc]
    rcases Nat.lt_or_ge (j + 1) i with hi | hi
    · -- `i ≥ j + 2`
      rw [tsw_comm n (by omega : j + 2 ≤ i), ← Category.assoc, ih (by omega) (by omega) (by omega),
        Category.assoc]
    · -- `i = j + 1`
      obtain rfl : i = j + 1 := by omega
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [cyc_succ n (j + 1) m', Category.assoc, ← tsw_braid (by omega : j + 2 < n),
        ← Category.assoc, cyc_comm_tsw n m' (by omega : j + 2 ≤ j + 1 + 1), Category.assoc,
        show j + 1 - 1 = j by omega]
      simp only [Category.assoc]

end Transpositions

section Antisymmetrizer

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] (X : C)

theorem neg_whiskerRight' {A B : C} (f : A ⟶ B) (W : C) : (-f) ▷ W = -(f ▷ W) := by
  rw [eq_neg_iff_add_eq_zero, ← MonoidalPreadditive.add_whiskerRight, neg_add_cancel,
    MonoidalPreadditive.zero_whiskerRight]

/-- The **antisymmetrizer** `e_k` on `X^{⊗k}`, by the coset recursion
`e_{k+1} = (k+1)⁻¹ Σ_{j ≤ k} (-1)^{k-j} (e_k ⊗ 1) ∘ P_j`. -/
def antisym : (k : ℕ) → (tpow X k ⟶ tpow X k)
  | 0 => 𝟙 _
  | k + 1 => ((k + 1 : ℂ)⁻¹) • ∑ j ∈ Finset.range (k + 1),
      ((-1 : ℂ) ^ (k - j)) • ((antisym k ▷ X : tpow X (k + 1) ⟶ tpow X (k + 1)) ≫ cyc (k + 1) j (k - j))

variable {X}

theorem antisym_zero : antisym X 0 = 𝟙 _ := rfl

theorem antisym_succ (k : ℕ) : antisym X (k + 1) = ((k + 1 : ℂ)⁻¹) • ∑ j ∈ Finset.range (k + 1),
    ((-1 : ℂ) ^ (k - j)) • ((antisym X k ▷ X : tpow X (k + 1) ⟶ tpow X (k + 1)) ≫ cyc (k + 1) j (k - j)) := rfl

/-- Right absorption one level up: `(e_k ⊗ 1) ∘ s_i = -(e_k ⊗ 1)` for `i + 1 < k`. -/
theorem antisym_whisker_comp_tsw {k i : ℕ} (hi : i + 1 < k)
    (h : antisym X k ≫ tsw X k i = -antisym X k) :
    ((antisym X k ▷ X) ≫ tsw X (k + 1) i : tpow X (k + 1) ⟶ tpow X (k + 1)) = -(antisym X k ▷ X) := by
  rw [tsw_succ_of_lt hi]
  erw [← comp_whiskerRight, h, neg_whiskerRight']

/-- **Right absorption**: `e_k ∘ s_i = -e_k` for every adjacent transposition `s_i` of
`X^{⊗k}`. -/
theorem antisym_comp_tsw (k : ℕ) : ∀ i, i + 1 < k → antisym X k ≫ tsw X k i = -antisym X k := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    have hik : i < k := by omega
    set E : tpow X (k + 1) ⟶ tpow X (k + 1) := antisym X k ▷ X with hE
    -- the summands
    set f : ℕ → (tpow X (k + 1) ⟶ tpow X (k + 1)) :=
      fun j => ((-1 : ℂ) ^ (k - j)) • (E ≫ cyc (k + 1) j (k - j)) with hf
    have habs : ∀ i', i' + 1 < k → E ≫ tsw X (k + 1) i' = -E := fun i' hi' =>
      antisym_whisker_comp_tsw hi' (ih i' hi')
    have key : ∀ j ∈ Finset.range (k + 1),
        f j ≫ tsw X (k + 1) i = -(f (Equiv.swap i (i + 1) j)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      simp only [hf, Linear.smul_comp, Category.assoc]
      rcases lt_trichotomy j i with hji | rfl | hji
      · -- `j < i`
        rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega),
          cyc_comp_tsw_shift (by omega : j + (k - j) < k + 1) (by omega) (by omega),
          ← Category.assoc, habs (i - 1) (by omega), Preadditive.neg_comp, smul_neg]
      · -- `j = i`
        rw [Equiv.swap_apply_left, show k - j = (k - (j + 1)) + 1 by omega,
          cyc_succ_comp_tsw, pow_succ, mul_neg_one, neg_smul]
      · rcases Nat.lt_or_ge (i + 1) j with hji' | hji'
        · -- `j ≥ i + 2`
          rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega),
            cyc_comm_tsw (k + 1) (k - j) (by omega : i + 2 ≤ j), ← Category.assoc,
            habs i (by omega), Preadditive.neg_comp, smul_neg]
        · -- `j = i + 1`
          obtain rfl : j = i + 1 := by omega
          rw [Equiv.swap_apply_right, show k - i = (k - (i + 1)) + 1 by omega, ← cyc_succ,
            pow_succ, mul_neg_one, neg_smul, neg_neg]
    rw [antisym_succ]
    erw [Linear.smul_comp, Preadditive.sum_comp]
    change ((k + 1 : ℂ)⁻¹) • ∑ j ∈ Finset.range (k + 1), f j ≫ tsw X (k + 1) i =
      -(((k + 1 : ℂ)⁻¹) • ∑ j ∈ Finset.range (k + 1), f j)
    rw [Finset.sum_congr rfl key, Finset.sum_neg_distrib, smul_neg, neg_inj]
    congr 1
    exact Finset.sum_equiv (Equiv.swap i (i + 1))
      (fun j => by
        simp only [Finset.mem_range]
        constructor
        · intro hj
          rcases eq_or_ne j i with rfl | h1
          · rw [Equiv.swap_apply_left]; omega
          rcases eq_or_ne j (i + 1) with rfl | h2
          · rw [Equiv.swap_apply_right]; omega
          rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hj
        · intro hj
          rcases eq_or_ne j i with rfl | h1
          · omega
          rcases eq_or_ne j (i + 1) with rfl | h2
          · omega
          rwa [Equiv.swap_apply_of_ne_of_ne h1 h2] at hj)
      (fun j _ => rfl)

/-- A morphism absorbing every `s_i ▷ W` with sign `-1` absorbs the cycles with sign `(-1)^m`. -/
theorem comp_cyc_whisker {k : ℕ} {W Z : C} (ψ : Z ⟶ tpow X k ⊗ W)
    (hψ : ∀ i, i + 1 < k → ψ ≫ (tsw X k i ▷ W) = -ψ) :
    ∀ (m j : ℕ), j + m < k → ψ ≫ (cyc k j m ▷ W) = ((-1 : ℂ) ^ m) • ψ := by
  intro m
  induction m with
  | zero => intro j _; simp [cyc_zero]
  | succ m ih =>
    intro j hj
    rw [cyc_succ, comp_whiskerRight, ← Category.assoc, ih (j + 1) (by omega), Linear.smul_comp,
      hψ j (by omega), smul_neg, pow_succ, mul_neg_one, neg_smul]

/-- **Absorption**: a morphism absorbing every `s_i ▷ W` with sign `-1` is fixed by `e_k ▷ W`. -/
theorem comp_antisym_whisker (k : ℕ) : ∀ {W Z : C} (ψ : Z ⟶ tpow X k ⊗ W),
    (∀ i, i + 1 < k → ψ ≫ (tsw X k i ▷ W) = -ψ) → ψ ≫ (antisym X k ▷ W) = ψ := by
  induction k with
  | zero => intro W Z ψ _; simp [antisym_zero]
  | succ k ih =>
    intro W Z ψ hψ
    -- `ψ` is fixed by `(e_k ▷ X) ▷ W`
    have h1 : ψ ≫ ((antisym X k ▷ X : tpow X (k + 1) ⟶ tpow X (k + 1)) ▷ W) = ψ := by
      have := ih (W := X ⊗ W) (ψ ≫ (α_ (tpow X k) X W).hom) (fun i hi => by
        rw [Category.assoc]
        erw [← associator_naturality_left]
        rw [← Category.assoc]
        have h' := hψ i (by omega)
        rw [tsw_succ_of_lt hi] at h'
        erw [h', Preadditive.neg_comp])
      rw [Category.assoc] at this
      erw [← associator_naturality_left] at this
      rw [← Category.assoc] at this
      exact (cancel_mono _).mp this
    rw [antisym_succ]
    erw [MonoidalLinear.smul_whiskerRight, sum_whiskerRight, Linear.comp_smul, Preadditive.comp_sum]
    have h2 : ∀ j ∈ Finset.range (k + 1), ψ ≫ ((((-1 : ℂ) ^ (k - j)) •
        ((antisym X k ▷ X : tpow X (k + 1) ⟶ tpow X (k + 1)) ≫ cyc (k + 1) j (k - j))) ▷ W) = ψ := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [MonoidalLinear.smul_whiskerRight, comp_whiskerRight]
      erw [Linear.comp_smul]
      rw [← Category.assoc, h1, comp_cyc_whisker ψ hψ (k - j) j (by omega), smul_smul, ← mul_pow, neg_one_mul, neg_neg,
        one_pow, one_smul]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by norm_cast), one_smul]

/-- **Idempotence** `e_k ∘ e_k = e_k`. -/
theorem antisym_idem (k : ℕ) : antisym X k ≫ antisym X k = antisym X k := by
  have h := comp_antisym_whisker k (W := 𝟙_ C) (antisym X k ≫ (ρ_ _).inv) (fun i hi => by
    rw [Category.assoc, ← rightUnitor_inv_naturality, ← Category.assoc, antisym_comp_tsw k i hi,
      Preadditive.neg_comp])
  rw [Category.assoc, ← rightUnitor_inv_naturality, ← Category.assoc] at h
  exact (cancel_mono _).mp h

end Antisymmetrizer

section PartialTrace

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] [RightRigidCategory C]

/-- The braided **partial trace** over the last factor: `ptr φ = (1 ⊗ ε c)(φ ⊗ 1)(1 ⊗ η)`. -/
def ptr {A Y : C} (φ : A ⊗ Y ⟶ A ⊗ Y) : A ⟶ A :=
  (ρ_ A).inv ≫ A ◁ η_ Y Yᘁ ≫ (α_ A Y Yᘁ).inv ≫ φ ▷ Yᘁ ≫ (α_ A Y Yᘁ).hom ≫
    A ◁ ((β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ) ≫ (ρ_ A).hom

theorem ptr_whisker_comp {A Y : C} (a : A ⟶ A) (φ : A ⊗ Y ⟶ A ⊗ Y) :
    ptr ((a ▷ Y) ≫ φ) = a ≫ ptr φ := by
  simp only [ptr, comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc]

theorem ptr_comp_whisker {A Y : C} (φ : A ⊗ Y ⟶ A ⊗ Y) (b : A ⟶ A) :
    ptr (φ ≫ (b ▷ Y)) = ptr φ ≫ b := by
  simp only [ptr, comp_whiskerRight, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]

theorem ptr_add {A Y : C} (φ ψ : A ⊗ Y ⟶ A ⊗ Y) : ptr (φ + ψ) = ptr φ + ptr ψ := by
  simp [ptr]

theorem ptr_smul {A Y : C} (c : ℂ) (φ : A ⊗ Y ⟶ A ⊗ Y) : ptr (c • φ) = c • ptr φ := by
  simp [ptr]

theorem ptr_id {A Y : C} {d : ℂ} (hd : trMor (𝟙 Y) = d • 𝟙 (𝟙_ C)) : ptr (𝟙 (A ⊗ Y)) = d • 𝟙 A := by
  have hd' : η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ = d • 𝟙 (𝟙_ C) := by rw [← hd, trMor_id]
  calc ptr (𝟙 (A ⊗ Y)) = (ρ_ A).inv ≫ A ◁ (η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ) ≫ (ρ_ A).hom := by
        simp [ptr]
    _ = d • 𝟙 A := by rw [hd']; simp

/-- Reidemeister I: the partial trace of the braiding `c_{X,X}` is `𝟙_X`. -/
theorem ptr_braiding (X : C) : ptr (β_ X X).hom = 𝟙 X := by
  unfold ptr
  calc
    _ = 𝟙 _ ⊗≫ X ◁ η_ X Xᘁ ⊗≫ ((β_ X X).hom ▷ Xᘁ ⊗≫ X ◁ (β_ X Xᘁ).hom) ⊗≫ X ◁ ε_ X Xᘁ ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ (X ◁ η_ X Xᘁ ≫ (β_ X (X ⊗ Xᘁ)).hom) ⊗≫ X ◁ ε_ X Xᘁ ⊗≫ 𝟙 _ := by
      rw [BraidedCategory.braiding_tensor_right_hom]; monoidal
    _ = 𝟙 _ ⊗≫ ((β_ X (𝟙_ C)).hom ≫ η_ X Xᘁ ▷ X) ⊗≫ X ◁ ε_ X Xᘁ ⊗≫ 𝟙 _ := by
      rw [BraidedCategory.braiding_naturality_right]
    _ = 𝟙 _ ⊗≫ (η_ X Xᘁ ▷ X ⊗≫ X ◁ ε_ X Xᘁ) ⊗≫ 𝟙 _ := by
      simp only [braiding_tensorUnit_right]; monoidal
    _ = _ := by
      rw [ExactPairing.evaluation_coevaluation'']; monoidal

variable (X : C)

/-- The partial trace of the last swap is the identity. -/
theorem ptr_lastSwap (B : C) : ptr (lastSwap X B) = 𝟙 (B ⊗ X) := by
  have h := ptr_braiding X
  unfold ptr at h ⊢
  unfold lastSwap
  calc
    _ = 𝟙 _ ⊗≫ B ◁ ((ρ_ X).inv ≫ X ◁ η_ X Xᘁ ≫ (α_ X X Xᘁ).inv ≫ (β_ X X).hom ▷ Xᘁ ≫
          (α_ X X Xᘁ).hom ≫ X ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) ≫ (ρ_ X).hom) ⊗≫ 𝟙 _ := by
      monoidal
    _ = _ := by rw [h]; monoidal

variable {X}

/-- The trace of a partial trace is the trace. -/
theorem trMor_ptr {A Y : C} (φ : A ⊗ Y ⟶ A ⊗ Y) : trMor (ptr φ) = trMor φ := by
  rw [trMor_eq_trWith φ (tensorPairing A Aᘁ Y Yᘁ)]
  have hev := braiding_tensorPairing_eval A Aᘁ Y Yᘁ
  change _ = (η_ A Aᘁ ⊗≫ A ◁ η_ Y Yᘁ ▷ Aᘁ ⊗≫ 𝟙 _) ≫ φ ▷ (Yᘁ ⊗ Aᘁ) ≫
      (β_ (A ⊗ Y) (Yᘁ ⊗ Aᘁ)).hom ≫ (𝟙 _ ⊗≫ Yᘁ ◁ ε_ A Aᘁ ▷ Y ⊗≫ ε_ Y Yᘁ)
  rw [hev]
  simp only [trMor, ptr, comp_whiskerRight]
  monoidal

end PartialTrace

section TraceOfAntisymmetrizer

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] [RightRigidCategory C]
  {X : C}

/-- `tr 𝟙_𝟙 = 𝟙`. -/
theorem trMor_id_unit : trMor (𝟙 (𝟙_ C)) = 𝟙 (𝟙_ C) := by
  rw [trMor_eq_trWith (𝟙 (𝟙_ C)) exactPairingUnit]
  simp only [trWith, id_whiskerRight, Category.id_comp]
  exact (by simp [unitors_inv_equal] : (ρ_ (𝟙_ C)).inv ≫ (β_ (𝟙_ C) (𝟙_ C)).hom ≫
    (ρ_ (𝟙_ C)).hom = 𝟙 _)

/-- The cycle `P_j` on `X^{⊗(k+2)}` starts with the last swap. -/
theorem cyc_succ_eq_lastSwap (k : ℕ) : ∀ (m j : ℕ), j + m = k →
    cyc (X := X) (k + 2) j (m + 1) = lastSwap X (tpow X k) ≫ (cyc (k + 1) j m ▷ X) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    subst hj
    simp [cyc_succ, cyc_zero, tsw_last]
  | succ m ih =>
    intro j hj
    rw [cyc_succ, ih (j + 1) (by omega), tsw_succ_of_lt (by omega : j + 1 < k + 1), Category.assoc,
      ← comp_whiskerRight, ← cyc_succ]

/-- `e_k ∘ P = (-1)^m e_k` for a cycle `P` of length `m` inside `X^{⊗k}`. -/
theorem antisym_comp_cyc (k : ℕ) : ∀ (m j : ℕ), j + m < k →
    antisym X k ≫ cyc k j m = ((-1 : ℂ) ^ m) • antisym X k := by
  intro m
  induction m with
  | zero => intro j _; simp [cyc_zero]
  | succ m ih =>
    intro j hj
    rw [cyc_succ, ← Category.assoc, ih (j + 1) (by omega), Linear.smul_comp,
      antisym_comp_tsw k j (by omega), smul_neg, pow_succ, mul_neg_one, neg_smul]

theorem trMor_antisym_term (k j : ℕ) (hj : j < k) :
    trMor ((antisym X k ▷ X : tpow X (k + 1) ⟶ tpow X (k + 1)) ≫ cyc (k + 1) j (k - j)) =
      ((-1 : ℂ) ^ (k - 1 - j)) • trMor (antisym X k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [show k' + 1 - j = (k' - j) + 1 by omega, cyc_succ_eq_lastSwap k' (k' - j) j (by omega),
    ← trMor_ptr]
  erw [ptr_whisker_comp, ptr_comp_whisker, ptr_lastSwap, Category.id_comp]
  rw [antisym_comp_cyc (k' + 1) (k' - j) j (by omega), trMor_smul, show k' + 1 - 1 - j = k' - j by omega]

/-- **The trace of the antisymmetrizer**: `tr e_k = d(d-1)⋯(d-k+1)/k!` where `d` is the
braided dimension of `X`. -/
theorem trMor_antisym {d : ℂ} (hd : trMor (𝟙 X) = d • 𝟙 (𝟙_ C)) (k : ℕ) :
    trMor (antisym X k) = ((descPochhammer ℂ k).eval d / (k.factorial : ℂ)) • 𝟙 (𝟙_ C) := by
  induction k with
  | zero => simp [antisym_zero, trMor_id_unit]
  | succ k ih =>
    rw [antisym_succ, trMor_smul, trMor_sum, Finset.sum_range_succ]
    simp only [trMor_smul]
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [trMor_antisym_term k j (Finset.mem_range.mp hj), smul_smul, ← pow_add,
        show k - j + (k - 1 - j) = 2 * (k - 1 - j) + 1 by have := Finset.mem_range.mp hj; omega,
        pow_succ, pow_mul, neg_one_sq, one_pow, one_mul])]
    rw [Nat.sub_self, pow_zero, one_smul, cyc_zero, Category.comp_id, ← trMor_ptr]
    erw [← Category.comp_id (antisym X k ▷ X), ptr_whisker_comp, ptr_id hd]
    rw [Linear.comp_smul, Category.comp_id, trMor_smul, ih, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℂ]
    simp only [smul_smul]
    rw [← add_smul, smul_smul]
    congr 1
    rw [descPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    field_simp
    ring

end TraceOfAntisymmetrizer

end VOA.Huang.TensorCat
