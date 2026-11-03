/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneFiberComplete

/-!
# Deligne's fiber functor — the symmetrizer and symmetric powers

In a symmetric (`ℂ`-linear) monoidal category, on the left-nested tensor powers `X^{⊗n}` (`tpow`):

* the **inverse cycles** `cycI n j m = s_j ≫ s_{j+1} ≫ ⋯ ≫ s_{j+m-1}` (move strand `j` to
  position `j + m`), with the commutation rules `tsw_comp_cycI_far`, `tsw_comp_cycI_shift`;
* the **symmetrizer** `symL X k` by the *left* coset recursion
  `σ_{k+1} = (k+1)⁻¹ Σ_{j ≤ k} cycI (k+1) j (k-j) ≫ (σ_k ▷ X)`;
* `tsw_comp_symL` — `s_i ≫ σ_k = σ_k` (invariance under every adjacent transposition applied
  first), `symL_whisker_comp` (absorption), `symL_idem`;
* concatenation `cat a b : X^{⊗a} ⊗ X^{⊗b} ⟶ X^{⊗(a+b)}` with its coherence (`cat_assoc`,
  `cat_zero_left`), and the block lemmas: `whiskerRight_cat`, `whiskerLeft_tsw_cat`,
  `cat_cycI_mv` (moving a strand past a block), `symL_whiskerLeft_absorb`,
  `symL_whiskerRight_absorb`, `braiding_cat_symL` (block swap).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false

noncomputable section

namespace VOA.Huang.TensorCat.DeligneFiber

open CategoryTheory MonoidalCategory Limits Module

universe v u

section Words

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] (X : C)

/-- `cycI n j m = s_j ≫ s_{j+1} ≫ ⋯ ≫ s_{j+m-1}`: moves strand `j` to position `j + m`. -/
def cycI (n j : ℕ) : ℕ → (tpow X n ⟶ tpow X n)
  | 0 => 𝟙 _
  | m + 1 => tsw X n j ≫ cycI n (j + 1) m

variable {X}

theorem cycI_zero (n j : ℕ) : cycI X n j 0 = 𝟙 _ := rfl

theorem cycI_succ (n j m : ℕ) : cycI X n j (m + 1) = tsw X n j ≫ cycI X n (j + 1) m := rfl

theorem cycI_add (n : ℕ) : ∀ (m₁ m₂ j : ℕ), cycI X n j (m₁ + m₂) = cycI X n j m₁ ≫ cycI X n (j + m₁) m₂ := by
  intro m₁
  induction m₁ with
  | zero => intro m₂ j; simp [cycI_zero]
  | succ m ih =>
    intro m₂ j
    rw [show m + 1 + m₂ = (m + m₂) + 1 by omega, cycI_succ, ih, cycI_succ, Category.assoc,
      show j + 1 + m = j + (m + 1) by omega]

theorem cycI_succ' (n j m : ℕ) : cycI X n j (m + 1) = cycI X n j m ≫ tsw X n (j + m) := by
  rw [cycI_add n m 1, cycI_succ, cycI_zero, Category.comp_id]

/-- Far transpositions commute with `cycI`. -/
theorem tsw_comp_cycI_far (n : ℕ) {i : ℕ} : ∀ (m j : ℕ), (i + 2 ≤ j ∨ j + m + 1 ≤ i) →
    tsw X n i ≫ cycI X n j m = cycI X n j m ≫ tsw X n i := by
  intro m
  induction m with
  | zero => intro j _; simp [cycI_zero]
  | succ m ih =>
    intro j h
    rw [cycI_succ, ← Category.assoc]
    rcases h with h | h
    · rw [tsw_comm n (by omega : i + 2 ≤ j), Category.assoc, ih (j + 1) (Or.inl (by omega)),
        Category.assoc]
    · rw [← tsw_comm n (by omega : j + 2 ≤ i), Category.assoc, ih (j + 1) (Or.inr (by omega)),
        Category.assoc]

/-- `s_i ≫ cycI j m = cycI j m ≫ s_{i-1}` for `j < i`, `i + 1 ≤ j + m`, `j + m < n`. -/
theorem tsw_comp_cycI_shift {n : ℕ} : ∀ (m j i : ℕ), j + m < n → j < i → i + 1 ≤ j + m →
    tsw X n i ≫ cycI X n j m = cycI X n j m ≫ tsw X n (i - 1) := by
  intro m
  induction m with
  | zero => intro j i _ h1 h2; omega
  | succ m ih =>
    intro j i hn h1 h2
    rw [cycI_succ]
    rcases Nat.lt_or_ge (j + 1) i with hi | hi
    · rw [← Category.assoc, ← tsw_comm n (by omega : j + 2 ≤ i), Category.assoc,
        ih (j + 1) i (by omega) hi (by omega), Category.assoc]
    · obtain rfl : i = j + 1 := by omega
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [cycI_succ, show j + 1 - 1 = j by omega]
      have hb := tsw_braid (X := X) (n := n) (i := j) (by omega)
      have hf := tsw_comp_cycI_far (X := X) n (i := j) m' (j + 1 + 1) (Or.inl (by omega))
      calc tsw X n (j + 1) ≫ tsw X n j ≫ tsw X n (j + 1) ≫ cycI X n (j + 1 + 1) m'
          = (tsw X n (j + 1) ≫ tsw X n j ≫ tsw X n (j + 1)) ≫ cycI X n (j + 1 + 1) m' := by
            simp only [Category.assoc]
        _ = (tsw X n j ≫ tsw X n (j + 1) ≫ tsw X n j) ≫ cycI X n (j + 1 + 1) m' := by rw [hb]
        _ = tsw X n j ≫ tsw X n (j + 1) ≫ (tsw X n j ≫ cycI X n (j + 1 + 1) m') := by
            simp only [Category.assoc]
        _ = _ := by rw [hf]; simp only [Category.assoc]

/-- `cycI` on `X^{⊗(n+1)}` inside the first `n` strands is a whiskering. -/
theorem cycI_succ_of_lt {n : ℕ} : ∀ (m j : ℕ), j + m < n →
    cycI X (n + 1) j m = cycI X n j m ▷ X := by
  intro m
  induction m with
  | zero => intro j _; simp [cycI_zero]
  | succ m ih =>
    intro j h
    rw [cycI_succ, cycI_succ, ih (j + 1) (by omega), tsw_succ_of_lt (by omega), comp_whiskerRight]

end Words

section Symmetrizer

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] (X : C)

/-- The **symmetrizer** `σ_k` on `X^{⊗k}`, by the left coset recursion
`σ_{k+1} = (k+1)⁻¹ Σ_{j ≤ k} cycI (k+1) j (k-j) ≫ (σ_k ▷ X)`. -/
def symL : (k : ℕ) → (tpow X k ⟶ tpow X k)
  | 0 => 𝟙 _
  | k + 1 => ((k + 1 : ℂ)⁻¹) • ∑ j ∈ Finset.range (k + 1),
      (cycI X (k + 1) j (k - j) ≫ (symL k ▷ X : tpow X (k + 1) ⟶ tpow X (k + 1)))

variable {X}

theorem symL_zero : symL X 0 = 𝟙 _ := rfl

theorem symL_succ (k : ℕ) : symL X (k + 1) = ((k + 1 : ℂ)⁻¹) • ∑ j ∈ Finset.range (k + 1),
    (cycI X (k + 1) j (k - j) ≫ (symL X k ▷ X : tpow X (k + 1) ⟶ tpow X (k + 1))) := rfl

/-- **Invariance**: `s_i ≫ σ_k = σ_k`. -/
theorem tsw_comp_symL (k : ℕ) : ∀ i, i + 1 < k → tsw X k i ≫ symL X k = symL X k := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    set f : ℕ → (tpow X (k + 1) ⟶ tpow X (k + 1)) :=
      fun j => cycI X (k + 1) j (k - j) ≫ (symL X k ▷ X : tpow X (k + 1) ⟶ tpow X (k + 1)) with hf
    have habs : ∀ i', i' + 1 < k → tsw X (k + 1) i' ≫ (symL X k ▷ X : tpow X (k + 1) ⟶ tpow X (k + 1)) =
        (symL X k ▷ X : tpow X (k + 1) ⟶ tpow X (k + 1)) := fun i' hi' => by
      rw [tsw_succ_of_lt hi']
      erw [← comp_whiskerRight, ih i' hi']
    have key : ∀ j ∈ Finset.range (k + 1), tsw X (k + 1) i ≫ f j = f (Equiv.swap i (i + 1) j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      simp only [hf]
      rcases lt_trichotomy j i with hji | rfl | hji
      · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega), ← Category.assoc,
          tsw_comp_cycI_shift (k - j) j i (by omega) hji (by omega), Category.assoc,
          habs (i - 1) (by omega)]
      · rw [Equiv.swap_apply_left, show k - j = (k - (j + 1)) + 1 by omega, cycI_succ,
          ← Category.assoc, ← Category.assoc, tsw_comp_self, Category.id_comp]
      · rcases Nat.lt_or_ge (i + 1) j with hji' | hji'
        · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega), ← Category.assoc,
            tsw_comp_cycI_far (k + 1) (k - j) j (Or.inl (by omega)), Category.assoc, habs i (by omega)]
        · obtain rfl : j = i + 1 := by omega
          rw [Equiv.swap_apply_right, ← Category.assoc, ← cycI_succ,
            show k - (i + 1) + 1 = k - i by omega]
    rw [symL_succ, Linear.comp_smul, Preadditive.comp_sum]
    change ((k + 1 : ℂ)⁻¹) • ∑ j ∈ Finset.range (k + 1), tsw X (k + 1) i ≫ f j =
      ((k + 1 : ℂ)⁻¹) • ∑ j ∈ Finset.range (k + 1), f j
    rw [Finset.sum_congr rfl key]
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

theorem cycI_comp_symL (k : ℕ) : ∀ (m j : ℕ), j + m < k → cycI X k j m ≫ symL X k = symL X k := by
  intro m
  induction m with
  | zero => intro j _; simp [cycI_zero]
  | succ m ih =>
    intro j h
    rw [cycI_succ, Category.assoc, ih (j + 1) (by omega), tsw_comp_symL k j (by omega)]

/-- A morphism invariant under every `s_i ▷ W` applied first is invariant under the cycles. -/
theorem cycI_whisker_comp {k : ℕ} {W Z : C} (φ : tpow X k ⊗ W ⟶ Z)
    (hφ : ∀ i, i + 1 < k → (tsw X k i ▷ W) ≫ φ = φ) :
    ∀ (m j : ℕ), j + m < k → (cycI X k j m ▷ W) ≫ φ = φ := by
  intro m
  induction m with
  | zero => intro j _; simp [cycI_zero]
  | succ m ih =>
    intro j hj
    rw [cycI_succ, comp_whiskerRight, Category.assoc, ih (j + 1) (by omega), hφ j (by omega)]

/-- **Absorption**: a morphism invariant under every `s_i ▷ W` absorbs `σ_k ▷ W`. -/
theorem symL_whisker_comp (k : ℕ) : ∀ {W Z : C} (φ : tpow X k ⊗ W ⟶ Z),
    (∀ i, i + 1 < k → (tsw X k i ▷ W) ≫ φ = φ) → (symL X k ▷ W) ≫ φ = φ := by
  induction k with
  | zero => intro W Z φ _; simp [symL_zero]
  | succ k ih =>
    intro W Z φ hφ
    have h1 : (((symL X k ▷ X : tpow X (k + 1) ⟶ tpow X (k + 1)) ▷ W)) ≫ φ = φ := by
      have := ih (W := X ⊗ W) ((α_ (tpow X k) X W).inv ≫ φ) (fun i hi => by
        rw [← Category.assoc]
        erw [associator_inv_naturality_left]
        rw [Category.assoc]
        have h' := hφ i (by omega)
        rw [tsw_succ_of_lt hi] at h'
        erw [h'])
      rw [← Category.assoc] at this
      erw [associator_inv_naturality_left] at this
      rw [Category.assoc] at this
      exact (cancel_epi _).mp this
    rw [symL_succ]
    erw [MonoidalLinear.smul_whiskerRight, sum_whiskerRight, Linear.smul_comp, Preadditive.sum_comp]
    have h2 : ∀ j ∈ Finset.range (k + 1), ((cycI X (k + 1) j (k - j) ≫
        (symL X k ▷ X : tpow X (k + 1) ⟶ tpow X (k + 1))) ▷ W) ≫ φ = φ := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [comp_whiskerRight, Category.assoc, h1, cycI_whisker_comp φ hφ (k - j) j (by omega)]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by norm_cast), one_smul]

/-- **Idempotence** `σ_k ≫ σ_k = σ_k`. -/
theorem symL_idem (k : ℕ) : symL X k ≫ symL X k = symL X k := by
  have h := symL_whisker_comp k (W := 𝟙_ C) ((ρ_ _).hom ≫ symL X k) (fun i hi => by
    rw [← Category.assoc, rightUnitor_naturality, Category.assoc, tsw_comp_symL k i hi])
  rw [← Category.assoc, rightUnitor_naturality, Category.assoc] at h
  exact (cancel_epi _).mp h

/-- `(σ_n ▷ X) ≫ σ_{n+1} = σ_{n+1}`. -/
theorem symL_whisker_symL (n : ℕ) :
    ((symL X n ▷ X : tpow X (n + 1) ⟶ tpow X (n + 1))) ≫ symL X (n + 1) = symL X (n + 1) :=
  symL_whisker_comp n (W := X) (symL X (n + 1)) (fun i hi => by
    rw [← tsw_succ_of_lt hi]; exact tsw_comp_symL (n + 1) i (by omega))

theorem symL_whisker_symL_assoc (n : ℕ) {Z : C} (h : tpow X (n + 1) ⟶ Z) :
    ((symL X n ▷ X : tpow X (n + 1) ⟶ tpow X (n + 1))) ≫ symL X (n + 1) ≫ h = symL X (n + 1) ≫ h := by
  rw [← Category.assoc, symL_whisker_symL]

end Symmetrizer

section Concat

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] (X : C)

/-- Transport between tensor powers along an equality of exponents. -/
def castT {a b : ℕ} (h : a = b) : tpow X a ⟶ tpow X b := eqToHom (congrArg (tpow X) h)

/-- Concatenation `X^{⊗a} ⊗ X^{⊗b} ⟶ X^{⊗(a+b)}`. -/
def cat (a : ℕ) : (b : ℕ) → (tpow X a ⊗ tpow X b ⟶ tpow X (a + b))
  | 0 => (ρ_ _).hom
  | b + 1 => (α_ _ _ _).inv ≫ (cat a b ▷ X)

/-- Extension of an endomorphism of `X^{⊗a}` to `X^{⊗(a+b)}` (acting on the first `a` strands). -/
def extR {a : ℕ} (g : tpow X a ⟶ tpow X a) : (b : ℕ) → (tpow X (a + b) ⟶ tpow X (a + b))
  | 0 => g
  | b + 1 => extR g b ▷ X

variable {X}

theorem castT_self {a : ℕ} (h : a = a) : castT X h = 𝟙 _ := rfl

theorem castT_trans {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) :
    castT X h₁ ≫ castT X h₂ = castT X (h₁.trans h₂) := by
  subst h₁ h₂; simp [castT]

theorem castT_whiskerRight {a b : ℕ} (h : a = b) :
    (castT X h ▷ X : tpow X (a + 1) ⟶ tpow X (b + 1)) = castT X (congrArg (· + 1) h) := by
  subst h; simp [castT]

theorem castT_comp_castT_symm {a b : ℕ} (h : a = b) : castT X h ≫ castT X h.symm = 𝟙 _ := by
  subst h; simp [castT]

theorem castT_comp_castT_eq_id {a b : ℕ} (h : a = b) (h' : b = a) : castT X h ≫ castT X h' = 𝟙 _ := by
  subst h; simp [castT]

theorem castT_conj {a b : ℕ} (h : a = b) (f : ∀ n, tpow X n ⟶ tpow X n) :
    castT X h ≫ f b = f a ≫ castT X h := by
  subst h; simp [castT]

theorem cat_zero (a : ℕ) : cat X a 0 = (ρ_ _).hom := rfl

theorem cat_succ (a b : ℕ) : cat X a (b + 1) = (α_ _ _ _).inv ≫ (cat X a b ▷ X) := rfl

@[reassoc]
theorem cat_zero_left : ∀ b : ℕ, cat X 0 b ≫ castT X (Nat.zero_add b) = (λ_ _).hom
  | 0 => by simp [cat_zero, castT_self, unitors_equal]
  | b + 1 => by
    have hc : castT X (Nat.zero_add (b + 1)) = (castT X (Nat.zero_add b) ▷ X) := by
      rw [castT_whiskerRight]
    rw [cat_succ, hc, Category.assoc, ← comp_whiskerRight, cat_zero_left b, leftUnitor_tensor_hom]

theorem whiskerRight_cat {a : ℕ} (g : tpow X a ⟶ tpow X a) :
    ∀ b, (g ▷ tpow X b) ≫ cat X a b = cat X a b ≫ extR X g b
  | 0 => by simp [cat_zero, extR]
  | b + 1 => by
    rw [cat_succ, ← Category.assoc]
    erw [associator_inv_naturality_left]
    rw [Category.assoc, ← comp_whiskerRight, whiskerRight_cat g b, comp_whiskerRight, ← Category.assoc]
    rfl

theorem extR_cycI {a : ℕ} {j m : ℕ} (h : j + m < a) : ∀ b, extR X (cycI X a j m) b = cycI X (a + b) j m
  | 0 => rfl
  | b + 1 => by
    rw [extR, extR_cycI h b, ← cycI_succ_of_lt m j (by omega)]
    rfl

/-- Naturality of the last swap in the base. -/
theorem lastSwap_natural {B B' : C} (f : B ⟶ B') :
    ((f ▷ X) ▷ X) ≫ lastSwap X B' = lastSwap X B ≫ ((f ▷ X) ▷ X) := by
  simp only [lastSwap, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc]
  simp

theorem whiskerLeft_tsw_cat (a : ℕ) : ∀ (b i : ℕ), i + 1 < b →
    (tpow X a ◁ tsw X b i) ≫ cat X a b = cat X a b ≫ tsw X (a + b) (a + i)
  | 0, i, h => by omega
  | b + 1, i, h => by
    rcases Nat.lt_or_ge (i + 1) b with hib | hib
    · rw [tsw_succ_of_lt hib, cat_succ, ← Category.assoc]
      erw [associator_inv_naturality_middle]
      rw [Category.assoc, ← comp_whiskerRight, whiskerLeft_tsw_cat a b i hib, comp_whiskerRight,
        ← Category.assoc, ← cat_succ]
      erw [← tsw_succ_of_lt (by omega : a + i + 1 < a + b)]
      rfl
    · obtain rfl : b = i + 1 := by omega
      rw [tsw_last]
      erw [tsw_last (a + i)]
      rw [cat_succ, cat_succ, comp_whiskerRight]
      simp only [Category.assoc]
      rw [lastSwap_natural (cat X a i)]
      simp only [← Category.assoc]
      congr 1
      simp only [lastSwap]
      monoidal

theorem whiskerLeft_cycI_cat (a b : ℕ) : ∀ (m j : ℕ), j + m < b →
    (tpow X a ◁ cycI X b j m) ≫ cat X a b = cat X a b ≫ cycI X (a + b) (a + j) m := by
  intro m
  induction m with
  | zero => intro j _; simp [cycI_zero]
  | succ m ih =>
    intro j h
    rw [cycI_succ, cycI_succ, whiskerLeft_comp, Category.assoc, ih (j + 1) (by omega),
      ← Category.assoc, whiskerLeft_tsw_cat a b j (by omega), Category.assoc]
    rfl

theorem tsw_castT {m m' : ℕ} (h : m = m') (i : ℕ) : tsw X m i ≫ castT X h = castT X h ≫ tsw X m' i := by
  subst h; simp [castT]

theorem tauSq_lastSwap_coh (c b : ℕ) :
    (α_ _ _ _).inv ≫ (tauSq X (tpow X c) (tpow X b) ▷ X) ≫ lastSwap X (tpow X c ⊗ tpow X b) =
      tauSq X (tpow X c) (tpow X b ⊗ X) ≫ ((α_ _ _ _).inv ▷ X) := by
  simp only [tauSq, lastSwap, BraidedCategory.braiding_tensor_right_hom]
  monoidal

/-- **Moving a strand past a block**: `cat (c+1) b ≫ cycI c b = τ ≫ (cat c b ▷ X)`. -/
theorem cat_cycI_mv (c : ℕ) : ∀ b : ℕ,
    cat X (c + 1) b ≫ cycI X (c + 1 + b) c b ≫ castT X (Nat.succ_add c b) =
      tauSq X (tpow X c) (tpow X b) ≫ (cat X c b ▷ X)
  | 0 => by
    rw [cycI_zero, castT_self, cat_zero, cat_zero, sq_right_unit_coh]
    simp
  | b + 1 => by
    have ih := cat_cycI_mv c b
    have h1 : cycI X (c + 1 + (b + 1)) c (b + 1) =
        (cycI X (c + 1 + b) c b ▷ X) ≫ tsw X (c + 1 + b + 1) (c + b) := by
      rw [cycI_succ']
      exact congrArg (· ≫ _) (cycI_succ_of_lt b c (show c + b < c + 1 + b by omega))
    have e1 : tsw X (c + 1 + b + 1) (c + b) ≫ castT X (Nat.succ_add c (b + 1)) =
        (castT X (Nat.succ_add c b) ▷ X) ≫ lastSwap X (tpow X (c + b)) := by
      rw [tsw_castT, castT_whiskerRight]
      congr 1
      exact tsw_last (c + b)
    calc cat X (c + 1) (b + 1) ≫ cycI X (c + 1 + (b + 1)) c (b + 1) ≫ castT X (Nat.succ_add c (b + 1))
        = (α_ _ _ _).inv ≫ ((cat X (c + 1) b ≫ cycI X (c + 1 + b) c b ≫ castT X (Nat.succ_add c b)) ▷ X) ≫
            lastSwap X (tpow X (c + b)) := by
          rw [h1, cat_succ]
          simp only [Category.assoc]
          rw [e1]
          simp only [comp_whiskerRight, Category.assoc]
      _ = (α_ _ _ _).inv ≫ ((tauSq X (tpow X c) (tpow X b) ≫ (cat X c b ▷ X)) ▷ X) ≫
            lastSwap X (tpow X (c + b)) := by rw [ih]
      _ = ((α_ _ _ _).inv ≫ (tauSq X (tpow X c) (tpow X b) ▷ X) ≫ lastSwap X (tpow X c ⊗ tpow X b)) ≫
            ((cat X c b ▷ X) ▷ X) := by
          rw [comp_whiskerRight]
          simp only [Category.assoc]
          rw [lastSwap_natural]
      _ = tauSq X (tpow X c) (tpow X (b + 1)) ≫ (cat X c (b + 1) ▷ X) := by
          rw [tauSq_lastSwap_coh, cat_succ, comp_whiskerRight]
          simp only [Category.assoc]

end Concat

section Absorb

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] {X : C}

theorem extR_symL_comp (a : ℕ) : ∀ b, extR X (symL X a) b ≫ symL X (a + b) = symL X (a + b)
  | 0 => symL_idem a
  | b + 1 => by
    change (extR X (symL X a) b ▷ X) ≫ symL X (a + b + 1) = _
    rw [← symL_whisker_symL (a + b), ← Category.assoc]
    erw [← comp_whiskerRight, extR_symL_comp a b]
    exact symL_whisker_symL (a + b)

/-- `(σ_a ▷ X^{⊗b}) ≫ cat ≫ σ_{a+b} = cat ≫ σ_{a+b}`. -/
@[reassoc]
theorem symL_whiskerRight_absorb (a b : ℕ) :
    (symL X a ▷ tpow X b) ≫ cat X a b ≫ symL X (a + b) = cat X a b ≫ symL X (a + b) := by
  rw [← Category.assoc, whiskerRight_cat, Category.assoc, extR_symL_comp]

/-- `(X^{⊗a} ◁ σ_b) ≫ cat ≫ σ_{a+b} = cat ≫ σ_{a+b}`. -/
@[reassoc]
theorem symL_whiskerLeft_absorb (a : ℕ) : ∀ b : ℕ,
    (tpow X a ◁ symL X b) ≫ cat X a b ≫ symL X (a + b) = cat X a b ≫ symL X (a + b)
  | 0 => by simp [symL_zero]
  | b + 1 => by
    have ih := symL_whiskerLeft_absorb a b
    have hterm : ∀ j ∈ Finset.range (b + 1), (tpow X a ◁ (cycI X (b + 1) j (b - j) ≫
        (symL X b ▷ X : tpow X (b + 1) ⟶ tpow X (b + 1)))) ≫ cat X a (b + 1) ≫ symL X (a + (b + 1)) =
        cat X a (b + 1) ≫ symL X (a + (b + 1)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hmid : (tpow X a ◁ (symL X b ▷ X : tpow X (b + 1) ⟶ tpow X (b + 1))) ≫ cat X a (b + 1) ≫
          symL X (a + (b + 1)) = cat X a (b + 1) ≫ symL X (a + (b + 1)) := by
        have hn := associator_inv_naturality_middle (tpow X a) (symL X b) X
        rw [cat_succ]
        simp only [Category.assoc]
        erw [reassoc_of% hn]
        rw [← Category.assoc (_ ▷ X), ← comp_whiskerRight]
        erw [← symL_whisker_symL (a + b)]
        rw [← Category.assoc (_ ▷ X), ← comp_whiskerRight, Category.assoc, ih, comp_whiskerRight,
          Category.assoc]
      rw [whiskerLeft_comp, Category.assoc, hmid, ← Category.assoc,
        whiskerLeft_cycI_cat a (b + 1) (b - j) j (by omega), Category.assoc,
        cycI_comp_symL (a + (b + 1)) (b - j) (a + j) (by omega)]
    rw [symL_succ, MonoidalLinear.whiskerLeft_smul, whiskerLeft_sum,
      Linear.smul_comp, Preadditive.sum_comp, Finset.sum_congr rfl hterm, Finset.sum_const,
      Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by norm_cast), one_smul]

/-- **Block swap**: `β ≫ cat b a ≫ σ = cat a b ≫ σ`. -/
@[reassoc]
theorem braiding_cat_symL : ∀ a b : ℕ,
    (β_ (tpow X a) (tpow X b)).hom ≫ cat X b a ≫ castT X (Nat.add_comm b a) ≫ symL X (a + b) =
      cat X a b ≫ symL X (a + b)
  | 0, b => by
    have h := cat_zero_left (X := X) b
    have hcc : castT X (Nat.zero_add b) ≫ castT X (Nat.add_comm b 0) = 𝟙 _ :=
      castT_comp_castT_eq_id (Nat.zero_add b) (Nat.add_comm b 0)
    rw [cat_zero, braiding_tensorUnit_left, ← h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% hcc]
  | a + 1, b => by
    have ih := braiding_cat_symL a b
    have hc : castT X (Nat.add_comm b (a + 1)) =
        (castT X (Nat.add_comm b a) ▷ X) ≫ castT X (Nat.succ_add a b).symm := by
      rw [castT_whiskerRight, castT_trans]
    calc (β_ (tpow X (a + 1)) (tpow X b)).hom ≫ cat X b (a + 1) ≫ castT X (Nat.add_comm b (a + 1)) ≫
          symL X (a + 1 + b)
        = tauSq X (tpow X a) (tpow X b) ≫ (((β_ (tpow X a) (tpow X b)).hom ≫ cat X b a ≫
            castT X (Nat.add_comm b a) ≫ symL X (a + b)) ▷ X) ≫ symL X (a + b + 1) ≫
            castT X (Nat.succ_add a b).symm := by
          rw [hc, BraidedCategory.braiding_tensor_left_hom, cat_succ]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
          rw [castT_conj (Nat.succ_add a b).symm (symL X)]
          simp only [tauSq, comp_whiskerRight, Category.assoc, symL_whisker_symL_assoc]
      _ = tauSq X (tpow X a) (tpow X b) ≫ ((cat X a b ≫ symL X (a + b)) ▷ X) ≫ symL X (a + b + 1) ≫
            castT X (Nat.succ_add a b).symm := by rw [ih]
      _ = (tauSq X (tpow X a) (tpow X b) ≫ (cat X a b ▷ X)) ≫ symL X (a + b + 1) ≫
            castT X (Nat.succ_add a b).symm := by
          simp only [comp_whiskerRight, Category.assoc, symL_whisker_symL_assoc]
      _ = cat X (a + 1) b ≫ symL X (a + 1 + b) := by
          rw [← cat_cycI_mv a b]
          simp only [Category.assoc]
          rw [← Category.assoc (castT X _), castT_conj (Nat.succ_add a b) (symL X), Category.assoc,
            castT_comp_castT_symm, Category.comp_id, cycI_comp_symL (a + 1 + b) b a (by omega)]

end Absorb

section CatAssoc

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] {X : C}

@[reassoc]
theorem cat_assoc (a b : ℕ) : ∀ c : ℕ,
    (cat X a b ▷ tpow X c) ≫ cat X (a + b) c ≫ castT X (Nat.add_assoc a b c) =
      (α_ _ _ _).hom ≫ (tpow X a ◁ cat X b c) ≫ cat X a (b + c)
  | 0 => by
    rw [castT_self, Category.comp_id, cat_zero, cat_zero]
    change (cat X a b ▷ 𝟙_ C) ≫ (ρ_ _).hom = (α_ _ _ (𝟙_ C)).hom ≫ (tpow X a ◁ (ρ_ _).hom) ≫ cat X a b
    rw [rightUnitor_naturality]
    monoidal
  | c + 1 => by
    have ih := cat_assoc a b c
    have hc : castT X (Nat.add_assoc a b (c + 1)) = (castT X (Nat.add_assoc a b c) ▷ X) := by
      rw [castT_whiskerRight]
    have e : cat X a (b + (c + 1)) = (α_ _ _ _).inv ≫ (cat X a (b + c) ▷ X) := rfl
    have hn := associator_inv_naturality_left (cat X a b) (tpow X c) X
    calc (cat X a b ▷ tpow X (c + 1)) ≫ cat X (a + b) (c + 1) ≫ castT X (Nat.add_assoc a b (c + 1))
        = (α_ _ _ _).inv ≫ ((cat X a b ▷ tpow X c ≫ cat X (a + b) c ≫ castT X (Nat.add_assoc a b c)) ▷ X) := by
          rw [hc, cat_succ]
          simp only [Category.assoc]
          erw [reassoc_of% hn]
          simp only [comp_whiskerRight, Category.assoc]
      _ = (α_ _ _ _).inv ≫ (((α_ _ _ _).hom ≫ (tpow X a ◁ cat X b c) ≫ cat X a (b + c)) ▷ X) := by rw [ih]
      _ = _ := by
          rw [e, cat_succ]
          simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
          monoidal

end CatAssoc

section GCMon

/-- A **graded commutative monoid** in a braided category: objects `B k`, a unit `𝟙 ⟶ B 0` and
multiplications `B a ⊗ B b ⟶ B (a + b)`, associative, unital and commutative up to the canonical
identifications of the indices. -/
structure GCMon (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] where
  B : ℕ → C
  u : 𝟙_ C ⟶ B 0
  uinv : B 0 ⟶ 𝟙_ C
  u_uinv : u ≫ uinv = 𝟙 _
  m : ∀ a b, B a ⊗ B b ⟶ B (a + b)
  assoc : ∀ a b c, (m a b ▷ B c) ≫ m (a + b) c ≫ eqToHom (congrArg B (Nat.add_assoc a b c)) =
    (α_ _ _ _).hom ≫ (B a ◁ m b c) ≫ m a (b + c)
  unit_left : ∀ a, (u ▷ B a) ≫ m 0 a ≫ eqToHom (congrArg B (Nat.zero_add a)) = (λ_ _).hom
  unit_right : ∀ a, (B a ◁ u) ≫ m a 0 = (ρ_ _).hom
  comm : ∀ a b, (β_ (B a) (B b)).hom ≫ m b a ≫ eqToHom (congrArg B (Nat.add_comm b a)) = m a b

end GCMon

section SymPow

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] [HasKernels C]

instance (priority := 100) isIdempotentComplete_of_hasKernels' : IsIdempotentComplete C :=
  (Idempotents.isIdempotentComplete_iff_idempotents_have_kernels C).mpr fun _ _ _ => inferInstance

/-- A splitting of the symmetrizer `σ_k = π ≫ ι`, `ι ≫ π = 𝟙`. -/
theorem symL_split (X : C) (k : ℕ) : ∃ (Y : C) (i : Y ⟶ tpow X k) (e : tpow X k ⟶ Y),
    i ≫ e = 𝟙 Y ∧ e ≫ i = symL X k :=
  IsIdempotentComplete.idempotents_split _ _ (symL_idem k)

/-- The symmetric power `S^k X` (image of the symmetrizer). -/
def symPow (X : C) (k : ℕ) : C := (symL_split X k).choose

def symι (X : C) (k : ℕ) : symPow X k ⟶ tpow X k := (symL_split X k).choose_spec.choose

def symπ (X : C) (k : ℕ) : tpow X k ⟶ symPow X k := (symL_split X k).choose_spec.choose_spec.choose

variable {X : C}

@[reassoc (attr := simp)]
theorem symι_symπ (k : ℕ) : symι X k ≫ symπ X k = 𝟙 _ :=
  (symL_split X k).choose_spec.choose_spec.choose_spec.1

theorem symπ_symι (k : ℕ) : symπ X k ≫ symι X k = symL X k :=
  (symL_split X k).choose_spec.choose_spec.choose_spec.2

@[reassoc]
theorem symL_symπ (k : ℕ) : symL X k ≫ symπ X k = symπ X k := by
  rw [← symπ_symι, Category.assoc, symι_symπ, Category.comp_id]

@[reassoc]
theorem symι_symL (k : ℕ) : symι X k ≫ symL X k = symι X k := by
  rw [← symπ_symι, ← Category.assoc, symι_symπ, Category.id_comp]

theorem symπ_eqToHom {a b : ℕ} (h : a = b) :
    symπ X a ≫ eqToHom (congrArg (symPow X) h) = castT X h ≫ symπ X b := by
  subst h; simp [castT]

/-- The multiplication `S^a ⊗ S^b ⟶ S^{a+b}`. -/
def symMul (X : C) (a b : ℕ) : symPow X a ⊗ symPow X b ⟶ symPow X (a + b) :=
  (symι X a ⊗ₘ symι X b) ≫ cat X a b ≫ symπ X (a + b)

theorem symMul_def (X : C) (a b : ℕ) :
    symMul X a b = (symι X a ⊗ₘ symι X b) ≫ cat X a b ≫ symπ X (a + b) := rfl

@[reassoc]
theorem symL_tensor_absorb_left {P Q : C} {n c : ℕ} (F : P ⟶ tpow X n) (g : Q ⟶ tpow X c) :
    ((F ≫ symL X n) ⊗ₘ g) ≫ cat X n c ≫ symπ X (n + c) = (F ⊗ₘ g) ≫ cat X n c ≫ symπ X (n + c) := by
  rw [← tensorHom_comp_whiskerRight, ← symL_symπ (n + c)]
  simp only [Category.assoc]
  rw [symL_whiskerRight_absorb_assoc]

@[reassoc]
theorem symL_tensor_absorb_right {P Q : C} {a n : ℕ} (f : P ⟶ tpow X a) (G : Q ⟶ tpow X n) :
    (f ⊗ₘ (G ≫ symL X n)) ≫ cat X a n ≫ symπ X (a + n) = (f ⊗ₘ G) ≫ cat X a n ≫ symπ X (a + n) := by
  rw [← tensorHom_comp_whiskerLeft, ← symL_symπ (a + n)]
  simp only [Category.assoc]
  rw [symL_whiskerLeft_absorb_assoc]

theorem symMul_assoc (a b c : ℕ) :
    (symMul X a b ▷ symPow X c) ≫ symMul X (a + b) c ≫ eqToHom (congrArg (symPow X) (Nat.add_assoc a b c)) =
      (α_ _ _ _).hom ≫ (symPow X a ◁ symMul X b c) ≫ symMul X a (b + c) := by
  have hL : (symMul X a b ▷ symPow X c) ≫ symMul X (a + b) c ≫
      eqToHom (congrArg (symPow X) (Nat.add_assoc a b c)) =
      ((symι X a ⊗ₘ symι X b) ⊗ₘ symι X c) ≫ (α_ _ _ _).hom ≫ (tpow X a ◁ cat X b c) ≫
        cat X a (b + c) ≫ symπ X (a + (b + c)) := by
    have h1 : symMul X a b ≫ symι X (a + b) = ((symι X a ⊗ₘ symι X b) ≫ cat X a b) ≫ symL X (a + b) := by
      simp only [symMul, Category.assoc, symπ_symι]
    calc (symMul X a b ▷ symPow X c) ≫ symMul X (a + b) c ≫ eqToHom (congrArg (symPow X) (Nat.add_assoc a b c))
        = ((symMul X a b ≫ symι X (a + b)) ⊗ₘ symι X c) ≫ cat X (a + b) c ≫ symπ X (a + b + c) ≫
            eqToHom (congrArg (symPow X) (Nat.add_assoc a b c)) := by
          rw [symMul_def X (a + b) c]
          simp only [Category.assoc]
          rw [whiskerRight_comp_tensorHom_assoc]
      _ = (((symι X a ⊗ₘ symι X b) ≫ cat X a b) ⊗ₘ symι X c) ≫ cat X (a + b) c ≫ symπ X (a + b + c) ≫
            eqToHom (congrArg (symPow X) (Nat.add_assoc a b c)) := by
          rw [h1, symL_tensor_absorb_left_assoc]
      _ = _ := by
          rw [symπ_eqToHom (Nat.add_assoc a b c), ← tensorHom_comp_whiskerRight]
          simp only [Category.assoc]
          rw [cat_assoc_assoc]
  have hR : (α_ _ _ _).hom ≫ (symPow X a ◁ symMul X b c) ≫ symMul X a (b + c) =
      ((symι X a ⊗ₘ symι X b) ⊗ₘ symι X c) ≫ (α_ _ _ _).hom ≫ (tpow X a ◁ cat X b c) ≫
        cat X a (b + c) ≫ symπ X (a + (b + c)) := by
    have h1 : symMul X b c ≫ symι X (b + c) = ((symι X b ⊗ₘ symι X c) ≫ cat X b c) ≫ symL X (b + c) := by
      simp only [symMul, Category.assoc, symπ_symι]
    calc (α_ _ _ _).hom ≫ (symPow X a ◁ symMul X b c) ≫ symMul X a (b + c)
        = (α_ _ _ _).hom ≫ (symι X a ⊗ₘ (symMul X b c ≫ symι X (b + c))) ≫ cat X a (b + c) ≫
            symπ X (a + (b + c)) := by
          rw [symMul_def X a (b + c), whiskerLeft_comp_tensorHom_assoc]
      _ = (α_ _ _ _).hom ≫ (symι X a ⊗ₘ ((symι X b ⊗ₘ symι X c) ≫ cat X b c)) ≫ cat X a (b + c) ≫
            symπ X (a + (b + c)) := by rw [h1, symL_tensor_absorb_right]
      _ = _ := by
          rw [← tensorHom_comp_whiskerLeft]
          simp only [Category.assoc]
          rw [associator_naturality_assoc]
  rw [hL, hR]

theorem symMul_unit_left (a : ℕ) :
    (symπ X 0 ▷ symPow X a) ≫ symMul X 0 a ≫ eqToHom (congrArg (symPow X) (Nat.zero_add a)) = (λ_ _).hom := by
  simp only [symMul, Category.assoc]
  rw [symπ_eqToHom (Nat.zero_add a), whiskerRight_comp_tensorHom_assoc, symπ_symι, symL_zero, id_tensorHom,
    ← Category.assoc (cat X 0 a), cat_zero_left]
  change (𝟙_ C ◁ symι X a) ≫ (λ_ _).hom ≫ symπ X a = _
  rw [leftUnitor_naturality_assoc, symι_symπ, Category.comp_id]

theorem symMul_unit_right (a : ℕ) : (symPow X a ◁ symπ X 0) ≫ symMul X a 0 = (ρ_ _).hom := by
  simp only [symMul, cat_zero]
  rw [whiskerLeft_comp_tensorHom_assoc, symπ_symι, symL_zero, tensorHom_id]
  change (symι X a ▷ 𝟙_ C) ≫ (ρ_ _).hom ≫ symπ X a = _
  rw [rightUnitor_naturality_assoc, symι_symπ, Category.comp_id]

theorem symMul_comm (a b : ℕ) :
    (β_ (symPow X a) (symPow X b)).hom ≫ symMul X b a ≫ eqToHom (congrArg (symPow X) (Nat.add_comm b a)) =
      symMul X a b := by
  simp only [symMul, Category.assoc]
  rw [symπ_eqToHom (Nat.add_comm b a), ← BraidedCategory.braiding_naturality_assoc, ← symL_symπ (a + b),
    braiding_cat_symL_assoc, symL_symπ]

/-- The **symmetric algebra** `Sym X = ⊕_k S^k X` as a graded commutative monoid. -/
def symGCMon (X : C) : GCMon C where
  B := symPow X
  u := symπ X 0
  uinv := symι X 0
  u_uinv := by rw [symπ_symι, symL_zero]
  m := symMul X
  assoc := symMul_assoc
  unit_left := symMul_unit_left
  unit_right := symMul_unit_right
  comm := symMul_comm

end SymPow

end VOA.Huang.TensorCat.DeligneFiber
