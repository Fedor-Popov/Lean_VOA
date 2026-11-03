/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneFiberFunctor

/-!
# Deligne's fiber functor — product calculus in a commutative algebra of `Ind(D)`

For a lax braided functor `G : C ⥤ ModuleCat ℂ` (a commutative algebra `A` in `Ind(C)`,
`G Y = Hom(𝟙, A ⊗ Y)`) and an object `X`, vectors `v : Fin k → G X` have a product
`prodG X k v ∈ G (X^{⊗k})`.  This file proves:

* elementwise forms of the lax axioms: `μ_assoc_apply`, `μ_assoc_inv_apply`, `μ_braid_apply`,
  `μ_whiskerLeft_apply`, `μ_whiskerRight_apply`;
* `map_tsw_prodG` — an adjacent transposition permutes the factors (commutativity);
  `map_cyc_prodG` — so do the cycles of `DeligneExterior`;
* `map_antisym_prodG` — **Leibniz formula**:
  `G(e_k)(v_1 ⋯ v_k) = (k!)⁻¹ Σ_σ sgn σ · v_{σ 1} ⋯ v_{σ k}`, from the coset recursion of the
  antisymmetrizer (no presentation of `S_k` is used: the recursion is matched with the bijection
  `(j, σ') ↦ lift σ' * cycP j`);
* contractions `κ` of a product of covectors with an element of `G(X^{⊗k})`
  (`kappa_succ`, `pc_apply`), and the vanishing/unit lemmas for products;
* `eq_zero_of_orthonormal` — if `Λ^{n+1} X = 0` (`antisym X (n+1) = 0`) and `(e, f)` is an
  orthonormal `n`-family, a vector `y` with `⟨f_i, y⟩ = 0` for all `i` vanishes.  (The heart of
  the completeness of a frame; this is where `Λ^{n+1} X = 0` enters Deligne's construction.)

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace VOA.Huang.TensorCat.DeligneFiber

open CategoryTheory MonoidalCategory Limits Module Functor.LaxMonoidal
open scoped TensorProduct

universe v u

section Elementwise

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (G : C ⥤ ModuleCat.{0} ℂ) [G.LaxBraided]

theorem μ_assoc_apply {A B E : C} (a : G.obj A) (b : G.obj B) (c : G.obj E) :
    (G.map (α_ A B E).hom).hom ((μ G (A ⊗ B) E).hom ((μ G A B).hom (a ⊗ₜ b) ⊗ₜ c)) =
      (μ G A (B ⊗ E)).hom (a ⊗ₜ (μ G B E).hom (b ⊗ₜ c)) := by
  have h := congrArg (fun φ => φ.hom ((a ⊗ₜ b) ⊗ₜ c)) (Functor.LaxMonoidal.associativity G A B E)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.associator_hom_apply] at h
  exact h

theorem μ_assoc_inv_apply {A B E : C} (a : G.obj A) (b : G.obj B) (c : G.obj E) :
    (G.map (α_ A B E).inv).hom ((μ G A (B ⊗ E)).hom (a ⊗ₜ (μ G B E).hom (b ⊗ₜ c))) =
      (μ G (A ⊗ B) E).hom ((μ G A B).hom (a ⊗ₜ b) ⊗ₜ c) := by
  rw [← μ_assoc_apply, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← G.map_comp, Iso.hom_inv_id,
    G.map_id]
  rfl

theorem μ_braid_apply {A B : C} (a : G.obj A) (b : G.obj B) :
    (G.map (β_ A B).hom).hom ((μ G A B).hom (a ⊗ₜ b)) = (μ G B A).hom (b ⊗ₜ a) := by
  have h := congrArg (fun φ => φ.hom (a ⊗ₜ b)) (Functor.LaxBraided.braided (F := G) A B)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply] at h
  exact h

theorem μ_whiskerLeft_apply {A B B' : C} (f : B ⟶ B') (a : G.obj A) (b : G.obj B) :
    (G.map (A ◁ f)).hom ((μ G A B).hom (a ⊗ₜ b)) = (μ G A B').hom (a ⊗ₜ (G.map f).hom b) := by
  have h := congrArg (fun φ => φ.hom (a ⊗ₜ b)) (Functor.LaxMonoidal.μ_natural_right G A f)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply] at h
  exact h.symm

theorem μ_whiskerRight_apply {A A' B : C} (f : A ⟶ A') (a : G.obj A) (b : G.obj B) :
    (G.map (f ▷ B)).hom ((μ G A B).hom (a ⊗ₜ b)) = (μ G A' B).hom ((G.map f).hom a ⊗ₜ b) := by
  have h := congrArg (fun φ => φ.hom (a ⊗ₜ b)) (Functor.LaxMonoidal.μ_natural_left G f B)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply] at h
  exact h.symm

theorem map_comp_apply {A B E : C} (f : A ⟶ B) (g : B ⟶ E) (a : G.obj A) :
    (G.map (f ≫ g)).hom a = (G.map g).hom ((G.map f).hom a) := by
  rw [G.map_comp]; rfl

end Elementwise

section Permutations

/-- The adjacent transposition `(i, i+1)` of `Fin n` (identity if `i + 1 ≥ n`). -/
def swapP (n i : ℕ) : Equiv.Perm (Fin n) :=
  if h : i + 1 < n then Equiv.swap ⟨i, by omega⟩ ⟨i + 1, h⟩ else 1

/-- `cycP n j m = swapP_{j+m-1} ⋯` matching `cyc n j m` (as permutations of positions). -/
def cycP (n j : ℕ) : ℕ → Equiv.Perm (Fin n)
  | 0 => 1
  | m + 1 => cycP n (j + 1) m * swapP n j

theorem sign_swapP {n i : ℕ} (h : i + 1 < n) : Equiv.Perm.sign (swapP n i) = -1 := by
  rw [swapP, dif_pos h, Equiv.Perm.sign_swap]
  intro heq
  have := congrArg Fin.val heq
  simp at this

theorem sign_cycP (n : ℕ) : ∀ (m j : ℕ), j + m < n → Equiv.Perm.sign (cycP n j m) = (-1) ^ m := by
  intro m
  induction m with
  | zero => intro j _; simp [cycP]
  | succ m ih =>
    intro j h
    rw [cycP, Equiv.Perm.sign_mul, ih (j + 1) (by omega), sign_swapP (by omega)]
    exact (pow_succ _ _).symm

theorem swapP_apply_of_lt {n i : ℕ} (x : Fin n) (hx : x.val < i) : swapP n i x = x := by
  unfold swapP
  split_ifs with h
  · exact Equiv.swap_apply_of_ne_of_ne (fun e => by simp [Fin.ext_iff] at e; omega)
      (fun e => by simp [Fin.ext_iff] at e; omega)
  · rfl

theorem swapP_apply_of_gt {n i : ℕ} (x : Fin n) (hx : i + 1 < x.val) : swapP n i x = x := by
  unfold swapP
  split_ifs with h
  · exact Equiv.swap_apply_of_ne_of_ne (fun e => by simp [Fin.ext_iff] at e; omega)
      (fun e => by simp [Fin.ext_iff] at e; omega)
  · rfl

theorem swapP_apply_left {n i : ℕ} (h : i + 1 < n) : swapP n i ⟨i, by omega⟩ = ⟨i + 1, h⟩ := by
  rw [swapP, dif_pos h, Equiv.swap_apply_left]

theorem swapP_apply_right {n i : ℕ} (h : i + 1 < n) : swapP n i ⟨i + 1, h⟩ = ⟨i, by omega⟩ := by
  rw [swapP, dif_pos h, Equiv.swap_apply_right]

theorem swapP_castSucc {k i : ℕ} (h : i + 1 < k + 1) (x : Fin (k + 1)) :
    swapP (k + 2) i x.castSucc = (swapP (k + 1) i x).castSucc := by
  unfold swapP
  rw [dif_pos h, dif_pos (by omega)]
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

/-- `cycP n j m` sends position `j` to position `j + m`. -/
theorem cycP_apply_self (n : ℕ) : ∀ (m j : ℕ) (h : j + m < n), cycP n j m ⟨j, by omega⟩ = ⟨j + m, h⟩ := by
  intro m
  induction m with
  | zero => intro j h; rfl
  | succ m ih =>
    intro j h
    rw [cycP, Equiv.Perm.mul_apply, swapP_apply_left (by omega), ih (j + 1) (by omega)]
    simp [Nat.add_assoc, Nat.add_comm 1 m]

/-- `cycP n j m` fixes positions `< j`. -/
theorem cycP_apply_of_lt (n : ℕ) : ∀ (m j : ℕ) (x : Fin n), x.val < j → cycP n j m x = x := by
  intro m
  induction m with
  | zero => intro j x _; rfl
  | succ m ih =>
    intro j x hx
    rw [cycP, Equiv.Perm.mul_apply, swapP_apply_of_lt x hx, ih (j + 1) x (by omega)]

/-- `cycP n j m` sends position `p ∈ (j, j+m]` to `p - 1`. -/
theorem cycP_apply_of_mem (n : ℕ) : ∀ (m j : ℕ) (x : Fin n), j < x.val → x.val ≤ j + m →
    (cycP n j m x).val = x.val - 1 := by
  intro m
  induction m with
  | zero => intro j x h1 h2; omega
  | succ m ih =>
    intro j x h1 h2
    rw [cycP, Equiv.Perm.mul_apply]
    rcases Nat.lt_or_ge (j + 1) x.val with hx | hx
    · rw [swapP_apply_of_gt x hx, ih (j + 1) x hx (by omega)]
    · have hxj : x.val = j + 1 := by omega
      have hlt : j + 1 < n := by omega
      have hx' : x = ⟨j + 1, hlt⟩ := Fin.ext hxj
      rw [hx', swapP_apply_right hlt, cycP_apply_of_lt n m (j + 1) _ (by simp)]
      simp

/-- Lift a permutation of `Fin k` to `Fin (k+1)` fixing the last element. -/
def liftP {k : ℕ} (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k + 1)) :=
  σ.viaFintypeEmbedding Fin.castSuccEmb

theorem liftP_castSucc {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    liftP σ i.castSucc = (σ i).castSucc :=
  Equiv.Perm.viaFintypeEmbedding_apply_image σ Fin.castSuccEmb i

theorem liftP_last {k : ℕ} (σ : Equiv.Perm (Fin k)) : liftP σ (Fin.last k) = Fin.last k := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

theorem sign_liftP {k : ℕ} (σ : Equiv.Perm (Fin k)) : Equiv.Perm.sign (liftP σ) = Equiv.Perm.sign σ := by
  unfold liftP Equiv.Perm.viaFintypeEmbedding
  exact Equiv.Perm.sign_extendDomain _ _

theorem liftP_injective {k : ℕ} : Function.Injective (liftP (k := k)) := by
  intro σ τ h
  ext i
  have := congrArg (fun π => π i.castSucc) h
  simp only [liftP_castSucc] at this
  exact congrArg Fin.val (Fin.castSucc_injective _ this)

/-- The decomposition map `(j, σ') ↦ lift σ' * c_j`, `c_j = cycP (k+1) j (k-j)`. -/
def decompMap (k : ℕ) (p : Fin (k + 1) × Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k + 1)) :=
  liftP p.2 * cycP (k + 1) p.1.val (k - p.1.val)

theorem decompMap_injective (k : ℕ) : Function.Injective (decompMap k) := by
  rintro ⟨j₁, σ₁⟩ ⟨j₂, σ₂⟩ h
  -- the preimage of the last position determines `j`
  have key : ∀ (j : Fin (k + 1)) (σ : Equiv.Perm (Fin k)), decompMap k (j, σ) j = Fin.last k := by
    intro j σ
    simp only [decompMap, Equiv.Perm.mul_apply]
    have := cycP_apply_self (k + 1) (k - j.val) j.val (by omega)
    rw [show (⟨j.val, _⟩ : Fin (k + 1)) = j from rfl] at this
    rw [this]
    have e : (⟨j.val + (k - j.val), by omega⟩ : Fin (k + 1)) = Fin.last k := Fin.ext (by simp; omega)
    rw [e, liftP_last]
  have hj : j₁ = j₂ := by
    have h1 := key j₁ σ₁
    have h2 := key j₂ σ₂
    rw [h] at h1
    exact (decompMap k (j₂, σ₂)).injective (h1.trans h2.symm)
  subst hj
  have : liftP σ₁ = liftP σ₂ := by
    simpa [decompMap] using h
  rw [liftP_injective this]

theorem decompMap_bijective (k : ℕ) : Function.Bijective (decompMap k) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨decompMap_injective k, ?_⟩
  simp [Fintype.card_perm, Nat.factorial_succ]

theorem sign_decompMap (k : ℕ) (p : Fin (k + 1) × Equiv.Perm (Fin k)) :
    Equiv.Perm.sign (decompMap k p) = Equiv.Perm.sign p.2 * (-1) ^ (k - p.1.val) := by
  rw [decompMap, Equiv.Perm.sign_mul, sign_liftP, sign_cycP _ _ _ (by omega)]

end Permutations

section Products

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  (G : C ⥤ ModuleCat.{0} ℂ) [G.LaxBraided]

/-- The product `v_0 ⋯ v_{k-1} ∈ G(X^{⊗k})` of vectors `v_i ∈ G X`. -/
def prodG (X : C) : (k : ℕ) → (Fin k → G.obj X) → G.obj (tpow X k)
  | 0, _ => (ε G).hom 1
  | k + 1, v => (μ G (tpow X k) X).hom (prodG X k (Fin.init v) ⊗ₜ v (Fin.last k))

theorem prodG_succ (X : C) (k : ℕ) (v : Fin (k + 1) → G.obj X) :
    prodG G X (k + 1) v = (μ G (tpow X k) X).hom (prodG G X k (Fin.init v) ⊗ₜ v (Fin.last k)) := rfl

theorem prodG_congr (X : C) {k : ℕ} {v w : Fin k → G.obj X} (h : v = w) :
    prodG G X k v = prodG G X k w := by rw [h]

/-- An adjacent transposition permutes the factors of a product. -/
theorem map_tsw_prodG (X : C) : ∀ (k i : ℕ) (v : Fin k → G.obj X),
    (G.map (tsw X k i)).hom (prodG G X k v) = prodG G X k (v ∘ swapP k i)
  | 0, i, v => by
    simp only [tsw, G.map_id]
    exact prodG_congr G X (funext fun x => x.elim0)
  | 1, i, v => by
    simp only [tsw, G.map_id]
    refine prodG_congr G X (funext fun x => ?_)
    simp [swapP]
  | k + 2, i, v => by
    by_cases hik : i = k
    · subst hik
      have hlt : i + 1 < i + 2 := by omega
      have e1 : Fin.init (Fin.init (v ∘ swapP (i + 2) i)) = Fin.init (Fin.init v) := by
        funext x
        simp only [Fin.init, Function.comp_apply]
        congr 1
        rw [swapP_apply_of_lt]
        simp
      have e2 : Fin.init (v ∘ swapP (i + 2) i) (Fin.last i) = v (Fin.last (i + 1)) := by
        simp only [Fin.init, Function.comp_apply]
        congr 1
        rw [show (Fin.castSucc (Fin.last i) : Fin (i + 2)) = ⟨i, by omega⟩ from Fin.ext (by simp),
          swapP_apply_left hlt]
        exact Fin.ext (by simp)
      have e3 : (v ∘ swapP (i + 2) i) (Fin.last (i + 1)) = Fin.init v (Fin.last i) := by
        simp only [Fin.init, Function.comp_apply]
        congr 1
        rw [show (Fin.last (i + 1) : Fin (i + 2)) = ⟨i + 1, hlt⟩ from Fin.ext (by simp),
          swapP_apply_right hlt]
        exact Fin.ext (by simp)
      rw [tsw_last, lastSwap, map_comp_apply, map_comp_apply, prodG_succ, prodG_succ,
        μ_assoc_apply, μ_whiskerLeft_apply, μ_braid_apply, μ_assoc_inv_apply,
        prodG_succ G X (i + 1) (v ∘ swapP (i + 2) i), prodG_succ G X i, e1, e2, e3]
    · by_cases hlt : i < k
      · have hlt' : i + 1 < k + 1 := by omega
        have e1 : Fin.init (v ∘ swapP (k + 2) i) = Fin.init v ∘ swapP (k + 1) i := by
          funext x
          simp only [Fin.init, Function.comp_apply, swapP_castSucc hlt']
        have e2 : (v ∘ swapP (k + 2) i) (Fin.last (k + 1)) = v (Fin.last (k + 1)) := by
          simp only [Function.comp_apply]
          congr 1
          rw [swapP_apply_of_gt]
          simp; omega
        rw [show tsw X (k + 2) i = tsw X (k + 1) i ▷ X from tsw_succ_of_lt hlt', prodG_succ,
          μ_whiskerRight_apply, map_tsw_prodG X (k + 1) i, prodG_succ G X (k + 1) (v ∘ swapP (k + 2) i),
          e1, e2]
      · rw [tsw_of_le (by omega : k + 2 ≤ i + 1), G.map_id]
        refine prodG_congr G X (funext fun x => ?_)
        simp only [Function.comp_apply, swapP, dif_neg (by omega : ¬ i + 1 < k + 2)]
        rfl

theorem map_cyc_prodG (X : C) (n : ℕ) : ∀ (m j : ℕ) (v : Fin n → G.obj X),
    (G.map (cyc n j m)).hom (prodG G X n v) = prodG G X n (v ∘ cycP n j m) := by
  intro m
  induction m with
  | zero => intro j v; simp [cyc_zero, cycP]
  | succ m ih =>
    intro j v
    rw [cyc_succ, map_comp_apply, ih, map_tsw_prodG, cycP, Equiv.Perm.coe_mul]
    rfl

theorem prodG_liftP (X : C) {k : ℕ} (σ : Equiv.Perm (Fin k)) (v : Fin (k + 1) → G.obj X) :
    prodG G X (k + 1) (v ∘ liftP σ) =
      (μ G (tpow X k) X).hom (prodG G X k (Fin.init v ∘ σ) ⊗ₜ v (Fin.last k)) := by
  rw [prodG_succ]
  congr 2
  · refine prodG_congr G X (funext fun i => ?_)
    simp [Fin.init, liftP_castSucc]
  · simp [liftP_last]

end Products

section Leibniz

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C]
  (G : C ⥤ ModuleCat.{0} ℂ) [G.LaxBraided] [G.Additive] [G.Linear ℂ]

/-- The sign of a permutation as a complex number. -/
def sgnC {k : ℕ} (σ : Equiv.Perm (Fin k)) : ℂ := ((Equiv.Perm.sign σ : ℤˣ) : ℤ)

theorem sgnC_mul_pow {k : ℕ} (σ : Equiv.Perm (Fin k)) (m : ℕ) :
    (((Equiv.Perm.sign σ * (-1) ^ m : ℤˣ) : ℤ) : ℂ) = sgnC σ * (-1) ^ m := by
  simp only [sgnC, Units.val_mul, Int.cast_mul]
  congr 1
  norm_cast

/-- **Leibniz formula** for the antisymmetrizer on a product of vectors. -/
theorem map_antisym_prodG (X : C) : ∀ (k : ℕ) (v : Fin k → G.obj X),
    (G.map (antisym X k)).hom (prodG G X k v) =
      ((k.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin k), sgnC σ • prodG G X k (v ∘ σ) := by
  intro k
  induction k with
  | zero =>
    intro v
    simp only [antisym_zero, G.map_id, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    rw [Fintype.sum_unique]
    simp [sgnC]
  | succ k ih =>
    intro v
    rw [antisym_succ, Functor.map_smul, Functor.map_sum]
    simp only [Functor.map_smul, ModuleCat.hom_smul, ModuleCat.hom_sum, LinearMap.smul_apply,
      LinearMap.coe_sum, Finset.sum_apply, map_comp_apply]
    -- the inner products
    have hinner : ∀ j ∈ Finset.range (k + 1),
        (G.map (cyc (k + 1) j (k - j))).hom ((G.map (antisym X k ▷ X)).hom (prodG G X (k + 1) v)) =
          ((k.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin k),
            sgnC σ • prodG G X (k + 1) (v ∘ ⇑(liftP σ * cycP (k + 1) j (k - j) : Equiv.Perm (Fin (k + 1)))) := by
      intro j _
      rw [prodG_succ, μ_whiskerRight_apply, ih, ← TensorProduct.smul_tmul', map_smul, map_smul,
        TensorProduct.sum_tmul, map_sum, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [← TensorProduct.smul_tmul', map_smul, map_smul, ← prodG_liftP, map_cyc_prodG]
      rfl
    rw [Finset.sum_congr rfl (fun j hj => by rw [hinner j hj])]
    rw [← Fintype.sum_bijective (decompMap k) (decompMap_bijective k)
      (fun p => sgnC (decompMap k p) • prodG G X (k + 1) (v ∘ decompMap k p)) _ (fun p => rfl),
      Fintype.sum_prod_type, Finset.sum_range]
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => ?_
    have hs : sgnC (decompMap k (j, σ)) = sgnC σ * (-1) ^ (k - j.val) := by
      rw [sgnC, sign_decompMap, sgnC_mul_pow]
    rw [hs]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    rw [mul_inv]
    ring

end Leibniz

section Contraction

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] [RightRigidCategory C]
  (G : C ⥤ ModuleCat.{0} ℂ) [G.LaxBraided] [G.Additive] [G.Linear ℂ]

/-- The pairing `⟨g, x⟩ = G(ε_X)(g · x) ∈ G 𝟙` of a covector `g ∈ G Xᘁ` with a vector `x ∈ G X`. -/
def pairG {X : C} (g : G.obj Xᘁ) (x : G.obj X) : G.obj (𝟙_ C) :=
  (G.map (ε_ X Xᘁ)).hom ((μ G Xᘁ X).hom (g ⊗ₜ x))

/-- Slotwise evaluation `Xᘁ^{⊗k} ⊗ X^{⊗k} ⟶ 𝟙`. -/
def evK (X : C) : (k : ℕ) → (tpow Xᘁ k ⊗ tpow X k ⟶ 𝟙_ C)
  | 0 => (λ_ (𝟙_ C)).hom
  | k + 1 => tensorμ (tpow Xᘁ k) Xᘁ (tpow X k) X ≫ (evK X k ⊗ₘ ε_ X Xᘁ) ≫ (λ_ (𝟙_ C)).hom

/-- Evaluation of the first `k` slots, the last one free. -/
def evK' (X : C) (k : ℕ) : tpow Xᘁ k ⊗ (tpow X k ⊗ X) ⟶ X :=
  (α_ _ _ _).inv ≫ (evK X k ▷ X) ≫ (λ_ X).hom

/-- `κ(g; z) = G(evK)(g_0 ⋯ g_{k-1} · z)`. -/
def kappa {X : C} {k : ℕ} (g : Fin k → G.obj Xᘁ) (z : G.obj (tpow X k)) : G.obj (𝟙_ C) :=
  (G.map (evK X k)).hom ((μ G _ _).hom (prodG G Xᘁ k g ⊗ₜ z))

/-- The partial contraction (first `k` slots with `g`, last slot free), as a linear map. -/
def pcLin {X : C} {k : ℕ} (g : Fin k → G.obj Xᘁ) : G.obj (tpow X (k + 1)) →ₗ[ℂ] G.obj X :=
  (G.map (evK' X k)).hom ∘ₗ (μ G (tpow Xᘁ k) (tpow X k ⊗ X)).hom ∘ₗ
    TensorProduct.mk ℂ (G.obj (tpow Xᘁ k)) (G.obj (tpow X k ⊗ X)) (prodG G Xᘁ k g)

theorem tensorμ_apply {W X' Y Z : C} (w : G.obj W) (x : G.obj X') (y : G.obj Y) (z : G.obj Z) :
    (G.map (tensorμ W X' Y Z)).hom ((μ G (W ⊗ X') (Y ⊗ Z)).hom ((μ G W X').hom (w ⊗ₜ x) ⊗ₜ (μ G Y Z).hom (y ⊗ₜ z))) =
      (μ G (W ⊗ Y) (X' ⊗ Z)).hom ((μ G W Y).hom (w ⊗ₜ y) ⊗ₜ (μ G X' Z).hom (x ⊗ₜ z)) := by
  have h := congrArg (fun φ => φ.hom ((w ⊗ₜ x) ⊗ₜ (y ⊗ₜ z)))
    (tensorμ_comp_μ_tensorHom_μ_comp_μ G W X' Y Z)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    tensorμ, ModuleCat.MonoidalCategory.associator_hom_apply, ModuleCat.MonoidalCategory.associator_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply] at h
  exact h.symm

theorem μ_tensorHom_apply {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') (a : G.obj A) (b : G.obj B) :
    (G.map (f ⊗ₘ g)).hom ((μ G A B).hom (a ⊗ₜ b)) = (μ G A' B').hom ((G.map f).hom a ⊗ₜ (G.map g).hom b) := by
  have h := congrArg (fun φ => φ.hom (a ⊗ₜ b)) (Functor.LaxMonoidal.μ_natural G f g)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul] at h
  exact h.symm

theorem kappa_succ {X : C} {k : ℕ} (g : Fin (k + 1) → G.obj Xᘁ) (z : G.obj (tpow X k)) (x : G.obj X) :
    kappa G g ((μ G (tpow X k) X).hom (z ⊗ₜ x)) =
      act G (kappa G (Fin.init g) z) (pairG G (g (Fin.last k)) x) := by
  simp only [kappa, evK, map_comp_apply, prodG_succ]
  rw [tensorμ_apply, μ_tensorHom_apply]
  rfl

theorem pcLin_apply {X : C} {k : ℕ} (g : Fin k → G.obj Xᘁ) (z : G.obj (tpow X k)) (x : G.obj X) :
    pcLin G g ((μ G (tpow X k) X).hom (z ⊗ₜ x)) = act G (kappa G g z) x := by
  change (G.map (evK' X k)).hom ((μ G _ _).hom (prodG G Xᘁ k g ⊗ₜ (μ G (tpow X k) X).hom (z ⊗ₜ x))) = _
  simp only [evK', map_comp_apply]
  rw [μ_assoc_inv_apply, μ_whiskerRight_apply]
  rfl

theorem act_zero_left {Y : C} (y : G.obj Y) : act G 0 y = 0 := by
  simp [act]

theorem kappa_prodG_eq_zero {X : C} : ∀ {k : ℕ} (g : Fin k → G.obj Xᘁ) (v : Fin k → G.obj X) (i : Fin k),
    pairG G (g i) (v i) = 0 → kappa G g (prodG G X k v) = 0
  | 0, _, _, i, _ => i.elim0
  | k + 1, g, v, i, h => by
    rw [prodG_succ, kappa_succ]
    by_cases hi : i = Fin.last k
    · subst hi
      rw [h, act_zero_right]
    · obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi
      rw [kappa_prodG_eq_zero (Fin.init g) (Fin.init v) i' h, act_zero_left]

theorem kappa_prodG_eq_one {X : C} : ∀ {k : ℕ} (g : Fin k → G.obj Xᘁ) (v : Fin k → G.obj X),
    (∀ i, pairG G (g i) (v i) = (ε G).hom 1) → kappa G g (prodG G X k v) = (ε G).hom 1
  | 0, g, v, _ => by
    simp only [kappa, evK, prodG]
    exact act_unit G _
  | k + 1, g, v, h => by
    rw [prodG_succ, kappa_succ, kappa_prodG_eq_one (Fin.init g) (Fin.init v) (fun i => h i.castSucc),
      h (Fin.last k), act_unit]

/-- **Completeness core.**  If `Λ^{n+1} X = 0` and `(e, f)` is an orthonormal `n`-family, a
vector orthogonal to all `f_i` vanishes. -/
theorem eq_zero_of_orthonormal {X : C} {n : ℕ} (hA : antisym X (n + 1) = 0)
    (e : Fin n → G.obj X) (f : Fin n → G.obj Xᘁ)
    (horth : ∀ i j, pairG G (f i) (e j) = if i = j then (ε G).hom 1 else 0)
    (y : G.obj X) (hy : ∀ i, pairG G (f i) y = 0) : y = 0 := by
  set w : Fin (n + 1) → G.obj X := Fin.snoc e y with hw
  have h0 : pcLin G f ((G.map (antisym X (n + 1))).hom (prodG G X (n + 1) w)) = 0 := by
    rw [hA, Functor.map_zero]
    simp
  rw [map_antisym_prodG, map_smul, map_sum] at h0
  have hterm : ∀ σ : Equiv.Perm (Fin (n + 1)),
      pcLin G f (sgnC σ • prodG G X (n + 1) (w ∘ σ)) = if σ = 1 then y else 0 := by
    intro σ
    rw [map_smul, prodG_succ, pcLin_apply]
    split_ifs with hσ
    · subst hσ
      have hinit : Fin.init (w ∘ (1 : Equiv.Perm (Fin (n + 1)))) = e := by
        funext i; simp [hw, Fin.init]
      rw [hinit, kappa_prodG_eq_one G f e (fun i => by rw [horth]; simp)]
      simp [sgnC, hw, act_unit]
    · -- some `i < n` is moved
      obtain ⟨i, hi⟩ : ∃ i : Fin n, σ i.castSucc ≠ i.castSucc := by
        by_contra hcon
        push Not at hcon
        apply hσ
        have hlast : σ (Fin.last n) = Fin.last n := by
          by_contra hl
          obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.2 hl
          have := σ.injective (hj.symm.trans (hcon j).symm)
          exact Fin.castSucc_ne_last j this.symm
        ext x
        refine Fin.lastCases ?_ (fun j => ?_) x
        · simp [hlast]
        · simp [hcon j]
      rw [kappa_prodG_eq_zero G f (Fin.init (w ∘ σ)) i, act_zero_left, smul_zero]
      simp only [Fin.init, Function.comp_apply, hw]
      by_cases hl : σ i.castSucc = Fin.last n
      · rw [hl, Fin.snoc_last]
        exact hy i
      · obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.2 hl
        rw [← hj, Fin.snoc_castSucc, horth, if_neg]
        intro hij
        subst hij
        exact hi hj.symm
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ), Finset.sum_ite_eq' Finset.univ (1 : Equiv.Perm (Fin (n + 1)))] at h0
  simp only [Finset.mem_univ, if_true] at h0
  rcases smul_eq_zero.1 h0 with h | h
  · exact absurd h (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _))
  · exact h

end Contraction

end VOA.Huang.TensorCat.DeligneFiber
