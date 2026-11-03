/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Linear codes

Ebeling §1.2 (and Chapter 2) works with linear codes over a finite field `𝔽_q`. Following
decision **D6** of `BLUEPRINT.md` a code is a `Submodule` of `(ZMod q)ⁿ`; the general `q` is
kept from the start because Chapter 5 needs `q = p` odd, even though Chapters 1–3 only use
`q = 2`.

Only the *definitions* live here, together with the duality theory that everything downstream
needs. Weight enumerators are M12, MacWilliams is M13.

## Main definitions

* `Code q n` — a linear code of length `n` over `ZMod q`.
* `Code.weight`, `Code.dist` — Hamming weight and distance, as `ℕ`.
* `Code.stdBilin` — the standard symmetric form `⟪x, y⟫ = ∑ᵢ xᵢyᵢ`.
* `Code.dual` — the dual code, `Cᗮ`.
* `Code.rank` — the dimension `k` of a `[n, k]` code.
* `Code.IsSelfOrthogonal`, `Code.IsSelfDual`, `Code.IsEven`, `Code.IsDoublyEven`.
* `Code.minDist` — the minimum distance `d` of a `[n, k, d]` code.
* `Code.PermEquiv`, `Code.MonomialEquiv` — permutation and monomial equivalence.

## Implementation notes

`Code.dual` is defined as Mathlib's `LinearMap.BilinForm.orthogonal` of the standard form, which
buys the dimension formula `dim C + dim Cᗮ = n` and `Cᗮᗮ = C` for free over a field.

## References

Ebeling, *Lattices and Codes*, 3rd ed., §1.2 and §2.7.
-/

open scoped Matrix
open Module (finrank)

/-- A **linear code** of length `n` over `ZMod q`: a submodule of `(ZMod q)ⁿ`. For `q` prime
this is Ebeling's `𝔽_q`-linear code. See `BLUEPRINT.md` D6. -/
abbrev Code (q n : ℕ) : Type := Submodule (ZMod q) (Fin n → ZMod q)

namespace Code

variable {q n : ℕ}

/-! ### Hamming weight and distance -/

/-- The **Hamming weight** of a word: the number of nonzero coordinates. -/
def weight (c : Fin n → ZMod q) : ℕ := hammingNorm c

/-- The **Hamming distance** between two words. -/
def dist (x y : Fin n → ZMod q) : ℕ := hammingDist x y

@[simp] theorem weight_zero : weight (0 : Fin n → ZMod q) = 0 := hammingNorm_zero

@[simp] theorem weight_eq_zero {c : Fin n → ZMod q} : weight c = 0 ↔ c = 0 := hammingNorm_eq_zero

@[simp] theorem weight_pos {c : Fin n → ZMod q} : 0 < weight c ↔ c ≠ 0 := hammingNorm_pos_iff

theorem weight_le (c : Fin n → ZMod q) : weight c ≤ n := by
  have h : hammingNorm c ≤ Fintype.card (Fin n) := hammingNorm_le_card_fintype
  simpa [weight] using h

theorem dist_eq_weight_sub (x y : Fin n → ZMod q) : dist x y = weight (y - x) := by
  rw [dist, weight, hammingDist_eq_hammingNorm]
  congr 1
  abel

@[simp] theorem dist_zero_right (x : Fin n → ZMod q) : dist x 0 = weight x :=
  hammingDist_zero_right x

theorem dist_comm (x y : Fin n → ZMod q) : dist x y = dist y x := hammingDist_comm x y

/-- The support of a word: the set of coordinates where it does not vanish. -/
def support (c : Fin n → ZMod q) : Finset (Fin n) := {i | c i ≠ 0}

theorem weight_eq_card_support (c : Fin n → ZMod q) : weight c = (support c).card := rfl

@[simp] theorem mem_support {c : Fin n → ZMod q} {i : Fin n} : i ∈ support c ↔ c i ≠ 0 := by
  simp [support]

/-! ### The standard bilinear form -/

/-- The standard symmetric bilinear form `⟪x, y⟫ = ∑ᵢ xᵢyᵢ` on `(ZMod q)ⁿ`, with respect to
which duality of codes is taken. -/
def stdBilin (q n : ℕ) : LinearMap.BilinForm (ZMod q) (Fin n → ZMod q) := Matrix.toBilin' 1

@[simp] theorem stdBilin_apply (x y : Fin n → ZMod q) : stdBilin q n x y = x ⬝ᵥ y := by
  rw [stdBilin, Matrix.toBilin'_apply', Matrix.one_mulVec]

theorem stdBilin_comm (x y : Fin n → ZMod q) : stdBilin q n x y = stdBilin q n y x := by
  simp [dotProduct_comm]

theorem stdBilin_isSymm : (stdBilin q n).IsSymm := ⟨fun x y => stdBilin_comm x y⟩

theorem stdBilin_isRefl : (stdBilin q n).IsRefl := stdBilin_isSymm.isRefl

theorem stdBilin_separatingLeft : (stdBilin q n).SeparatingLeft := by
  intro x hx
  funext i
  have h := hx (Pi.single i 1)
  rw [stdBilin_apply, dotProduct_single] at h
  simpa using h

theorem stdBilin_nondegenerate : (stdBilin q n).Nondegenerate := by
  refine ⟨stdBilin_separatingLeft, fun y hy => ?_⟩
  refine stdBilin_separatingLeft y fun z => ?_
  rw [stdBilin_comm]
  exact hy z

/-! ### The dual code -/

/-- The **dual code** `Cᗮ` with respect to `⟪x, y⟫ = ∑ᵢ xᵢyᵢ`. -/
def dual (C : Code q n) : Code q n := (stdBilin q n).orthogonal C

@[simp] theorem mem_dual {C : Code q n} {x : Fin n → ZMod q} :
    x ∈ C.dual ↔ ∀ y ∈ C, y ⬝ᵥ x = 0 := by
  simp [dual, LinearMap.BilinForm.isOrtho_def]

theorem mem_dual' {C : Code q n} {x : Fin n → ZMod q} :
    x ∈ C.dual ↔ ∀ y ∈ C, x ⬝ᵥ y = 0 := by
  rw [mem_dual]
  exact forall₂_congr fun y _ => by rw [dotProduct_comm]

theorem dual_le_dual {C D : Code q n} (h : C ≤ D) : D.dual ≤ C.dual :=
  LinearMap.BilinForm.orthogonal_le h

theorem le_dual_dual (C : Code q n) : C ≤ C.dual.dual :=
  LinearMap.BilinForm.le_orthogonal_orthogonal stdBilin_isRefl

@[simp] theorem dual_bot : (⊥ : Code q n).dual = ⊤ := LinearMap.BilinForm.orthogonal_bot

theorem dual_top : (⊤ : Code q n).dual = ⊥ :=
  LinearMap.BilinForm.orthogonal_top_eq_bot stdBilin_nondegenerate

/-! ### Dimension -/

/-- The **dimension** (rank) `k` of an `[n, k]` code. -/
noncomputable def rank (C : Code q n) : ℕ := finrank (ZMod q) C

section Field

variable [Fact (Nat.Prime q)]

theorem finrank_ambient (q n : ℕ) [Fact (Nat.Prime q)] :
    finrank (ZMod q) (Fin n → ZMod q) = n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

theorem rank_le (C : Code q n) : C.rank ≤ n := by
  have := Submodule.finrank_le C
  rwa [finrank_ambient] at this

@[simp] theorem rank_dual (C : Code q n) : C.dual.rank = n - C.rank := by
  rw [rank, rank, dual,
    LinearMap.BilinForm.finrank_orthogonal stdBilin_nondegenerate C, finrank_ambient]

theorem rank_add_rank_dual (C : Code q n) : C.rank + C.dual.rank = n := by
  rw [rank_dual]
  have := rank_le C
  omega

@[simp] theorem dual_dual (C : Code q n) : C.dual.dual = C :=
  LinearMap.BilinForm.orthogonal_orthogonal stdBilin_nondegenerate stdBilin_isRefl C

theorem rank_mono {C D : Code q n} (h : C ≤ D) : C.rank ≤ D.rank :=
  Submodule.finrank_mono h

end Field

/-! ### Self-orthogonal, self-dual, even and doubly even codes -/

/-- A code is **self-orthogonal** when it is contained in its dual, i.e. all inner products of
codewords vanish. -/
def IsSelfOrthogonal (C : Code q n) : Prop := C ≤ C.dual

/-- A code is **self-dual** when it equals its dual. -/
def IsSelfDual (C : Code q n) : Prop := C.dual = C

theorem isSelfOrthogonal_iff {C : Code q n} :
    C.IsSelfOrthogonal ↔ ∀ x ∈ C, ∀ y ∈ C, x ⬝ᵥ y = 0 := by
  constructor
  · intro h x hx y hy
    exact mem_dual'.mp (h hx) y hy
  · intro h x hx
    exact mem_dual'.mpr fun y hy => h x hx y hy

theorem IsSelfDual.isSelfOrthogonal {C : Code q n} (h : C.IsSelfDual) : C.IsSelfOrthogonal :=
  le_of_eq h.symm

/-- A self-orthogonal code has dimension at most `n/2`. -/
theorem IsSelfOrthogonal.two_mul_rank_le [Fact (Nat.Prime q)] {C : Code q n}
    (h : C.IsSelfOrthogonal) : 2 * C.rank ≤ n := by
  have h1 : C.rank ≤ C.dual.rank := rank_mono h
  have h2 := rank_add_rank_dual C
  omega

/-- A binary code is **even** when every codeword has even weight. -/
def IsEven (C : Code 2 n) : Prop := ∀ c ∈ C, 2 ∣ weight c

/-- A binary code is **doubly even** when every codeword has weight divisible by `4`.
Ebeling §1.2. -/
def IsDoublyEven (C : Code 2 n) : Prop := ∀ c ∈ C, 4 ∣ weight c

theorem IsDoublyEven.isEven {C : Code 2 n} (h : C.IsDoublyEven) : C.IsEven := fun c hc =>
  dvd_trans ⟨2, rfl⟩ (h c hc)


/-! ### Binary codes: weights and inner products

Over `ZMod 2` the inner product of two words is the parity of the size of the intersection of
their supports, and weights add up to the size of the symmetric difference. Together these give
Ebeling's observation that a doubly even binary code is automatically self-orthogonal.
-/

section Binary

variable (x y : Fin n → ZMod 2)

theorem support_add : support (x + y) = (support x ∪ support y) \ (support x ∩ support y) := by
  have key : ∀ a b : ZMod 2, (a + b ≠ 0) ↔ ((a ≠ 0 ∨ b ≠ 0) ∧ ¬(a ≠ 0 ∧ b ≠ 0)) := by decide
  ext i
  simp only [mem_support, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, Pi.add_apply]
  exact key (x i) (y i)

theorem dotProduct_eq_card_inter :
    x ⬝ᵥ y = ((support x ∩ support y).card : ZMod 2) := by
  have key : ∀ a b : ZMod 2, a * b = if a ≠ 0 ∧ b ≠ 0 then 1 else 0 := by decide
  rw [dotProduct]
  have : ∀ i : Fin n, x i * y i = if i ∈ support x ∩ support y then (1 : ZMod 2) else 0 := by
    intro i
    rw [key]
    congr 1
    simp [Finset.mem_inter]
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Weights of binary words add up to the size of the symmetric difference of their supports. -/
theorem weight_add_two_mul_card_inter :
    weight (x + y) + 2 * (support x ∩ support y).card = weight x + weight y := by
  have hsub : support x ∩ support y ⊆ support x ∪ support y :=
    Finset.inter_subset_union
  have h1 : (support x ∪ support y).card + (support x ∩ support y).card
      = (support x).card + (support y).card := Finset.card_union_add_card_inter _ _
  have h3 : (support x ∩ support y).card ≤ (support x ∪ support y).card :=
    Finset.card_le_card hsub
  have h2 : weight (x + y) = (support x ∪ support y).card - (support x ∩ support y).card := by
    rw [weight_eq_card_support, support_add, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hsub]
  rw [h2, weight_eq_card_support x, weight_eq_card_support y]
  omega

/-- A doubly even binary code is self-orthogonal. Ebeling §1.2. -/
theorem IsDoublyEven.isSelfOrthogonal {C : Code 2 n} (h : C.IsDoublyEven) :
    C.IsSelfOrthogonal := by
  rw [isSelfOrthogonal_iff]
  intro x hx y hy
  obtain ⟨a, ha⟩ := h x hx
  obtain ⟨b, hb⟩ := h y hy
  obtain ⟨c, hc⟩ := h (x + y) (C.add_mem hx hy)
  have hw := weight_add_two_mul_card_inter x y
  have hm : (support x ∩ support y).card = 2 * (a + b - c) := by omega
  rw [dotProduct_eq_card_inter, hm, Nat.cast_mul, ZMod.natCast_self, zero_mul]

end Binary

/-! ### Self-duality -/

section SelfDual

variable [Fact (Nat.Prime q)]

theorem isSelfDual_iff {C : Code q n} :
    C.IsSelfDual ↔ C.IsSelfOrthogonal ∧ 2 * C.rank = n := by
  constructor
  · intro h
    refine ⟨h.isSelfOrthogonal, ?_⟩
    have := rank_add_rank_dual C
    rw [h] at this
    omega
  · rintro ⟨hso, hr⟩
    have hd : C.dual.rank = C.rank := by
      rw [rank_dual]
      omega
    exact (Submodule.eq_of_le_of_finrank_le hso
      (show finrank (ZMod q) C.dual ≤ finrank (ZMod q) C from le_of_eq hd)).symm

theorem IsSelfDual.two_mul_rank {C : Code q n} (h : C.IsSelfDual) : 2 * C.rank = n :=
  (isSelfDual_iff.mp h).2

end SelfDual

/-! ### Minimum distance -/

/-- The **minimum distance** of a code: the least weight of a nonzero codeword. By the `Nat.sInf`
convention this is `0` for the zero code. -/
noncomputable def minDist (C : Code q n) : ℕ := sInf {w | ∃ c ∈ C, c ≠ 0 ∧ weight c = w}

theorem minDist_le_weight {C : Code q n} {c : Fin n → ZMod q} (hc : c ∈ C) (hne : c ≠ 0) :
    C.minDist ≤ weight c :=
  Nat.sInf_le ⟨c, hc, hne, rfl⟩

theorem exists_weight_eq_minDist {C : Code q n} (h : C ≠ ⊥) :
    ∃ c ∈ C, c ≠ 0 ∧ weight c = C.minDist := by
  have hne : {w | ∃ c ∈ C, c ≠ 0 ∧ weight c = w}.Nonempty := by
    obtain ⟨c, hc, hcne⟩ := (Submodule.ne_bot_iff C).mp h
    exact ⟨weight c, c, hc, hcne, rfl⟩
  exact Nat.sInf_mem hne

theorem minDist_pos {C : Code q n} (h : C ≠ ⊥) : 0 < C.minDist := by
  obtain ⟨c, hc, hcne, hw⟩ := exists_weight_eq_minDist h
  rw [← hw]
  exact weight_pos.mpr hcne

@[simp] theorem minDist_bot : (⊥ : Code q n).minDist = 0 := by
  rw [minDist, Nat.sInf_eq_zero]
  right
  ext w
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, hc, hne, -⟩
  exact hne ((Submodule.mem_bot _).mp hc)

/-- Distinct codewords are at least `minDist` apart. -/
theorem minDist_le_dist {C : Code q n} {x y : Fin n → ZMod q} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x ≠ y) : C.minDist ≤ dist x y := by
  rw [dist_eq_weight_sub]
  refine minDist_le_weight (C.sub_mem hy hx) ?_
  intro h
  exact hxy (by rw [← sub_eq_zero]; rw [sub_eq_zero] at h ⊢; exact h.symm)

/-! ### Permutation and monomial equivalence -/

/-- Permuting the coordinates of a word by `σ`. -/
def permEquiv (σ : Equiv.Perm (Fin n)) : (Fin n → ZMod q) ≃ₗ[ZMod q] (Fin n → ZMod q) where
  toFun x := fun i => x (σ i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := fun i => x (σ.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

@[simp] theorem permEquiv_apply (σ : Equiv.Perm (Fin n)) (x : Fin n → ZMod q) (i : Fin n) :
    permEquiv σ x i = x (σ i) := rfl

/-- Permuting the coordinates of a word by `σ` and rescaling coordinate `i` by the unit `u i`.
This is the general notion of equivalence of codes over `𝔽_q`; for `q = 2` the units are trivial
and it reduces to permutation equivalence. -/
def monomialEquiv (σ : Equiv.Perm (Fin n)) (u : Fin n → (ZMod q)ˣ) :
    (Fin n → ZMod q) ≃ₗ[ZMod q] (Fin n → ZMod q) where
  toFun x := fun i => (u i : ZMod q) * x (σ i)
  map_add' x y := by funext i; simp [mul_add]
  map_smul' c x := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  invFun y := fun i => ((u (σ.symm i))⁻¹ : (ZMod q)ˣ) * y (σ.symm i)
  left_inv x := by
    funext i
    simp only [Equiv.apply_symm_apply]
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  right_inv y := by
    funext i
    simp only [Equiv.symm_apply_apply]
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

@[simp] theorem monomialEquiv_apply (σ : Equiv.Perm (Fin n)) (u : Fin n → (ZMod q)ˣ)
    (x : Fin n → ZMod q) (i : Fin n) : monomialEquiv σ u x i = (u i : ZMod q) * x (σ i) := rfl

theorem permEquiv_eq_monomialEquiv (σ : Equiv.Perm (Fin n)) :
    permEquiv (q := q) σ = monomialEquiv σ 1 := by
  ext x i
  simp

theorem monomialEquiv_one : monomialEquiv (q := q) (n := n) 1 1 = LinearEquiv.refl _ _ := by
  ext x i
  simp

theorem monomialEquiv_symm (σ : Equiv.Perm (Fin n)) (u : Fin n → (ZMod q)ˣ) :
    (monomialEquiv σ u).symm = monomialEquiv σ.symm (fun i => (u (σ.symm i))⁻¹) := by
  ext y i
  rfl

theorem monomialEquiv_trans (σ τ : Equiv.Perm (Fin n)) (u w : Fin n → (ZMod q)ˣ) :
    (monomialEquiv σ u).trans (monomialEquiv τ w) =
      monomialEquiv (τ.trans σ) (fun i => w i * u (τ i)) := by
  ext x i
  simp [mul_assoc]

/-- The weight is unchanged by a monomial transformation. -/
@[simp] theorem weight_monomialEquiv (σ : Equiv.Perm (Fin n)) (u : Fin n → (ZMod q)ˣ)
    (x : Fin n → ZMod q) : weight (monomialEquiv σ u x) = weight x := by
  show (support (monomialEquiv σ u x)).card = (support x).card
  refine Finset.card_equiv σ fun i => ?_
  simp [Units.mul_right_eq_zero]

@[simp] theorem weight_permEquiv (σ : Equiv.Perm (Fin n)) (x : Fin n → ZMod q) :
    weight (permEquiv σ x) = weight x := by
  rw [permEquiv_eq_monomialEquiv, weight_monomialEquiv]

/-- Two codes are **monomial equivalent** when one is carried to the other by a coordinate
permutation composed with a rescaling of each coordinate by a unit. Ebeling §1.2. -/
def MonomialEquiv (C D : Code q n) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (u : Fin n → (ZMod q)ˣ),
    C.map (monomialEquiv σ u).toLinearMap = D

/-- Two codes are **permutation equivalent** when one is carried to the other by a permutation of
the coordinates. -/
def PermEquiv (C D : Code q n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), C.map (permEquiv σ).toLinearMap = D

theorem PermEquiv.monomialEquiv {C D : Code q n} (h : C.PermEquiv D) : C.MonomialEquiv D := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ, 1, by rw [← permEquiv_eq_monomialEquiv]; exact hσ⟩

@[refl] theorem MonomialEquiv.refl (C : Code q n) : C.MonomialEquiv C :=
  ⟨1, 1, by rw [monomialEquiv_one]; simp⟩

@[symm] theorem MonomialEquiv.symm {C D : Code q n} (h : C.MonomialEquiv D) : D.MonomialEquiv C := by
  obtain ⟨σ, u, rfl⟩ := h
  refine ⟨σ.symm, fun i => (u (σ.symm i))⁻¹, ?_⟩
  rw [← monomialEquiv_symm, ← Submodule.map_comp]
  have hid : (monomialEquiv σ u).symm.toLinearMap.comp (monomialEquiv σ u).toLinearMap
      = LinearMap.id := by
    ext x
    simp
  rw [hid, Submodule.map_id]

@[trans] theorem MonomialEquiv.trans {C D E : Code q n} (h₁ : C.MonomialEquiv D)
    (h₂ : D.MonomialEquiv E) : C.MonomialEquiv E := by
  obtain ⟨σ, u, rfl⟩ := h₁
  obtain ⟨τ, w, rfl⟩ := h₂
  refine ⟨τ.trans σ, fun i => w i * u (τ i), ?_⟩
  rw [← monomialEquiv_trans, ← Submodule.map_comp]
  rfl

@[refl] theorem PermEquiv.refl (C : Code q n) : C.PermEquiv C :=
  ⟨1, by rw [permEquiv_eq_monomialEquiv, monomialEquiv_one]; simp⟩

theorem permEquiv_symm (σ : Equiv.Perm (Fin n)) :
    (permEquiv (q := q) σ).symm = permEquiv σ.symm := by
  ext y i
  rfl

theorem permEquiv_trans (σ τ : Equiv.Perm (Fin n)) :
    (permEquiv (q := q) σ).trans (permEquiv τ) = permEquiv (τ.trans σ) := by
  ext x i
  rfl

@[symm] theorem PermEquiv.symm {C D : Code q n} (h : C.PermEquiv D) : D.PermEquiv C := by
  obtain ⟨σ, rfl⟩ := h
  refine ⟨σ.symm, ?_⟩
  rw [← Submodule.map_comp]
  have hid : (permEquiv (q := q) σ.symm).toLinearMap.comp (permEquiv σ).toLinearMap
      = LinearMap.id := by
    apply LinearMap.ext
    intro x
    funext i
    simp [LinearMap.comp_apply]
  rw [hid, Submodule.map_id]

@[trans] theorem PermEquiv.trans {C D E : Code q n} (h₁ : C.PermEquiv D) (h₂ : D.PermEquiv E) :
    C.PermEquiv E := by
  obtain ⟨σ, rfl⟩ := h₁
  obtain ⟨τ, rfl⟩ := h₂
  refine ⟨τ.trans σ, ?_⟩
  rw [← Submodule.map_comp]
  rfl

/-- Monomial equivalence preserves the dimension. -/
theorem MonomialEquiv.rank_eq {C D : Code q n} (h : C.MonomialEquiv D) : C.rank = D.rank := by
  obtain ⟨σ, u, rfl⟩ := h
  exact LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (monomialEquiv σ u).toLinearMap
      (monomialEquiv σ u).injective C)

/-- Monomial equivalence preserves the minimum distance. -/
theorem MonomialEquiv.minDist_eq {C D : Code q n} (h : C.MonomialEquiv D) :
    C.minDist = D.minDist := by
  obtain ⟨σ, u, rfl⟩ := h
  have hset : {w | ∃ c ∈ C, c ≠ 0 ∧ weight c = w}
      = {w | ∃ c ∈ C.map (monomialEquiv σ u).toLinearMap, c ≠ 0 ∧ weight c = w} := by
    ext w
    constructor
    · rintro ⟨c, hc, hne, rfl⟩
      refine ⟨monomialEquiv σ u c, ⟨c, hc, rfl⟩, ?_, ?_⟩
      · simpa using fun hcontra => hne ((monomialEquiv σ u).map_eq_zero_iff.mp hcontra)
      · exact weight_monomialEquiv σ u c
    · rintro ⟨c, ⟨c₀, hc₀, rfl⟩, hne, rfl⟩
      refine ⟨c₀, hc₀, ?_, ?_⟩
      · intro hcontra
        exact hne (by rw [hcontra]; simp)
      · exact (weight_monomialEquiv σ u c₀).symm
  rw [minDist, minDist, hset]

/-- Monomial equivalence preserves double evenness. -/
theorem MonomialEquiv.isDoublyEven {C D : Code 2 n} (h : C.MonomialEquiv D)
    (hC : C.IsDoublyEven) : D.IsDoublyEven := by
  obtain ⟨σ, u, rfl⟩ := h
  rintro c ⟨c₀, hc₀, rfl⟩
  rw [show (monomialEquiv σ u).toLinearMap c₀ = monomialEquiv σ u c₀ from rfl,
    weight_monomialEquiv]
  exact hC c₀ hc₀

end Code
