/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbPrimInvariant

/-! # OrbOcta (I): invariants of the octahedral group `S₄ ⊂ SO(3)` on `ℂ[x, y, z]`

`S₄ = A₄ ⋊ ⟨s₃⟩` with `s₃ : (x, y, z) ↦ (-x, z, y)` (this is how `rot2 = octHom (0 1)` acts on
`(V₂)₁`; see `OrbOctaSpan.phiE_rot2`). On the `A₄` generators `s₃` acts by
`r² ↦ r²`, `I₃ ↦ -I₃`, `I₄ ↦ I₄`, `I₆ ↦ -I₆`.

`mem_span_evenMon`: a homogeneous `S₄`-invariant of degree `n` is a linear combination of the
generator monomials `r^{2a} I₃^b I₄^c I₆^d` of degree `n` with `b + d` even.

`evenMon_cases`: such a monomial is `1`, one of the five atoms `r², I₄, I₃², I₃I₆, I₆²`, or a
product of two such monomials of positive degree.

No relation `I₆² = …` is used: `I₆²` is simply kept as a fifth atom.
-/

noncomputable section
namespace VOA.Classification.COne.OrbOcta
open MvPolynomial VOA.Classification.COne.OrbPrim

/-- The octahedral involution `(x, y, z) ↦ (-x, z, y)`. -/
def s3 : P3 →ₐ[ℂ] P3 := aeval ![C (-1) * X 0, X 2, X 1]

theorem s3_X0 : s3 (X 0) = C (-1) * X 0 := by simp [s3]
theorem s3_X1 : s3 (X 1) = X 2 := by simp [s3]
theorem s3_X2 : s3 (X 2) = X 1 := by simp [s3]

theorem s3_r2 : s3 r2 = r2 := by
  simp only [r2, map_add, map_pow, s3_X0, s3_X1, s3_X2, map_neg, map_one]; ring

theorem s3_I3 : s3 I3 = -I3 := by
  simp only [I3, map_mul, s3_X0, s3_X1, s3_X2, map_neg, map_one]; ring

theorem s3_I4 : s3 I4 = I4 := by
  simp only [I4, map_add, map_pow, s3_X0, s3_X1, s3_X2, map_neg, map_one]; ring

theorem s3_I6 : s3 I6 = -I6 := by
  simp only [I6, map_mul, map_sub, map_pow, s3_X0, s3_X1, s3_X2, map_neg, map_one]; ring

/-- The `s₃`-parity of a generator monomial. -/
def par (t : ℕ × ℕ × ℕ × ℕ) : ℕ := t.2.1 + t.2.2.2

theorem s3_genMon (t : ℕ × ℕ × ℕ × ℕ) : s3 (genMon t) = (-1 : P3) ^ par t * genMon t := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [genMon, par, map_mul, map_pow, s3_r2, s3_I3, s3_I4, s3_I6, neg_pow I3, neg_pow I6,
    pow_add]
  ring

theorem s3_genMon_even {t : ℕ × ℕ × ℕ × ℕ} (h : par t % 2 = 0) : s3 (genMon t) = genMon t := by
  rw [s3_genMon, Even.neg_one_pow (Nat.even_iff.mpr h), one_mul]

theorem s3_genMon_odd {t : ℕ × ℕ × ℕ × ℕ} (h : par t % 2 = 1) : s3 (genMon t) = -genMon t := by
  rw [s3_genMon, Odd.neg_one_pow (Nat.odd_iff.mpr h), neg_one_mul]

/-- `S₄`-invariance: `A₄`-invariance plus `s₃`-invariance. -/
def IsS4Inv (f : P3) : Prop := IsA4Inv f ∧ s3 f = f

/-- Generator monomials of degree `n` and even parity. -/
def evenMon (n : ℕ) : Set P3 := genMon '' {t | gdeg t = n ∧ par t % 2 = 0}

/-- The projector `(1 + s₃)/2`. -/
def proj : P3 →ₗ[ℂ] P3 := (1 / 2 : ℂ) • (LinearMap.id + s3.toLinearMap)

theorem proj_apply (f : P3) : proj f = (1 / 2 : ℂ) • (f + s3 f) := rfl

/-- **(I) for `S₄`, homogeneous form.** -/
theorem mem_span_evenMon {f : P3} {n : ℕ} (hf : IsS4Inv f) (hh : f.IsHomogeneous n) :
    f ∈ Submodule.span ℂ (evenMon n) := by
  have h1 := mem_span_genMon_of_isHomogeneous hf.1 hh
  have hp : proj f = f := by
    rw [proj_apply, hf.2, ← two_smul ℂ f, smul_smul]; norm_num
  rw [← hp]
  have hmap := Submodule.mem_map_of_mem (f := proj) h1
  rw [Submodule.map_span] at hmap
  refine Submodule.span_le.mpr ?_ hmap
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  rcases Nat.mod_two_eq_zero_or_one (par t) with h | h
  · have : proj (genMon t) = genMon t := by
      rw [proj_apply, s3_genMon_even h, ← two_smul ℂ (genMon t), smul_smul]; norm_num
    rw [SetLike.mem_coe, this]
    exact Submodule.subset_span ⟨t, ⟨ht, h⟩, rfl⟩
  · have : proj (genMon t) = 0 := by
      rw [proj_apply, s3_genMon_odd h, add_neg_cancel, smul_zero]
    rw [SetLike.mem_coe, this]
    exact Submodule.zero_mem _

/-- Classification of even generator monomials: `1`, an atom, or a product of two even
monomials of positive degree. -/
theorem evenMon_cases (t : ℕ × ℕ × ℕ × ℕ) (ht : par t % 2 = 0) :
    t = (0, 0, 0, 0) ∨ t = (1, 0, 0, 0) ∨ t = (0, 0, 1, 0) ∨ t = (0, 2, 0, 0) ∨
      t = (0, 1, 0, 1) ∨ t = (0, 0, 0, 2) ∨
      ∃ u v : ℕ × ℕ × ℕ × ℕ, par u % 2 = 0 ∧ par v % 2 = 0 ∧ 1 ≤ gdeg u ∧ 1 ≤ gdeg v ∧
        gdeg u + gdeg v = gdeg t ∧ genMon t = genMon u * genMon v := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [par] at ht
  have key : ∀ u v : ℕ × ℕ × ℕ × ℕ, (a, b, c, d) =
      (u.1 + v.1, u.2.1 + v.2.1, u.2.2.1 + v.2.2.1, u.2.2.2 + v.2.2.2) →
      genMon (a, b, c, d) = genMon u * genMon v ∧ gdeg u + gdeg v = gdeg (a, b, c, d) := by
    intro u v h
    rw [genMon_mul, h]
    refine ⟨rfl, ?_⟩
    simp only [gdeg, Prod.mk.injEq] at h ⊢
    omega
  by_cases h0 : a + b + c + d = 0
  · left; simp only [Prod.mk.injEq]; omega
  right
  by_cases ha : 1 ≤ a
  · by_cases ha1 : a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 0
    · left; obtain ⟨rfl, rfl, rfl, rfl⟩ := ha1; rfl
    right; right; right; right; right
    obtain ⟨h1, h2⟩ := key (1, 0, 0, 0) (a - 1, b, c, d) (by simp; omega)
    exact ⟨_, _, by simp [par], by simp only [par]; omega, by simp [gdeg],
      by simp only [gdeg]; omega, h2, h1⟩
  right
  by_cases hc : 1 ≤ c
  · by_cases hc1 : a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 0
    · left; obtain ⟨rfl, rfl, rfl, rfl⟩ := hc1; rfl
    right; right; right; right
    obtain ⟨h1, h2⟩ := key (0, 0, 1, 0) (a, b, c - 1, d) (by simp; omega)
    exact ⟨_, _, by simp [par], by simp only [par]; omega, by simp [gdeg],
      by simp only [gdeg]; omega, h2, h1⟩
  right
  have ha0 : a = 0 := by omega
  have hc0 : c = 0 := by omega
  subst ha0 hc0
  by_cases hb : 2 ≤ b
  · by_cases hb2 : b = 2 ∧ d = 0
    · left; obtain ⟨rfl, rfl⟩ := hb2; rfl
    right; right; right
    obtain ⟨h1, h2⟩ := key (0, 2, 0, 0) (0, b - 2, 0, d) (by simp; omega)
    exact ⟨_, _, by simp [par], by simp only [par]; omega, by simp [gdeg],
      by simp only [gdeg]; omega, h2, h1⟩
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · -- `d` even and positive
    by_cases hd2 : d = 2
    · right; right; left; subst hd2; rfl
    right; right; right
    obtain ⟨h1, h2⟩ := key (0, 0, 0, 2) (0, 0, 0, d - 2) (by simp; omega)
    exact ⟨_, _, by simp [par], by simp only [par]; omega, by simp [gdeg],
      by simp only [gdeg]; omega, h2, h1⟩
  · by_cases hd1 : d = 1
    · right; left; subst hd1; rfl
    right; right; right
    obtain ⟨h1, h2⟩ := key (0, 1, 0, 1) (0, 0, 0, d - 1) (by simp; omega)
    exact ⟨_, _, by simp [par], by simp only [par]; omega, by simp [gdeg],
      by simp only [gdeg]; omega, h2, h1⟩

theorem isS4Inv_genMon {t : ℕ × ℕ × ℕ × ℕ} (h : par t % 2 = 0) : IsS4Inv (genMon t) :=
  ⟨isA4Inv_genMon t, s3_genMon_even h⟩

theorem genMon_I4 : genMon (0, 0, 1, 0) = I4 := by simp [genMon]
theorem genMon_r2 : genMon (1, 0, 0, 0) = r2 := by simp [genMon]
theorem genMon_one : genMon (0, 0, 0, 0) = 1 := by simp [genMon]
theorem genMon_I3sq : genMon (0, 2, 0, 0) = I3 * I3 := by simp [genMon, pow_two]
theorem genMon_I3I6 : genMon (0, 1, 0, 1) = I3 * I6 := by simp [genMon]
theorem genMon_I6sq : genMon (0, 0, 0, 2) = I6 * I6 := by simp [genMon, pow_two]

end VOA.Classification.COne.OrbOcta
