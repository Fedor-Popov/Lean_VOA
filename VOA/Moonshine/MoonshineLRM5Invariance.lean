import VOA.Moonshine.MoonshineLRM5Poly

/-!
# `SL₂(ℤ)`-invariance of the Hecke sum from the modular generators

* `smul_invariant_of_S_T`: a function on `ℍ` invariant under `S` and `T` is invariant under all of
  `SL₂(ℤ)` (`SpecialLinearGroup.SL2Z_generators`).
* `qHeckeSum_T_smul`: the Hecke sum `R_M` of any `q`-series is `T`-invariant. In each block,
  `b ↦ a + b` permutes the residues mod `d`, and `f` is `1`-periodic.

The `S`-invariance of `R_M` for an `SL₂(ℤ)`-invariant `f` (the coset bijection of
`Notes/moonshine/MOON_BKM.md`) is the next file.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open UpperHalfPlane Real
open scoped MatrixGroups

/-- Invariance under the generators `S`, `T` gives invariance under `SL₂(ℤ)`. -/
theorem smul_invariant_of_S_T {R : ℍ → ℂ} (hS : ∀ τ : ℍ, R (ModularGroup.S • τ) = R τ)
    (hT : ∀ τ : ℍ, R (ModularGroup.T • τ) = R τ) (γ : SL(2, ℤ)) (τ : ℍ) : R (γ • τ) = R τ := by
  have hγ : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top γ
  induction hγ using Subgroup.closure_induction generalizing τ with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact hS τ
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hT τ
  | one => rw [one_smul]
  | mul x y _ _ ihx ihy => rw [mul_smul, ihx, ihy]
  | inv x _ ihx => rw [← ihx (x⁻¹ • τ), smul_inv_smul]

/-- One Hecke block is `T`-invariant: `B(a, d)(τ + 1) = B(a, d)(τ)`. -/
theorem qHeckeBlock_vadd_one (c : ℕ → ℂ) (a d : ℕ) (τ : ℍ) :
    qHeckeBlock c a d ((1 : ℝ) +ᵥ τ) = qHeckeBlock c a d τ := by
  by_cases h : 0 < a ∧ 0 < d
  · obtain ⟨ha, hd⟩ := h
    rw [qHeckeBlock_of_pos c a d ha hd, qHeckeBlock_of_pos c a d ha hd]
    have hpt : ∀ b : ℕ, heckePoint a d b ha hd ((1 : ℝ) +ᵥ τ) = heckePoint a d (a + b) ha hd τ := by
      intro b
      apply UpperHalfPlane.ext
      rw [coe_heckePoint_apply, coe_heckePoint_apply, coe_vadd]
      push_cast
      ring
    simp_rw [hpt]
    refine sum_comp_eq_sum_range_of_periodic (Finset.range d) (fun b => a + b)
      (fun n => qSeriesFun c (heckePoint a d n ha hd τ)) hd ?_ ?_ (Finset.card_range d)
    · intro n
      apply qSeriesFun_eq_of_eq_add_int (n := 1)
      rw [coe_heckePoint_apply, coe_heckePoint_apply]
      have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      push_cast
      field_simp
      ring
    · intro b hb b' hb' heq
      simp only [Finset.coe_range, Set.mem_Iio] at hb hb'
      have h1 : a + b ≡ a + b' [MOD d] := heq
      have h2 := Nat.ModEq.add_left_cancel' a h1
      unfold Nat.ModEq at h2
      rwa [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at h2
  · rw [qHeckeBlock, dif_neg h, qHeckeBlock, dif_neg h]

/-- **`T`-invariance of the Hecke sum** of any `q`-series. -/
theorem qHeckeSum_T_smul (c : ℕ → ℂ) (M : ℕ) (τ : ℍ) :
    qHeckeSum c M (ModularGroup.T • τ) = qHeckeSum c M τ := by
  rw [modular_T_smul]
  simp only [qHeckeSum, qHeckeBlock_vadd_one]

end VOA.Moonshine.ConwayNorton.M8
