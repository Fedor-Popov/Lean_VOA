/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetConformal
import VOA.Examples.Sl2CosetTensor
import VOA.Examples.Sl2CosetConcreteTranslation

/-!
# Quadratic Sugawara states and their coset difference

The finite quadratic Sugawara state is defined for any affine sl2 action.
Its singular current products are computed directly from the affine
commutator. This supplies the conformal-difference membership theorem for
tensor factors without presupposing a conformal VOA on the commutant.
-/

namespace VOA.Sl2CosetConcrete

open Sl2SemiInfinite Sl2Coset AffineVOA
open Module (End)
open scoped BigOperators TensorProduct

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- The current quadratic Casimir, before the Sugawara normalization. -/
noncomputable def quadraticState (A : AffineSl2Action V k) : M :=
  ∑ b : Fin 3, ∑ c : Fin 3,
    kappaInv b c • mode (V.Y (A.current b)) (-1) (A.current c)

/-- The Sugawara state of the given affine action, at its own level. -/
noncomputable def sugawaraState (A : AffineSl2Action V k) : M :=
  (2 * (k + 2))⁻¹ • quadraticState A

/-- The quadratic Sugawara state has ambient conformal weight two. -/
theorem sugawaraState_weight (A : AffineSl2Action V k) :
    sugawaraState A ∈ V.grading 2 := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro b hb
  apply Submodule.sum_mem
  intro c hc
  apply Submodule.smul_mem
  convert V.grading_mode _ (A.current_weight b) _ (A.current_weight c) (-1) using 1 <;>
    norm_num

/-- The quadratic Sugawara state is even. -/
theorem sugawaraState_even (A : AffineSl2Action V k) :
    sugawaraState A ∈ V.parity 0 := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro b hb
  apply Submodule.sum_mem
  intro c hc
  apply Submodule.smul_mem
  simpa using V.parity_mode _ (A.current_even b) _ (A.current_even c) (-1)

private theorem current_quadratic_term (A : AffineSl2Action V k)
    (a b c : Fin 3) (n : ℤ) :
    mode (V.Y (A.current a)) n (mode (V.Y (A.current b)) (-1) (A.current c)) =
      mode (V.Y (A.current b)) (-1) (mode (V.Y (A.current a)) n (A.current c)) +
      (∑ d, fabc a b d • mode (V.Y (A.current d)) (n - 1) (A.current c)) +
      if n = 1 then (k * kappa a b) • A.current c else 0 := by
  have h := congrArg (fun f : End ℂ M => f (A.current c))
    (A.current_comm a b n (-1))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  by_cases hn : n = 1
  · subst n
    simp only [Int.cast_one, one_mul, show (1 : ℤ) + -1 = 0 by norm_num,
      ite_true, LinearMap.smul_apply, LinearMap.id_apply] at h
    simpa only [sub_self, ite_true] using h.trans (by abel)
  · simp only [if_neg (show n + -1 ≠ 0 by omega), LinearMap.zero_apply,
      add_zero] at h
    simpa only [if_neg hn, add_zero, sub_eq_add_neg] using h.trans (by abel)

/-- The zero current modes kill the quadratic Casimir. -/
theorem current_quadratic_zero (A : AffineSl2Action V k) (a : Fin 3) :
    mode (V.Y (A.current a)) 0 (quadraticState A) = 0 := by
  simp only [quadraticState, map_sum, map_smul, current_quadratic_term,
    A.current_product_zero, show (0 : ℤ) - 1 = -1 by norm_num,
    zero_ne_one, if_false, add_zero]
  fin_cases a <;>
    norm_num [Fin.sum_univ_three, kappaInv, fabc, map_add, map_smul,
      smul_add, smul_smul] <;> module

/-- The first current product gives the dual-Coxeter shifted level. -/
theorem current_quadratic_one (A : AffineSl2Action V k) (a : Fin 3) :
    mode (V.Y (A.current a)) 1 (quadraticState A) =
      (2 * (k + 2)) • A.current a := by
  simp only [quadraticState, map_sum, map_smul, current_quadratic_term,
    A.current_product_one, show (1 : ℤ) - 1 = 0 by norm_num,
    A.current_product_zero, ite_true, map_smul, (V.creation _).1]
  fin_cases a <;>
    norm_num [Fin.sum_univ_three, kappaInv, kappa, fabc,
      smul_add, smul_smul]
  · module
  · module
  · change (2 : ℂ) • A.current 2 + (2 : ℂ) • A.current 2 +
        (((1 : ℂ) / 2 * (k * 2)) • A.current 2 +
          ((1 : ℂ) / 2 * (k * 2)) • A.current 2) =
        (2 * (k + 2)) • A.current 2
    module

/-- The second current product of the quadratic Casimir vanishes. -/
theorem current_quadratic_two (A : AffineSl2Action V k) (a : Fin 3) :
    mode (V.Y (A.current a)) 2 (quadraticState A) = 0 := by
  simp only [quadraticState, map_sum, map_smul, current_quadratic_term,
    A.current_product_high _ _ 2 (by omega), show (2 : ℤ) - 1 = 1 by norm_num,
    A.current_product_one, map_zero, zero_add,
    show (2 : ℤ) ≠ 1 by omega, if_false, add_zero]
  fin_cases a <;>
    norm_num [Fin.sum_univ_three, kappaInv, kappa, fabc,
      smul_add, smul_smul]

/-- All higher nonnegative current products of the quadratic state vanish. -/
theorem current_quadratic_high (A : AffineSl2Action V k)
    (a : Fin 3) (n : ℤ) (hn : 3 ≤ n) :
    mode (V.Y (A.current a)) n (quadraticState A) = 0 := by
  simp only [quadraticState, map_sum, map_smul, current_quadratic_term,
    A.current_product_high _ _ n (by omega),
    A.current_product_high _ _ (n - 1) (by omega), map_zero, smul_zero,
    Finset.sum_const_zero, zero_add, if_neg (show n ≠ 1 by omega)]

/-- Singular current products of Sugawara are exactly the weight-one pole. -/
theorem current_sugawara (A : AffineSl2Action V k) (hk : k + 2 ≠ 0)
    (a : Fin 3) (n : ℤ) (hn : 0 ≤ n) :
    mode (V.Y (A.current a)) n (sugawaraState A) =
      if n = 1 then A.current a else 0 := by
  rw [sugawaraState, map_smul]
  by_cases h0 : n = 0
  · subst n
    rw [current_quadratic_zero, smul_zero, if_neg (by norm_num : (0 : ℤ) ≠ 1)]
  by_cases h1 : n = 1
  · subst n
    rw [current_quadratic_one, smul_smul, inv_mul_cancel₀ (mul_ne_zero (by norm_num) hk)]
    simp
  by_cases h2 : n = 2
  · subst n
    rw [current_quadratic_two, smul_zero, if_neg (by norm_num : (2 : ℤ) ≠ 1)]
  rw [current_quadratic_high A a n (by omega), smul_zero, if_neg h1]

/-- The full current--Sugawara commutator follows from its two singular products. -/
theorem current_sugawara_comm (A : AffineSl2Action V k)
    (H : TranslationCovariant V) (hk : k + 2 ≠ 0)
    (a : Fin 3) (m n : ℤ) :
    mode (V.Y (A.current a)) m * mode (V.Y (sugawaraState A)) n -
      mode (V.Y (sugawaraState A)) n * mode (V.Y (A.current a)) m =
      (m : ℂ) • mode (V.Y (A.current a)) (m + n - 1) := by
  have h := H.mode_commutator_two (A.current_even a) (sugawaraState_even A)
    (fun j hj => by rw [current_sugawara A hk a j (by omega),
      if_neg (show j ≠ 1 by omega)]) m n
  simpa only [koszul_zero_left, one_smul, current_sugawara A hk a 0 (by omega),
    current_sugawara A hk a 1 (by omega), zero_ne_one, if_false, ite_true,
    map_zero, mode_zero, zero_add] using h

/-- Sugawara acts on a current creation mode by the expected derivative term. -/
theorem sugawara_current_creation (A : AffineSl2Action V k)
    (H : TranslationCovariant V) (hk : k + 2 ≠ 0)
    (a : Fin 3) (n : ℤ) (x : M) :
    mode (V.Y (sugawaraState A)) n (mode (V.Y (A.current a)) (-1) x) =
      mode (V.Y (A.current a)) (-1) (mode (V.Y (sugawaraState A)) n x) +
        mode (V.Y (A.current a)) (n - 2) x := by
  have h := congrArg (fun f : End ℂ M => f x)
    (current_sugawara_comm A H hk a (-1) n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Int.cast_neg, Int.cast_one, neg_one_smul, LinearMap.neg_apply] at h
  rw [show (-1 : ℤ) + n - 1 = n - 2 by omega] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/-- Nonnegative Sugawara modes on a current state, before splitting the index. -/
theorem sugawara_current (A : AffineSl2Action V k)
    (H : TranslationCovariant V) (hk : k + 2 ≠ 0)
    (a : Fin 3) (n : ℤ) (hn : 0 ≤ n) :
    mode (V.Y (sugawaraState A)) n (A.current a) =
      mode (V.Y (A.current a)) (n - 2) V.vacuum := by
  conv_lhs => rw [← (V.creation (A.current a)).1]
  rw [sugawara_current_creation A H hk, (V.creation _).2 n hn, map_zero, zero_add]

private theorem sugawara_quadratic (A : AffineSl2Action V k)
    (H : TranslationCovariant V) (hk : k + 2 ≠ 0)
    (n : ℤ) (hn : 0 ≤ n) :
    mode (V.Y (sugawaraState A)) n (quadraticState A) =
      ∑ b : Fin 3, ∑ c : Fin 3, kappaInv b c •
        (mode (V.Y (A.current b)) (-1)
            (mode (V.Y (A.current c)) (n - 2) V.vacuum) +
          mode (V.Y (A.current b)) (n - 2) (A.current c)) := by
  simp only [quadraticState, map_sum, map_smul, sugawara_current_creation A H hk,
    sugawara_current A H hk _ n hn]

/-- The simple pole of the Sugawara self-OPE is its ambient translation. -/
theorem sugawara_self_zero (A : AffineSl2Action V k)
    (H : TranslationCovariant V) (hk : k + 2 ≠ 0) :
    mode (V.Y (sugawaraState A)) 0 (sugawaraState A) = H.T (sugawaraState A) := by
  have ht (a : Fin 3) (x : M) :
      H.T (mode (V.Y (A.current a)) (-1) x) =
        mode (V.Y (A.current a)) (-1) (H.T x) +
          mode (V.Y (A.current a)) (-2) x := by
    have h := congrArg (fun f : End ℂ M => f x) (H.covariant (A.current a) 0)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, zero_add,
      one_smul, sub_eq_iff_eq_add] at h
    change H.T (V.Y (A.current a) 0 x) =
      V.Y (A.current a) 0 (H.T x) + V.Y (A.current a) 1 x
    rw [h]
    abel
  have hc (a : Fin 3) : H.T (A.current a) =
      mode (V.Y (A.current a)) (-2) V.vacuum := by
    have h := ht a V.vacuum
    simpa only [(V.creation _).1, H.vacuum_zero, map_zero, zero_add] using h
  conv_lhs => arg 2; rw [sugawaraState]
  rw [map_smul, sugawara_quadratic A H hk 0 (by omega)]
  conv_rhs => rw [sugawaraState, map_smul, quadraticState]
  simp only [map_sum, map_smul, ht, hc, show (0 : ℤ) - 2 = -2 by norm_num]

/-- The double pole of the Sugawara self-OPE is twice the Sugawara state. -/
theorem sugawara_self_one (A : AffineSl2Action V k)
    (H : TranslationCovariant V) (hk : k + 2 ≠ 0) :
    mode (V.Y (sugawaraState A)) 1 (sugawaraState A) =
      (2 : ℂ) • sugawaraState A := by
  conv_lhs => arg 2; rw [sugawaraState]
  rw [map_smul, sugawara_quadratic A H hk 1 (by omega)]
  simp only [show (1 : ℤ) - 2 = -1 by norm_num, (V.creation _).1,
    smul_add, Finset.sum_add_distrib]
  change sugawaraState A + sugawaraState A = _
  rw [two_smul]

/-- The third-order pole of the Sugawara self-OPE vanishes. -/
theorem sugawara_self_two (A : AffineSl2Action V k)
    (H : TranslationCovariant V) (hk : k + 2 ≠ 0) :
    mode (V.Y (sugawaraState A)) 2 (sugawaraState A) = 0 := by
  conv_lhs => arg 2; rw [sugawaraState]
  rw [map_smul, sugawara_quadratic A H hk 2 (by omega)]
  simp only [show (2 : ℤ) - 2 = 0 by norm_num, (V.creation _).2 0 (by omega),
    map_zero, zero_add, A.current_product_zero]
  norm_num [Fin.sum_univ_three, kappaInv, fabc]

/-- The fourth-order pole records the Sugawara central charge. -/
theorem sugawara_self_three (A : AffineSl2Action V k)
    (H : TranslationCovariant V) (hk : k + 2 ≠ 0) :
    mode (V.Y (sugawaraState A)) 3 (sugawaraState A) =
      (3 * k / (2 * (k + 2))) • V.vacuum := by
  conv_lhs => arg 2; rw [sugawaraState]
  rw [map_smul, sugawara_quadratic A H hk 3 (by omega)]
  simp only [show (3 : ℤ) - 2 = 1 by norm_num, (V.creation _).2 1 (by omega),
    map_zero, zero_add, A.current_product_one]
  norm_num [Fin.sum_univ_three, kappaInv, kappa, smul_add, smul_smul]
  simp only [← add_smul]
  congr 1
  field_simp
  ring

/-- There are no higher poles in the Sugawara self-OPE. -/
theorem sugawara_self_high (A : AffineSl2Action V k)
    (H : TranslationCovariant V) (hk : k + 2 ≠ 0)
    (n : ℤ) (hn : 4 ≤ n) :
    mode (V.Y (sugawaraState A)) n (sugawaraState A) = 0 := by
  conv_lhs => arg 2; rw [sugawaraState]
  rw [map_smul, sugawara_quadratic A H hk n (by omega)]
  simp only [(V.creation _).2 (n - 2) (by omega), map_zero,
    A.current_product_high _ _ (n - 2) (by omega), add_zero,
    smul_zero, Finset.sum_const_zero]

/-- Every noncritical affine action has the full Sugawara Virasoro relation. -/
theorem sugawara_virasoro (A : AffineSl2Action V k)
    (H : TranslationCovariant V) (hk : k + 2 ≠ 0) (m n : ℤ) :
    ⁅mode (V.Y (sugawaraState A)) (m + 1), mode (V.Y (sugawaraState A)) (n + 1)⁆ =
      ((m : ℂ) - n) • mode (V.Y (sugawaraState A)) (m + n + 1) +
      (if m + n = 0 then
        (((m : ℂ) ^ 3 - m) / 12 * (3 * k / (k + 2))) • (1 : End ℂ M) else 0) := by
  let f : ℕ → End ℂ M := fun j =>
    gBinom (m + 1) j • mode (V.Y (mode (V.Y (sugawaraState A)) j
      (sugawaraState A))) (m + 1 + (n + 1) - j)
  have h0 : f 0 = (-((m + n + 2 : ℤ) : ℂ)) •
      mode (V.Y (sugawaraState A)) (m + n + 1) := by
    dsimp only [f]
    rw [Nat.cast_zero, gBinom_zero, one_smul, sub_zero,
      show m + 1 + (n + 1) = m + n + 2 by ring,
      sugawara_self_zero A H hk, translation_mode H,
      show m + n + 2 - 1 = m + n + 1 by ring]
    rw [← Int.cast_smul_eq_zsmul ℂ (-(m + n + 2) : ℤ), Int.cast_neg]
  have h1 : f 1 = ((m + 1 : ℤ) : ℂ) •
      ((2 : ℂ) • mode (V.Y (sugawaraState A)) (m + n + 1)) := by
    dsimp only [f]
    rw [Nat.cast_one, Vir.gBinom_one, sugawara_self_one A H hk, map_smul, mode_smul,
      show m + 1 + (n + 1) - 1 = m + n + 1 by ring]
  have h2 : f 2 = 0 := by
    dsimp only [f]
    rw [Nat.cast_ofNat, sugawara_self_two A H hk, map_zero, mode_zero, smul_zero]
  have h3 : f 3 = if m + n = 0 then
      (((m : ℂ) ^ 3 - m) / 12 * (3 * k / (k + 2))) • (1 : End ℂ M) else 0 := by
    dsimp only [f]
    rw [Nat.cast_ofNat, Vir.gBinom_three, sugawara_self_three A H hk,
      map_smul, mode_smul, V.vacuum_Y,
      show m + 1 + (n + 1) - 3 = m + n - 1 by ring]
    by_cases hmn : m + n = 0
    · rw [if_pos hmn]
      have hone : mode (1 : FormalDist (End ℂ M)) (m + n - 1) = 1 := by
        rw [mode_apply, show -(m + n - 1) - 1 = -(m + n) by ring,
          hmn, neg_zero, FormalDist.one_apply, if_pos rfl]
      rw [hone, smul_smul]
      congr 1
      push_cast
      field_simp
      ring
    · rw [if_neg hmn]
      have hone : mode (1 : FormalDist (End ℂ M)) (m + n - 1) = 0 := by
        rw [mode_apply, FormalDist.one_apply,
          if_neg (by omega : ¬ -(m + n - 1) - 1 = 0)]
      rw [hone, smul_zero, smul_zero]
  have h := H.mode_commutator_bound (sugawaraState_even A) (sugawaraState_even A) 4
    (fun j hj => sugawara_self_high A H hk j (by omega)) (m + 1) (n + 1)
  simp only [koszul_zero_left, one_smul] at h
  rw [LieRing.of_associative_ring_bracket, h]
  change (∑ j ∈ Finset.range 4, f j) = _
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1, h2, h3, add_zero]
  congr 1
  rw [smul_smul, ← add_smul]
  congr 1
  push_cast
  ring

/-- A coset state has no singular products with the quadratic Sugawara state. -/
theorem coset_mode_sugawara (A : AffineSl2Action V k)
    (H : TranslationCovariant V) {x : M} (hx : x ∈ cosetSubspace A)
    (n : ℤ) (hn : 0 ≤ n) :
    mode (V.Y x) n (sugawaraState A) = 0 := by
  have hc (b : Fin 3) : mode (V.Y x) n (A.current b) = 0 := by
    have h := congrArg (fun f : End ℂ M => f V.vacuum)
      (current_mode_coset_mode_commute A H hx b (-1) n)
    simpa only [Module.End.mul_apply, (V.creation x).2 n hn,
      (V.creation (A.current b)).1, map_zero] using h.symm
  rw [sugawaraState, quadraticState, map_smul]
  suffices h : (∑ b : Fin 3, ∑ c : Fin 3,
      kappaInv b c • mode (V.Y x) n
        (mode (V.Y (A.current b)) (-1) (A.current c))) = 0 by
    simpa only [map_sum, map_smul, h, smul_zero]
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro c hc'
  have h := congrArg (fun f : End ℂ M => f (A.current c))
    (current_mode_coset_mode_commute A H hx b (-1) n)
  simp only [Module.End.mul_apply, hc c, map_zero] at h
  rw [← h, smul_zero]

/-- Every nonnegative Sugawara mode vanishes on the commutant. In particular,
the diagonal Sugawara contribution to both translation and grading is zero. -/
theorem sugawara_mode_coset (A : AffineSl2Action V k)
    (H : TranslationCovariant V) {x : M} (hx : x ∈ cosetSubspace A)
    (n : ℤ) (hn : 0 ≤ n) :
    mode (V.Y (sugawaraState A)) n x = 0 := by
  have hom : ∀ {p : ZMod 2} {w : M}, w ∈ cosetSubspace A → w ∈ V.parity p →
      mode (V.Y (sugawaraState A)) n w = 0 := by
    intro p w hw hp
    have h := H.mode_commutator_bound hp (sugawaraState_even A) 0
      (fun j _ => coset_mode_sugawara A H hw j (Int.natCast_nonneg j)) (-1) n
    simp only [koszul_zero_right, one_smul, Finset.range_zero,
      Finset.sum_empty, sub_eq_zero] at h
    have hv := congrArg (fun f : End ℂ M => f V.vacuum) h
    simpa only [Module.End.mul_apply, (V.creation _).2 n hn,
      (V.creation _).1, map_zero] using hv.symm
  obtain ⟨x₀, hx₀, hp₀, x₁, hx₁, hp₁, rfl⟩ := exists_parity_decomp_coset A hx
  rw [map_add, hom hx₀ hp₀, hom hx₁ hp₁, zero_add]

/-- Every Sugawara mode commutes with every field mode of a coset state. -/
theorem sugawara_mode_coset_mode_commute (A : AffineSl2Action V k)
    (H : TranslationCovariant V) {x : M} (hx : x ∈ cosetSubspace A)
    (m n : ℤ) :
    mode (V.Y (sugawaraState A)) m * mode (V.Y x) n =
      mode (V.Y x) n * mode (V.Y (sugawaraState A)) m := by
  have hom : ∀ {p : ZMod 2} {w : M}, w ∈ cosetSubspace A → w ∈ V.parity p →
      mode (V.Y (sugawaraState A)) m * mode (V.Y w) n =
        mode (V.Y w) n * mode (V.Y (sugawaraState A)) m := by
    intro p w hw hp
    have h := H.mode_commutator_bound (sugawaraState_even A) hp 0
      (fun j _ => sugawara_mode_coset A H hw j (Int.natCast_nonneg j)) m n
    simpa only [koszul_zero_left, one_smul, Finset.range_zero,
      Finset.sum_empty, sub_eq_zero] using h
  obtain ⟨x₀, hx₀, hp₀, x₁, hx₁, hp₁, rfl⟩ := exists_parity_decomp_coset A hx
  simp only [map_add, mode_add, mul_add, add_mul]
  rw [hom hx₀ hp₀, hom hx₁ hp₁]

/-- The abstract quadratic state agrees with the existing universal
Sugawara conformal vector. -/
theorem sugawaraState_affineAction (k : ℂ) (hk : k + 2 ≠ 0) :
    sugawaraState (affineAction k hk) = omegaA k := by
  rw [Vir.omegaA_creation_form]
  unfold sugawaraState quadraticState
  change (2 * (k + 2))⁻¹ •
      (∑ b : Fin 3, ∑ c : Fin 3, kappaInv b c •
        mode (YA k hk (J k b (-1) (vacuumA k))) (-1)
          (J k c (-1) (vacuumA k))) = _
  simp only [Vir.YA_current_state, Jfield_mode]
  rfl

section Tensor
variable {N : Type*} [AddCommGroup N] [Module ℂ N]
variable {W : SuperVertexAlgebra N} {l : ℂ}

/-- The sum of the two factor Sugawara states in the tensor vertex algebra. -/
noncomputable def tensorSugawaraState (A : AffineSl2Action V k)
    (B : AffineSl2Action W l) : M ⊗[ℂ] N :=
  sugawaraState A ⊗ₜ[ℂ] W.vacuum + V.vacuum ⊗ₜ[ℂ] sugawaraState B

/-- The diagonal currents see the two-factor conformal vector as weight one. -/
theorem current_tensorSugawara (A : AffineSl2Action V k)
    (B : AffineSl2Action W l) (hk : k + 2 ≠ 0) (hl : l + 2 ≠ 0)
    (a : Fin 3) (n : ℤ) (hn : 0 ≤ n) :
    mode (TensorVA.tenY V W (tensorCurrentState A B a)) n (tensorSugawaraState A B) =
      if n = 1 then tensorCurrentState A B a else 0 := by
  rw [tensorSugawaraState, map_add, tensorCurrentMode_tmul, tensorCurrentMode_tmul,
    current_sugawara A hk a n hn, current_sugawara B hl a n hn,
    (V.creation _).2 n hn, (W.creation _).2 n hn,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero, zero_add]
  by_cases h : n = 1
  · rw [if_pos h, if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h, if_neg h,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add]

/-- The two-factor Sugawara state minus diagonal Sugawara is a genuine
commutant state. All current-annihilation obligations are proved. -/
def tensorCosetConformalData (A : AffineSl2Action V k)
    (B : AffineSl2Action W l) (hk : k + 2 ≠ 0) (hl : l + 2 ≠ 0)
    (hkl : k + l + 2 ≠ 0)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) :
    CosetConformalData (tensorAffineAction A B hV hW hg)
      (tensorSugawaraState A B) (sugawaraState (tensorAffineAction A B hV hW hg)) := by
  apply CosetConformalData.of_current_modes
  intro a n hn
  rw [current_sugawara _ hkl a n hn]
  exact current_tensorSugawara A B hk hl a n hn

/-- The normalized Sugawara difference as an element of the commutant. -/
noncomputable def tensorCosetConformalState (A : AffineSl2Action V k)
    (B : AffineSl2Action W l) (hk : k + 2 ≠ 0) (hl : l + 2 ≠ 0)
    (hkl : k + l + 2 ≠ 0)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) :
    cosetSubspace (tensorAffineAction A B hV hW hg) :=
  cosetConformalState _ _ _ (tensorCosetConformalData A B hk hl hkl hV hW hg)

/-- The conformal difference has weight two in the ambient tensor algebra. -/
theorem tensorCosetConformalState_weight (A : AffineSl2Action V k)
    (B : AffineSl2Action W l) (hk : k + 2 ≠ 0) (hl : l + 2 ≠ 0)
    (hkl : k + l + 2 ≠ 0)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) :
    (tensorCosetConformalState A B hk hl hkl hV hW hg : M ⊗[ℂ] N) ∈
      (TensorVA.tensorSVA V W hV hW hg).grading 2 := by
  apply Submodule.sub_mem
  · apply Submodule.add_mem
    · simpa only [add_zero] using tmul_mem_tenGrading_add V W
        (sugawaraState_weight A) W.vacuum_mem
    · simpa only [zero_add] using tmul_mem_tenGrading_add V W
        V.vacuum_mem (sugawaraState_weight B)
  · exact sugawaraState_weight _

/-- The conformal difference is even in the ambient tensor algebra. -/
theorem tensorCosetConformalState_even (A : AffineSl2Action V k)
    (B : AffineSl2Action W l) (hk : k + 2 ≠ 0) (hl : l + 2 ≠ 0)
    (hkl : k + l + 2 ≠ 0)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) :
    (tensorCosetConformalState A B hk hl hkl hV hW hg : M ⊗[ℂ] N) ∈
      (TensorVA.tensorSVA V W hV hW hg).parity 0 := by
  apply Submodule.sub_mem
  · apply Submodule.add_mem
    · exact TensorVA.tmul_mem_tenParity V W (sugawaraState_even A) W.vacuum_parity
    · exact TensorVA.tmul_mem_tenParity V W V.vacuum_parity (sugawaraState_even B)
  · exact sugawaraState_even _

end Tensor

end VOA.Sl2CosetConcrete
