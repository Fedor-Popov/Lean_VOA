/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteTranslation

/-!
# Normal ordering for translation-covariant super vertex algebras

The negative first state product is identified with the actual normal-ordered field
using super locality, translation covariance and creation. This supplies a mode-algebra
expansion without assuming any BRST identity.
-/

namespace VOA.Sl2SemiInfinite.TranslationCovariant
open Module (End)
open scoped BigOperators
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {V : SuperVertexAlgebra 𝒱}

/-- Creation and translation uniquely determine the vacuum coefficients of a field. -/
theorem vacuum_recursion_eqε (H : TranslationCovariant V) (B : FormalDist (End ℂ 𝒱)) (w : 𝒱)
    (hneg : ∀ s : ℤ, s < 0 → B s V.vacuum = 0)
    (hbase : B 0 V.vacuum = w)
    (hrec : ∀ s : ℤ, H.T (B s V.vacuum) = (s + 1) • B (s + 1) V.vacuum)
    (s : ℤ) : B s V.vacuum = (V.Y w) s V.vacuum := by
  by_cases hs : s < 0
  · rw [hneg s hs, V.Y_apply_vacuum_eq_zero w hs]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, s = (j : ℤ) := ⟨s.toNat, by omega⟩
    clear hs
    induction j with
    | zero =>
        rw [Nat.cast_zero, hbase]
        exact (V.Y_apply_vacuum_zero _).symm
    | succ i ih =>
        have hYrec : H.T ((V.Y w) (i : ℤ) V.vacuum)
            = ((i : ℤ) + 1) • (V.Y w) ((i : ℤ) + 1) V.vacuum := by
          have h := DFunLike.congr_fun (comm_Ycoeff H w (i : ℤ)) V.vacuum
          rw [LinearMap.smul_apply, LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
            Module.End.mul_apply, Module.End.mul_apply, H.vacuum_zero, map_zero,
            sub_zero] at h
          exact h
        have key : ((i : ℤ) + 1) • B ((i : ℤ) + 1) V.vacuum
            = ((i : ℤ) + 1) • (V.Y w) ((i : ℤ) + 1) V.vacuum := by
          rw [← hrec, ih, hYrec]
        have hc : (((i : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
        rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1),
          ← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1)] at key
        rw [Nat.cast_succ]
        exact smul_right_injective 𝒱 hc key


/-- The field of a negative first product is the super normal-ordered product. -/
theorem normal_product (H : TranslationCovariant V) {p q : ZMod 2}
    {u v : 𝒱} (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) :
    V.Y (mode (V.Y u) (-1) v) = nprodε (koszul p q)
      (TensorVA.isField_superY V u) (TensorVA.isField_superY V v) := by
  let ha := TensorVA.isField_superY V u
  let hb := TensorVA.isField_superY V v
  symm
  refine V.goddard_uniquenessε _ (mode (V.Y u) (-1) v)
    (V.smul_mem_parity hu hv (-1)) (fun r b hb' => ?_) (fun s => ?_)
  · have h := dong_negε (koszul_mul_self p q) ha hb
      (V.locality u hu v hv) (V.locality u hu b hb') (V.locality v hv b hb')
    rwa [← koszul_add_left] at h
  · apply vacuum_recursion_eqε H _ (mode (V.Y u) (-1) v)
    · intro s hs
      exact nprodε_vacuum_neg_gen (koszul p q) ha hb V.vacuum
        (fun t ht => V.Y_apply_vacuum_eq_zero u ht)
        (fun t ht => V.Y_apply_vacuum_eq_zero v ht) hs
    · rw [nprodε_vacuum_base_gen (koszul p q) ha hb V.vacuum
        (fun t ht => V.Y_apply_vacuum_eq_zero u ht)
        (fun t ht => V.Y_apply_vacuum_eq_zero v ht), V.Y_apply_vacuum_zero]
      rfl
    · intro t
      have hcov := DCovariant.nprodε (koszul p q) ha hb
        (H.covariant u) (H.covariant v)
      have ht := congrArg (fun f : End ℂ 𝒱 => f V.vacuum) (hcov t)
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, H.vacuum_zero,
        map_zero, sub_zero, LinearMap.smul_apply] using ht

/-- All modes of a negative first product, as the locally finite normal-ordering sum. -/
theorem normal_product_mode (H : TranslationCovariant V) {p q : ZMod 2}
    {u v : 𝒱} (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) (n : ℤ) (x : 𝒱) :
    mode (V.Y (mode (V.Y u) (-1) v)) n x =
      ∑ᶠ m : ℤ, normalOrderedε (koszul p q) (V.Y u) (V.Y v) m (-n - 1 - m) x := by
  rw [normal_product H hu hv, mode_apply, nprodε_apply]

end VOA.Sl2SemiInfinite.TranslationCovariant
