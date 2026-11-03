import VOA.Commutative.PoissonVertexAlgebra
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Tactic

/-!
# Verifying Poisson vertex homomorphisms on differential generators

The compatibility predicate compares independently supplied mode operations. Its
closure laws reduce genuine homomorphism obligations to algebra generators.
-/
namespace VOA.PoissonVertexAlgebra
open scoped BigOperators
noncomputable section
variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

/-- An algebra map preserving translation and every nonnegative product. -/
structure Hom (P : VOA.PoissonVertexAlgebra A) (Q : VOA.PoissonVertexAlgebra B) where
  toAlgHom : A →ₐ[ℂ] B
  map_translation : ∀ x, toAlgHom (P.translation x) = Q.translation (toAlgHom x)
  map_mode : ∀ n x y, toAlgHom (P.mode n x y) = Q.mode n (toAlgHom x) (toAlgHom y)

/-- Compatibility for one pair, simultaneously in every nonnegative mode. -/
def Compatible (P : VOA.PoissonVertexAlgebra A) (Q : VOA.PoissonVertexAlgebra B)
    (F : A →ₐ[ℂ] B) (x y : A) : Prop :=
  ∀ n, F (P.mode n x y) = Q.mode n (F x) (F y)

variable (P : VOA.PoissonVertexAlgebra A) (Q : VOA.PoissonVertexAlgebra B)
    (F : A →ₐ[ℂ] B)

@[simp] theorem mode_one_right (n : ℕ) (x : A) : P.mode n x 1 = 0 := by
  have h := P.leibniz n x 1 1
  simp only [one_mul, mul_one] at h
  have hh : P.mode n x 1 + P.mode n x 1 = P.mode n x 1 + 0 := by
    simpa only [add_zero] using h.symm
  exact add_left_cancel hh

@[simp] theorem mode_algebraMap_right (n : ℕ) (x : A) (c : ℂ) :
    P.mode n x (algebraMap ℂ A c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, mode_one_right, smul_zero]

theorem compatible_const_right (x : A) (c : ℂ) :
    Compatible P Q F x (algebraMap ℂ A c) := by
  intro n
  rw [mode_algebraMap_right, map_zero, F.commutes, mode_algebraMap_right]

theorem compatible_add_right {x y z : A} (hy : Compatible P Q F x y)
    (hz : Compatible P Q F x z) : Compatible P Q F x (y+z) := by
  intro n
  simp only [map_add, hy n, hz n]

theorem compatible_smul_right {x y : A} (hy : Compatible P Q F x y) (c : ℂ) :
    Compatible P Q F x (c • y) := by
  intro n
  simp only [map_smul, hy n]

theorem compatible_smul_left {x y : A} (hx : Compatible P Q F x y) (c : ℂ) :
    Compatible P Q F (c • x) y := by
  intro n
  simp only [map_smul, LinearMap.smul_apply, hx n]

theorem compatible_mul_right {x y z : A} (hy : Compatible P Q F x y)
    (hz : Compatible P Q F x z) : Compatible P Q F x (y*z) := by
  intro n
  rw [P.leibniz, map_add, map_mul, map_mul, hy n, hz n, map_mul, Q.leibniz]

theorem compatible_translate_left (hT : ∀ x, F (P.translation x) = Q.translation (F x))
    {x y : A} (h : Compatible P Q F x y) : Compatible P Q F (P.translation x) y := by
  intro n
  cases n with
  | zero => rw [P.translation_left_zero, map_zero, hT, Q.translation_left_zero]
  | succ n => rw [P.translation_left_succ, map_smul, h n, hT, Q.translation_left_succ]

theorem compatible_translate_right (hT : ∀ x, F (P.translation x) = Q.translation (F x))
    {x y : A} (h : Compatible P Q F x y) : Compatible P Q F x (P.translation y) := by
  intro n
  have hp := congrArg F (P.translation_mode n x y)
  rw [map_add, hT, h n, compatible_translate_left P Q F hT h n, hT] at hp
  have hq := Q.translation_mode n (F x) (F y)
  rw [hT y]
  exact add_left_cancel (hp.symm.trans hq)

theorem map_translation_pow (hT : ∀ x, F (P.translation x) = Q.translation (F x))
    (j : ℕ) (x : A) :
    F ((P.translation.toLinearMap^j) x) = (Q.translation.toLinearMap^j) (F x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [pow_succ', Module.End.mul_apply]
      change F (P.translation ((P.translation.toLinearMap ^ j) x)) =
        Q.translation ((Q.translation.toLinearMap ^ j) (F x))
      rw [hT, ih]

/-- Skew-symmetry transfers compatibility to the reversed pair. -/
theorem compatible_swap (hT : ∀ x, F (P.translation x) = Q.translation (F x))
    {x y : A} (h : Compatible P Q F x y) : Compatible P Q F y x := by
  intro n
  rw [P.skew, Q.skew]
  have hfin : (Function.support fun j : ℕ => (j.factorial : ℂ)⁻¹ •
      (-1 : ℂ)^(n+j+1) • ((P.translation.toLinearMap^j) (P.mode (n+j) x y))).Finite := by
    obtain ⟨B,hB⟩ := P.locality x y
    apply (Set.finite_Iio B).subset
    intro j hj
    change j < B
    by_contra hlt
    have hm := hB (n+j) (by omega)
    simp only [Function.mem_support] at hj
    apply hj
    rw [hm, map_zero, smul_zero, smul_zero]
  have hmap := F.toLinearMap.toAddMonoidHom.map_finsum hfin
  change F (∑ᶠ j : ℕ, _) = _ at hmap
  rw [hmap]
  apply finsum_congr
  intro j
  change F ((j.factorial : ℂ)⁻¹ • (-1 : ℂ)^(n+j+1) •
    ((P.translation.toLinearMap^j) (P.mode (n+j) x y))) = _
  rw [map_smul, map_smul, map_translation_pow P Q F hT, h (n+j)]

end
end VOA.PoissonVertexAlgebra
