/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroMinimalClassicalFreeness
import VOA.Filtered.InfiniteLiPoisson
import VOA.Commutative.InfiniteJetPoissonUniqueness
import VOA.Commutative.PoissonVertexEquiv

/-!
# The Poisson vertex structure of `gr^{Li} M(2, 2m+3)`

For the Li filtration the λ-bracket of two degree-zero classes is
`{a_λ b} = [a_(0) b]` in degree zero (all positive products drop in degree).  For the Virasoro
generator, `ω_(0) ω = L_{-1} ω = L_{-3}|0⟩ ∈ C₂`, so **every** product of `[ω]` with itself
vanishes in `gr^{Li}`.  By the generator test (`poissonVertexHomOfBaseGenerators`), the
canonical isomorphism of `VirasoroClassicalFreeness.classicallyFree` is therefore a Poisson
vertex isomorphism from the arc algebra with the **zero** λ-bracket and the jet derivation:

* `zeroPVA`: the Poisson vertex algebra with translation `T` and all products zero;
* `arcPoissonEquiv m : Equiv (arcPVA m) (liPoissonVertexAlgebra L(c_{2,2m+3},0))`;
* `liPoissonVertexAlgebra_mode_eq_zero`: all products in `gr^{Li} M(2,2m+3)` vanish.

This is the Virasoro counterpart of `AffineSl2BoundaryClassicalFreeness.arcPoissonEquiv`.
-/

namespace VOA

/-- The Poisson vertex algebra with prescribed translation and all products zero. -/
noncomputable def zeroPVA (A : Type*) [CommRing A] [Algebra ℂ A] (T : Derivation ℂ A A) :
    PoissonVertexAlgebra A where
  translation := T
  mode := 0
  locality _ _ := ⟨0, fun _ _ => rfl⟩
  translation_left_zero _ _ := rfl
  translation_left_succ _ _ _ := by simp
  translation_mode _ _ _ := by simp
  leibniz _ _ _ _ := by simp
  skew _ _ _ := by simp
  jacobi _ _ _ _ _ := by simp

namespace VirasoroClassicalFreeness

open VOA.VirModule VOA.VirSimple VOA.VirasoroLi

noncomputable section

variable (c : ℂ)

/-- `ω_(0) ω = L_{-3}|0⟩` in the universal Virasoro VOA. -/
theorem smul_omega_zero_omega :
    (virasoroVOA c).smul (omegaVir c) 0 (omegaVir c) = negWordVir c [1] := by
  rw [LeeYang.smul_omegaVir, omegaVir, LeeYang.Lop_apply_comm, Lop_vacuum c (by norm_num)]
  simp only [map_zero, zero_add]
  norm_num
  rfl

/-- The `(0)`-product of `[ω]` with itself lies in `C₂` of the simple quotient. -/
theorem poissonBracket_omegaBar_mem_O₂ :
    poissonBracket (virasoroSimple c) (omegaBar c) (omegaBar c) ∈ O₂ (virasoroSimple c) := by
  change (virasoroSimple c).smul ((maxIdealVir c).mkQ (omegaVir c)) 0
    ((maxIdealVir c).mkQ (omegaVir c)) ∈ _
  rw [virasoroSimple_mkQ_smul, smul_omega_zero_omega, ← liFiltration_one_eq_O₂]
  exact mkQ_negWordVir_mem_liFiltration c 1 [1] (by simp)

/-- **All products of `[ω]` with itself vanish in `gr^{Li} L(c,0)`**, for every `c`. -/
theorem mode_x_x (n : ℕ) :
    (liPoissonVertexAlgebra (virasoroSimple c)).mode n (x c 0) (x c 0) = 0 := by
  cases n with
  | zero =>
      change liAssociatedGradedMode (virasoroSimple c) 0 _ _ = 0
      rw [liDegreeZeroClass_mode_zero _ 2 2 (by norm_num)]
      exact liDegreeZeroClass_eq_zero_of_mem_O₂ _ _ _ (poissonBracket_omegaBar_mem_O₂ c)
  | succ n =>
      exact liDegreeZeroClass_mode_succ _ 2 2 n _ _

/-- The arc Poisson vertex algebra of `ℂ[T]/(T^{m+1})`: jet derivation, zero λ-bracket. -/
abbrev arcPVA (m : ℕ) : PoissonVertexAlgebra (InfiniteJet.PresentedJet (relIdeal m)) :=
  zeroPVA _ (InfiniteJet.translation (relIdeal m))

/-- The canonical map is a Poisson vertex homomorphism from the zero-bracket arc PVA. -/
def arcLiPoissonHom (m : ℕ) (hJ : TwoSeriesCharacter.HasJetRelations c m) :
    PoissonVertexAlgebra.Hom (arcPVA m) (liPoissonVertexAlgebra (virasoroSimple c)) :=
  InfiniteJet.poissonVertexHomOfBaseGenerators (relIdeal m) (arcPVA m)
    (liPoissonVertexAlgebra (virasoroSimple c))
    (liInfinitePresentedJetMap (virasoroSimple c) (x c) (relIdeal m) (relIdeal_le_li c m hJ))
    rfl (fun a => jetMap_translation c m hJ a)
    (fun i j n => by
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi hj
      change _ = (liPoissonVertexAlgebra (virasoroSimple c)).mode n _ _
      rw [liInfinitePresentedJetMap_generator_zero, mode_x_x]
      exact map_zero _)

/-- **Poisson vertex classical freeness of `M(2, 2m+3)`.**  The canonical map is an
isomorphism of Poisson vertex algebras `J_∞(ℂ[T]/(T^{m+1})) ≅ gr^{Li} L(c_{2,2m+3},0)`, the
source carrying the jet derivation and the (forced) zero λ-bracket. -/
def arcPoissonEquiv (m : ℕ) :
    PoissonVertexAlgebra.Equiv (arcPVA m) (liPoissonVertexAlgebra (virasoroSimple (cm m))) :=
  PoissonVertexAlgebra.Equiv.ofBijective (arcLiPoissonHom (cm m) m (hasJetRelations m))
    (classicallyFree m)

/-- Consequently every product of `gr^{Li} M(2,2m+3)` vanishes. -/
theorem liPoissonVertexAlgebra_mode_eq_zero (m n : ℕ)
    (a b : liAssociatedGraded (virasoroSimple (cm m))) :
    (liPoissonVertexAlgebra (virasoroSimple (cm m))).mode n a b = 0 := by
  obtain ⟨a', rfl⟩ := (arcPoissonEquiv m).toAlgEquiv.surjective a
  obtain ⟨b', rfl⟩ := (arcPoissonEquiv m).toAlgEquiv.surjective b
  rw [← (arcPoissonEquiv m).map_mode]
  change (arcPoissonEquiv m).toAlgEquiv 0 = 0
  exact map_zero _

end

end VirasoroClassicalFreeness
end VOA
