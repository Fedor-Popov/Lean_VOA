import VOA.Huang.NgSchauenburgGeneralized
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.ZMod.Basic

/-!
# Congruence contracts and the scalar descent step

Only the elementary matrix descent step is proved here. The NS and DLN
theorems are named Props, retaining the distinction between scalar action
and identity action on a principal congruence subgroup.
-/

noncomputable section
universe v u

namespace VOA.Huang.NgSchauenburg

open CategoryTheory MonoidalCategory Limits
open scoped MatrixGroups

/-- The elementary algebra in the center-to-projective descent: if a tensor
product of two matrices is the identity, each factor is a nonzero scalar.
No congruence or categorical premise is hidden in this statement. -/
theorem scalar_of_kronecker_eq_one {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (h : Matrix.kronecker A B = 1) :
    ∃ c : ℂ, c ≠ 0 ∧ A = c • (1 : Matrix ι ι ℂ) := by
  classical
  let a : ι := Classical.choice inferInstance
  let b : κ := Classical.choice inferInstance
  have haa : A a a * B b b = 1 := by
    simpa [Matrix.kronecker_apply] using congrFun (congrFun h (a, b)) (a, b)
  have hb : B b b ≠ 0 := by
    intro hb
    simp [hb] at haa
  refine ⟨(B b b)⁻¹, inv_ne_zero hb, ?_⟩
  ext i j
  apply mul_right_cancel₀ hb
  have hij := congrFun (congrFun h (i, b)) (j, b)
  by_cases he : i = j
  · subst j
    simpa [Matrix.kronecker_apply, hb] using hij
  · simpa [Matrix.kronecker_apply, Matrix.one_apply, he, hb] using hij

/-- Entrywise reduction to the identity, i.e. membership in `Γ(N)`.
Positive levels are imposed by each congruence theorem, not by this predicate. -/
def InPrincipalCongruence (N : ℕ) (γ : SL(2, ℤ)) : Prop :=
  ∀ i j : Fin 2, (γ i j : ZMod N) = (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) i j

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def KernelContainsGamma (ρ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W)) (N : ℕ) : Prop :=
  ∀ γ, InPrincipalCongruence N γ → ρ γ = 1

def ProjectiveKernelContainsGamma (ρ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W)) (N : ℕ) : Prop :=
  ∀ γ, InPrincipalCongruence N γ → ∃ c : ℂˣ, ∀ w, ρ γ w = (c : ℂ) • w

/-- DLN Theorem 2.3, a useful containment form. This is unproved here.
It upgrades projective congruence of a genuine linear lift to genuine congruence. -/
def DLNLiftingTheorem (ρ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W)) [FiniteDimensional ℂ W] : Prop :=
  ∀ N : ℕ, 0 < N → ProjectiveKernelContainsGamma ρ N → KernelContainsGamma ρ (12 * N)

/-- The normal-kernel exact-level lemma (DLN Appendix A), to be proved.
Finiteness of the order is part of the conclusion. -/
def ExactLevelTheorem (ρ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W)) : Prop :=
  (∃ N : ℕ, 0 < N ∧ KernelContainsGamma ρ N) →
    0 < orderOf (ρ ModularGroup.T) ∧ KernelContainsGamma ρ (orderOf (ρ ModularGroup.T))

/-- Assembly of the two independent group-theoretic inputs. -/
theorem congruenceAtOrder_of_projective [FiniteDimensional ℂ W]
    (ρ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W)) (hlift : DLNLiftingTheorem ρ)
    (hlevel : ExactLevelTheorem ρ) {N : ℕ} (hN : 0 < N)
    (hprojective : ProjectiveKernelContainsGamma ρ N) :
    0 < orderOf (ρ ModularGroup.T) ∧ KernelContainsGamma ρ (orderOf (ρ ModularGroup.T)) :=
  hlevel ⟨12 * N, Nat.mul_pos (by decide) hN, hlift N hN hprojective⟩

section Categorical

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- A genuine representation lifting the categorical projective S,T action.
Both scalar normalizations must be nonzero. -/
def IsModularRepresentation (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ))) : Prop :=
  ∃ a b : ℂˣ,
    (∀ z i, ρ ModularGroup.S z i = (a : ℂ) * ∑ j, categoricalS F i j * z j) ∧
    (∀ z i, ρ ModularGroup.T z i = (b : ℂ) * M.twistScalar i * z i)

/-- NS Theorem 6.8: the projective kernel is congruence of exactly the FS level.
The universal quantification is over genuine lifts of the categorical action. -/
def ProjectiveCongruenceTheorem (F : SphericalFusion C) (M : Modular F) : Prop :=
  0 < fsExponent F ∧ ∀ ρ, IsModularRepresentation F M ρ →
    ProjectiveKernelContainsGamma ρ (fsExponent F) ∧
      ∀ N : ℕ, 0 < N → ProjectiveKernelContainsGamma ρ N → fsExponent F ≤ N

end Categorical

end VOA.Huang.NgSchauenburg
