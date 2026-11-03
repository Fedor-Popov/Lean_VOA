/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Vector-valued symmetric polynomial coefficients

A finitely supported family of vectors indexed by monomials, invariant under
permutation of the variables, is exactly a tensor of the vector space with the
scalar symmetric-polynomial algebra. A basis makes this elementary linear algebra:
each basis coordinate is a scalar symmetric polynomial. No averaging is used.
-/

namespace VOA.SymmetricPolynomialTensorCoefficients

open Module
open scoped TensorProduct

noncomputable section

variable {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W]

abbrev Exponent (d : ℕ) := Fin d →₀ ℕ

/-- A vector-valued finite polynomial family fixed by all variable permutations. -/
def invariantCoefficients (d : ℕ) : Submodule K (Exponent d →₀ W) where
  carrier := {c | ∀ (h : Equiv.Perm (Fin d)) a, c (a.mapDomain h) = c a}
  zero_mem' := fun _ _ => rfl
  add_mem' := by intro c e hc he h a; simp only [Finsupp.add_apply, hc h a, he h a]
  smul_mem' := by intro k c hc h a; simp only [Finsupp.smul_apply, hc h a]

/-- Scalar symmetry can be checked on coefficients at permuted monomials. -/
theorem isSymmetric_iff_coefficients {d : ℕ} (p : MvPolynomial (Fin d) K) :
    p.IsSymmetric ↔ ∀ (h : Equiv.Perm (Fin d)) a,
      p.coeff (a.mapDomain h) = p.coeff a := by
  constructor
  · intro hp h a
    have hc := congrArg (MvPolynomial.coeff (a.mapDomain h)) (hp h)
    rw [MvPolynomial.coeff_rename_mapDomain h h.injective] at hc
    exact hc.symm
  · intro hp h
    apply MvPolynomial.ext
    intro a
    obtain ⟨a, rfl⟩ := Finsupp.mapDomain_surjective h.surjective a
    rw [MvPolynomial.coeff_rename_mapDomain h h.injective, hp h a]

/-- Change vector coordinates to a chosen basis and transpose the two finite
coefficient indices. -/
def transpose (b : Basis ι K W) (d : ℕ) :
    (Exponent d →₀ W) ≃ₗ[K] ι →₀ MvPolynomial (Fin d) K :=
  (Finsupp.mapRange.linearEquiv b.repr).trans
    ((Finsupp.curryLinearEquiv K).symm.trans
      ((Finsupp.domLCongr (Equiv.prodComm (Exponent d) ι)).trans
        ((Finsupp.curryLinearEquiv K).trans
          (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv K).symm))))

@[simp] theorem transpose_coeff (b : Basis ι K W) (d : ℕ)
    (c : Exponent d →₀ W) (i : ι) (a : Exponent d) :
    MvPolynomial.coeff a (transpose b d c i) = b.repr (c a) i := by
  rfl

/-- Vector invariance is equivalent to symmetry of every basis-coordinate
polynomial. -/
theorem invariant_iff_transpose (b : Basis ι K W) (d : ℕ)
    (c : Exponent d →₀ W) :
    c ∈ invariantCoefficients (K := K) (W := W) d ↔
      ∀ i, (transpose b d c i).IsSymmetric := by
  simp only [isSymmetric_iff_coefficients, transpose_coeff]
  constructor
  · intro hc i h a
    rw [hc h a]
  · intro hc h a
    apply b.repr.injective
    apply Finsupp.ext
    intro i
    exact hc i h a

/-- Lift the symmetric coordinate polynomials to the symmetric subalgebra. -/
def basisCoordinates (b : Basis ι K W) (d : ℕ)
    (c : invariantCoefficients (K := K) (W := W) d) :
    ι →₀ MvPolynomial.symmetricSubalgebra (Fin d) K :=
  Finsupp.ofSupportFinite
    (fun i => ⟨transpose b d c.1 i, (invariant_iff_transpose b d c.1).mp c.2 i⟩)
    (by
      apply (transpose b d c.1).hasFiniteSupport.subset
      intro i hi hz
      apply hi
      exact Subtype.ext hz)

@[simp] theorem basisCoordinates_val (b : Basis ι K W) (d : ℕ)
    (c : invariantCoefficients (K := K) (W := W) d) (i : ι) :
    (basisCoordinates b d c i).1 = transpose b d c.1 i := rfl

def basisCoordinatesLinear (b : Basis ι K W) (d : ℕ) :
    invariantCoefficients (K := K) (W := W) d →ₗ[K]
      (ι →₀ MvPolynomial.symmetricSubalgebra (Fin d) K) where
  toFun := basisCoordinates b d
  map_add' c e := by
    apply Finsupp.ext
    intro i
    apply Subtype.ext
    exact DFunLike.congr_fun ((transpose b d).map_add c.1 e.1) i
  map_smul' k c := by
    apply Finsupp.ext
    intro i
    apply Subtype.ext
    exact DFunLike.congr_fun ((transpose b d).map_smul k c.1) i

theorem basisCoordinatesLinear_bijective (b : Basis ι K W) (d : ℕ) :
    Function.Bijective (basisCoordinatesLinear b d) := by
  constructor
  · intro c e h
    apply Subtype.ext
    apply (transpose b d).injective
    apply Finsupp.ext
    intro i
    exact congrArg Subtype.val (DFunLike.congr_fun h i)
  · intro f
    let raw : ι →₀ MvPolynomial (Fin d) K :=
      Finsupp.mapRange.linearMap (MvPolynomial.symmetricSubalgebra (Fin d) K).val.toLinearMap f
    let c := (transpose b d).symm raw
    have hc : c ∈ invariantCoefficients (K := K) (W := W) d := by
      apply (invariant_iff_transpose b d c).mpr
      intro i
      change (transpose b d ((transpose b d).symm raw) i).IsSymmetric
      rw [LinearEquiv.apply_symm_apply]
      exact (f i).2
    refine ⟨⟨c, hc⟩, ?_⟩
    apply Finsupp.ext
    intro i
    apply Subtype.ext
    change transpose b d ((transpose b d).symm raw) i = _
    rw [LinearEquiv.apply_symm_apply]
    rfl

/-- Exact tensor factorization of vector-valued symmetric polynomial families.
The chosen basis is used only in the construction of the inverse. -/
def tensorEquivOfBasis (b : Basis ι K W) (d : ℕ) :
    invariantCoefficients (K := K) (W := W) d ≃ₗ[K]
      W ⊗[K] MvPolynomial.symmetricSubalgebra (Fin d) K := by
  classical
  exact (LinearEquiv.ofBijective (basisCoordinatesLinear b d)
    (basisCoordinatesLinear_bijective b d)).trans
      (((LinearEquiv.rTensor (MvPolynomial.symmetricSubalgebra (Fin d) K) b.repr).trans
        (TensorProduct.finsuppScalarLeft K
          (MvPolynomial.symmetricSubalgebra (Fin d) K) ι)).symm)

/-- Every vector space has the required basis, so no basis hypothesis is needed. -/
def tensorEquiv (d : ℕ) :
    invariantCoefficients (K := K) (W := W) d ≃ₗ[K]
      W ⊗[K] MvPolynomial.symmetricSubalgebra (Fin d) K :=
  tensorEquivOfBasis (Module.Free.chooseBasis K W) d

/-- The inverse sends a pure tensor to the expected scalar-times-vector
coefficient family; in particular the equivalence is the ordinary tensor factor. -/
theorem tensorEquivOfBasis_symm_tmul (b : Basis ι K W) (d : ℕ)
    (w : W) (s : MvPolynomial.symmetricSubalgebra (Fin d) K) (a : Exponent d) :
    ((tensorEquivOfBasis b d).symm (w ⊗ₜ[K] s)).1 a = s.1.coeff a • w := by
  classical
  let E := LinearEquiv.ofBijective (basisCoordinatesLinear b d)
    (basisCoordinatesLinear_bijective b d)
  let T := (LinearEquiv.rTensor (MvPolynomial.symmetricSubalgebra (Fin d) K) b.repr).trans
    (TensorProduct.finsuppScalarLeft K (MvPolynomial.symmetricSubalgebra (Fin d) K) ι)
  have hc : basisCoordinatesLinear b d ((tensorEquivOfBasis b d).symm (w ⊗ₜ[K] s)) =
      T (w ⊗ₜ[K] s) := E.apply_symm_apply (T (w ⊗ₜ[K] s))
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  have hi := congrArg
    (fun f : ι →₀ MvPolynomial.symmetricSubalgebra (Fin d) K =>
      MvPolynomial.coeff a (f i).1) hc
  change b.repr (((tensorEquivOfBasis b d).symm (w ⊗ₜ[K] s)).1 a) i =
    MvPolynomial.coeff a (T (w ⊗ₜ[K] s) i).1 at hi
  simpa [T, MvPolynomial.coeff_smul, mul_comm] using hi

theorem tensorEquiv_symm_tmul (d : ℕ)
    (w : W) (s : MvPolynomial.symmetricSubalgebra (Fin d) K) (a : Exponent d) :
    ((tensorEquiv (K := K) (W := W) d).symm (w ⊗ₜ[K] s)).1 a = s.1.coeff a • w :=
  tensorEquivOfBasis_symm_tmul (Module.Free.chooseBasis K W) d w s a

end

end VOA.SymmetricPolynomialTensorCoefficients

section AxiomAudit
#print axioms VOA.SymmetricPolynomialTensorCoefficients.tensorEquiv
end AxiomAudit
