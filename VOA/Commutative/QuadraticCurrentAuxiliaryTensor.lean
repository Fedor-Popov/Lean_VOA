/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QuadraticCurrentAuxiliaryCoefficients
import VOA.Commutative.SymmetricPolynomialTensorCoefficients

/-!
# The exact auxiliary symmetric-polynomial tensor factor

Reconstruct tensor polynomials from arbitrary finite current-carrier-valued
coefficient families. Auxiliary symmetry is exactly permutation invariance of
these coefficients. Consequently the literal current carrier with `d` auxiliary
variables is the tensor product of the current-only carrier and the scalar
symmetric polynomials in `d` roots. This is an actual equivalence, in all degrees.
-/

namespace VOA.QuadraticCurrentAuxiliaryTensor

open VOA.DeligneAuxiliaryCollision
open VOA.QuadraticCurrentFunctionalCarrier
open VOA.QuadraticCurrentAuxiliaryCoefficients
open VOA.SymmetricPolynomialTensorCoefficients
open scoped TensorProduct

noncomputable section

variable {K σ ρ : Type*} [Field K] [Fintype σ]

omit [Fintype σ] in
theorem coefficient_auxiliary_rename {m d : ℕ} (a : Exponent d)
    (h : Equiv.Perm (Fin d)) (p : MvPolynomial (Particle m d) K) :
    MvPolynomial.coeff (a.mapDomain h)
        (split m d (MvPolynomial.rename
          (particlePermutation (Equiv.refl (Fin m)) h) p)) =
      MvPolynomial.coeff a (split m d p) := by
  rw [particlePermutation_coe, split_rename]
  simp only [Equiv.coe_refl, MvPolynomial.rename_id]
  change MvPolynomial.coeff (a.mapDomain h)
    (MvPolynomial.rename h (MvPolynomial.map (RingHom.id _) (split m d p))) = _
  rw [MvPolynomial.map_id, MvPolynomial.coeff_rename_mapDomain h h.injective]

omit [Fintype σ] in
/-- Scalar symmetry of the auxiliary roots means that the vector coefficients
are constant on permutation orbits of auxiliary monomials. -/
theorem auxiliarySymmetric_iff_coefficients {m d : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m d) :
    AuxiliarySymmetric p ↔ ∀ (h : Equiv.Perm (Fin d)) a,
      auxiliaryCoefficient (a.mapDomain h) p = auxiliaryCoefficient a p := by
  constructor
  · intro hp h a
    funext t
    have hc := congrArg (fun f => MvPolynomial.coeff (a.mapDomain h) (split m d f))
      (hp h t)
    dsimp only at hc
    rw [coefficient_auxiliary_rename] at hc
    exact hc.symm
  · intro hp h t
    apply (split (K := K) m d).injective
    apply MvPolynomial.ext
    intro a
    obtain ⟨a, rfl⟩ := Finsupp.mapDomain_surjective h.surjective a
    rw [coefficient_auxiliary_rename]
    exact (congrFun (hp h a) t).symm

/-- Read one tensor component of a current-only carrier vector. -/
def componentLinear (Q : ρ → σ × σ → K) (m : ℕ) (t : Fin m → σ) :
    currentCarrier Q m 0 →ₗ[K] MvPolynomial (Fin m) K :=
  (LinearMap.proj t).comp (currentCarrier Q m 0).subtype

/-- Assemble an arbitrary finite family of current-only carrier vectors into
a tensor polynomial in both populations of roots. -/
def assembleLinear (Q : ρ → σ × σ → K) (m d : ℕ) :
    (Exponent d →₀ currentCarrier Q m 0) →ₗ[K]
      TensorPolynomial (K := K) (σ := σ) m d :=
  LinearMap.pi fun t => (split (K := K) m d).symm.toLinearMap.comp
    ((AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap.comp
      (Finsupp.mapRange.linearMap (componentLinear Q m t)))

@[simp] theorem auxiliaryCoefficient_assemble (Q : ρ → σ × σ → K) (m d : ℕ)
    (c : Exponent d →₀ currentCarrier Q m 0) (a : Exponent d) :
    auxiliaryCoefficient a (assembleLinear Q m d c) = (c a).1 := by
  funext t
  change MvPolynomial.coeff a
    (split m d ((split m d).symm
      ((AddMonoidAlgebra.coeffLinearEquiv K).symm
        (Finsupp.mapRange.linearMap (componentLinear Q m t) c)))) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- A finite coefficient family reconstructs a carrier vector exactly when it
is invariant under auxiliary-root permutations. -/
theorem assemble_mem_currentCarrier_iff (Q : ρ → σ × σ → K) (m d : ℕ)
    (c : Exponent d →₀ currentCarrier Q m 0) :
    assembleLinear Q m d c ∈ currentCarrier Q m d ↔
      c ∈ invariantCoefficients (K := K) (W := currentCarrier Q m 0) d := by
  rw [mem_currentCarrier_iff_coefficients, auxiliarySymmetric_iff_coefficients]
  simp only [auxiliaryCoefficient_assemble]
  constructor
  · rintro ⟨hc, _⟩ h a
    exact Subtype.ext (hc h a)
  · intro hc
    exact ⟨fun h a => congrArg Subtype.val (hc h a), fun a => (c a).2⟩

theorem coefficientsLinear_mem_invariant (Q : ρ → σ × σ → K) (m d : ℕ)
    (p : currentCarrier Q m d) :
    coefficientsLinear Q m d p ∈
      invariantCoefficients (K := K) (W := currentCarrier Q m 0) d := by
  intro h a
  apply Subtype.ext
  have hp := (mem_currentCarrier_iff_coefficients Q p.1).mp p.2
  exact (auxiliarySymmetric_iff_coefficients p.1).mp hp.1 h a

/-- Coefficient extraction with its exact invariant codomain. -/
def invariantCoefficientsLinear (Q : ρ → σ × σ → K) (m d : ℕ) :
    currentCarrier Q m d →ₗ[K]
      invariantCoefficients (K := K) (W := currentCarrier Q m 0) d :=
  (coefficientsLinear Q m d).codRestrict _ (coefficientsLinear_mem_invariant Q m d)

/-- Reconstruction proves surjectivity, without a Hilbert comparison. -/
theorem invariantCoefficientsLinear_bijective (Q : ρ → σ × σ → K) (m d : ℕ) :
    Function.Bijective (invariantCoefficientsLinear Q m d) := by
  constructor
  · intro p q h
    exact coefficientsLinear_injective Q m d (congrArg Subtype.val h)
  · intro c
    let p : currentCarrier Q m d := ⟨assembleLinear Q m d c.1,
      (assemble_mem_currentCarrier_iff Q m d c.1).mpr c.2⟩
    refine ⟨p, ?_⟩
    apply Subtype.ext
    apply Finsupp.ext
    intro a
    apply Subtype.ext
    exact auxiliaryCoefficient_assemble Q m d c.1 a

/-- The full literal carrier is exactly the space of finite, invariant,
current-carrier-valued auxiliary coefficient families. -/
def invariantCoefficientsEquiv (Q : ρ → σ × σ → K) (m d : ℕ) :
    currentCarrier Q m d ≃ₗ[K]
      invariantCoefficients (K := K) (W := currentCarrier Q m 0) d :=
  LinearEquiv.ofBijective (invariantCoefficientsLinear Q m d)
    (invariantCoefficientsLinear_bijective Q m d)

/-- Exact auxiliary tensor separation for arbitrary quadratic current relations.
This holds over every field, in all particle numbers and all degrees. -/
def currentAuxiliaryTensorEquiv (Q : ρ → σ × σ → K) (m d : ℕ) :
    currentCarrier Q m d ≃ₗ[K]
      currentCarrier Q m 0 ⊗[K] MvPolynomial.symmetricSubalgebra (Fin d) K :=
  (invariantCoefficientsEquiv Q m d).trans (tensorEquiv d)

theorem currentAuxiliaryTensorEquiv_symm_tmul_coefficient
    (Q : ρ → σ × σ → K) (m d : ℕ) (w : currentCarrier Q m 0)
    (s : MvPolynomial.symmetricSubalgebra (Fin d) K) (a : Exponent d) :
    auxiliaryCoefficient a
        ((currentAuxiliaryTensorEquiv Q m d).symm (w ⊗ₜ[K] s)).1 =
      (s.1.coeff a • w).1 := by
  have hc := congrArg (fun c : invariantCoefficients
      (K := K) (W := currentCarrier Q m 0) d => c.1 a)
    ((invariantCoefficientsEquiv Q m d).apply_symm_apply
      ((tensorEquiv (K := K) (W := currentCarrier Q m 0) d).symm (w ⊗ₜ[K] s)))
  dsimp only at hc
  rw [tensorEquiv_symm_tmul] at hc
  exact congrArg Subtype.val hc

omit [Fintype σ] in
theorem split_rename_current (m d : ℕ) (p : MvPolynomial (Fin m) K) :
    split m d (MvPolynomial.rename (Fin.castAdd d) p) = MvPolynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [split]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp => simp [map_mul, hp]

omit [Fintype σ] in
theorem split_rename_auxiliary (m d : ℕ) (p : MvPolynomial (Fin d) K) :
    split m d (MvPolynomial.rename (Fin.natAdd m) p) =
      MvPolynomial.map MvPolynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [split]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp => simp [map_mul, hp]

/-- On pure tensors the inverse is literally multiplication of the auxiliary
symmetric polynomial and the current tensor polynomial in their separate roots. -/
theorem currentAuxiliaryTensorEquiv_symm_tmul
    (Q : ρ → σ × σ → K) (m d : ℕ) (w : currentCarrier Q m 0)
    (s : MvPolynomial.symmetricSubalgebra (Fin d) K) (t : Fin m → σ) :
    ((currentAuxiliaryTensorEquiv Q m d).symm (w ⊗ₜ[K] s)).1 t =
      MvPolynomial.rename (Fin.natAdd m) s.1 *
        MvPolynomial.rename (Fin.castAdd d) (w.1 t) := by
  apply (split (K := K) m d).injective
  rw [map_mul, split_rename_auxiliary, split_rename_current]
  apply MvPolynomial.ext
  intro a
  rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  have hc := congrFun
    (currentAuxiliaryTensorEquiv_symm_tmul_coefficient Q m d w s a) t
  simpa [auxiliaryCoefficient, Algebra.smul_def, mul_comm] using hc

/-- The fundamental theorem of symmetric polynomials gives an ordinary
polynomial tensor factor, whose elementary generators have weights `1,...,d`. -/
def currentAuxiliaryElementaryTensorEquiv (Q : ρ → σ × σ → K) (m d : ℕ) :
    currentCarrier Q m d ≃ₗ[K]
      currentCarrier Q m 0 ⊗[K] MvPolynomial (Fin d) K :=
  (currentAuxiliaryTensorEquiv Q m d).trans
    (LinearEquiv.lTensor (currentCarrier Q m 0)
      (MvPolynomial.esymmAlgEquiv (Fin d) K (Fintype.card_fin d)).symm.toLinearEquiv)

/-- The auxiliary collision carrier is conductor times the exact tensor factor.
Characteristic zero enters only through the collision-square theorem. -/
def auxiliaryTensorEquiv [CharZero K] (Q : ρ → σ × σ → K) (m d : ℕ) :
    auxiliaryCarrier Q m d ≃ₗ[K]
      currentCarrier Q m 0 ⊗[K] MvPolynomial.symmetricSubalgebra (Fin d) K :=
  (conductorEquiv Q m d).symm.trans (currentAuxiliaryTensorEquiv Q m d)

/-- The full auxiliary factorization on a pure tensor includes exactly the
universal mixed-collision and auxiliary-collision conductor. -/
theorem auxiliaryTensorEquiv_symm_tmul [CharZero K]
    (Q : ρ → σ × σ → K) (m d : ℕ) (w : currentCarrier Q m 0)
    (s : MvPolynomial.symmetricSubalgebra (Fin d) K) (t : Fin m → σ) :
    ((auxiliaryTensorEquiv Q m d).symm (w ⊗ₜ[K] s)).1 t =
      conductor m d * (MvPolynomial.rename (Fin.natAdd m) s.1 *
        MvPolynomial.rename (Fin.castAdd d) (w.1 t)) := by
  change conductor m d *
    ((currentAuxiliaryTensorEquiv Q m d).symm (w ⊗ₜ[K] s)).1 t = _
  rw [currentAuxiliaryTensorEquiv_symm_tmul]

end

end VOA.QuadraticCurrentAuxiliaryTensor

section AxiomAudit
#print axioms VOA.QuadraticCurrentAuxiliaryTensor.invariantCoefficientsLinear_bijective
#print axioms VOA.QuadraticCurrentAuxiliaryTensor.currentAuxiliaryTensorEquiv
#print axioms VOA.QuadraticCurrentAuxiliaryTensor.currentAuxiliaryTensorEquiv_symm_tmul
#print axioms VOA.QuadraticCurrentAuxiliaryTensor.currentAuxiliaryElementaryTensorEquiv
#print axioms VOA.QuadraticCurrentAuxiliaryTensor.auxiliaryTensorEquiv
#print axioms VOA.QuadraticCurrentAuxiliaryTensor.auxiliaryTensorEquiv_symm_tmul
end AxiomAudit
