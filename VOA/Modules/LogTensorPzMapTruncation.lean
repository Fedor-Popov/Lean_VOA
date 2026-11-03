/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzBaseJacobi

/-! # Genuine source truncation supplies P(1) lower truncation

A map intertwining the actual weak source modes with the twisted coproduct is
lower truncated for the untwisted coproduct. The proof is the finite double twist,
so its cutoff is uniform in both tensor inputs.
-/

namespace VOA.LogTensor.Pz
open scoped BigOperators
open VOA.Huang.PzTensorRho
universe u
variable {V M₁ M₂ R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup R] [Module ℂ R] {W : VertexOperatorAlgebra V}
variable (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂) (A : WeakModule W R)

/-- The actual double twist turns the weak-module upper cutoff into the uniform
lower cutoff required in the algebraic tensor dual. -/
theorem mapMode_truncated (psi : R →ₗ[ℂ] BilinearDual (M₁ := M₁) (M₂ := M₂))
    (hpsi : ∀ (d : ℤ) (v : V), v ∈ W.grading d → ∀ (p : ℤ) (r : R),
      psi (mode (A.YM v) p r) = tauHat A₁ A₂ d v p (psi r))
    (r : R) (d : ℤ) (v : V) (hv : v ∈ W.grading d) :
    TruncAt A₁ A₂ v (psi r) := by
  classical
  choose K hK using fun j : ℕ => A.truncation ((W.L 1 ^ j) v) r
  let s := Finset.range (d.toNat+1)
  have hs : s.Nonempty := ⟨0,by simp [s]⟩
  let B : ℤ := s.sup' hs (fun j => (j:ℤ)+K j)
  refine ⟨2*d-2-B,fun p hp => ?_⟩
  rw [← VOA.Huang.PzTensorY4.twist_twist A₁ A₂ hv p (psi r)]
  have hz : ∀ j ∈ s,
      tauHat A₁ A₂ (d-j) ((W.L 1 ^ j) v) (2*d-p-2-j) (psi r) = 0 := by
    intro j hj
    rw [← hpsi (d-j) ((W.L 1 ^ j) v) (VertexOperatorAlgebra.L_one_pow_mem W hv j)]
    have hjB : (j:ℤ)+K j ≤ B := Finset.le_sup' (fun j : ℕ => (j:ℤ)+K j) hj
    rw [hK j _ (by omega),map_zero]
  have he : ∑ j ∈ Finset.range (d.toNat+1), (j.factorial:ℂ)⁻¹ •
      tauHat A₁ A₂ (d-j) ((W.L 1 ^ j) v) (2*d-p-2-j) (psi r) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hz j hj,smul_zero]
  rw [he,smul_zero]

end VOA.LogTensor.Pz
