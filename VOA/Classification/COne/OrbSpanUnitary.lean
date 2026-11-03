import VOA.Classification.COne.OrbSpanGlue
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # OrbSpan: Virasoro unitarity gives the primary decomposition

A positive-definite Hermitian form with `L(n)† = L(-n)` forces every weight space to be
spanned by Virasoro primaries and lower descendants (`virPrimaryDecomp_of_unitary`): the
orthogonal complement of the descendants in `W_N` consists of primaries.

The form passes to every vertex operator subalgebra (`VirUnitaryForm.restrict`), so for the
tetrahedral orbifold the primary decomposition reduces to Virasoro unitarity of `V₂` itself.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbSpan
open VOA VertexOperatorAlgebra
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- A positive-definite Hermitian form (linear in the first slot) for which
`L(n)` and `L(-n)` are adjoint. -/
structure VirUnitaryForm (W : VertexOperatorAlgebra V) where
  form : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ
  hermitian : ∀ x y : V, form y x = starRingEnd ℂ (form x y)
  pos : ∀ x : V, x ≠ 0 → 0 < (form x x).re
  adjoint : ∀ (n : ℤ) (x y : V), form (W.L n x) y = form x (W.L (-n) y)

theorem L_mem_grading_aux (W : VertexOperatorAlgebra V) {ℓ : ℤ} {v : V}
    (hv : v ∈ W.grading ℓ) (m : ℤ) : W.L m v ∈ W.grading (ℓ - m) := by
  have h := W.grading_mode W.conformalVector W.conformal_mem v hv (m + 1)
  rw [show (2 + ℓ - (m + 1) - 1) = ℓ - m from by ring] at h
  exact h

theorem lowerDesc_le_grading (W : VertexOperatorAlgebra V) (N : ℤ) :
    lowerDesc W N ≤ W.grading N := by
  apply Submodule.span_le.mpr
  rintro x ⟨m, y, hy, rfl⟩
  have h := L_mem_grading_aux W hy (-(m : ℤ) - 1)
  rwa [show N - m - 1 - (-(m : ℤ) - 1) = N by ring] at h

theorem VirUnitaryForm.self_eq_zero {W : VertexOperatorAlgebra V} (U : VirUnitaryForm W)
    {x : V} (h : U.form x x = 0) : x = 0 := by
  by_contra hx
  have := U.pos x hx
  rw [h] at this
  simp at this

/-- The inner product on one weight space (Mathlib convention: conjugate-linear on the left). -/
@[reducible] def VirUnitaryForm.core {W : VertexOperatorAlgebra V} (U : VirUnitaryForm W) (N : ℤ) :
    InnerProductSpace.Core ℂ (W.grading N) where
  inner x y := U.form (y : V) (x : V)
  conj_inner_symm x y := by
    change starRingEnd ℂ (U.form (x : V) (y : V)) = U.form (y : V) (x : V)
    rw [U.hermitian, Complex.conj_conj]
  re_inner_nonneg x := by
    change 0 ≤ (U.form (x : V) (x : V)).re
    by_cases hx : (x : V) = 0
    · rw [hx]; simp
    · exact (U.pos _ hx).le
  add_left x y z := by
    change U.form (z : V) ((x + y : W.grading N) : V) = _
    rw [Submodule.coe_add, map_add]
  smul_left x y r := by
    change U.form (y : V) ((r • x : W.grading N) : V) = _
    rw [Submodule.coe_smul, LinearMap.map_smulₛₗ, smul_eq_mul]
  definite x h := by
    apply Subtype.ext
    exact U.self_eq_zero h

/-- **Unitarity ⇒ primary decomposition.** -/
theorem virPrimaryDecomp_of_unitary {W : VertexOperatorAlgebra V} (U : VirUnitaryForm W) :
    VirPrimaryDecomp W := by
  intro N x hx
  letI core := U.core N
  letI : NormedAddCommGroup (W.grading N) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ (W.grading N) := InnerProductSpace.ofCore core.toCore
  haveI : FiniteDimensional ℂ (W.grading N) := W.finrank N
  let K : Submodule ℂ (W.grading N) := (lowerDesc W N).comap (W.grading N).subtype
  have hsup : K ⊔ Kᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
  have hmem : (⟨x, hx⟩ : W.grading N) ∈ K ⊔ Kᗮ := by rw [hsup]; trivial
  obtain ⟨d, hd, p, hp, hdp⟩ := Submodule.mem_sup.mp hmem
  have horth : ∀ z ∈ lowerDesc W N, U.form (p : V) z = 0 := by
    intro z hz
    have hzK : (⟨z, lowerDesc_le_grading W N hz⟩ : W.grading N) ∈ K := hz
    exact (Submodule.mem_orthogonal K p).mp hp _ hzK
  have hprim : (p : V) ∈ prim W N := by
    rw [mem_prim]
    refine ⟨p.2, fun m => ?_⟩
    set q := W.L ((m : ℤ) + 1) (p : V) with hq
    have hqg : q ∈ W.grading (N - m - 1) := by
      have := L_mem_grading_aux W p.2 ((m : ℤ) + 1)
      rwa [show N - ((m : ℤ) + 1) = N - m - 1 by ring] at this
    have hdesc : W.L (-(m : ℤ) - 1) q ∈ lowerDesc W N :=
      Submodule.subset_span ⟨m, q, hqg, rfl⟩
    apply U.self_eq_zero
    rw [hq, U.adjoint, show -((m : ℤ) + 1) = -(m : ℤ) - 1 by ring]
    exact horth _ hdesc
  have hx' : x = (d : V) + (p : V) := by
    rw [← Submodule.coe_add, hdp]
  rw [hx']
  exact Submodule.add_mem _ (Submodule.mem_sup_right hd) (Submodule.mem_sup_left hprim)

/-- The form restricts to any vertex operator subalgebra. -/
def VirUnitaryForm.restrict {W : VertexOperatorAlgebra V} (U : VirUnitaryForm W)
    (S : VOASubalgebra W) : VirUnitaryForm S.toVOA where
  form := (U.form.compl₂ S.carrier.subtype).comp S.carrier.subtype
  hermitian x y := U.hermitian (x : V) (y : V)
  pos x hx := U.pos (x : V) (fun h => hx (Subtype.ext h))
  adjoint n x y := U.adjoint n (x : V) (y : V)

/-- **Primary decomposition for every subalgebra of a Virasoro-unitary VOA.** -/
theorem virPrimaryDecomp_of_subalgebra {W : VertexOperatorAlgebra V} (U : VirUnitaryForm W)
    (S : VOASubalgebra W) : VirPrimaryDecomp S.toVOA :=
  virPrimaryDecomp_of_unitary (U.restrict S)

end VOA.Classification.COne.OrbSpan
