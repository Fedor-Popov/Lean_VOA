import VOA.Huang.GenusOneLiMatrixSeparation
import VOA.Huang.GenusOneLiBimodule

/-! # Separation from the insertion quotient actions

The all-pairs matrix separation theorem gives the converse to the
construction of quotient actions from separation. This does not assert those
quotient actions exist for a rational VOA.
-/
namespace VOA.Huang.GenusOne
open VOA VOA.FZ FusionTop LiFusion
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {ι : Type u} {P : ι → LWModule W}

/-- An arbitrary rectangular bimodule map gives genuine Frenkel–Zhu top data. -/
noncomputable def fzSpaceOfBimoduleMap (B : InsertionTopBimodule A P) (i j : ι)
    (T : (M ⧸ fzO A.toWeakModule) →ₗ[ℂ] (bot (P i) →ₗ[ℂ] bot (P j)))
    (hL : ∀ a x, T (B.actions.left a x) = (a j).comp (T x))
    (hR : ∀ a x, T (B.actions.right a x) = (T x).comp (a i)) :
    fzSpace A (P i) (P j) :=
  ⟨T.comp (fzO A.toWeakModule).mkQ, by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      change T ((fzO A.toWeakModule).mkQ w) = 0
      have hz : (fzO A.toWeakModule).mkQ w = 0 := by simpa using hw
      rw [hz, map_zero]
    · intro p a ha w y
      change (T ((fzO A.toWeakModule).mkQ (fzLeft A.toWeakModule p a w)) y : (P j).carrier) = _
      rw [← B.left_mk p a ha w, hL]
      change (rhoLW (P j).isMod (P j).h a _ : (P j).carrier) = _
      rw [rhoLW_apply_coe, oMod_homogeneous (P j).isMod ha]
      rfl
    · intro p _ a ha w y y' hy
      change T ((fzO A.toWeakModule).mkQ (fzRight A.toWeakModule p a w)) y = _
      rw [← B.right_mk p a ha w, hR]
      change T ((fzO A.toWeakModule).mkQ w) (rhoLW (P i).isMod (P i).h a y) =
        T ((fzO A.toWeakModule).mkQ w) y'
      congr 1
      apply Subtype.ext
      rw [rhoLW_apply_coe, oMod_homogeneous (P i).isMod ha, hy]⟩

/-- Quotient actions imply separation, including every off-diagonal block.
The quotient need not be finite-dimensional. -/
theorem topDataSeparate_of_bimodule [Finite ι] (B : InsertionTopBimodule A P) :
    TopDataSeparate A P := by
  intro w hw
  have hz : (fzO A.toWeakModule).mkQ w = 0 := by
    apply BimoduleTrace.eq_zero_of_end_bimodule_maps (fun i => bot (P i)) B.actions
    intro i j T hL hR
    exact hw i j (fzSpaceOfBimoduleMap B i j T hL hR)
  simpa using hz

/-- For a full finite family, separation and the original bimodule interface
are equivalent. Neither side is discharged merely by this equivalence. -/
theorem topDataSeparate_iff_bimoduleExists [Finite ι]
    (hfull : Function.Surjective (insertionTopRep P)) :
    TopDataSeparate A P ↔ InsertionTopBimoduleExists A P :=
  ⟨insertionTopBimoduleExists_of_full_separate hfull,
    fun ⟨B⟩ => topDataSeparate_of_bimodule B⟩

end VOA.Huang.GenusOne
