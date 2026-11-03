import VOA.Huang.GenusOneLiTopFull
import VOA.Huang.LiFusionZhuActions

/-! # Recovering the insertion bimodule from top-data separation

The remaining input is an annihilator assertion on the original quotient,
`LiFusion.TopDataSeparate`. It supplies descent of the raw actions, and all
bimodule laws are then proved by testing against the actual `fzSpace` data.
Fullness is discharged for distinct irreducible tops by Jacobson density.
No assertion that rationality implies separation is made here.
-/
namespace VOA.Huang.GenusOne
open VOA VOA.FZ FusionTop LiFusion
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {ι : Type u} {P : ι → LWModule W}

/-- Descend a state-linear family of operators through an invariant subspace. -/
noncomputable def descendOps (S : Submodule ℂ M) (L : V →ₗ[ℂ] Module.End ℂ M)
    (hL : ∀ a, ∀ w ∈ S, L a w ∈ S) : V →ₗ[ℂ] Module.End ℂ (M ⧸ S) where
  toFun a := S.mapQ S (L a) (hL a)
  map_add' a b := by
    apply LinearMap.ext
    intro x
    obtain ⟨w, rfl⟩ := S.mkQ_surjective x
    change S.mkQ (L (a + b) w) = S.mkQ (L a w) + S.mkQ (L b w)
    simp
  map_smul' c a := by
    apply LinearMap.ext
    intro x
    obtain ⟨w, rfl⟩ := S.mkQ_surjective x
    change S.mkQ (L (c • a) w) = c • S.mkQ (L a w)
    simp

@[simp] theorem descendOps_mk (S : Submodule ℂ M) (L : V →ₗ[ℂ] Module.End ℂ M)
    (hL : ∀ a, ∀ w ∈ S, L a w ∈ S) (a : V) (w : M) :
    descendOps S L hL a (S.mkQ w) = S.mkQ (L a w) := rfl

/-- The quotient left action, still parameterized by VOA states. -/
noncomputable def quotientLeft (hsep : TopDataSeparate A P) :
    V →ₗ[ℂ] Module.End ℂ (M ⧸ fzO A.toWeakModule) :=
  descendOps (fzO A.toWeakModule) (rawLeft A)
    (fun a _ hw => rawLeft_preserves_fzO hsep a hw)

/-- The quotient right action, still parameterized by VOA states. -/
noncomputable def quotientRight (hsep : TopDataSeparate A P) :
    V →ₗ[ℂ] Module.End ℂ (M ⧸ fzO A.toWeakModule) :=
  descendOps (fzO A.toWeakModule) (rawRight A)
    (fun a _ hw => rawRight_preserves_fzO hsep a hw)

theorem topQuot_left (hsep : TopDataSeparate A P) (i j : ι)
    (T : fzSpace A (P i) (P j)) (a : V) (x : M ⧸ fzO A.toWeakModule) :
    topQuot T (quotientLeft hsep a x) =
      (rhoLW (P j).isMod (P j).h a).comp (topQuot T x) := by
  obtain ⟨w, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective x
  exact fzSpace_rawLeft T a w

theorem topQuot_right (hsep : TopDataSeparate A P) (i j : ι)
    (T : fzSpace A (P i) (P j)) (a : V) (x : M ⧸ fzO A.toWeakModule) :
    topQuot T (quotientRight hsep a x) =
      (topQuot T x).comp (rhoLW (P i).isMod (P i).h a) := by
  obtain ⟨w, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective x
  exact fzSpace_rawRight T a w

/-- All quotient-action and associator obligations follow from separation.
Only fullness and the annihilator statement are inputs to this construction. -/
theorem insertionTopBimoduleExists_of_full_separate
    (hfull : Function.Surjective (insertionTopRep P))
    (hsep : TopDataSeparate A P) : InsertionTopBimoduleExists A P := by
  obtain ⟨s, hs⟩ := (insertionTopRep P).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hfull)
  have hsi (a : ∀ i, Module.End ℂ (bot (P i))) (i : ι) :
      rhoLW (P i).isMod (P i).h (s a) = a i := by
    have h := LinearMap.congr_fun hs a
    exact congrFun h i
  let L := (quotientLeft hsep).comp s
  let R := (quotientRight hsep).comp s
  have hL (i j : ι) (T : fzSpace A (P i) (P j)) (a) (x) :
      topQuot T (L a x) = (a j).comp (topQuot T x) := by
    change topQuot T (quotientLeft hsep (s a) x) = _
    rw [topQuot_left, hsi]
  have hR (i j : ι) (T : fzSpace A (P i) (P j)) (a) (x) :
      topQuot T (R a x) = (topQuot T x).comp (a i) := by
    change topQuot T (quotientRight hsep (s a) x) = _
    rw [topQuot_right, hsi]
  refine ⟨{
    actions := {
      left := L
      right := R
      left_one := ?_
      right_one := ?_
      left_mul := ?_
      right_mul := ?_
      commute := ?_ }
    full := hfull
    left_mk := ?_
    right_mk := ?_ }⟩
  · intro x
    apply quotient_ext_of_topDataSeparate hsep
    intro i j T
    rw [hL]
    rfl
  · intro x
    apply quotient_ext_of_topDataSeparate hsep
    intro i j T
    rw [hR]
    rfl
  · intro a b x
    apply quotient_ext_of_topDataSeparate hsep
    intro i j T
    rw [hL, hL, hL]
    rfl
  · intro a b x
    apply quotient_ext_of_topDataSeparate hsep
    intro i j T
    rw [hR, hR, hR]
    rfl
  · intro a b x
    apply quotient_ext_of_topDataSeparate hsep
    intro i j T
    rw [hL, hR, hR, hL]
    rfl
  · intro p a ha w
    apply quotient_ext_of_topDataSeparate hsep
    intro i j T
    rw [hL, topQuot_mk, topQuot_mk, fzSpace_left T ha]
    rfl
  · intro p a ha w
    apply quotient_ext_of_topDataSeparate hsep
    intro i j T
    rw [hR, topQuot_mk, topQuot_mk, fzSpace_right T ha]
    rfl

/-- For distinct irreducible tops, only separation of `M/O(M)` remains.
Completeness and rationality are intended hypotheses for that remaining input,
not conclusions of this theorem. -/
theorem insertionTopBimoduleExists_of_separate [Finite ι]
    (P : ι → LWModule W) (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod))
    (hsep : TopDataSeparate A P) : InsertionTopBimoduleExists A P :=
  insertionTopBimoduleExists_of_full_separate (insertionTopRep_surjective P hP hne) hsep

end VOA.Huang.GenusOne
