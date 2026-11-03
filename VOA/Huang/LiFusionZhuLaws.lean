import VOA.Huang.LiFusionTopFaithful
import VOA.Huang.GenusOneLiSeparation

/-! # Reducing top separation to the classical module Zhu identities

`RawZhuBimoduleLaws` asks only for seven explicit identities modulo the original
`fzO`: stability, annihilation by `O(V)`, the two product laws, and commutation.
They are the classical Frenkel–Zhu bimodule theorem, for arbitrary insertion
modules, with no rationality, complete family, top data, or intertwiners in the
statement. Their general proof is not supplied here. The unit laws and all
quotient and semisimple algebra transport are proved below.
-/
namespace VOA.Huang.LiFusion
open VOA VOA.FZ FusionTop GenusOne VHat VHat.DLM3
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

/-- The concrete, family-independent remaining module Zhu identities. -/
structure RawZhuBimoduleLaws (A : OrdVModule W M) : Prop where
  left_stable : ∀ a w, w ∈ fzO A.toWeakModule → rawLeft A a w ∈ fzO A.toWeakModule
  right_stable : ∀ a w, w ∈ fzO A.toWeakModule → rawRight A a w ∈ fzO A.toWeakModule
  left_O : ∀ a, a ∈ O W → ∀ w, rawLeft A a w ∈ fzO A.toWeakModule
  right_O : ∀ a, a ∈ O W → ∀ w, rawRight A a w ∈ fzO A.toWeakModule
  left_mul : ∀ a b w, rawLeft A (zhuMul W a b) w - rawLeft A a (rawLeft A b w)
    ∈ fzO A.toWeakModule
  right_mul : ∀ a b w, rawRight A (zhuMul W a b) w - rawRight A b (rawRight A a w)
    ∈ fzO A.toWeakModule
  commute : ∀ a b w, rawLeft A a (rawRight A b w) - rawRight A b (rawLeft A a w)
    ∈ fzO A.toWeakModule

theorem rawLeft_vacuum (w : M) : rawLeft A W.vacuum w = w := by
  rw [rawLeft_homogeneous (p := 0) W.vacuum_mem_grading_zero]
  simp only [fzLeft, Nat.zero_add, Finset.range_one, Finset.sum_singleton,
    Nat.cast_zero, zero_sub, cbz_zero, one_smul]
  rw [← WeakModule.act_def, WeakModule.act_vacuum, if_pos rfl]

theorem rawRight_vacuum (w : M) : rawRight A W.vacuum w = w := by
  rw [rawRight_homogeneous (p := 0) W.vacuum_mem_grading_zero]
  simp only [fzRight, Nat.zero_add, Finset.range_one, Finset.sum_singleton,
    Nat.cast_zero, zero_sub, cbz_zero, one_smul]
  rw [← WeakModule.act_def, WeakModule.act_vacuum, if_pos rfl]

/-- Descend first in the module argument and then in the VOA state. -/
noncomputable def zhuQuotientOp (L : V →ₗ[ℂ] Module.End ℂ M)
    (hs : ∀ a w, w ∈ fzO A.toWeakModule → L a w ∈ fzO A.toWeakModule)
    (hO : ∀ a, a ∈ O W → ∀ w, L a w ∈ fzO A.toWeakModule) :
    VOA.A W →ₗ[ℂ] Module.End ℂ (M ⧸ fzO A.toWeakModule) :=
  (O W).liftQ (descendOps (fzO A.toWeakModule) L hs) (by
    intro a ha
    apply LinearMap.ext
    intro x
    obtain ⟨w, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective x
    change (fzO A.toWeakModule).mkQ (L a w) = 0
    simpa using hO a ha w)

@[simp] theorem zhuQuotientOp_mk (L : V →ₗ[ℂ] Module.End ℂ M)
    (hs : ∀ a w, w ∈ fzO A.toWeakModule → L a w ∈ fzO A.toWeakModule)
    (hO : ∀ a, a ∈ O W → ∀ w, L a w ∈ fzO A.toWeakModule) (a : V) (w : M) :
    zhuQuotientOp L hs hO (VOA.mk W a) ((fzO A.toWeakModule).mkQ w) =
      (fzO A.toWeakModule).mkQ (L a w) := rfl

/-- Construct the genuine `A(V)` bimodule, without any separation assumption. -/
noncomputable def zhuQuotientActions (h : RawZhuBimoduleLaws A) :
    letI := instRingA W; letI := instAlgebraA W;
    BimoduleTrace.Actions (VOA.A W) (M ⧸ fzO A.toWeakModule) := by
  letI := instRingA W
  letI := instAlgebraA W
  let q := (fzO A.toWeakModule).mkQ
  have he (x y : M) (hxy : x - y ∈ fzO A.toWeakModule) : q x = q y := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hxy
  refine {
    left := zhuQuotientOp (rawLeft A) h.left_stable h.left_O
    right := zhuQuotientOp (rawRight A) h.right_stable h.right_O
    left_one := ?_
    right_one := ?_
    left_mul := ?_
    right_mul := ?_
    commute := ?_ }
  · intro x
    obtain ⟨w, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective x
    change q (rawLeft A W.vacuum w) = q w
    rw [rawLeft_vacuum]
  · intro x
    obtain ⟨w, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective x
    change q (rawRight A W.vacuum w) = q w
    rw [rawRight_vacuum]
  · intro a b x
    obtain ⟨a, rfl⟩ := VOA.mk_surjective W a
    obtain ⟨b, rfl⟩ := VOA.mk_surjective W b
    obtain ⟨w, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective x
    rw [show VOA.mk W a * VOA.mk W b = VOA.mk W (zhuMul W a b) from
      Amul_mk (zhuRingData_holds W) a b]
    exact he _ _ (h.left_mul a b w)
  · intro a b x
    obtain ⟨a, rfl⟩ := VOA.mk_surjective W a
    obtain ⟨b, rfl⟩ := VOA.mk_surjective W b
    obtain ⟨w, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective x
    rw [show VOA.mk W a * VOA.mk W b = VOA.mk W (zhuMul W a b) from
      Amul_mk (zhuRingData_holds W) a b]
    exact he _ _ (h.right_mul a b w)
  · intro a b x
    obtain ⟨a, rfl⟩ := VOA.mk_surjective W a
    obtain ⟨b, rfl⟩ := VOA.mk_surjective W b
    obtain ⟨w, rfl⟩ := (fzO A.toWeakModule).mkQ_surjective x
    exact he _ _ (h.commute a b w)

/-- Separation forces the classical identities, so the raw-law residual
is not stronger than the intended separation conclusion. -/
theorem rawZhuBimoduleLaws_of_separate {ι : Type u} {P : ι → LWModule W}
    (hsep : TopDataSeparate A P) : RawZhuBimoduleLaws A := by
  refine ⟨fun a _ hw => rawLeft_preserves_fzO hsep a hw,
    fun a _ hw => rawRight_preserves_fzO hsep a hw, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha w
    apply hsep
    intro i j T
    rw [fzSpace_rawLeft, O_le_ker_rhoLW (P j).isMod (P j).isLow ha, LinearMap.zero_comp]
  · intro a ha w
    apply hsep
    intro i j T
    rw [fzSpace_rawRight, O_le_ker_rhoLW (P i).isMod (P i).isLow ha, LinearMap.comp_zero]
  · intro a b w
    apply hsep
    intro i j T
    rw [map_sub, fzSpace_rawLeft, fzSpace_rawLeft, fzSpace_rawLeft,
      rhoLW_zhuMul (P j).isMod (P j).isLow]
    exact sub_eq_zero.mpr rfl
  · intro a b w
    apply hsep
    intro i j T
    rw [map_sub, fzSpace_rawRight, fzSpace_rawRight, fzSpace_rawRight,
      rhoLW_zhuMul (P i).isMod (P i).isLow]
    exact sub_eq_zero.mpr rfl
  · intro a b w
    apply hsep
    intro i j T
    rw [map_sub, fzSpace_rawLeft, fzSpace_rawRight, fzSpace_rawRight, fzSpace_rawLeft]
    exact sub_eq_zero.mpr rfl

variable {ι : Type u} [Finite ι]

/-- Transport the classical Zhu bimodule along the faithful full top algebra. -/
theorem insertionTopBimoduleExists_of_rawLaws
    (h : RawZhuBimoduleLaws A) (P : ι → LWModule W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W))
    (hcomplete : CompleteTopFamily P) (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod)) :
    InsertionTopBimoduleExists A P := by
  letI := instRingA W
  letI := instAlgebraA W
  let e := AlgEquiv.ofBijective (topAlgHom P) (topAlgHom_bijective P hss hcomplete hP hne)
  let B := zhuQuotientActions h
  have hei (a : V) : e.symm (insertionTopRep P a) = VOA.mk W a := by
    rw [← topAlgHom_mk]
    exact e.symm_apply_apply (VOA.mk W a)
  refine ⟨{
    actions := {
      left := B.left.comp e.symm.toLinearMap
      right := B.right.comp e.symm.toLinearMap
      left_one := fun x => by simp [B.left_one]
      right_one := fun x => by simp [B.right_one]
      left_mul := fun a b x => by simp [B.left_mul]
      right_mul := fun a b x => by simp [B.right_mul]
      commute := fun a b x => B.commute _ _ x }
    full := insertionTopRep_surjective P hP hne
    left_mk := ?_
    right_mk := ?_ }⟩
  · intro p a ha w
    change B.left (e.symm (insertionTopRep P a)) ((fzO A.toWeakModule).mkQ w) = _
    rw [hei]
    change (fzO A.toWeakModule).mkQ (rawLeft A a w) = _
    rw [rawLeft_homogeneous ha]
  · intro p a ha w
    change B.right (e.symm (insertionTopRep P a)) ((fzO A.toWeakModule).mkQ w) = _
    rw [hei]
    change (fzO A.toWeakModule).mkQ (rawRight A a w) = _
    rw [rawRight_homogeneous ha]

/-- Rationality and a complete irredundant simple family reduce separation
solely to the family-independent raw module Zhu identities. -/
theorem topDataSeparate_of_admissiblyRational_rawLaws
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hrat : AdmissiblyRational W) (h : RawZhuBimoduleLaws A) (P : ι → LWModule W)
    (hcomplete : CompleteTopFamily P) (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod)) :
    TopDataSeparate A P := by
  obtain ⟨B⟩ := insertionTopBimoduleExists_of_rawLaws h P
    (ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational Pr hrat) hcomplete hP hne
  exact topDataSeparate_of_bimodule B

/-- With a complete distinct simple family, the raw-law target is exactly
separation; it introduces no stronger insertion-module hypothesis. -/
theorem topDataSeparate_iff_rawLaws
    (P : ι → LWModule W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W))
    (hcomplete : CompleteTopFamily P) (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod)) :
    TopDataSeparate A P ↔ RawZhuBimoduleLaws A := by
  refine ⟨rawZhuBimoduleLaws_of_separate, fun h => ?_⟩
  obtain ⟨B⟩ := insertionTopBimoduleExists_of_rawLaws h P hss hcomplete hP hne
  exact topDataSeparate_of_bimodule B

end VOA.Huang.LiFusion
