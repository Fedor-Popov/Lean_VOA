import VOA.Huang.LiFusionInduced
import VOA.Huang.GenusOneLiTopFull

/-! # Faithfulness of a complete family of simple Zhu modules

Semisimplicity and completeness make the simultaneous top representation
faithful on `A(V)`. Together with the density theorem this identifies
`A(V)` with the full product of top endomorphism algebras. The PBW datum is
explicit when semisimplicity is supplied by admissible rationality.
-/
namespace VOA.Huang.LiFusion
open VOA VOA.FZ FusionTop GenusOne VHat VHat.DLM3
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {W : VertexOperatorAlgebra V} {ι : Type u}

/-- Completeness at the algebraic bottom: every simple `A(V)` module occurs.
This condition contains no insertion-module or intertwiner assertion. -/
def CompleteTopFamily (P : ι → LWModule W) : Prop :=
  ∀ U : AMod W, IsSimpleAMod U → ∃ i, Nonempty (AModEquiv W U (P i).toAMod)

/-- A left ideal, regarded as a bundled Zhu module. -/
noncomputable def leftIdealAMod
    (I : letI := instRingA W; Submodule (VOA.A W) (VOA.A W)) : AMod W :=
  letI := instRingA W
  letI := instAlgebraA W
  { carrier := I
    ρ := (Algebra.lsmul ℂ ℂ I).toLinearMap
    ρ_one := (Algebra.lsmul ℂ ℂ I).map_one
    ρ_mul := fun a b => by
      change (Algebra.lsmul ℂ ℂ I) (VOA.mk W (zhuMul W a b)) = _
      rw [show VOA.mk W (zhuMul W a b) = VOA.mk W a * VOA.mk W b from
        (Amul_mk (zhuRingData_holds W) a b).symm, map_mul]
      rfl }

/-- The actual Zhu representation on all chosen bottoms. -/
noncomputable def topAlgHom (P : ι → LWModule W) :
    letI := instRingA W; letI := instAlgebraA W;
    VOA.A W →ₐ[ℂ] (∀ i, Module.End ℂ (bot (P i))) :=
  letI := instRingA W
  letI := instAlgebraA W
  AlgHom.ofLinearMap (LinearMap.pi fun i => (P i).toAMod.ρ)
    (funext fun i => (P i).toAMod.ρ_one)
    (fun a b => funext fun i => (P i).toAMod.ρRingHom.map_mul a b)

@[simp] theorem topAlgHom_mk (P : ι → LWModule W) (a : V) :
    topAlgHom P (VOA.mk W a) = insertionTopRep P a := by
  funext i
  exact actA_mk (P i).isMod (P i).isLow a

/-- A complete simple family detects every element of a semisimple Zhu algebra. -/
theorem topAlgHom_injective (P : ι → LWModule W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W))
    (hcomplete : CompleteTopFamily P) : Function.Injective (topAlgHom P) := by
  letI := instRingA W
  letI := instAlgebraA W
  letI : IsSemisimpleRing (VOA.A W) := hss
  apply (topAlgHom P).toLinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro a ha
  have ha' : topAlgHom P a = 0 := ha
  let S := {I : Submodule (VOA.A W) (VOA.A W) // IsSimpleModule (VOA.A W) I}
  have htop : (⨆ I : S, I.val) = ⊤ := by
    simpa only [sSup_eq_iSup, iSup_subtype'] using
      IsSemisimpleModule.sSup_simples_eq_top (VOA.A W) (VOA.A W)
  have hkill (I : S) (x : VOA.A W) (hx : x ∈ I.val) : a * x = 0 := by
    have hI : IsSimpleAMod (leftIdealAMod I.val) := by
      rw [isSimpleAMod_iff_isSimpleModule]
      exact I.property
    obtain ⟨i, ⟨e⟩⟩ := hcomplete (leftIdealAMod I.val) hI
    have hz : (P i).toAMod.ρ a = 0 := congrFun ha' i
    have he := e.map_ρ a ⟨x, hx⟩
    rw [hz, LinearMap.zero_apply] at he
    have he' := e.toLinearEquiv.injective (he.trans e.toLinearEquiv.map_zero.symm)
    exact congrArg Subtype.val he'
  have h1 : (1 : VOA.A W) ∈ ⨆ I : S, I.val := by rw [htop]; trivial
  have hh : a * (1 : VOA.A W) = 0 :=
    Submodule.iSup_induction _ (motive := fun x => a * x = 0) h1 hkill
      (mul_zero a) (fun x y hx hy => by dsimp only at hx hy ⊢; rw [mul_add, hx, hy, add_zero])
  simpa using hh

/-- Rationality supplies semisimplicity; completeness supplies faithfulness. -/
theorem topAlgHom_injective_of_admissiblyRational
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hrat : AdmissiblyRational W) (P : ι → LWModule W)
    (hcomplete : CompleteTopFamily P) : Function.Injective (topAlgHom P) :=
  topAlgHom_injective P (ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational Pr hrat) hcomplete

/-- Density and faithfulness identify the full algebra on distinct simple tops. -/
theorem topAlgHom_bijective [Finite ι] (P : ι → LWModule W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W))
    (hcomplete : CompleteTopFamily P) (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod)) :
    Function.Bijective (topAlgHom P) := by
  refine ⟨topAlgHom_injective P hss hcomplete, ?_⟩
  intro b
  obtain ⟨a, ha⟩ := insertionTopRep_surjective P hP hne b
  exact ⟨VOA.mk W a, (topAlgHom_mk P a).trans ha⟩

end VOA.Huang.LiFusion
