import VOA.Classification.COne.PlusFiniteLengthOrdinary

/-! Finite length transfers between the actual mode algebra and an ambient
ring action whenever ambient submodules are invariant under every mode. -/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.PlusFiniteLength

open PlusRational FiniteLengthAlgebra ABDWeakAdmissible
open VOA.Huang.LogRemovalAdmissible

universe u v
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱}

/-- Compare composition length through the concrete invariant subspace lattice. -/
theorem finiteLength_of_mode_invariance
    {R X : Type*} [Ring R] [Algebra ℂ R]
    [AddCommGroup X] [Module ℂ X] [Module R X] [IsScalarTower ℂ R X]
    (A : WeakModule W X) (hfin : IsFiniteLength (modeAlg A) X)
    (hstable : ∀ P : Submodule R X, ∀ a n x, x ∈ P → A.act a n x ∈ P) :
    IsFiniteLength R X := by
  let f : Submodule R X → Submodule (modeAlg A) X := fun P =>
    toR A { carrier := P.restrictScalars ℂ, act_mem := fun a n x hx => hstable P a n x hx }
  have hf : StrictMono f := by
    intro P Q hPQ
    exact lt_of_le_of_ne (fun _ hx => hPQ.le hx) (fun he => hPQ.ne (by
      ext x
      exact Iff.of_eq (congrArg (fun S : Submodule (modeAlg A) X => x ∈ S) he)))
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfin
  letI := hN
  letI := hA
  haveI : WellFoundedLT (Submodule R X) := hf.wellFoundedLT
  haveI : WellFoundedGT (Submodule R X) := hf.wellFoundedGT
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_iff'.mpr inferInstance, inferInstance⟩

variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- Restricting the mode action to a submodule does not alter finite length
when it is measured using the ambient mode algebra. -/
theorem finiteLength_submodule_of_restricted (A : WeakModule W M)
    (P : Submodule (modeAlg A) M)
    (hfin : IsFiniteLength (modeAlg (show WeakModule W P from
      WeakModule.submodule A (ofR A P))) P) :
    IsFiniteLength (modeAlg A) P := by
  apply finiteLength_of_mode_invariance (X := P)
    (show WeakModule W P from WeakModule.submodule A (ofR A P)) hfin
  intro Q a n x hx
  exact Q.smul_mem
    (⟨mode (A.YM a) n, Algebra.subset_adjoin ⟨a, n, rfl⟩⟩ : modeAlg A) hx

/-- The quotient weak action agrees with the ambient quotient ring action. -/
theorem finiteLength_quotient_of_descended (A : WeakModule W M)
    (P : Submodule (modeAlg A) M)
    (hfin : IsFiniteLength (modeAlg (show WeakModule W (M ⧸ P) from
      WeakModule.quotient A (ofR A P))) (M ⧸ P)) : IsFiniteLength (modeAlg A) (M ⧸ P) := by
  let B : WeakModule W (M ⧸ P) := WeakModule.quotient A (ofR A P)
  apply finiteLength_of_mode_invariance (R := modeAlg A) (X := M ⧸ P) B hfin
  intro Q a n x hx
  let r : modeAlg A := ⟨mode (A.YM a) n, Algebra.subset_adjoin ⟨a, n, rfl⟩⟩
  have he : B.act a n x = r • x := by
    induction x using Submodule.Quotient.induction_on with
    | H y => exact WeakModule.quotient_act_mk A (ofR A P) a n y
  rw [he]
  exact Q.smul_mem r hx

/-- A surjective weak-module homomorphism takes a cyclic generator to a cyclic generator. -/
theorem cyclic_eq_top_of_surjective_hom
    {X : Type v} [AddCommGroup X] [Module ℂ X]
    (A : WeakModule W M) (B : WeakModule W X) (f : A.Hom B)
    (hf : Function.Surjective f.toLinearMap) (x : M) (hx : cyclic A x = ⊤) :
    cyclic B (f.toLinearMap x) = ⊤ := by
  let Q := ofR B (cyclic B (f.toLinearMap x))
  let P : WeakModule.Submodule' A :=
    { carrier := Q.carrier.comap f.toLinearMap
      act_mem := by
        intro a n y hy
        change f.toLinearMap (A.act a n y) ∈ Q.carrier
        rw [f.map_act]
        exact Q.act_mem a n hy }
  have hle : cyclic A x ≤ toR A P :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (Submodule.mem_span_singleton_self (f.toLinearMap x)))
  rw [hx] at hle
  apply top_unique
  intro y _
  obtain ⟨z, rfl⟩ := hf y
  exact hle (Submodule.mem_top : z ∈ (⊤ : Submodule (modeAlg A) M))

end VOA.Classification.COne.PlusFiniteLength
