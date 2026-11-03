import VOA.Huang.LiFusionVacuum
import VOA.Huang.GenusOneZhuBridge
import VOA.Modularity.CharIndependenceAMod

/-! # Full simultaneous action on distinct irreducible tops

Jacobson density upgrades character separation to arbitrary endomorphisms on
all tops simultaneously. Completeness of the family and semisimplicity of the
whole Zhu algebra are not needed for this surjectivity assertion. Distinctness
is stated for the actual bottom `AMod`s. This discharges the `full` field of
`InsertionTopBimodule`; it does not construct its quotient actions.
-/
namespace VOA.Huang.GenusOne
open VOA FusionTop LiFusion
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {W : VertexOperatorAlgebra V} {ι : Type u} [Finite ι]

/-- Arbitrary endomorphisms of a finite family of pairwise nonisomorphic
irreducible bottoms are simultaneously realized by one VOA state. -/
theorem insertionTopRep_surjective (P : ι → LWModule W)
    (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod)) :
    Function.Surjective (insertionTopRep P) := by
  classical
  letI := Fintype.ofFinite ι
  letI := instRingA W
  letI := instAlgebraA W
  let r := Fintype.card ι
  let e : Fin r ≃ ι := (Fintype.equivFin ι).symm
  let P' := fun i => P (e i)
  let U := fun i => (P' i).toAMod
  letI : ∀ i, Module (VOA.A W) (U i).carrier := fun i => (U i).moduleA
  haveI : ∀ i, IsSimpleModule (VOA.A W) (U i).carrier := fun i =>
    (isSimpleAMod_iff_isSimpleModule (U i)).mp
      (LWBottomRecovery.isSimpleAMod_toAMod_of_irreducible (P' i) (hP (e i)))
  haveI : ∀ i, SMulCommClass (VOA.A W) ℂ (U i).carrier := fun i =>
    ⟨fun a c x => ((U i).ρ a).map_smul c x⟩
  haveI : ∀ i, FiniteDimensional ℂ (U i).carrier := fun i => (P' i).isMod.finrank _
  haveI : IsSemisimpleModule (VOA.A W) (∀ i, (U i).carrier) :=
    isSemisimpleModule_pi_of_simple _ fun _ => inferInstance
  haveI : SMulCommClass (VOA.A W) ℂ (∀ i, (U i).carrier) :=
    ⟨fun a c x => funext fun i => SMulCommClass.smul_comm a c (x i)⟩
  haveI : Module.Finite (Module.End (VOA.A W) (∀ i, (U i).carrier))
      (∀ i, (U i).carrier) :=
    Module.Finite.of_restrictScalars_finite ℂ _ _
  have hneA : ∀ i j : Fin r, i ≠ j →
      IsEmpty ((U i).carrier ≃ₗ[VOA.A W] (U j).carrier) := by
    intro i j hij
    refine ⟨fun d => (hne (e i) (e j) (fun h => hij (e.injective h))).false ?_⟩
    exact
      { toLinearEquiv :=
          { d.toAddEquiv with
            map_smul' := fun c x => by
              rw [← (U i).algebraMap_smul_eq, ← (U j).algebraMap_smul_eq]
              exact d.map_smul _ x }
        map_ρ := fun a x => d.map_smul a x }
  have hdiag (f : Module.End (VOA.A W) (∀ i, (U i).carrier)) (i : Fin r) :
      ∃ c : ℂ, ∀ x : ∀ j, (U j).carrier, f x i = c • x i := by
    let g : Module.End ℂ (U i).carrier :=
      { toFun := fun y => f (Pi.single i y) i
        map_add' := fun x y => by
          rw [Pi.single_add, map_add]
          rfl
        map_smul' := fun c y => by
          have hs : Pi.single i (c • y) =
              (algebraMap ℂ (VOA.A W) c) • (Pi.single i y : ∀ j, (U j).carrier) := by
            ext j
            by_cases hj : j = i
            · subst j; simp [(U i).algebraMap_smul_eq]
            · simp [Pi.single_eq_of_ne hj]
          rw [hs, f.map_smul]
          exact (U i).algebraMap_smul_eq _ _ }
    have hg (a : V) (y : bot (P' i)) :
        g (rhoLW (P' i).isMod (P' i).h a y) =
          rhoLW (P' i).isMod (P' i).h a (g y) := by
      change f (Pi.single i ((U i).ρ (VOA.mk W a) y)) i =
        (U i).ρ (VOA.mk W a) (f (Pi.single i y) i)
      have hs : Pi.single i ((U i).ρ (VOA.mk W a) y) =
          (VOA.mk W a) • (Pi.single i y : ∀ j, (U j).carrier) := by
        ext j
        by_cases hj : j = i
        · subst j; simp only [Pi.single_eq_same, Pi.smul_apply]; rfl
        · simp [Pi.single_eq_of_ne hj]
      rw [hs, f.map_smul]
      rfl
    obtain ⟨c, hc⟩ := bottom_endomorphism_scalar (P' i) (hP (e i)) g hg
    refine ⟨c, fun x => ?_⟩
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
    · exact congrArg (fun t : Module.End ℂ (bot (P' i)) => t (x i)) hc
    · intro j _ hji
      exact offDiag_eq_zero _ (fun _ => inferInstance) hneA f j i hji.symm (x j)
    · simp
  intro b
  let b' : ∀ i, Module.End ℂ (U i).carrier := fun i => b (e i)
  let F : Module.End (Module.End (VOA.A W) (∀ i, (U i).carrier))
      (∀ i, (U i).carrier) :=
    { toFun := fun x i => b' i (x i)
      map_add' := fun x y => funext fun i => map_add (b' i) _ _
      map_smul' := fun f x => by
        funext i
        obtain ⟨c, hc⟩ := hdiag f i
        change b' i (f x i) = f (fun j => b' j (x j)) i
        rw [hc, hc, map_smul] }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective
    (R := VOA.A W) (M := ∀ i, (U i).carrier) F
  obtain ⟨v, rfl⟩ := VOA.mk_surjective W a
  refine ⟨v, funext fun k => ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective k
  apply LinearMap.ext
  intro y
  have he := congrArg (fun t => t (Pi.single i y) i) ha
  change ((VOA.mk W v) • (Pi.single i y : ∀ j, (U j).carrier)) i =
    b' i ((Pi.single i y : ∀ j, (U j).carrier) i) at he
  simp only [Pi.smul_apply, Pi.single_eq_same] at he
  exact he

end VOA.Huang.GenusOne
