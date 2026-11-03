import VOA.Classification.COne.OrbPos11Fields

/-! # Removing the identity twist without changing the carrier or fields -/
noncomputable section
namespace VOA.Classification.COne.OrbPos11
open VOA OrbPos2
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- A period-one identity-twisted module is an ordinary module. -/
def identityTwistedOrdinary (T : TwistedModule (1 : Aut W) 1 M) : OrdVModule W M where
  toWeakModule := by
    let S : VOASubalgebra W :=
      ⟨⊤, trivial, trivial, fun _ _ _ _ _ => trivial, fun _ _ _ => trivial⟩
    let f : V →ₗ[ℂ] S.carrier := (LinearMap.id : V →ₗ[ℂ] V).codRestrict _ (fun _ => trivial)
    have hf : IsVOAHom W S.toVOA f := ⟨rfl, fun _ _ _ => rfl⟩
    exact ConverseUniverse.pullWeak hf (restrictedWeakModule T (by decide) S (fun _ => rfl))
  weight := T.weight
  isInternal := T.isInternal
  L0_weight α x hx := by
    change T.YM W.conformalVector (1 * (-(-1 - 1) - 1)) x = α • x
    norm_num
    exact T.L0_weight α x hx
  finrank := T.finrank
  boundedBelow := T.boundedBelow

@[simp] theorem identityTwistedOrdinary_mode (T : TwistedModule (1 : Aut W) 1 M)
    (v : V) (k : ℤ) : mode ((identityTwistedOrdinary T).YM v) k = T.YM v k := by
  change T.YM v (1 * (-(-k - 1) - 1)) = T.YM v k
  rw [show (1 : ℤ) * (-(-k - 1) - 1) = k by ring]

theorem identityTwistedOrdinary_irreducible (T : TwistedModule (1 : Aut W) 1 M)
    (hT : TwistedIrreducible T) : (identityTwistedOrdinary T).IsIrreducible := by
  refine ⟨hT.1, fun P => hT.2 P.carrier (fun v k x hx => ?_)⟩
  simpa only [WeakModule.act_def, identityTwistedOrdinary_mode] using P.act_mem v k hx

end VOA.Classification.COne.OrbPos11
