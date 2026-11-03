import VOA.Examples.AffineSl2ParabolicExact
import VOA.Examples.AffineSl2VacuumExactSequence

/-! # The zeroth parabolic module is the actual universal affine vacuum module -/
namespace VOA.AffineVOA.HighestModule
noncomputable section
open AffineLie UniversalEnvelopingAlgebra

/-- Equality of the actual defining left ideals, with no character comparison. -/
theorem parabolicIdeal_zero (k : ℂ) :
    parabolicIdeal k 0 = vacuumIdeal kappaForm kappaForm_isInvariant k := by
  simp only [parabolicIdeal,parabolicRelation,Nat.cast_zero,zero_add,pow_one]
  apply le_antisymm
  · apply sup_le
    · intro u hu
      have hz : (Submodule.Quotient.mk u : Verma k 0)=0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hu
      have he := congrArg (vacuumProjection k) hz
      rw [vacuumProjection_mk,map_zero,Submodule.Quotient.mk_eq_zero] at he
      exact he
    · apply Submodule.span_le.mpr
      intro u hu
      rcases Set.mem_singleton_iff.mp hu with rfl
      exact vacuumGens_subset_ideal _ _ k (Or.inl ⟨basis 1,0,by omega,rfl⟩)
  · intro u hu
    obtain ⟨v,hv⟩ := vacuum_ideal_range k u hu
    obtain ⟨a,rfl⟩ := Submodule.Quotient.mk_surjective (highestIdeal k (-2)) v
    rw [horizontalEmbedding_mk] at hv
    have hh : (Submodule.Quotient.mk (a*ι ℂ (modeElement 1 0)) : Verma k 0)=
        Submodule.Quotient.mk u := by
      simpa only [horizontalVector,mode,highestVector,rho_mk,mul_one,
        ← Submodule.Quotient.mk_smul,smul_eq_mul] using hv
    rw [Submodule.Quotient.eq] at hh
    let P : Submodule U U := highestIdeal k 0 ⊔ Submodule.span U {ι ℂ (modeElement 1 0)}
    have hleft : a*ι ℂ (modeElement 1 0) ∈ P :=
      (show Submodule.span U {ι ℂ (modeElement 1 0)} ≤ P from le_sup_right)
        (Submodule.mem_span_singleton.mpr ⟨a,rfl⟩)
    have hdiff : a*ι ℂ (modeElement 1 0)-u ∈ P :=
      (show highestIdeal k 0 ≤ P from le_sup_left) hh
    have heq : u = a*ι ℂ (modeElement 1 0)-(a*ι ℂ (modeElement 1 0)-u) := by abel
    rw [heq]
    exact P.sub_mem hleft hdiff

/-- The actual base term of the parabolic resolution identifies with the
universal vacuum carrier by the same enveloping representatives. -/
def parabolicVacuumEquiv (k : ℂ) : Parabolic k 0 ≃ₗ[ℂ] WakModule k :=
  (Submodule.quotEquivOfEq _ _ (parabolicIdeal_zero k)).restrictScalars ℂ

@[simp] theorem parabolicVacuumEquiv_mk (k : ℂ) (u : U) :
    parabolicVacuumEquiv k (Submodule.Quotient.mk u)=Submodule.Quotient.mk u := rfl

@[simp] theorem parabolicVacuumEquiv_highest (k : ℂ) :
    parabolicVacuumEquiv k (parabolicHighest k 0)=vacuumA k := rfl

/-- The carrier identification preserves every actual affine current. -/
theorem parabolicVacuumEquiv_mode (k : ℂ) (a : Fin 3) (n : ℤ) (u : Parabolic k 0) :
    parabolicVacuumEquiv k (parabolicMode k 0 a n u)=J k a n (parabolicVacuumEquiv k u) := by
  obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective (parabolicIdeal k 0) u
  rfl

end
end VOA.AffineVOA.HighestModule
