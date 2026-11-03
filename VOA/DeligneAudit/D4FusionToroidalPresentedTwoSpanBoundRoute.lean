import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSpanQuotient

/-! The two local Weyl checks imply the sharp positive-span rank bound. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector

noncomputable section

def twoPositiveToOne : twoPositiveSpan →ₗ[ℂ] twoOneQuot :=
  (twoM 1).mkQ.comp twoPositiveSpan.subtype

theorem twoPositiveToOne_range_le :
    LinearMap.range twoPositiveToOne ≤ cycSubG twoOneCurrent twoOneGen := by
  rintro q ⟨x, rfl⟩
  have hle : twoPositiveSpan ≤
      (cycSubG twoOneCurrent twoOneGen).comap (twoM 1).mkQ :=
    le_of_eq twoPositiveSpan_comap
  exact hle x.property

def twoPositiveKerToM : (LinearMap.ker twoPositiveToOne) →ₗ[ℂ] twoM 1 where
  toFun x := ⟨x.1.1, by
    have hx : (twoM 1).mkQ x.1.1 = 0 := x.property
    exact (Submodule.Quotient.mk_eq_zero _).mp hx⟩
  map_add' x y := Subtype.ext rfl
  map_smul' a x := Subtype.ext rfl

theorem twoPositiveKerToM_injective : Function.Injective twoPositiveKerToM := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  simpa [twoPositiveKerToM] using congrArg Subtype.val h

theorem twoPositiveSpanBound_of_localWeyl
    (h₁ : LocalWeylRelG D4sector twoCurrent (twoGen 1) 1)
    (h₀ : LocalWeylRelG D4sector twoOneCurrent twoOneGen 1) :
    TwoPositiveSpanBound := by
  have hM := twoM_one_rank_bound_of_localWeyl h₁
  have hQ := one_cycSubG_rank_bound twoOneCurrent twoOneGen h₀
  letI : FiniteDimensional ℂ (twoM 1) := hM.1
  letI : FiniteDimensional ℂ (cycSubG twoOneCurrent twoOneGen) := hQ.1
  haveI : FiniteDimensional ℂ ((twoM 1).mkQ.ker) := by
    rw [Submodule.ker_mkQ]
    exact hM.1
  have hfinite : FiniteDimensional ℂ twoPositiveSpan := by
    rw [twoPositiveSpan_comap]
    infer_instance
  letI : FiniteDimensional ℂ twoPositiveSpan := hfinite
  have hrange : Module.finrank ℂ (LinearMap.range twoPositiveToOne) ≤ 28 :=
    (Submodule.finrank_mono twoPositiveToOne_range_le).trans hQ.2
  have hker : Module.finrank ℂ (LinearMap.ker twoPositiveToOne) ≤ 28 :=
    (LinearMap.finrank_le_finrank_of_injective twoPositiveKerToM_injective).trans hM.2
  have hsum := twoPositiveToOne.finrank_range_add_finrank_ker
  exact ⟨hfinite, by omega⟩

theorem presentedRankBoundE_two_of_localWeyl
    (h₁ : LocalWeylRelG D4sector twoCurrent (twoGen 1) 1)
    (h₀ : LocalWeylRelG D4sector twoOneCurrent twoOneGen 1) :
    PresentedRankBoundE 2 (by norm_num) :=
  presentedRankBoundE_two_of_span (twoPositiveSpanBound_of_localWeyl h₁ h₀)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoPositiveToOne_range_le
#print axioms VOA.DeligneAudit.Toroidal.twoPositiveKerToM_injective
#print axioms VOA.DeligneAudit.Toroidal.twoPositiveSpanBound_of_localWeyl
#print axioms VOA.DeligneAudit.Toroidal.presentedRankBoundE_two_of_localWeyl
