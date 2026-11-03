import VOA.DeligneAudit.D4FusionRealizationSmallCharacter
import VOA.DeligneAudit.DeligneFusionD1SiteGSat
import VOA.DeligneAudit.D4FusionKernelGeneric
import VOA.DeligneAudit.DeligneFusionD1SiteGD4
import VOA.DeligneAudit.DeligneFusionD1SiteGGraded
import VOA.DeligneAudit.DeligneCharacterD4Positivity

/-! Actual D4 Demazure realizations at n = 0 and n = 1. The complete
coefficient comparisons use the trivial module and the explicit coadjoint
module plus a line. No realization assumption is used. -/
namespace VOA.DeligneAudit.D4Small

open PowerSeries
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneCharacter
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

/-- The full integer coefficient function, including all higher zeros. -/
theorem hilbInt_one (N : ℕ) :
    D4K.hilbInt 1 N = if N = 0 then 28 else if N = 1 then 1 else 0 := by
  unfold D4K.hilbInt
  rw [cartanD4, VOA.DeligneAudit.DeligneCharacter.thetaD4, wordD4, charOne_eq]
  simpa using charOne_coeff N

theorem hilbInt_zero (N : ℕ) : D4K.hilbInt 0 N = if N = 0 then 1 else 0 := by
  by_cases h : N = 0
  · subst N; rfl
  have h' : (0 : ℤ) ≠ (N : ℤ) := by omega
  simp [D4K.hilbInt, demazureChar, h, h']

def trivialCurrent {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) : CurrentModule f ℂ where
  op _ _ := 0
  comm _ _ _ _ _ := by simp

private theorem trivial_word {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ)
    (x : Fin n × ℕ) (l : List (Fin n × ℕ)) :
    wordOp (trivialCurrent f) (x :: l) 1 = 0 := rfl

/-- The zero highest weight presentation holds in the actual trivial module. -/
theorem trivial_sat (S : DeligneSectorData) :
    Sat S.f (trivialCurrent S.f) 1 (ravFam S 0 0) := by
  constructor
  · intro t ht
    simp only [ravFam, ravSpec, Nat.mul_zero, zero_mul, zero_add, Set.mem_setOf_eq] at ht
    rcases ht with ⟨e, r, he, rfl⟩ | ⟨h, r, hh, hr, rfl⟩ |
      ⟨i, hi, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨h, r, hh, hr, rfl⟩
    all_goals rfl
  · rintro q (⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩) <;>
      simp [trivialCurrent]

/-- D4 U7 at n = 0, with no named input. -/
theorem demazureRealization_zero :
    DemazureRealizationG D4sector (ravFam D4sector) D4Wp.hilbSeriesZ 0 := by
  refine ⟨ℂ, inferInstance, inferInstance, trivialCurrent D4sector.f, 1,
    trivial_sat D4sector, fun N => ?_⟩
  rw [D4Wp.hilbSeriesZ, coeff_mk, hilbInt_zero]
  by_cases h : N = 0
  · subst N
    have hm : (1 : ℂ) ∈ cycDeg (trivialCurrent D4sector.f) 1 0 :=
      Submodule.subset_span ⟨[], rfl, rfl⟩
    have htop : cycDeg (trivialCurrent D4sector.f) 1 0 = ⊤ := by
      apply top_unique
      intro x _
      simpa using Submodule.smul_mem _ x hm
    simp [htop]
  · simp [h]

/-- D4 U7 at n = 1 from the constructed site and its exact degree ranks. -/
theorem demazureRealization_one :
    DemazureRealizationG D4sector (ravFam D4sector) D4Wp.hilbSeriesZ 1 := by
  let hs : ∀ a b c, D4sector.f a b c = -D4sector.f b a c :=
    D1SiteG.D4Check.table_skewC
  let R := D1SiteG.rep D4sector.f D4sector.jacobi hs
  let w := D1SiteG.w D4sector.c₀
  have hspec : D1SiteG.oneSiteSpec D4sector = ravFam D4sector 1 0 := by
    simp only [D1SiteG.oneSiteSpec, ravFam, ravSpec, Nat.add_zero, Nat.mul_one, one_mul]
  have hsat : Sat D4sector.f R w (ravFam D4sector 1 0) := by
    rw [← hspec]
    exact D1SiteG.site_sat D4sector hs
  refine ⟨D1SiteG.Space 28, inferInstance, inferInstance, R, w, hsat, fun N => ?_⟩
  rw [D4Wp.hilbSeriesZ, coeff_mk, hilbInt_one]
  by_cases h0 : N = 0
  · subst N
    have hdim := D1SiteG.finrank_cycDeg_zero D4sector.f D4sector.jacobi hs
      D4sector.c₀ 10 D1SiteG.D4Check.coadjoint_cyclic
    change (28 : ℚ) ≤ (Module.finrank ℂ (cycDeg R w 0) : ℚ)
    rw [hdim]
    exact le_rfl
  by_cases h1 : N = 1
  · subst N
    have hdim := D1SiteG.finrank_cycDeg_one D4sector.f D4sector.jacobi hs D4sector.c₀
    simp only [show (1 : ℕ) ≠ 0 by decide, if_false, if_true, Int.cast_one]
    change (1 : ℚ) ≤ (Module.finrank ℂ (cycDeg R w 1) : ℚ)
    rw [hdim]
    norm_num
  · simp [h0, h1]

end
end VOA.DeligneAudit.D4Small

#print axioms VOA.DeligneAudit.D4Small.demazureRealization_zero
#print axioms VOA.DeligneAudit.D4Small.demazureRealization_one
