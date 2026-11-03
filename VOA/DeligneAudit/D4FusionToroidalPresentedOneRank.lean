import VOA.DeligneAudit.D4FusionToroidalPresentedOneEquiv
import VOA.DeligneAudit.D4FusionContactOne
import VOA.DeligneAudit.D4FusionTruncatedWeyl

/-! The multiplicity-one rank bound reduced to stability of the extra line. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.SectorGraded
open VOA.DeligneAudit.DeligneSector

noncomputable section

def oneTop : OneU :=
  (univRepG D4sector.f OneR).op D4sector.c₀ 1 (wUG D4sector.f OneR)

theorem oneTop_killed_high (c : Fin 28) (r : ℕ) (hr : 2 ≤ r) :
    (univRepG D4sector.f OneR).op c r oneTop = 0 := by
  let ρ := univRepG D4sector.f OneR
  let w := wUG D4sector.f OneR
  have hk := rav_high_kills_generator (m := 1) (R := ρ) (w := w)
    (by omega) (univG_sat D4sector.f OneR)
  have hc := ρ.comm c D4sector.c₀ r 1 w
  have hz : (∑ e, D4sector.f c D4sector.c₀ e • ρ.op e (r + 1) w) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    rw [hk e (r + 1) (by omega)]
    simp
  rw [hk c r hr, map_zero, hz, sub_zero] at hc
  simpa [oneTop, ρ, w] using hc

def oneTopLine : Submodule ℂ OneU := Submodule.span ℂ {oneTop}

def OneTopLineKilled : Prop :=
  ∀ c r, (univRepG D4sector.f OneR).op c r oneTop = 0

theorem oneTopLine_inv (h : OneTopLineKilled) :
    ∀ c r, oneTopLine ≤
      oneTopLine.comap ((univRepG D4sector.f OneR).op c r) := by
  intro c r
  rw [oneTopLine, Submodule.span_le]
  intro x hx
  have hx : x = oneTop := Set.mem_singleton_iff.mp hx
  subst x
  change (univRepG D4sector.f OneR).op c r oneTop ∈ oneTopLine
  rw [h c r]
  exact Submodule.zero_mem _

private def oneQuotRep (h : OneTopLineKilled) :
    CurrentModule D4sector.f (OneU ⧸ oneTopLine) :=
  quotRepG (univRepG D4sector.f OneR) oneTopLine (oneTopLine_inv h)

private def oneQuotGen : OneU ⧸ oneTopLine :=
  oneTopLine.mkQ (wUG D4sector.f OneR)

theorem oneQuot_localWeyl (h : OneTopLineKilled) :
    LocalWeylRelG D4sector (oneQuotRep h) oneQuotGen 1 := by
  have hs : SpecStep OneR (ravSpec D4sector 1 1) [(D4sector.c₀, 1)] := by
    simpa [OneR, ravFam_zero_right] using ravSpec_step D4sector 1 2 1
  have hk : wordOp (univRepG D4sector.f OneR) [(D4sector.c₀, 1)]
      (wUG D4sector.f OneR) ∈ oneTopLine := by
    exact Submodule.subset_span (Set.mem_singleton oneTop)
  have hq := sat_quotG oneTopLine (oneTopLine_inv h)
    (univG_sat D4sector.f OneR) hs hk
  apply (localWeylRelG_iff D4sector (oneQuotRep h) oneQuotGen 1).mpr
  simpa only [ravSpec_self] using hq

theorem oneQuot_cycZero_top (h : OneTopLineKilled) :
    cycDeg (oneQuotRep h) oneQuotGen 0 = ⊤ := by
  let Q := cycDeg (oneQuotRep h) oneQuotGen 0
  have hw (l : List (Ltr 28)) :
      wordOp (oneQuotRep h) l oneQuotGen ∈ Q := by
    by_cases hd : VOA.DeligneAudit.SectorGraded.wordDeg l = 0
    · exact Submodule.subset_span ⟨l, hd, rfl⟩
    · have hp : 0 < VOA.DeligneAudit.SectorGraded.wordDeg l := by omega
      have hm : wordOp (oneQuotRep h) l oneQuotGen ∈
          cycDeg (oneQuotRep h) oneQuotGen
            (VOA.DeligneAudit.SectorGraded.wordDeg l) :=
        Submodule.subset_span ⟨l, rfl, rfl⟩
      rw [D4FusionContact.localWeyl_one_cycDeg_eq_bot
        (oneQuot_localWeyl h) (VOA.DeligneAudit.SectorGraded.wordDeg l) hp] at hm
      rw [Submodule.mem_bot] at hm
      rw [hm]
      exact Submodule.zero_mem Q
  have hall : ∀ y : OneU, oneTopLine.mkQ y ∈ Q := by
    intro y
    have hy : y ∈ Submodule.span ℂ
        (Set.range fun l : List (Ltr 28) =>
          wordOp (univRepG D4sector.f OneR) l (wUG D4sector.f OneR)) := by
      have ht := D4FusionContact.Polynomial.universal_word_span D4sector.f OneR
      exact ht.symm ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨l, rfl⟩ := hy
        rw [← quot_wordOpG (univRepG D4sector.f OneR) oneTopLine
          (oneTopLine_inv h) (wUG D4sector.f OneR) l]
        exact hw l
    | zero => exact Submodule.zero_mem Q
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem Q hx hy
    | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem Q a hx
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective oneTopLine x
  exact hall y

theorem oneUniv_rank_of_line_killed (h : OneTopLineKilled) :
    Module.finrank ℂ OneU ≤ 29 := by
  letI : FiniteDimensional ℂ OneU := rav_finiteDimensional 1 (by omega)
  have h0 := D4FusionContact.localWeyl_one_zero_bound (oneQuot_localWeyl h)
  have hq : Module.finrank ℂ (OneU ⧸ oneTopLine) ≤ 28 := by
    haveI : FiniteDimensional ℂ (OneU ⧸ oneTopLine) := inferInstance
    have hle : (⊤ : Submodule ℂ (OneU ⧸ oneTopLine)) ≤
        cycDeg (oneQuotRep h) oneQuotGen 0 := by
      rw [oneQuot_cycZero_top h]
    have hr := (Submodule.finrank_mono hle).trans h0.2
    simpa using hr
  have hl : Module.finrank ℂ oneTopLine ≤ 1 := by
    simpa [oneTopLine] using
      (finrank_span_le_card (R := ℂ) (s := ({oneTop} : Set OneU)))
  calc
    Module.finrank ℂ OneU =
        Module.finrank ℂ (OneU ⧸ oneTopLine) + Module.finrank ℂ oneTopLine :=
      (oneTopLine.finrank_quotient_add_finrank).symm
    _ ≤ 28 + 1 := Nat.add_le_add hq hl
    _ = 29 := by norm_num

theorem presentedRankBoundE_one_of_line_killed (h : OneTopLineKilled) :
    PresentedRankBoundE 1 (le_refl 1) := by
  letI : FiniteDimensional ℂ OneU := rav_finiteDimensional 1 (by omega)
  letI : FiniteDimensional ℂ (PTE 1) := Module.Finite.equiv presentedOneEquiv.symm
  change FiniteDimensional ℂ (PTE 1) ∧ Module.finrank ℂ (PTE 1) ≤ 29 ^ 1
  refine ⟨inferInstance, ?_⟩
  simpa only [pow_one, presentedOneEquiv.finrank_eq] using
    oneUniv_rank_of_line_killed h

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.oneQuot_localWeyl
#print axioms VOA.DeligneAudit.Toroidal.oneTop_killed_high
#print axioms VOA.DeligneAudit.Toroidal.oneTopLine_inv
#print axioms VOA.DeligneAudit.Toroidal.oneQuot_cycZero_top
#print axioms VOA.DeligneAudit.Toroidal.oneUniv_rank_of_line_killed
#print axioms VOA.DeligneAudit.Toroidal.presentedRankBoundE_one_of_line_killed
