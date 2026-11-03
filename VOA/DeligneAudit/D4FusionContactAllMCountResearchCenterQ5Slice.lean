import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterQ5Ideal
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterUStatic

/-! The quintic slice modulo J234 (the literal polar ideal of source powers
2, 3, 4) is spanned by ONE static quintic polar Q5 = coeff_(2m-3) of the
(2,2,2)-lowered fifth power. Every quintic U row is 5^(number of shifts) Q5
modulo J234, the static quartic rows and J23 lie in J234, and the C branch was
already reduced to J23. Membership only; no dimension of the quotient is claimed. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D4FusionContact.Polynomial
open Cube (polarRangeIdeal)
noncomputable section

/-- The single static quintic polar of the slice. -/
def quinticStaticPolar (m : ℕ) : Ring ℂ m :=
  PowerSeries.coeff (2 * m - 3) (Cube.currentMap m (Cube.orbit ℂ 5 2 2 2))

theorem quinticStaticPolar_mem_candidate (m : ℕ) :
    quinticStaticPolar m ∈ AllM.candidateIdeal m :=
  Cube.current_orbit_coeff_mem m 5 2 2 2 (2 * m - 3) (by norm_num) (by omega)

/-- Every quintic U source is 5^(number of shifts) times its static polar, modulo J234. -/
theorem u_quintic_source_sub_static_mem (m : ℕ) (i : OrbitSourceIndex m)
    (hb : i.seed.val.1 = false) (hr : i.seed.val.2.1 = 5) :
    orbitSourcePoly m i - (5 ^ i.shifts.length) •
      PowerSeries.coeff (i.seed.val.2.2 + i.shifts.sum + (i.outer.map Prod.snd).sum)
        (Cube.currentMap m
          (Cube.orbit ℂ 5 (uAxisCount i 0) (uAxisCount i 1) (uAxisCount i 2))) ∈
      polarRangeIdeal m 4 := by
  have hth := u_seed_threshold m i hb
  rw [hr] at hth
  have h := Cube.shift_negativeModeWord_static_mem_polarRange m 4 i.seed.val.2.2
    i.shifts (i.outer.map toAxis) (by norm_num) (by omega)
  rw [toAxis_modes] at h
  rw [u_orbitSourcePoly_eq m i hb,hr]
  exact h

/-- MAIN (quintic rows): every matching quintic U row is 5^(shifts) Q5 modulo J234. -/
theorem quinticU5_row_sub_static_mem (m : ℕ)
    (q : OrbitSourceIndex m × ((Fin 9 × Fin m) →₀ ℕ))
    (hq : q ∈ boundedColorComponentPairs m 5 (2 * m - 3) (fun _ => 2))
    (hb : q.1.seed.val.1 = false) (hr : q.1.seed.val.2.1 = 5) :
    MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1 -
      (5 ^ q.1.shifts.length) • quinticStaticPolar m ∈ polarRangeIdeal m 4 := by
  obtain ⟨he,hs,ha⟩ := quinticU5_row_shape m q hq hb hr
  have h := u_quintic_source_sub_static_mem m q.1 hb hr
  rw [hs,ha 0,ha 1,ha 2] at h
  rw [he,← MvPolynomial.C_apply,MvPolynomial.C_1,one_mul]
  exact h

/-- Every static quartic polar of a U source is a literal J234 generator. -/
theorem uQuarticStatic_mem_polarRange (m : ℕ) (i : OrbitSourceIndex m)
    (hb : i.seed.val.1 = false) (hr : i.seed.val.2.1 = 4) :
    uQuarticStatic m i ∈ polarRangeIdeal m 4 := by
  have hth := u_seed_threshold m i hb
  unfold uQuarticStatic
  exact Cube.polarRange_coeff_mem m 4 4 _ _ _ _ (by norm_num) le_rfl (by omega)

/-- MAIN: modulo J234 the candidate quintic slice is spanned by the single static
quintic polar Q5 (m >= 2, inherited from the C-branch coverage). -/
theorem candidate_quintic_slice_eq_Q5_sup_polarRange (m : ℕ) (hm : 2 ≤ m) :
    (AllM.candidateIdeal m).restrictScalars ℂ ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m)
        (quinticColorDegree m) =
    (Submodule.span ℂ {quinticStaticPolar m} ⊔ (polarRangeIdeal m 4).restrictScalars ℂ) ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m)
        (quinticColorDegree m) := by
  apply le_antisymm
  · rw [candidate_quintic_slice_eq_U5_static_sup_polar m hm]
    apply inf_le_inf_right
    apply sup_le (sup_le ?_ ?_) ?_
    · apply Submodule.span_le.mpr
      rintro p ⟨q,⟨hq,hb,hr⟩,rfl⟩
      have hd := quinticU5_row_sub_static_mem m q hq hb hr
      change MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1 ∈ _
      rw [← sub_add_cancel (MvPolynomial.monomial q.2 (1 : ℂ) * orbitSourcePoly m q.1)
        ((5 ^ q.1.shifts.length) • quinticStaticPolar m)]
      exact Submodule.add_mem _ (Submodule.mem_sup_right hd)
        (Submodule.mem_sup_left (Submodule.smul_of_tower_mem _ _
          (Submodule.mem_span_singleton_self _)))
    · apply Submodule.span_le.mpr
      rintro p ⟨q,⟨-,hb,hr⟩,rfl⟩
      exact Submodule.mem_sup_right
        (Ideal.mul_mem_left _ _ (uQuarticStatic_mem_polarRange m q.1 hb hr))
    · intro p hp
      exact Submodule.mem_sup_right
        (Cube.quadraticCubicPolarIdeal_le_polarRange m 4 (by norm_num) hp)
  · intro p hp
    refine ⟨?_,hp.2⟩
    have hQ : Submodule.span ℂ {quinticStaticPolar m} ≤
        (AllM.candidateIdeal m).restrictScalars ℂ := by
      rw [Submodule.span_le,Set.singleton_subset_iff]
      exact quinticStaticPolar_mem_candidate m
    have hJ : (polarRangeIdeal m 4).restrictScalars ℂ ≤
        (AllM.candidateIdeal m).restrictScalars ℂ :=
      fun x hx => Cube.polarRangeIdeal_le_candidate m 4 hx
    exact (sup_le hQ hJ) hp.1

end
#print axioms u_quintic_source_sub_static_mem
#print axioms quinticU5_row_sub_static_mem
#print axioms uQuarticStatic_mem_polarRange
#print axioms candidate_quintic_slice_eq_Q5_sup_polarRange
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
