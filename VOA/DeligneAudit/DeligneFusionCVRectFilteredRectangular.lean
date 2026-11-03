import VOA.DeligneAudit.DeligneFusionCVRectFilteredCases
import VOA.DeligneAudit.DeligneFusionCVRectFilteredCutoff
import VOA.DeligneAudit.DeligneFusionCVTotal

/-!
# Proved sharp mixed rectangular base bounds for the actual CV modules

The source relations, PBW symbol exactness, canonical polynomial action,
STAR quotient product count, and filtered dimension transfer are all proved.
No coefficient family, annihilator inclusion, original finite-dimensionality,
KR identification, or rectangular dimension bound is a premise here.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVRectCommutative
open VOA.DeligneAudit.A2.CVRectStarCount

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ε ν ϱ : Weight}

/-- The actual cyclic mixed rectangular source has the sharp product bound.
Every coefficient relation used in the polynomial quotient map is proved. -/
theorem rectangular_source_bound (h : CV3Rel R w ε ν ϱ 0)
    (hε : ε = (0, 0) ∨ ε = (1, 0) ∨ ε = (0, 1))
    (hspan : currentCyclic R w = ⊤) :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤
      3 ^ (ε.1 + ε.2) * 6 ^ (ν.1 + ν.2) * 10 ^ (ϱ.1 + ϱ.2) := by
  have hx : ∀ t, (parts ϱ.1 ν.1 ε.1).length ≤ t → R.op 3 t w = 0 := by
    intro t ht
    apply trunc_of_cvrel h.first
    simpa only [Nat.add_zero] using ht
  have hz : ∀ t, (parts ϱ.2 ν.2 ε.2).length ≤ t → R.op 4 t w = 0 := by
    intro t ht
    apply trunc_of_cvrel h.second
    simpa only [Nat.add_zero] using ht
  have hy : ∀ t, (parts ϱ.1 ν.1 ε.1).length + (parts ϱ.2 ν.2 ε.2).length +
      ([] : List ℕ).length ≤ t → R.op 5 t w = 0 := by
    intro t ht
    apply trunc_of_cvrel h.highest
    simp only [parts_length, List.length_nil] at ht ⊢
    omega
  have hb := source_star_bound_of_clipped R w h hspan
    (parts ϱ.1 ν.1 ε.1) (parts ϱ.2 ν.2 ε.2) [] hx hy hz (by
      intro p q r s hs
      apply orderedCoeff_all_small_mem h hε p q r s
      simpa only [clippedSum, List.map_nil, List.sum_nil, Nat.add_zero] using hs)
  refine ⟨hb.1, ?_⟩
  simpa only [parts, starWeight_parts, List.map_nil, List.prod_nil, mul_one] using hb.2

end

end VOA.DeligneAudit.A2.CVRectFiltered

namespace VOA.DeligneAudit.A2.CVUniv

open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVRectFiltered

noncomputable section

/-- The sharp mixed rectangular base family is proved
for the actual universal CV modules. No mathematical base input is assumed. -/
theorem sharpRectangularBases : SharpRectangularBases := by
  intro ε ν ϱ hε
  have hspan : currentCyclic (cvUnivRep ε ν ϱ 0) (cv_wU ε ν ϱ 0) = ⊤ :=
    cv_span_top ε ν ϱ 0
  obtain ⟨hFD, hdim⟩ := rectangular_source_bound (cvUniv_rel ε ν ϱ 0) hε hspan
  exact ⟨hFD, by simpa only [cvCount, pow_zero, mul_one] using hdim⟩

end

end VOA.DeligneAudit.A2.CVUniv

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.rectangular_source_bound
#print axioms VOA.DeligneAudit.A2.CVUniv.sharpRectangularBases
