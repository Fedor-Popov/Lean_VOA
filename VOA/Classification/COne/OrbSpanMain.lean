import VOA.Classification.COne.OrbSpanTetra
import VOA.Classification.COne.OrbSpanLattice
import VOA.Classification.COne.OrbSpanConverse

/-! # OrbSpan: headlines

* `v2VirUnitary_holds`: `V₂` is Virasoro-unitary (no hypotheses).
* `virPrimaryDecomp_orbifold`: every orbifold `V_{2m}^G` (indeed every subalgebra) is spanned,
  weight by weight, by Virasoro primaries and lower descendants (no hypotheses).
* `tetrahedralVirasoroSpan_iff_primaryReduction`: the B2 span input `TetrahedralVirasoroSpan`
  is EQUIVALENT to `TetraPrimaryReduction` (a statement about Virasoro primaries only).
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbSpan
open VOA VertexOperatorAlgebra OrbC2b OrbC2c OrbC2Fix VOA.LatGen VOA.LatGen.Triplet

/-- `V_{2m}` is Virasoro-unitary. -/
def v2mVirUnitary (m : ℕ) (hm : 1 ≤ m) : VirUnitaryForm (V2m m hm) :=
  latticeVirUnitary (latP m) (latP_even m) (latP_posDef m hm)

theorem v2VirUnitary_holds : V2VirUnitary := ⟨v2mVirUnitary 1 le_rfl⟩

/-- Primary decomposition for every orbifold of `V_{2m}`. -/
theorem virPrimaryDecomp_orbifold (m : ℕ) (hm : 1 ≤ m) (G : Subgroup (Aut (V2m m hm))) :
    VirPrimaryDecomp (orbifoldVOA G) :=
  virPrimaryDecomp_of_subalgebra (v2mVirUnitary m hm) (orbifold G)

theorem tetraPrimaryDecomp : VirPrimaryDecomp (orbifoldVOA tetra) :=
  virPrimaryDecomp_orbifold 1 le_rfl tetra

/-- **B2 span input reduced to a statement about primaries.** -/
theorem tetrahedralVirasoroSpan_of_primaryReduction (hG : TetraPrimaryReduction) :
    TetrahedralVirasoroSpan :=
  tetrahedralVirasoroSpan_of_decomp tetraPrimaryDecomp hG

/-- The reduction is exact. -/
theorem tetrahedralVirasoroSpan_iff_primaryReduction :
    TetrahedralVirasoroSpan ↔ TetraPrimaryReduction := by
  constructor
  · rintro ⟨u, v, hu, hv, h⟩
    exact ⟨u, v, hu, hv, (dongJiangVirasoroSpan_iff_primary _ tetraPrimaryDecomp hu hv).mp h⟩
  · exact tetrahedralVirasoroSpan_of_primaryReduction

theorem tetrahedralConformalSpan_of_primaryReduction (hG : TetraPrimaryReduction) :
    TetrahedralConformalSpan :=
  tetrahedralConformalSpan_of_unitary v2VirUnitary_holds hG

/-- `C₂` for `V₂^{A₄}` from the primary reduction and the corrected relations. -/
theorem tetra_c2Cofinite_of_primaryReduction (hG : TetraPrimaryReduction)
    (hr : TetrahedralDongJiangRelationsCorrected) : C2Cofinite (orbifoldVOA tetra) :=
  tetra_c2Cofinite_of_unitary v2VirUnitary_holds hG hr

end VOA.Classification.COne.OrbSpan
