import VOA.Classification.COne.OrbSpanUnitary
import VOA.Classification.COne.OrbC2Fix

/-! # OrbSpan: the tetrahedral Virasoro span, reduced

`OrbC2c.TetrahedralVirasoroSpan` (Dong--Jiang Lemma 4.2 for `V₂^{A₄}`) is reduced to

* `V2VirUnitary`: a positive-definite Hermitian form on `V₂` with `L(n)† = L(-n)`; and
* `TetraPrimaryReduction`: every Virasoro primary of `V₂^{A₄}` of weight `N` lies in
  `C₂ + span{𝟙, u, v, u₍ₙ₎u} + Σ_{m≥1} L(-m) W_{N-m}` for some `u ∈ W₉`, `v ∈ W₁₆`.

`tetrahedralVirasoroSpan_iff_towers` records the exact `A₂`-tower form of the target.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbSpan
open VOA VertexOperatorAlgebra OrbC2b OrbC2c OrbC2Fix

/-- Virasoro unitarity of `V₂` (true; standard Fock-space form). -/
def V2VirUnitary : Prop := Nonempty (VirUnitaryForm (V2m 1 le_rfl))

/-- OPEN: the statement about primaries left after the decomposition. -/
def TetraPrimaryReduction : Prop :=
  ∃ u v : (orbifold tetra).carrier,
    u ∈ (orbifoldVOA tetra).grading 9 ∧ v ∈ (orbifoldVOA tetra).grading 16 ∧
    PrimaryC2Reduction (orbifoldVOA tetra) (djSeedSet (orbifoldVOA tetra) u v)

theorem tetraPrimaryDecomp_of_unitary (h : V2VirUnitary) :
    VirPrimaryDecomp (orbifoldVOA tetra) :=
  virPrimaryDecomp_of_subalgebra h.some (orbifold tetra)

/-- Exact `A₂`-tower form of the target. -/
theorem tetrahedralVirasoroSpan_iff_towers :
    TetrahedralVirasoroSpan ↔ ∃ u v : (orbifold tetra).carrier,
      u ∈ (orbifoldVOA tetra).grading 9 ∧ v ∈ (orbifoldVOA tetra).grading 16 ∧
      towerSpan (orbifoldVOA tetra) (seedFamily (orbifoldVOA tetra) u v) = ⊤ := by
  constructor
  · rintro ⟨u, v, hu, hv, h⟩
    exact ⟨u, v, hu, hv, (dongJiangVirasoroSpan_iff_towerSpan _ u v).mp h⟩
  · rintro ⟨u, v, hu, hv, h⟩
    exact ⟨u, v, hu, hv, (dongJiangVirasoroSpan_iff_towerSpan _ u v).mpr h⟩

/-- The target from a primary decomposition and the primary reduction. -/
theorem tetrahedralVirasoroSpan_of_decomp (hD : VirPrimaryDecomp (orbifoldVOA tetra))
    (hG : TetraPrimaryReduction) : TetrahedralVirasoroSpan := by
  obtain ⟨u, v, hu, hv, h⟩ := hG
  exact ⟨u, v, hu, hv, dongJiangVirasoroSpan_of_primary _ u v hD h⟩

/-- **B2 span reduction.** -/
theorem tetrahedralVirasoroSpan_of_unitary (hU : V2VirUnitary) (hG : TetraPrimaryReduction) :
    TetrahedralVirasoroSpan :=
  tetrahedralVirasoroSpan_of_decomp (tetraPrimaryDecomp_of_unitary hU) hG

theorem tetrahedralConformalSpan_of_unitary (hU : V2VirUnitary) (hG : TetraPrimaryReduction) :
    TetrahedralConformalSpan :=
  tetrahedralConformalSpan_of_virasoroSpan (tetrahedralVirasoroSpan_of_unitary hU hG)

/-- `C₂` for `V₂^{A₄}` from unitarity, the primary reduction and the corrected relations. -/
theorem tetra_c2Cofinite_of_unitary (hU : V2VirUnitary) (hG : TetraPrimaryReduction)
    (hr : TetrahedralDongJiangRelationsCorrected) : C2Cofinite (orbifoldVOA tetra) :=
  tetra_c2Cofinite_of_dongJiang_corrected (tetrahedralConformalSpan_of_unitary hU hG) hr

end VOA.Classification.COne.OrbSpan
