import VOA.DeligneAudit.DeligneFusionCVRectAdjointFamily
import VOA.DeligneAudit.DeligneFusionCVRectAdjointFiveOrder

/-! # Exact finite-coordinate form of the five-monomial tail -/

namespace VOA.DeligneAudit.A2.CVRectAdjointFiveFamily

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectStarBase
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectAdjointOrder
open VOA.DeligneAudit.A2.CVRectAdjointFiveOrder
open VOA.DeligneAudit.A2.CVRectAdjointFamily

noncomputable section

abbrev FiveTailFamily (active center : List ℕ) :=
  Model (active.length + 1) (active.length + center.length + 1) 0
    (fiveTailOrder active center)

abbrev ThreeTailFamily (active center : List ℕ) :=
  Model (active.length + 1) (active.length + center.length + 1) 0
    (threeTailOrder active center)

abbrev TwoTailFamily (active center : List ℕ) :=
  Model active.length (active.length + center.length + 1) 0 (twoTailOrder active center)

def leafSwapIndex (L N R : ℕ) :
    (Fin L ⊕ (Fin N ⊕ Fin R)) ≃ (Fin R ⊕ (Fin N ⊕ Fin L)) where
  toFun
    | Sum.inl i => Sum.inr (Sum.inr i)
    | Sum.inr (Sum.inl j) => Sum.inr (Sum.inl j)
    | Sum.inr (Sum.inr k) => Sum.inl k
  invFun
    | Sum.inl k => Sum.inr (Sum.inr k)
    | Sum.inr (Sum.inl j) => Sum.inr (Sum.inl j)
    | Sum.inr (Sum.inr i) => Sum.inl i
  left_inv x := by cases x with
    | inl i => rfl
    | inr x => cases x <;> rfl
  right_inv x := by cases x with
    | inl k => rfl
    | inr x => cases x <;> rfl

def leafSwapVars (L N R : ℕ) : StarRing L N R ≃ₐ[ℂ] StarRing R N L :=
  MvPolynomial.renameEquiv ℂ (leafSwapIndex L N R)

theorem leafSwap_starX (L N R : ℕ) :
    PowerSeries.map (leafSwapVars L N R).toRingHom (starX L N R) = starZ R N L := by
  simp [starX, starZ, leafSwapVars, leafSwapIndex, MvPolynomial.renameEquiv_apply]

theorem leafSwap_starY (L N R : ℕ) :
    PowerSeries.map (leafSwapVars L N R).toRingHom (starY L N R) = starY R N L := by
  simp [starY, leafSwapVars, leafSwapIndex, MvPolynomial.renameEquiv_apply]

theorem leafSwap_starZ (L N R : ℕ) :
    PowerSeries.map (leafSwapVars L N R).toRingHom (starZ L N R) = starX R N L := by
  simp [starX, starZ, leafSwapVars, leafSwapIndex, MvPolynomial.renameEquiv_apply]

theorem coefficientIdeal3_swap {A : Type*} [CommRing A] (X Y Z : PowerSeries A)
    (μ : ℕ → ℕ → ℕ → ℕ) :
    coefficientIdeal3 Z Y X μ = coefficientIdeal3 X Y Z (fun p q r => μ r q p) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro P ⟨p, q, r, j, hj, rfl⟩
    apply Ideal.subset_span
    refine ⟨r, q, p, j, hj, ?_⟩
    congr 1
    ring
  · apply Ideal.span_le.mpr
    rintro P ⟨p, q, r, j, hj, rfl⟩
    apply Ideal.subset_span
    refine ⟨r, q, p, j, hj, ?_⟩
    congr 1
    ring

theorem five_tail_order (active center : List ℕ) :
    (fun p q r => fiveSiteOrder [] active center r q p) = fiveTailOrder active center := by
  funext p q r
  simp only [fiveSiteOrder, background, excess, List.map_nil, List.sum_nil,
    Nat.zero_add, fiveTailOrder, tailBackground, Nat.add_comm q p]

theorem five_tail_ideal_map (active center : List ℕ) :
    Ideal.map (leafSwapVars 0 (active.length + center.length + 1)
      (active.length + 1)).toRingHom
      (ideal 0 (active.length + center.length + 1) (active.length + 1)
        (fiveSiteOrder [] active center)) =
      ideal (active.length + 1) (active.length + center.length + 1) 0
        (fiveTailOrder active center) := by
  unfold ideal
  rw [coefficientIdeal3_map, leafSwap_starX, leafSwap_starY, leafSwap_starZ,
    coefficientIdeal3_swap, five_tail_order]

/-- The original no-xy-site five-shape quotient is the exact selected-z
tail family, by a coordinate permutation and equality of the full ideals. -/
def fiveTailEquiv (active center : List ℕ) :
    FiveFamily [] active center ≃ₐ[ℂ] FiveTailFamily active center := by
  unfold FiveFamily FiveTailFamily Model ideal
  rw [List.length_nil, Nat.zero_add]
  exact Ideal.quotientEquivAlg _ _
    (leafSwapVars 0 (active.length + center.length + 1) (active.length + 1))
    (five_tail_ideal_map active center).symm

end
end VOA.DeligneAudit.A2.CVRectAdjointFiveFamily

#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveFamily.fiveTailEquiv
