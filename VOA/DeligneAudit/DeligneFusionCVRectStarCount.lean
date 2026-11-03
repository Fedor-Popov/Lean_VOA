import VOA.DeligneAudit.DeligneFusionCVRectCount
import VOA.DeligneAudit.DeligneFusionCVRectList

/-! # Product-count and well-founded measure arithmetic for star leaf elimination -/

namespace VOA.DeligneAudit.A2.CVRectStarCount

open VOA.DeligneAudit.A2.CVRectCount

def starWeight (left right center : List ℕ) : ℕ :=
  (left.map rectangleWeight).prod * (right.map rectangleWeight).prod *
    (center.map (fun k => k + 1)).prod

theorem starWeight_base (right center : List ℕ) :
    starWeight [] right center = familyWeight right center := by
  simp only [starWeight, familyWeight, List.map_nil, List.prod_nil, one_mul]

theorem starWeight_active (left right center : List ℕ) (K : ℕ) (hK : 1 ≤ K) :
    starWeight (K :: left) right center =
      starWeight left right (K :: center) + starWeight ((K - 1) :: left) right center := by
  simp only [starWeight, List.map_cons, List.prod_cons, rectangleWeight_pos K hK]
  ring

theorem starWeight_zero (left right center : List ℕ) :
    starWeight (0 :: left) right center = starWeight left right center := by
  simp only [starWeight, List.map_cons, List.prod_cons, rectangleWeight_zero, one_mul]

theorem starWeight_perm {left left' : List ℕ} (h : left.Perm left') (right center : List ℕ) :
    starWeight left right center = starWeight left' right center := by
  simp only [starWeight, (h.map rectangleWeight).prod_eq]

/-- The two rectangular orientations contribute the expected combined
`3/6/10` product, with arbitrary optional central one-color factors. -/
theorem starWeight_parts (r n e r' n' e' : ℕ) (center : List ℕ) :
    starWeight (List.replicate r 3 ++ List.replicate n 2 ++ List.replicate e 1)
      (List.replicate r' 3 ++ List.replicate n' 2 ++ List.replicate e' 1) center =
      3 ^ (e + e') * 6 ^ (n + n') * 10 ^ (r + r') *
        (center.map (fun k => k + 1)).prod := by
  simp only [starWeight, List.map_append, List.prod_append, List.map_replicate,
    List.prod_replicate, rectangleWeight_three, rectangleWeight_two, rectangleWeight_one,
    pow_add]
  ring

/-- The other capacities may vary in the induction; only the selected
leaf's total capacity and number of sites are needed for termination. -/
def leafComplexity (left : List ℕ) : ℕ := left.sum + left.length

theorem leafComplexity_remove (left : List ℕ) (K : ℕ) :
    leafComplexity left < leafComplexity (K :: left) := by
  simp only [leafComplexity, List.sum_cons, List.length_cons]
  omega

theorem leafComplexity_decrement (left : List ℕ) (K : ℕ) (hK : 1 ≤ K) :
    leafComplexity ((K - 1) :: left) < leafComplexity (K :: left) := by
  simp only [leafComplexity, List.sum_cons, List.length_cons]
  omega

theorem leafComplexity_perm {left left' : List ℕ} (h : left.Perm left') :
    leafComplexity left = leafComplexity left' := by
  simp only [leafComplexity, h.sum_eq, h.length_eq]

end VOA.DeligneAudit.A2.CVRectStarCount

#print axioms VOA.DeligneAudit.A2.CVRectStarCount.starWeight_active
#print axioms VOA.DeligneAudit.A2.CVRectStarCount.leafComplexity_decrement
#print axioms VOA.DeligneAudit.A2.CVRectStarCount.starWeight_parts
