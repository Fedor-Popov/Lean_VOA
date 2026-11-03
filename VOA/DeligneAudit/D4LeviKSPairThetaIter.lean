import VOA.DeligneAudit.D4LeviKSPairThetaWords

/-! Iteration of the f₃ conversion over a list of current modes. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pairAdjoint_add (F : ℕ → Module.End ℂ V)
    (rs : List ℕ) (A B : Module.End ℂ V) :
    pairAdjoint F rs (A + B) =
      pairAdjoint F rs A + pairAdjoint F rs B := by
  induction rs generalizing A B with
  | nil => rfl
  | cons r rs ih =>
      simp only [pairAdjoint]
      have h : F r * (A + B) - (A + B) * F r =
          (F r * A - A * F r) + (F r * B - B * F r) := by
        noncomm_ring
      rw [h, ih]

theorem pairAdjoint_zero (F : ℕ → Module.End ℂ V) (rs : List ℕ) :
    pairAdjoint F rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simpa [pairAdjoint] using ih

theorem pairAdjoint_list_sum (F : ℕ → Module.End ℂ V)
    (rs : List ℕ) (As : List (Module.End ℂ V)) :
    pairAdjoint F rs As.sum = (As.map (pairAdjoint F rs)).sum := by
  induction As with
  | nil => simpa using pairAdjoint_zero F rs
  | cons A As ih =>
      simp only [List.sum_cons, List.map_cons, pairAdjoint_add, ih]

/-- Every path through the one-mode conversion tree, retaining multiplicity. -/
def threeWordsIter : List ℕ → List (Fin 6 × ℕ) →
    List (List (Fin 6 × ℕ))
  | [], l => [l]
  | r :: rs, l => (threeWords r l).flatMap (threeWordsIter rs)

/-- Operator-level Θ5: each converted letter contributes the D4 minus sign. -/
theorem fThree_adjoint_iter_radicalOp
    (ρ : CurrentModule D4sector.f V) (rs : List ℕ)
    (l : List (Fin 6 × ℕ)) :
    pairAdjoint (ρ.op (17 : Fin 28)) rs (pairRadicalOp ρ l) =
      (-1 : ℂ) ^ rs.length •
        ((threeWordsIter rs l).map (pairRadicalOp ρ)).sum := by
  induction rs generalizing l with
  | nil => simp [pairAdjoint, threeWordsIter]
  | cons r rs ih =>
      simp only [pairAdjoint, fThree_adjoint_radicalOp,
        pairAdjoint_neg, pairAdjoint_list_sum]
      simp only [List.map_map, Function.comp_def, ih,
        threeWordsIter, List.length_cons, pow_succ]
      induction threeWords r l with
      | nil => simp
      | cons q qs hqs =>
          simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
            List.map_append, List.sum_append]
          rw [neg_add]
          rw [hqs]
          simp [smul_add]

/-- The iterated conversion formula after applying a radical word to any
    vector. It does not require a cyclic-vector or saturation hypothesis. -/
theorem fThree_adjoint_iter_radicalWord
    (ρ : CurrentModule D4sector.f V) (rs : List ℕ)
    (l : List (Fin 6 × ℕ)) (v : V) :
    pairAdjoint (ρ.op (17 : Fin 28)) rs (pairRadicalOp ρ l) v =
      (-1 : ℂ) ^ rs.length •
        ((threeWordsIter rs l).map (radicalWord ρ v)).sum := by
  have h := congrArg (fun A : Module.End ℂ V => A v)
    (fThree_adjoint_iter_radicalOp ρ rs l)
  simpa only [LinearMap.smul_apply, pairRadicalOp_sum_apply] using h

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairAdjoint_add
#print axioms VOA.DeligneAudit.D4Levi.pairAdjoint_zero
#print axioms VOA.DeligneAudit.D4Levi.pairAdjoint_list_sum
#print axioms VOA.DeligneAudit.D4Levi.fThree_adjoint_iter_radicalOp
#print axioms VOA.DeligneAudit.D4Levi.fThree_adjoint_iter_radicalWord
