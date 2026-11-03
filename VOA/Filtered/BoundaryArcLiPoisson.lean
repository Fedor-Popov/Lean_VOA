import VOA.Filtered.BoundaryArcPoisson
import VOA.Filtered.InfiniteLiPoisson

/-! # The intrinsic boundary arc-to-Li Poisson vertex homomorphism -/
namespace VOA.AffineVOA.CurrentLi
open VOA.AffineVOA.Inst VOA.AffineSl2GeneralRigidity VOA.AffineSl2UniversalC2PBW
open scoped BigOperators
noncomputable section
variable (k : ℂ) (hk : k + 2 ≠ 0)
variable (J : Submodule ℂ (WakModule k))
    (hJ : (affineSl2VOA_closed k hk).IsIdeal J)
    (hgr : QuotVOA.IsGradedIdeal (affineSl2VOA_closed k hk) J)
local notation "QW" => QuotVOA.quotientVOA (affineSl2VOA_closed k hk) J hJ hgr

/-- Exact sl2 brackets descend to all graded affine quotients and then to genuine Li classes. -/
theorem quotientAffineCurrentLiClass_mode_zero (a b : Fin 3) :
    liAssociatedGradedMode QW 0 (quotientAffineCurrentLiClass k hk J hJ hgr a)
      (quotientAffineCurrentLiClass k hk J hJ hgr b) =
      ∑ c : Fin 3, fabc a b c • quotientAffineCurrentLiClass k hk J hJ hgr c := by
  unfold quotientAffineCurrentLiClass
  rw [liDegreeZeroClass_mode_zero QW 1 1 (by omega)]
  let x (c : Fin 3) : liWeightPiece QW 0 1 :=
    ⟨J.mkQ (currentState k c), by
      constructor
      · rw [liFiltration_zero_eq_top]; trivial
      · exact QuotVOA.quotientVOA_mkQ_grading hJ hgr (currentState_mem_grading k hk c)⟩
  change liHomogeneousClassLinear QW 0 1 _ =
    ∑ c : Fin 3, fabc a b c • liHomogeneousClassLinear QW 0 1 (x c)
  simp only [← map_smul,← map_sum]
  apply congrArg (liHomogeneousClassLinear QW 0 1)
  apply Subtype.ext
  change poissonBracket QW (J.mkQ (currentState k a)) (J.mkQ (currentState k b)) =
    ∑ c : Fin 3, fabc a b c • J.mkQ (currentState k c)
  rw [poissonBracket_def,QuotVOA.quotientVOA_mkQ_smul]
  have h := congrArg J.mkQ (universal_current_poissonBracket k hk a b)
  simpa only [poissonBracket_def,map_sum,map_smul] using h

/-- In paper coordinates the quotient Li bracket is the specified geometric Poisson bracket. -/
theorem quotientAffineCurrentLiClass_paper_bracket (i j : Fin 3) :
    liAssociatedGradedMode QW 0
      (quotientAffineCurrentLiClass k hk J hJ hgr (symbolToCurrentColor i))
      (quotientAffineCurrentLiClass k hk J hJ hgr (symbolToCurrentColor j)) =
      MvPolynomial.aeval (fun a => quotientAffineCurrentLiClass k hk J hJ hgr
        (symbolToCurrentColor a)) (BoundaryAuxiliary.currentPoissonBracket (R := ℂ) i j) := by
  rw [quotientAffineCurrentLiClass_mode_zero]
  fin_cases i <;> fin_cases j <;>
    simp [BoundaryAuxiliary.currentPoissonBracket,Fin.sum_univ_succ,fabc,
      smul_eq_mul,two_smul,two_mul]

/-- Once the actual base relations hold, the canonical boundary arc map preserves the full
intrinsic PVA structure. The source PVA and every mode-compatibility law are constructed. -/
def boundaryArcLiPoissonHom (m : ℕ)
    (hI : BoundaryAuxiliary.baseIdeal (R := ℂ) m ≤ RingHom.ker
      (MvPolynomial.aeval (fun a => quotientAffineCurrentLiClass k hk J hJ hgr
        (symbolToCurrentColor a))).toRingHom) :
    PoissonVertexAlgebra.Hom (BoundaryAuxiliary.arcPVA m) (liPoissonVertexAlgebra QW) :=
  liInfinitePresentedJetPoissonHom QW (fun _ : Fin 3 => 1)
    (fun i => ⟨J.mkQ (currentState k (symbolToCurrentColor i)),
      QuotVOA.quotientVOA_mkQ_grading hJ hgr (currentState_mem_grading k hk _)⟩)
    (BoundaryAuxiliary.baseIdeal m) hI (BoundaryAuxiliary.arcPVA m)
    (BoundaryAuxiliary.arcPVA_translation m) BoundaryAuxiliary.currentPoissonBracket
    (BoundaryAuxiliary.arcPVA_base_zero m) (BoundaryAuxiliary.arcPVA_base_succ m)
    (quotientAffineCurrentLiClass_paper_bracket k hk J hJ hgr)

/-- The PVA map is exactly the canonical arc evaluation algebra map. -/
theorem boundaryArcLiPoissonHom_toAlgHom (m : ℕ)
    (hI : BoundaryAuxiliary.baseIdeal (R := ℂ) m ≤ RingHom.ker
      (MvPolynomial.aeval (fun a => quotientAffineCurrentLiClass k hk J hJ hgr
        (symbolToCurrentColor a))).toRingHom) :
    (boundaryArcLiPoissonHom k hk J hJ hgr m hI).toAlgHom =
      liInfinitePresentedJetMap QW
        (fun a => quotientAffineCurrentLiClass k hk J hJ hgr (symbolToCurrentColor a))
        (BoundaryAuxiliary.baseIdeal m) hI := rfl

end
end VOA.AffineVOA.CurrentLi
