/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuCertificate
import VOA.Examples.TripletWpTwoZhuSparseLhsFastFinal

/-!
# Fast Zhu-omega semantics: one homogeneous step

This file certifies the three sparse children used by the fast recurrence as the intrinsic
actions `L(-2)`, `2 L(-1)`, and `L(0)`.  The stored natural weight is used only in the
last branch, through the VOA grading axiom.
-/

namespace VOA.LatGen.WpTwoZhuFastSemantic

open VOA VOA.LatGen VOA.LatGen.Triplet
open VOA.IntegralLattice
open VOA.LatGen.Wp
open VOA.LatGen.WpC2
open VOA.SparseRational HeisenbergN
open VOA.LatGen.WpTwoAMCoords
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute
open VOA.LatGen.WpTwoZhuSparseSemantics

private noncomputable abbrev Ltwo : IntegralLattice := latP 2
private noncomputable abbrev W0 : VertexOperatorAlgebra (FockN (rank Ltwo)) :=
  heisenbergNVOA (rank Ltwo) 1 one_ne_zero

private theorem omega_mem_W0 :
    evalZhuSparseQ omegaSparseQ ∈ W0.grading 2 := by
  exact mem_gradingZN_of_gradingWN
    WpTwoZhuCertificate.evalZhuSparseQ_omegaSparseQ_mem_grading

private theorem W0_smul_omega_eq_LSecBg (hp : 1 ≤ 2) (m : ℤ)
    (Q : FockN (rank Ltwo)) :
    W0.smul (evalZhuSparseQ omegaSparseQ) (m + 1) Q =
      BgA.LSecBg Ltwo (lamP 2) 0 m Q := by
  have hL := DFunLike.congr_fun (tripletLatticeVOA_L 2 hp m)
    (latStateGen Ltwo Q 0)
  change (tripletLatticeVOA 2 hp).smul (omegaTrip 2) (m + 1)
      (latStateGen Ltwo Q 0) =
    BgA.LBg Ltwo (lamP 2) m (latStateGen Ltwo Q 0) at hL
  rw [omegaTrip_two_eq_vVar_state,
    ← WpTwoZhuCertificate.evalZhuSparseQ_omegaSparseQ,
    tripletLatticeVOA_smul_neutral,
    show BgA.LBg Ltwo (lamP 2) m (latStateGen Ltwo Q 0) =
      latStateGen Ltwo (BgA.LSecBg Ltwo (lamP 2) 0 m Q) 0 by
        exact BgA.LBg_mkEα Ltwo (latP_posDef 2 hp) (lamP 2) m Q 0] at hL
  have hc := congrArg (fun z => coordEα Ltwo 0 z) hL
  change mode (YN (rank Ltwo) 1 (evalZhuSparseQ omegaSparseQ)) (m + 1) Q = _
  simpa only [latStateGen, coordEα_apply, if_pos rfl] using hc

theorem eval_omegaMode_eq_virAct (hp : 1 ≤ 2)
    (mode : ℕ) (hmode : 1 ≤ mode) (rightWeight : ℕ)
    (P : SparseRational.Poly ℕ)
    (hP : evalZhuSparseQ P ∈ gradingWN (rank Ltwo) rightWeight) :
    evalZhuSparseQ
        (voaModeActSparseQ omegaSparseQ (1 - (mode : ℤ)) rightWeight P) =
      evalZhuSparseQ (virActSparseQ mode P) := by
  rw [eval_voaModeActSparseQ omegaSparseQ (1 - (mode : ℤ)) rightWeight P hP,
    evalZhuSparseQ_virActSparseQ mode hmode P,
    ← W0_smul_omega_eq_LSecBg hp (-(mode : ℤ)) (evalZhuSparseQ P)]
  rw [PreVertexAlgebra.smul_def]
  congr 2
  ring

theorem eval_virAct_mem_grading (hp : 1 ≤ 2)
    (mode rightWeight : ℕ) (hmode : 1 ≤ mode)
    (P : SparseRational.Poly ℕ)
    (hP : evalZhuSparseQ P ∈ gradingWN (rank Ltwo) rightWeight) :
    evalZhuSparseQ (virActSparseQ mode P) ∈
      gradingWN (rank Ltwo) (rightWeight + mode) := by
  rw [evalZhuSparseQ_virActSparseQ mode hmode P,
    ← W0_smul_omega_eq_LSecBg hp (-(mode : ℤ)) (evalZhuSparseQ P)]
  have ht := W0.smul_mem_grading omega_mem_W0
    (mem_gradingZN_of_gradingWN hP) (-(mode : ℤ) + 1)
  have hindex :
      (2 : ℤ) + rightWeight - (-(mode : ℤ) + 1) - 1 =
        ((rightWeight + mode : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hindex] at ht
  change W0.smul (evalZhuSparseQ omegaSparseQ) (-(mode : ℤ) + 1)
      (evalZhuSparseQ P) ∈
    gradingZN (rank Ltwo) ((rightWeight + mode : ℕ) : ℤ) at ht
  rw [gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at ht
  exact ht

theorem coe_omegaMode_eq_eval_virAct (hp : 1 ≤ 2)
    (mode rightWeight : ℕ) (hmode : 1 ≤ mode)
    (P : SparseRational.Poly ℕ) (x : (tripletW 2 hp).carrier)
    (hx : (x : LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ P) 0)
    (hP : evalZhuSparseQ P ∈ gradingWN (rank Ltwo) rightWeight) :
    (((tripletWVOA 2 hp).smul (tripletWVOA 2 hp).conformalVector
        (1 - (mode : ℤ)) x : (tripletW 2 hp).carrier) : LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ (virActSparseQ mode P)) 0 := by
  rw [smul_coe,
    WpTwoZhuCertificate.conformalVector_coe_eq_eval_omegaSparseQ hp, hx,
    tripletLatticeVOA_smul_neutral,
    ← eval_voaModeActSparseQ omegaSparseQ (1 - (mode : ℤ)) rightWeight P hP,
    eval_omegaMode_eq_virAct hp mode hmode rightWeight P hP]

noncomputable def omegaPartIntrinsic (hp : 1 ≤ 2)
    (x : ℕ × (tripletW 2 hp).carrier) :
    List (ℕ × (tripletW 2 hp).carrier) :=
  [(x.1 + 2, (tripletWVOA 2 hp).smul (tripletWVOA 2 hp).conformalVector (-1) x.2),
   (x.1 + 1, (2 : ℂ) •
      (tripletWVOA 2 hp).smul (tripletWVOA 2 hp).conformalVector 0 x.2),
   (x.1, (tripletWVOA 2 hp).smul (tripletWVOA 2 hp).conformalVector 1 x.2)]

def OmegaFastRel (hp : 1 ≤ 2)
    (x : ℕ × (tripletW 2 hp).carrier)
    (P : ℕ × SparseRational.Poly ℕ) : Prop :=
  x.1 = P.1 ∧
    x.2 ∈ (tripletWVOA 2 hp).grading (x.1 : ℤ) ∧
    ((x.2 : (tripletW 2 hp).carrier) : LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ P.2) 0 ∧
    evalZhuSparseQ P.2 ∈ gradingWN (rank Ltwo) P.1

theorem omegaPartFast_rel (hp : 1 ≤ 2)
    {x : ℕ × (tripletW 2 hp).carrier}
    {P : ℕ × SparseRational.Poly ℕ} (h : OmegaFastRel hp x P) :
    List.Forall₂ (OmegaFastRel hp) (omegaPartIntrinsic hp x)
      (WpTwoZhuSparseLhs.zhuOmegaPartFastSparseQ P) := by
  rcases x with ⟨w, x⟩
  rcases P with ⟨wP, P⟩
  rcases h with ⟨hweight, hxgrade, hx, hPgrade⟩
  simp only at hweight
  subst wP
  have hneg1grade := (tripletWVOA 2 hp).smul_mem_grading
    (tripletWVOA 2 hp).conformal_mem hxgrade (-1)
  have hzerograde := (tripletWVOA 2 hp).smul_mem_grading
    (tripletWVOA 2 hp).conformal_mem hxgrade 0
  have honegrade := (tripletWVOA 2 hp).smul_mem_grading
    (tripletWVOA 2 hp).conformal_mem hxgrade 1
  have htwoFock := eval_virAct_mem_grading hp 2 w (by norm_num) P hPgrade
  have honeFock := eval_virAct_mem_grading hp 1 w (by norm_num) P hPgrade
  have hzeroFock :
      evalZhuSparseQ (scaleQ (w : ℚ) P) ∈ gradingWN (rank Ltwo) w := by
    rw [evalZhuSparseQ_scaleQ]
    exact (gradingWN (rank Ltwo) w).smul_mem _ hPgrade
  simp only [omegaPartIntrinsic, WpTwoZhuSparseLhs.zhuOmegaPartFastSparseQ]
  constructor
  · refine ⟨rfl, ?_,
      coe_omegaMode_eq_eval_virAct hp 2 w (by norm_num) P x hx hPgrade,
      htwoFock⟩
    convert hneg1grade using 1 <;> simp <;> push_cast <;> ring
  constructor
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · exact (tripletWVOA 2 hp).grading (↑(w + 1)) |>.smul_mem _ (by
        convert hzerograde using 1 <;> simp <;> push_cast <;> ring)
    · simp only [Submodule.coe_smul]
      have honeCoe :=
        coe_omegaMode_eq_eval_virAct hp 1 w (by norm_num) P x hx hPgrade
      norm_num at honeCoe
      rw [honeCoe, evalZhuSparseQ_scaleQ, latStateGen_smul_boson]
      norm_num
    · rw [evalZhuSparseQ_scaleQ]
      exact (gradingWN (rank Ltwo) (w + 1)).smul_mem _ honeFock
  constructor
  · refine ⟨rfl, ?_, ?_, hzeroFock⟩
    · convert honegrade using 1 <;> simp <;> push_cast <;> ring
    · have hLzero := (tripletWVOA 2 hp).L_zero_grading x hxgrade
      have hsmul :
          (tripletWVOA 2 hp).smul (tripletWVOA 2 hp).conformalVector 1 x =
            (w : ℂ) • x := by
        change (tripletWVOA 2 hp).L 0 x = (w : ℂ) • x
        simpa using hLzero
      rw [hsmul, Submodule.coe_smul, hx,
        evalZhuSparseQ_scaleQ, latStateGen_smul_boson]
      norm_num
  exact List.Forall₂.nil

end VOA.LatGen.WpTwoZhuFastSemantic

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuFastSemantic.eval_omegaMode_eq_virAct
#print axioms VOA.LatGen.WpTwoZhuFastSemantic.eval_virAct_mem_grading
#print axioms VOA.LatGen.WpTwoZhuFastSemantic.coe_omegaMode_eq_eval_virAct
#print axioms VOA.LatGen.WpTwoZhuFastSemantic.omegaPartFast_rel
end AxiomAudit
