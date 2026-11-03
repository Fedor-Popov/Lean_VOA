/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuFastSemanticFinal
import VOA.Examples.TripletWpTwoZhuSparseRhsEvaluatedAssembly

/-!
# Terminal lattice W(2) assembly from evaluated sparse coordinates

The semantic evaluator need not be injective for the Zhu certificate: equality of the evaluated
states already identifies the intrinsic representative with the explicit sum of Zhu-circle terms.
This file transports that weaker, sufficient equality to simplicity, strong finiteness, and the two
formalized irrationality conclusions.  A second interface isolates the sole residual mode-zero H
calculation.
-/

namespace VOA.LatGen.WpTwoZhuFastEvaluatedAssembly

open VOA VOA.LatGen VOA.LatGen.Triplet
open VOA.LatGen.Wp
open VOA.LatGen.WpTwoZhuSparseCompute
open VOA.LatGen.WpTwoZhuSparseLhs
open VOA.LatGen.WpTwoZhuSparseSemantics
open VOA.LatGen.WpTwoZhuFastSemantic
open VOA.LatGen.WpTwoZhuCertificate

theorem fTwoZhuRepresentative_eq_intrinsicCertificateRhs_of_fast_eval
    (hp : 1 ≤ 2)
    (heval : evalZhuSparseQ fTwoFastSparseQ =
      evalZhuSparseQ certificateRhsSparseQ) :
    fTwoZhuRepresentative (tripletWVOA 2 hp) = intrinsicCertificateRhs hp := by
  apply Subtype.ext
  rw [fTwoZhuRepresentative_coe_eq_eval_fast hp,
    intrinsicCertificateRhs_coe_eq_eval_sparse hp, heval]

theorem fTwoZhuCertificateWp_of_fast_eval
    (hp : 1 ≤ 2)
    (heval : evalZhuSparseQ fTwoFastSparseQ =
      evalZhuSparseQ certificateRhsSparseQ) :
    FTwoZhuCertificateWp hp := by
  change fTwoZhuRepresentative (tripletWVOA 2 hp) ∈ O (tripletWVOA 2 hp)
  rw [fTwoZhuRepresentative_eq_intrinsicCertificateRhs_of_fast_eval hp heval]
  exact intrinsicCertificateRhs_mem_O hp

theorem tripletWVOA_two_isSimple_of_fast_eval
    (hp : 1 ≤ 2)
    (heval : evalZhuSparseQ fTwoFastSparseQ =
      evalZhuSparseQ certificateRhsSparseQ) :
    (tripletWVOA 2 hp).IsSimple :=
  tripletWVOA_two_isSimple_of_fTwoZhuCertificate hp
    (fTwoZhuCertificateWp_of_fast_eval hp heval)

theorem tripletWVOA_two_stronglyFinite_of_fast_eval
    (hp : 1 ≤ 2)
    (heval : evalZhuSparseQ fTwoFastSparseQ =
      evalZhuSparseQ certificateRhsSparseQ) :
    StronglyFinite (tripletWVOA 2 hp) :=
  tripletWVOA_two_stronglyFinite_of_isSimple hp
    (tripletWVOA_two_isSimple_of_fast_eval hp heval)

theorem tripletWVOA_two_stronglyFinite_and_irrational_of_fast_eval
    (hp : 1 ≤ 2)
    (heval : evalZhuSparseQ fTwoFastSparseQ =
      evalZhuSparseQ certificateRhsSparseQ) :
    StronglyFinite (tripletWVOA 2 hp) ∧
      ¬ AdmissiblyRational (tripletWVOA 2 hp) ∧
      ¬ GannonRational (tripletWVOA 2 hp) :=
  tripletWVOA_two_stronglyFinite_and_irrational_of_isSimple hp
    (tripletWVOA_two_isSimple_of_fast_eval hp heval)

theorem eval_fast_eq_certificateRhs_of_mode0
    (h0 : evalZhuSparseQ (hEntryModeSparseQ 0) =
      evalZhuSparseQ hEntry0Mode0ExpectedQ) :
    evalZhuSparseQ fTwoFastSparseQ = evalZhuSparseQ certificateRhsSparseQ := by
  have hfast := congrArg evalZhuSparseQ fTwoFastSparseQ_eq_expected
  have hrhs := eval_certificateRhsSparseQ_eq_expected_of_mode0 h0
  exact hfast.trans hrhs.symm

theorem fTwoZhuCertificateWp_of_mode0_eval
    (hp : 1 ≤ 2)
    (h0 : evalZhuSparseQ (hEntryModeSparseQ 0) =
      evalZhuSparseQ hEntry0Mode0ExpectedQ) :
    FTwoZhuCertificateWp hp :=
  fTwoZhuCertificateWp_of_fast_eval hp
    (eval_fast_eq_certificateRhs_of_mode0 h0)

theorem tripletWVOA_two_isSimple_of_mode0_eval
    (hp : 1 ≤ 2)
    (h0 : evalZhuSparseQ (hEntryModeSparseQ 0) =
      evalZhuSparseQ hEntry0Mode0ExpectedQ) :
    (tripletWVOA 2 hp).IsSimple :=
  tripletWVOA_two_isSimple_of_fast_eval hp
    (eval_fast_eq_certificateRhs_of_mode0 h0)

theorem tripletWVOA_two_stronglyFinite_of_mode0_eval
    (hp : 1 ≤ 2)
    (h0 : evalZhuSparseQ (hEntryModeSparseQ 0) =
      evalZhuSparseQ hEntry0Mode0ExpectedQ) :
    StronglyFinite (tripletWVOA 2 hp) :=
  tripletWVOA_two_stronglyFinite_of_fast_eval hp
    (eval_fast_eq_certificateRhs_of_mode0 h0)

theorem tripletWVOA_two_stronglyFinite_and_irrational_of_mode0_eval
    (hp : 1 ≤ 2)
    (h0 : evalZhuSparseQ (hEntryModeSparseQ 0) =
      evalZhuSparseQ hEntry0Mode0ExpectedQ) :
    StronglyFinite (tripletWVOA 2 hp) ∧
      ¬ AdmissiblyRational (tripletWVOA 2 hp) ∧
      ¬ GannonRational (tripletWVOA 2 hp) :=
  tripletWVOA_two_stronglyFinite_and_irrational_of_fast_eval hp
    (eval_fast_eq_certificateRhs_of_mode0 h0)

end VOA.LatGen.WpTwoZhuFastEvaluatedAssembly

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuFastEvaluatedAssembly.fTwoZhuRepresentative_eq_intrinsicCertificateRhs_of_fast_eval
#print axioms VOA.LatGen.WpTwoZhuFastEvaluatedAssembly.fTwoZhuCertificateWp_of_fast_eval
#print axioms VOA.LatGen.WpTwoZhuFastEvaluatedAssembly.tripletWVOA_two_isSimple_of_fast_eval
#print axioms VOA.LatGen.WpTwoZhuFastEvaluatedAssembly.tripletWVOA_two_stronglyFinite_of_fast_eval
#print axioms VOA.LatGen.WpTwoZhuFastEvaluatedAssembly.tripletWVOA_two_stronglyFinite_and_irrational_of_fast_eval
#print axioms VOA.LatGen.WpTwoZhuFastEvaluatedAssembly.tripletWVOA_two_stronglyFinite_and_irrational_of_mode0_eval
end AxiomAudit
