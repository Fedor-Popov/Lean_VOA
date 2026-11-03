/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuFastSemanticFinal

/-!
# Terminal lattice W(2) assembly from the finite sparse equality

All representation-theoretic and semantic consequences are discharged here.  The sole hypothesis
is the exact rational equality between the fast f2 coordinate and the assembled Zhu-O coordinate.
-/

namespace VOA.LatGen.WpTwoZhuFastAssembly

open VOA VOA.LatGen VOA.LatGen.Triplet
open VOA.LatGen.Wp
open VOA.LatGen.WpTwoZhuSparseCompute
open VOA.LatGen.WpTwoZhuSparseLhs
open VOA.LatGen.WpTwoZhuFastSemantic
open VOA.LatGen.WpTwoZhuCertificate

theorem fTwoZhuRepresentative_eq_intrinsicCertificateRhs_of_fast_sparse
    (hp : 1 ≤ 2)
    (hcoord : fTwoFastSparseQ = certificateRhsSparseQ) :
    fTwoZhuRepresentative (tripletWVOA 2 hp) = intrinsicCertificateRhs hp := by
  apply Subtype.ext
  rw [fTwoZhuRepresentative_coe_eq_eval_fast hp,
    intrinsicCertificateRhs_coe_eq_eval_sparse hp, hcoord]

theorem fTwoZhuCertificateWp_of_fast_sparse
    (hp : 1 ≤ 2)
    (hcoord : fTwoFastSparseQ = certificateRhsSparseQ) :
    FTwoZhuCertificateWp hp := by
  change fTwoZhuRepresentative (tripletWVOA 2 hp) ∈ O (tripletWVOA 2 hp)
  rw [fTwoZhuRepresentative_eq_intrinsicCertificateRhs_of_fast_sparse hp hcoord]
  exact intrinsicCertificateRhs_mem_O hp

theorem tripletWVOA_two_isSimple_of_fast_sparse
    (hp : 1 ≤ 2)
    (hcoord : fTwoFastSparseQ = certificateRhsSparseQ) :
    (tripletWVOA 2 hp).IsSimple :=
  tripletWVOA_two_isSimple_of_fTwoZhuCertificate hp
    (fTwoZhuCertificateWp_of_fast_sparse hp hcoord)

theorem tripletWVOA_two_stronglyFinite_of_fast_sparse
    (hp : 1 ≤ 2)
    (hcoord : fTwoFastSparseQ = certificateRhsSparseQ) :
    StronglyFinite (tripletWVOA 2 hp) :=
  tripletWVOA_two_stronglyFinite_of_isSimple hp
    (tripletWVOA_two_isSimple_of_fast_sparse hp hcoord)

theorem tripletWVOA_two_stronglyFinite_and_irrational_of_fast_sparse
    (hp : 1 ≤ 2)
    (hcoord : fTwoFastSparseQ = certificateRhsSparseQ) :
    StronglyFinite (tripletWVOA 2 hp) ∧
      ¬ AdmissiblyRational (tripletWVOA 2 hp) ∧
      ¬ GannonRational (tripletWVOA 2 hp) :=
  tripletWVOA_two_stronglyFinite_and_irrational_of_isSimple hp
    (tripletWVOA_two_isSimple_of_fast_sparse hp hcoord)

end VOA.LatGen.WpTwoZhuFastAssembly

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuFastAssembly.fTwoZhuRepresentative_eq_intrinsicCertificateRhs_of_fast_sparse
#print axioms VOA.LatGen.WpTwoZhuFastAssembly.fTwoZhuCertificateWp_of_fast_sparse
#print axioms VOA.LatGen.WpTwoZhuFastAssembly.tripletWVOA_two_isSimple_of_fast_sparse
#print axioms VOA.LatGen.WpTwoZhuFastAssembly.tripletWVOA_two_stronglyFinite_of_fast_sparse
#print axioms VOA.LatGen.WpTwoZhuFastAssembly.tripletWVOA_two_stronglyFinite_and_irrational_of_fast_sparse
end AxiomAudit
