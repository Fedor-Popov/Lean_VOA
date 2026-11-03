/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode0Collect
import VOA.Examples.TripletWpTwoZhuFastEvaluatedAssembly

/-!
# Unconditional lattice W(2) Zhu certificate and consequences

The finite mode-zero H calculation closes the evaluated sparse certificate.  The public endpoints
below contain no residual representation-theoretic or coordinate hypotheses.
-/

namespace VOA.LatGen.Wp

open VOA
open VOA.LatGen.WpTwoZhuSparseSemantics
open VOA.LatGen.WpTwoZhuFastEvaluatedAssembly

/-- The explicit f2 representative lies in Zhu's O-space for the lattice W(2) carrier. -/
theorem fTwoZhuCertificateWp (hp : 1 ≤ 2) : FTwoZhuCertificateWp hp :=
  fTwoZhuCertificateWp_of_mode0_eval hp eval_hEntryMode0_eq_expected

/-- The lattice W(2) vertex operator algebra is simple. -/
theorem tripletWVOA_two_isSimple (hp : 1 ≤ 2) : (tripletWVOA 2 hp).IsSimple :=
  tripletWVOA_two_isSimple_of_mode0_eval hp eval_hEntryMode0_eq_expected

/-- The lattice W(2) vertex operator algebra is strongly finite. -/
theorem tripletWVOA_two_stronglyFinite (hp : 1 ≤ 2) :
    StronglyFinite (tripletWVOA 2 hp) :=
  tripletWVOA_two_stronglyFinite_of_mode0_eval hp eval_hEntryMode0_eq_expected

/-- The lattice W(2) vertex operator algebra is strongly finite but irrational in both formalized
senses. -/
theorem tripletWVOA_two_stronglyFinite_and_irrational (hp : 1 ≤ 2) :
    StronglyFinite (tripletWVOA 2 hp) ∧
      ¬ AdmissiblyRational (tripletWVOA 2 hp) ∧
      ¬ GannonRational (tripletWVOA 2 hp) :=
  tripletWVOA_two_stronglyFinite_and_irrational_of_mode0_eval hp
    eval_hEntryMode0_eq_expected

#print axioms fTwoZhuCertificateWp
#print axioms tripletWVOA_two_isSimple
#print axioms tripletWVOA_two_stronglyFinite
#print axioms tripletWVOA_two_stronglyFinite_and_irrational

end VOA.LatGen.Wp
