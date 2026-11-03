import VOA.DeligneAudit.D4FusionToroidalFusionD4
import VOA.DeligneAudit.D4FusionToroidalFusionRavFam

/-!
# D4 Ravinder-family relations in the fusion associated graded

The current letter of mode `r` is represented by toroidal degrees
`(r / N, r % N)`. These are the full tail and eigenrelation conditions
of `ravFam D4sector N 0` on the fusion highest vector.
-/

namespace VOA.DeligneAudit.Toroidal.D4Fusion

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem graded_ravFam_tail (N : ℕ) (hN : 0 < N)
    (t : List (Ltr 28)) (ht : t ∈ (ravFam D4sector N 0).tails) :
    wordOpT (gradedAction N) (symbolLetters N t) (gradedHighest N) = 0 :=
  FusionGr.ravFam_symbol_tail D4sector D1SiteG.D4Check.table_skewC
    (D1TensorG.points N) hN t ht

theorem graded_ravFam_eig (N : ℕ) (hN : 0 < N)
    (q : Fin 28 × ℂ) (hq : q ∈ (ravFam D4sector N 0).eig) :
    (gradedAction N).op q.1 0 0 (gradedHighest N) =
      q.2 • gradedHighest N :=
  FusionGr.ravFam_symbol_eig D4sector D1SiteG.D4Check.table_skewC
    (D1TensorG.points N) hN q hq

end

end VOA.DeligneAudit.Toroidal.D4Fusion

#print axioms VOA.DeligneAudit.Toroidal.D4Fusion.graded_ravFam_tail
#print axioms VOA.DeligneAudit.Toroidal.D4Fusion.graded_ravFam_eig
