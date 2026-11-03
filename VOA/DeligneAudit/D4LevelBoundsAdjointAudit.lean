import VOA.DeligneAudit.D4LevelBoundsAudit
import VOA.DeligneAudit.D4LevelReductionAdjointAssembly
import VOA.DeligneAudit.D4LevelReductionCentralBounds

/-!
Collision and axiom audit for the all-m adjoint boundary of the D4 level filtration.
The pure adjoint multiplicity spaces are filtered by decreasing current degree.
Their homogeneous Grassmannian boxes have total cardinality at most a binomial
coefficient. Every cyclic quotient satisfies the mixed truncated sl₄ bound.
At zero adjoint count, Y words lie in the next level. Converted Garland relations
bound the central multiplicity by its Grassmannian box, and the remaining cyclic
quotients satisfy the local exterior-square bound. Both boundary families hold
for every multiplicity, including zero; the zero-adjoint theorem covers all integer grades.
-/

#print axioms VOA.DeligneAudit.D4LevelReduction.keyVectorOrbit_quotient_eq_cyclic
#print axioms VOA.DeligneAudit.D4LevelReduction.keyOrbit_quotient_rank_le
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointKey_finrank_le_gradedBox
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointGradedBox_sum_le
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointOrbit_quotient_rank_le
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointEdge_coinvariants_rank_le
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_adjoint_edge

#print axioms VOA.DeligneAudit.D4LevelReduction.centralBoundary_eq_orbits_sup_next

#print axioms VOA.DeligneAudit.D4LevelReduction.centralGarland_spectator_mem_next

#print axioms VOA.DeligneAudit.D4LevelReduction.centralKey_quotient_rank_le

#print axioms VOA.DeligneAudit.D4LevelReduction.centralKey_quotient_finrank_le_gradedBox

#print axioms VOA.DeligneAudit.D4LevelReduction.centralBoundary_rank_le

#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_central_boundary

#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_zero_adjoint
