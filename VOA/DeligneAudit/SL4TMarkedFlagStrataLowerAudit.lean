import VOA.DeligneAudit.SL4TMarkedFlagStrataCountAudit
import VOA.DeligneAudit.SL4TAdjointSiteFlatTopAudit
import VOA.DeligneAudit.SL4TSinglyMarkedOmittedPointBound

/-!
# Lower bounds for the marked full-flag strata: declaration and axiom audit

**Status.** The omitted-point stratum of the singly marked full flag without doubles is proved
for all parameters:

    singlyMarkedFlag_omittedPoint_finrank_ge (n : ℕ) (V Y : Finset (Fin n)) (hV : V.Nonempty) :
      ((Vᶜ ∩ Y).card * V.card + (V ∩ Y).card * (V.card - 1)) * (n - 2).factorial ≤
        finrank (omittedPointStratumIdeal (singlyMarkedFlagIdeal n V (n - 1)) V Y)

with `omittedPointStratumIdeal I V Y = (∏ Yᶜ, ∏ (V ∩ Y) · c(Yᶜ))`, `c` the subleading coefficient.
The right side counts the configurations whose root at the first nonzero point lies in `Y`.

Tools (`SL4TSinglyMarkedOmittedPointTools`): the two-generator layer step
(`pairStratum_layers_le`), the transport of a two-generator child ideal through an injective layer
map (`childPair_finrank_le_layer`), the subleading coefficient after a deletion
(`groupSubtopCoefficient_deleted_of_notMem`, `groupSubtopCoefficient_deleted_of_mem`), the
membership `c(V) ∈ (∏ Z, ∏(V ∖ Z) · c(Z))` for `Z ⊆ V` (`groupSubtopCoefficient_mem_span`), and the
identification of the all-marked ring without doubles with the unmarked one
(`singlyMarkedFlagIdeal_univ_eq`).

**Not proved here.** `OneAdjointStratumCount B 1` remains open: the singly marked stratum with one
double, the product stratum, the omitted zero, the doubly marked stratum without doubles, the weak
stratum, the doubly marked strata `j = 1, 2`, the deformation for stratum quotients, the
complement form of the stratum ideals, and the Reynolds descent with the match to the coefficient
ring.

Axioms of every declaration are printed below.
-/

-- SL4TSinglyMarkedOmittedPointTools.lean
#print axioms VOA.DeligneAudit.SL4T.pairStratum_layers_le
#print axioms VOA.DeligneAudit.SL4T.aeval_deletedLayerRoot
#print axioms VOA.DeligneAudit.SL4T.childPair_finrank_le_layer
#print axioms VOA.DeligneAudit.SL4T.groupElementaryPolynomial_deleted_of_notMem
#print axioms VOA.DeligneAudit.SL4T.groupSubtopCoefficient_deleted_of_notMem
#print axioms VOA.DeligneAudit.SL4T.groupSubtopCoefficient_deleted_of_mem
#print axioms VOA.DeligneAudit.SL4T.groupSubtopCoefficient_mem_span
#print axioms VOA.DeligneAudit.SL4T.esymm_card_eq_prod
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlagIdeal_univ_eq
-- SL4TSinglyMarkedOmittedPointBound.lean
#print axioms VOA.DeligneAudit.SL4T.omittedPointStratumIdeal
#print axioms VOA.DeligneAudit.SL4T.omittedPointStratumIdeal_eq_span
#print axioms VOA.DeligneAudit.SL4T.aeval_omittedPointGenerators
#print axioms VOA.DeligneAudit.SL4T.deletedGroup_inter
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_omittedPoint_finrank_ge
