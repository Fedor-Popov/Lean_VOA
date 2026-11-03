import VOA.DeligneAudit.SL4TMarkedFlagStrataAudit
import VOA.DeligneAudit.SL4TAdjointSiteFlatTopRelation

/-!
# The flat top relation at one adjoint site: declaration and axiom audit

**Status.** The residual `AdjointSiteFlatTopRelation B h` of
`SL4TAdjointSiteFlatRelation` is proved for every `B` and `h`:

    adjointSiteFlatTopRelation_holds (B h : ℕ) : AdjointSiteFlatTopRelation B h

The generic statement (`flatTopRelation_of_compound`, any module with the local Weyl relations of
weight `(1, B, 1)`, `g(h) v = 0`, `h ≥ 1` and truncation above `h`) follows this order:
move `q^e` to the left of `x^d` instead of past it
(`lastPairPow_firstPow_mem_flatKernelSpace`: `q^e x^d g^B v - [d]_e z^e x^(d-e) g^B v ∈ K₃`), so
`D_f (q^e x^d g^B v) ∈ K₃` (`flatNewton_expandedTopWord_mem`), and `F(h)` kills `K₃`; the expansion
of `x^d g^B v` has the single marked correction `g^(B-d+1) y^(d-1) x v`, of first Levi key
`(1, d-1, 0)`, above `(0, d, 0)`. For `h = 0` the generator vanishes when `B ≥ 1`
(`adjointSiteGenerator_eq_zero_of_noRoom`), and the range is empty when `B = 0`.

Consequences:

    zeroAdjointFlatRelation_all (B k : ℕ) (hk : 1 ≤ k) (hkB : 2 * k ≤ B) :
      ZeroAdjointFlatRelation B k
    adjointSiteLawB_of_stratumCount (B k : ℕ) (hk : 1 ≤ k) (hkB : 2 * k ≤ B) :
      OneAdjointStratumCount B k → AdjointSiteLawB B k

So Law B at one adjoint site rests only on the ring statement `OneAdjointStratumCount B k`.

Axioms of every declaration are printed below.
-/

#print axioms VOA.DeligneAudit.SL4T.lastPair_first_comm
#print axioms VOA.DeligneAudit.SL4T.lastPair_firstPow
#print axioms VOA.DeligneAudit.SL4T.flatKernelSpace_parabolicPow
#print axioms VOA.DeligneAudit.SL4T.lastPairPow_firstPow_mem_flatKernelSpace
#print axioms VOA.DeligneAudit.SL4T.flatNewton_expandedTopWord_mem
#print axioms VOA.DeligneAudit.SL4T.flatMarkedSpan_zero_le
#print axioms VOA.DeligneAudit.SL4T.flatLeakSpan_zero_eq_bot
#print axioms VOA.DeligneAudit.SL4T.flatTopRelation_of_compound
#print axioms VOA.DeligneAudit.SL4T.bracket_middleRaising_middle
#print axioms VOA.DeligneAudit.SL4T.adjointSiteGenerator_eq_zero_of_noRoom
#print axioms VOA.DeligneAudit.SL4T.adjointSiteFlatTopRelation_holds
#print axioms VOA.DeligneAudit.SL4T.zeroAdjointFlatRelation_all
#print axioms VOA.DeligneAudit.SL4T.adjointSiteLawB_of_stratumCount
