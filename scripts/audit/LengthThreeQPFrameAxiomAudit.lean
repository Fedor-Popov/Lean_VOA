import VOA.Examples.LengthThreeQPFrame

-- Axiom audit for the Lee-Yang length-three quasi-primary frame
-- (`VOA/Examples/LengthThreeQPFrame.lean`).
--
-- Probed here: the general LDL negative-definiteness lemmas, the per-weight
-- rank-one identities (layer route = QP-frame route), the per-weight
-- negative-definiteness theorems, and the hatG-indefiniteness witnesses --
-- every one at the exact trust boundary
-- `[propext, Classical.choice, Quot.sound]`.
--
-- Excluded per the PolarizedReesStrongGenerator/WeilPolarizedChannelParity
-- precedent (kernel `decide` computations reporting a strict subset of the
-- base axioms -- here no axioms at all): a3count, pLe3, u3count,
-- a3count_eq_pLe3_shift, a3count_vanishes_below_twelve,
-- u3count_eq_pLe3_shift, and the rational data definitions g*/n*/q*/rho*.

#print axioms VOA.LengthThreeQPFrame.negDef1
#print axioms VOA.LengthThreeQPFrame.negDef2
#print axioms VOA.LengthThreeQPFrame.negDef3
#print axioms VOA.LengthThreeQPFrame.rankOne_w12
#print axioms VOA.LengthThreeQPFrame.rankOne_w14
#print axioms VOA.LengthThreeQPFrame.rankOne_w15
#print axioms VOA.LengthThreeQPFrame.rankOne_w16
#print axioms VOA.LengthThreeQPFrame.rankOne_w17
#print axioms VOA.LengthThreeQPFrame.rankOne_w18
#print axioms VOA.LengthThreeQPFrame.rankOne_w19
#print axioms VOA.LengthThreeQPFrame.rankOne_w20
#print axioms VOA.LengthThreeQPFrame.rankOne_w21
#print axioms VOA.LengthThreeQPFrame.rankOne_w22
#print axioms VOA.LengthThreeQPFrame.rankOne_w23
#print axioms VOA.LengthThreeQPFrame.rankOne_w24
#print axioms VOA.LengthThreeQPFrame.negDef_w12
#print axioms VOA.LengthThreeQPFrame.negDef_w14
#print axioms VOA.LengthThreeQPFrame.negDef_w15
#print axioms VOA.LengthThreeQPFrame.negDef_w16
#print axioms VOA.LengthThreeQPFrame.negDef_w17
#print axioms VOA.LengthThreeQPFrame.negDef_w18
#print axioms VOA.LengthThreeQPFrame.negDef_w19
#print axioms VOA.LengthThreeQPFrame.negDef_w20
#print axioms VOA.LengthThreeQPFrame.negDef_w21
#print axioms VOA.LengthThreeQPFrame.negDef_w22
#print axioms VOA.LengthThreeQPFrame.negDef_w23
#print axioms VOA.LengthThreeQPFrame.negDef_w24
#print axioms VOA.LengthThreeQPFrame.totallyPositive_w18
#print axioms VOA.LengthThreeQPFrame.totallyPositive_w20
#print axioms VOA.LengthThreeQPFrame.totallyPositive_w21
#print axioms VOA.LengthThreeQPFrame.totallyPositive_w22
#print axioms VOA.LengthThreeQPFrame.totallyPositive_w23
#print axioms VOA.LengthThreeQPFrame.totallyPositive_w24
#print axioms VOA.LengthThreeQPFrame.hatG_indefinite_w20
#print axioms VOA.LengthThreeQPFrame.hatG_indefinite_w22
#print axioms VOA.LengthThreeQPFrame.hatG_indefinite_w24
