import VOA.Examples.WeilPolarizedChannelParity

-- §§1–5, §7 The decidable core: normal-form fusion arithmetic, the derived
--    Lee-Yang structure constants, the thirteen channel bidegrees, the Weil
--    parity of the recorded channel signs, and the landing-degree forcing.
-- (Every declaration of the decidable core reports a strict subset of the
--  base axioms — `[]` or `[propext]` — because the proofs are kernel
--  `decide`/`rfl` computations; per the PolarizedReesStrongGenerator
--  precedent they are excluded from the enforced probe.  The excluded
--  declarations, all in namespace VOA.WeilParity, are: MonoLt,
--  eq_of_not_monoLt, insertMono, addP, negP, subP, monoMul, mulP, sumP, w,
--  deltaE, mulOne, colorElem, mulColor, structConst, colorElem_two_eq,
--  colorElem_three_eq, mul_two_two_eq, structConst_two_two_zero,
--  structConst_two_two_one, structConst_two_two_two,
--  structConst_two_two_three, structConst_two_zero_two,
--  structConst_zero_zero_zero, Sector, Channel, treePoly, channelPoly,
--  channels, channels_length, channel_class_sizes, ValidInternal,
--  channels_admissible, internal_color_forced, internal_color_allphi,
--  bidegree?, sectorBidegree, k0_channel_bidegree, k2_channel_bidegrees,
--  k3_channel_bidegrees, aphi0_channel_bidegree, aphiphi_channel_bidegree,
--  channel_bidegrees, sectorBidegree_weight_eight, sectorBidegree_diff_even,
--  squeezePoly, channel_sum, weil, Xsign, kappaSign,
--  weil_parity_cutoff_three, Landing, Landing.deg, classSize, flagMult,
--  inducedCount, IsUniformLanding, validLandings, landing_mem_ker,
--  landing_count, landing_forced_ker, landing_k2_k3_forced, twist, optionA,
--  optionC, anchored_ker, anchored_twist_eq_option_a, twist_k2_ker,
--  option_c_not_realizable.)

-- §6 The MvPolynomial bridge: the certified evaluation of the normal-form
--    list arithmetic in Mathlib's polynomial ring, and the squeeze identity
--    there.
#print axioms VOA.WeilParity.mvMono
#print axioms VOA.WeilParity.toMv
#print axioms VOA.WeilParity.mvMono_add_same
#print axioms VOA.WeilParity.mvMono_zero
#print axioms VOA.WeilParity.mvMono_neg
#print axioms VOA.WeilParity.mvMono_mul
#print axioms VOA.WeilParity.toMv_insertMono
#print axioms VOA.WeilParity.toMv_addP
#print axioms VOA.WeilParity.toMv_negP
#print axioms VOA.WeilParity.toMv_subP
#print axioms VOA.WeilParity.toMv_monoMul
#print axioms VOA.WeilParity.toMv_mulP
#print axioms VOA.WeilParity.toMv_sumP
#print axioms VOA.WeilParity.channel_sum_toMv

-- §8 The bundled option-(a) package (squeeze identity + Weil parity +
--    landing forcing + option-(c) exclusion).
#print axioms VOA.WeilParity.weil_polarized_twist_option_a
