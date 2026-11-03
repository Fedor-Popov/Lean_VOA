import VOA.DeligneAudit.A2DivisorPairData

/-! A single two-slot certificate: 64 integer output entries. -/
namespace VOA.DeligneAudit.A2.PairCert

set_option maxRecDepth 100000 in
theorem sym_cert_pair_6_1 : (fun c' d' => 72 * symT 6 1 c' d') =
    fun c' d' => comb (symL 6 1) c' d' + ∑ r, phiZ r (symT 6 1) * UZ r c' d' := by
  decide +kernel

end VOA.DeligneAudit.A2.PairCert
