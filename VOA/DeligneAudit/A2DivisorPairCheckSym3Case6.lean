import VOA.DeligneAudit.A2DivisorPairData

/-! A single two-slot certificate: 64 integer output entries. -/
namespace VOA.DeligneAudit.A2.PairCert

set_option maxRecDepth 100000 in
theorem sym_cert_pair_3_6 : (fun c' d' => 72 * symT 3 6 c' d') =
    fun c' d' => comb (symL 3 6) c' d' + ∑ r, phiZ r (symT 3 6) * UZ r c' d' := by
  decide +kernel

end VOA.DeligneAudit.A2.PairCert
