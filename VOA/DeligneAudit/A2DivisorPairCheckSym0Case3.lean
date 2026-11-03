import VOA.DeligneAudit.A2DivisorPairData

/-! A single two-slot certificate: 64 integer output entries. -/
namespace VOA.DeligneAudit.A2.PairCert

set_option maxRecDepth 100000 in
theorem sym_cert_pair_0_3 : (fun c' d' => 72 * symT 0 3 c' d') =
    fun c' d' => comb (symL 0 3) c' d' + ∑ r, phiZ r (symT 0 3) * UZ r c' d' := by
  decide +kernel

end VOA.DeligneAudit.A2.PairCert
