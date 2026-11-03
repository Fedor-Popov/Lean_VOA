import VOA.DeligneAudit.A2DivisorPairData

/-! A single two-slot certificate: 64 integer output entries. -/
namespace VOA.DeligneAudit.A2.PairCert

set_option maxRecDepth 100000 in
theorem anti_cert_pair_0_0 : (fun c' d' => 6 * antiT 0 0 c' d') = comb (antiL 0 0) := by
  decide +kernel

end VOA.DeligneAudit.A2.PairCert
