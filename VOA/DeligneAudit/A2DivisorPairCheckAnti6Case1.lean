import VOA.DeligneAudit.A2DivisorPairData

/-! A single two-slot certificate: 64 integer output entries. -/
namespace VOA.DeligneAudit.A2.PairCert

set_option maxRecDepth 100000 in
theorem anti_cert_pair_6_1 : (fun c' d' => 6 * antiT 6 1 c' d') = comb (antiL 6 1) := by
  decide +kernel

end VOA.DeligneAudit.A2.PairCert
