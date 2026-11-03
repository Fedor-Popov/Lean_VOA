import VOA.DeligneAudit.A2DivisorPairData

/-! A single two-slot certificate: 64 integer output entries. -/
namespace VOA.DeligneAudit.A2.PairCert

set_option maxRecDepth 100000 in
theorem anti_cert_pair_3_6 : (fun c' d' => 6 * antiT 3 6 c' d') = comb (antiL 3 6) := by
  decide +kernel

end VOA.DeligneAudit.A2.PairCert
