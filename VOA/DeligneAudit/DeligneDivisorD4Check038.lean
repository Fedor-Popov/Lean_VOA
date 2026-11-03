import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4Check038Part0
import VOA.DeligneAudit.DeligneDivisorD4Check038Part1
import VOA.DeligneAudit.DeligneDivisorD4Check038Part2
import VOA.DeligneAudit.DeligneDivisorD4Check038Part3

/-! Assemble the unchanged node-range theorem from five-node checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

theorem d4_small_038 : nodeChecks 760 780 = true :=
  nodeChecks_join 760 765 780 (by decide) (by decide) d4_node_038_0
    (nodeChecks_join 765 770 780 (by decide) (by decide) d4_node_038_1
      (nodeChecks_join 770 775 780 (by decide) (by decide) d4_node_038_2 d4_node_038_3))

end VOA.DeligneAudit.DeligneDivisor.D4
