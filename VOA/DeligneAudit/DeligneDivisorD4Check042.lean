import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4Check042Case0
import VOA.DeligneAudit.DeligneDivisorD4Check042Case1
import VOA.DeligneAudit.DeligneDivisorD4Check042Case2
import VOA.DeligneAudit.DeligneDivisorD4Check042Case3
import VOA.DeligneAudit.DeligneDivisorD4Check042Case4
import VOA.DeligneAudit.DeligneDivisorD4Check042Case5
import VOA.DeligneAudit.DeligneDivisorD4Check042Case6

/-! Assemble the unchanged antisymmetric row theorem from four-pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

theorem d4_small_042 : antiChecks 2 3 = true := by
  apply antiChecks_row_of_range 2 3 (by decide)
  exact (check_range_join 0 4 4 24 28 (by decide) (by decide) d4_anti_two_0
      (check_range_join 4 4 8 20 24 (by decide) (by decide) d4_anti_two_1
      (check_range_join 8 4 12 16 20 (by decide) (by decide) d4_anti_two_2
      (check_range_join 12 4 16 12 16 (by decide) (by decide) d4_anti_two_3
      (check_range_join 16 4 20 8 12 (by decide) (by decide) d4_anti_two_4
      (check_range_join 20 4 24 4 8 (by decide) (by decide) d4_anti_two_5
      d4_anti_two_6))))))
end VOA.DeligneAudit.DeligneDivisor.D4
