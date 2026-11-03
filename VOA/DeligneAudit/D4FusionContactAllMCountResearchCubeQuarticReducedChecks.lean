import Mathlib.Tactic.FinCases
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck00
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck01
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck02
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck03
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck04
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck05
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck06
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck07
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck08
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck09
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck10
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck11
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck12
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck13
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck14
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck15
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck16
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck17
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck18
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCheck19

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced

theorem certificate_check (i : Fin 20) :
    QuarticReducedRows.fastCollect (residualRow i) = [] := by
  fin_cases i
  · exact certificate00
  · exact certificate01
  · exact certificate02
  · exact certificate03
  · exact certificate04
  · exact certificate05
  · exact certificate06
  · exact certificate07
  · exact certificate08
  · exact certificate09
  · exact certificate10
  · exact certificate11
  · exact certificate12
  · exact certificate13
  · exact certificate14
  · exact certificate15
  · exact certificate16
  · exact certificate17
  · exact certificate18
  · exact certificate19

#print axioms certificate_check
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced
