import VOA.Classification.COne.MainConverseB2
import VOA.Classification.COne.OrbIcoZFinal

/-! The actual exceptional positive-weight input is proved.
The classification converse has only the rationality and Xu-symbol inputs. -/
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne

/-- The classification converse after the actual B2 and B5 theorems. -/
theorem gannonRayhaunConverse_of_B3_B4 (hXu : XuIcosahedralPoissonRelations)
    (hRat : FiniteV2OrbifoldRationalOfC2Fact) : GannonRayhaunConverse.{0} :=
  gannonRayhaunConverse_of_B3_B4_B5 hXu hRat
    OrbIcoZ.exceptionalOrbifoldPositiveWeightsFact_holds

end VOA.Classification.COne
