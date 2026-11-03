/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksRaising04
import VOA.DeligneAudit.F4SectorChecksRaising05
import VOA.DeligneAudit.F4SectorChecksRaising07
import VOA.DeligneAudit.F4SectorChecksRaising08
import VOA.DeligneAudit.F4SectorChecksRaising14
import VOA.DeligneAudit.F4SectorChecksRaising15
import VOA.DeligneAudit.F4SectorChecksRaising16
import VOA.DeligneAudit.F4SectorChecksRaising17
import VOA.DeligneAudit.F4SectorChecksRaising19
import VOA.DeligneAudit.F4SectorChecksRaising21
import VOA.DeligneAudit.F4SectorChecksRaising22
import VOA.DeligneAudit.F4SectorChecksRaising23
import VOA.DeligneAudit.F4SectorChecksRaising24
import VOA.DeligneAudit.F4SectorChecksRaising25
import VOA.DeligneAudit.F4SectorChecksRaising27
import VOA.DeligneAudit.F4SectorChecksRaising30
import VOA.DeligneAudit.F4SectorChecksRaising33
import VOA.DeligneAudit.F4SectorChecksRaising34
import VOA.DeligneAudit.F4SectorChecksRaising35
import VOA.DeligneAudit.F4SectorChecksRaising36
import VOA.DeligneAudit.F4SectorChecksRaising37
import VOA.DeligneAudit.F4SectorChecksRaising42
import VOA.DeligneAudit.F4SectorChecksRaising44
import VOA.DeligneAudit.F4SectorChecksRaising50
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR001N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR005N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR009N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR013N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR017N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR021N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR025N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR029N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR033N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR037N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR041N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR045N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR049N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR053N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR057N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR061N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR065N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR069N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR073N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR077N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR081N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR085N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR089N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR093N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR097N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR101N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR105N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR109N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR113N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR117N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR121N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR125N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR129N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR133N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR137N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR141N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR145N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR149N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR153N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR157N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR161N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR165N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR169N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR173N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR177N04
import VOA.DeligneAudit.F4SectorChecksCyclicNodesR181N04
import VOA.DeligneAudit.F4SectorChecksCyclicRow00
import VOA.DeligneAudit.F4SectorChecksCyclicRow01
import VOA.DeligneAudit.F4SectorChecksCyclicRow02
import VOA.DeligneAudit.F4SectorChecksCyclicRow03
import VOA.DeligneAudit.F4SectorChecksCyclicRow04
import VOA.DeligneAudit.F4SectorChecksCyclicRow05
import VOA.DeligneAudit.F4SectorChecksCyclicRow06
import VOA.DeligneAudit.F4SectorChecksCyclicRow07
import VOA.DeligneAudit.F4SectorChecksCyclicRow08
import VOA.DeligneAudit.F4SectorChecksCyclicRow09
import VOA.DeligneAudit.F4SectorChecksCyclicRow10
import VOA.DeligneAudit.F4SectorChecksCyclicRow11
import VOA.DeligneAudit.F4SectorChecksCyclicRow12
import VOA.DeligneAudit.F4SectorChecksCyclicRow13
import VOA.DeligneAudit.F4SectorChecksCyclicRow14
import VOA.DeligneAudit.F4SectorChecksCyclicRow15
import VOA.DeligneAudit.F4SectorChecksCyclicRow16
import VOA.DeligneAudit.F4SectorChecksCyclicRow17
import VOA.DeligneAudit.F4SectorChecksCyclicRow18
import VOA.DeligneAudit.F4SectorChecksCyclicRow19
import VOA.DeligneAudit.F4SectorChecksCyclicRow20
import VOA.DeligneAudit.F4SectorChecksCyclicRow21
import VOA.DeligneAudit.F4SectorChecksCyclicRow22
import VOA.DeligneAudit.F4SectorChecksCyclicRow23
import VOA.DeligneAudit.F4SectorChecksCyclicRow24
import VOA.DeligneAudit.F4SectorChecksCyclicRow25
import VOA.DeligneAudit.F4SectorChecksCyclicRow26
import VOA.DeligneAudit.F4SectorChecksCyclicRow27
import VOA.DeligneAudit.F4SectorChecksCyclicRow28
import VOA.DeligneAudit.F4SectorChecksCyclicRow29
import VOA.DeligneAudit.F4SectorChecksCyclicRow30
import VOA.DeligneAudit.F4SectorChecksCyclicRow31
import VOA.DeligneAudit.F4SectorChecksCyclicRow32
import VOA.DeligneAudit.F4SectorChecksCyclicRow33
import VOA.DeligneAudit.F4SectorChecksCyclicRow34
import VOA.DeligneAudit.F4SectorChecksCyclicRow35
import VOA.DeligneAudit.F4SectorChecksCyclicRow36
import VOA.DeligneAudit.F4SectorChecksCyclicRow37
import VOA.DeligneAudit.F4SectorChecksCyclicRow38
import VOA.DeligneAudit.F4SectorChecksCyclicRow39
import VOA.DeligneAudit.F4SectorChecksCyclicRow40
import VOA.DeligneAudit.F4SectorChecksCyclicRow41
import VOA.DeligneAudit.F4SectorChecksCyclicRow42
import VOA.DeligneAudit.F4SectorChecksCyclicRow43
import VOA.DeligneAudit.F4SectorChecksCyclicRow44
import VOA.DeligneAudit.F4SectorChecksCyclicRow45
import VOA.DeligneAudit.F4SectorChecksCyclicRow46
import VOA.DeligneAudit.F4SectorChecksCyclicRow47
import VOA.DeligneAudit.F4SectorChecksCyclicRow48
import VOA.DeligneAudit.F4SectorChecksCyclicRow49
import VOA.DeligneAudit.F4SectorChecksCyclicRow50
import VOA.DeligneAudit.F4SectorChecksCyclicRow51

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem raising_ok : ∀ e y : Fin 52, e.val ∈ posL → fZ br e y 45 = 0 := by
    apply f4_raising_from_rows
    intro e he
    simp only [posL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact f4_raising_row_04
    · exact f4_raising_row_05
    · exact f4_raising_row_07
    · exact f4_raising_row_08
    · exact f4_raising_row_14
    · exact f4_raising_row_15
    · exact f4_raising_row_16
    · exact f4_raising_row_17
    · exact f4_raising_row_19
    · exact f4_raising_row_21
    · exact f4_raising_row_22
    · exact f4_raising_row_23
    · exact f4_raising_row_24
    · exact f4_raising_row_25
    · exact f4_raising_row_27
    · exact f4_raising_row_30
    · exact f4_raising_row_33
    · exact f4_raising_row_34
    · exact f4_raising_row_35
    · exact f4_raising_row_36
    · exact f4_raising_row_37
    · exact f4_raising_row_42
    · exact f4_raising_row_44
    · exact f4_raising_row_50

theorem cycNodes_ok : cycNodes = true := by
  exact f4_cycNodes_of_rows 184 (by decide +kernel)
    (f4_range_join 1 92 93 92 184 (by decide +kernel) (by decide +kernel)
    (f4_range_join 1 44 45 48 92 (by decide +kernel) (by decide +kernel)
    (f4_range_join 1 20 21 24 44 (by decide +kernel) (by decide +kernel)
    (f4_range_join 1 8 9 12 20 (by decide +kernel) (by decide +kernel)
    (f4_range_join 1 4 5 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r001_n04
    f4_cyclic_nodes_r005_n04)
    (f4_range_join 9 4 13 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r009_n04
    (f4_range_join 13 4 17 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r013_n04
    f4_cyclic_nodes_r017_n04)))
    (f4_range_join 21 12 33 12 24 (by decide +kernel) (by decide +kernel)
    (f4_range_join 21 4 25 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r021_n04
    (f4_range_join 25 4 29 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r025_n04
    f4_cyclic_nodes_r029_n04))
    (f4_range_join 33 4 37 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r033_n04
    (f4_range_join 37 4 41 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r037_n04
    f4_cyclic_nodes_r041_n04))))
    (f4_range_join 45 24 69 24 48 (by decide +kernel) (by decide +kernel)
    (f4_range_join 45 12 57 12 24 (by decide +kernel) (by decide +kernel)
    (f4_range_join 45 4 49 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r045_n04
    (f4_range_join 49 4 53 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r049_n04
    f4_cyclic_nodes_r053_n04))
    (f4_range_join 57 4 61 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r057_n04
    (f4_range_join 61 4 65 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r061_n04
    f4_cyclic_nodes_r065_n04)))
    (f4_range_join 69 12 81 12 24 (by decide +kernel) (by decide +kernel)
    (f4_range_join 69 4 73 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r069_n04
    (f4_range_join 73 4 77 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r073_n04
    f4_cyclic_nodes_r077_n04))
    (f4_range_join 81 4 85 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r081_n04
    (f4_range_join 85 4 89 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r085_n04
    f4_cyclic_nodes_r089_n04)))))
    (f4_range_join 93 44 137 48 92 (by decide +kernel) (by decide +kernel)
    (f4_range_join 93 20 113 24 44 (by decide +kernel) (by decide +kernel)
    (f4_range_join 93 8 101 12 20 (by decide +kernel) (by decide +kernel)
    (f4_range_join 93 4 97 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r093_n04
    f4_cyclic_nodes_r097_n04)
    (f4_range_join 101 4 105 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r101_n04
    (f4_range_join 105 4 109 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r105_n04
    f4_cyclic_nodes_r109_n04)))
    (f4_range_join 113 12 125 12 24 (by decide +kernel) (by decide +kernel)
    (f4_range_join 113 4 117 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r113_n04
    (f4_range_join 117 4 121 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r117_n04
    f4_cyclic_nodes_r121_n04))
    (f4_range_join 125 4 129 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r125_n04
    (f4_range_join 129 4 133 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r129_n04
    f4_cyclic_nodes_r133_n04))))
    (f4_range_join 137 24 161 24 48 (by decide +kernel) (by decide +kernel)
    (f4_range_join 137 12 149 12 24 (by decide +kernel) (by decide +kernel)
    (f4_range_join 137 4 141 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r137_n04
    (f4_range_join 141 4 145 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r141_n04
    f4_cyclic_nodes_r145_n04))
    (f4_range_join 149 4 153 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r149_n04
    (f4_range_join 153 4 157 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r153_n04
    f4_cyclic_nodes_r157_n04)))
    (f4_range_join 161 12 173 12 24 (by decide +kernel) (by decide +kernel)
    (f4_range_join 161 4 165 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r161_n04
    (f4_range_join 165 4 169 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r165_n04
    f4_cyclic_nodes_r169_n04))
    (f4_range_join 173 4 177 8 12 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r173_n04
    (f4_range_join 177 4 181 4 8 (by decide +kernel) (by decide +kernel)
    f4_cyclic_nodes_r177_n04
    f4_cyclic_nodes_r181_n04))))))

theorem cyc_ok : cycCheck = true := by
  exact f4_cycCheck_of_rows
    (f4_range_join 0 26 26 26 52 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 13 13 13 26 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 6 6 7 13 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 3 3 3 6 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 1 1 2 3 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_00
    (f4_range_join 1 1 2 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_01
    f4_cyclic_row_02))
    (f4_range_join 3 1 4 2 3 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_03
    (f4_range_join 4 1 5 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_04
    f4_cyclic_row_05)))
    (f4_range_join 6 3 9 4 7 (by decide +kernel) (by decide +kernel)
    (f4_range_join 6 1 7 2 3 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_06
    (f4_range_join 7 1 8 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_07
    f4_cyclic_row_08))
    (f4_range_join 9 2 11 2 4 (by decide +kernel) (by decide +kernel)
    (f4_range_join 9 1 10 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_09
    f4_cyclic_row_10)
    (f4_range_join 11 1 12 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_11
    f4_cyclic_row_12))))
    (f4_range_join 13 6 19 7 13 (by decide +kernel) (by decide +kernel)
    (f4_range_join 13 3 16 3 6 (by decide +kernel) (by decide +kernel)
    (f4_range_join 13 1 14 2 3 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_13
    (f4_range_join 14 1 15 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_14
    f4_cyclic_row_15))
    (f4_range_join 16 1 17 2 3 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_16
    (f4_range_join 17 1 18 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_17
    f4_cyclic_row_18)))
    (f4_range_join 19 3 22 4 7 (by decide +kernel) (by decide +kernel)
    (f4_range_join 19 1 20 2 3 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_19
    (f4_range_join 20 1 21 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_20
    f4_cyclic_row_21))
    (f4_range_join 22 2 24 2 4 (by decide +kernel) (by decide +kernel)
    (f4_range_join 22 1 23 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_22
    f4_cyclic_row_23)
    (f4_range_join 24 1 25 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_24
    f4_cyclic_row_25)))))
    (f4_range_join 26 13 39 13 26 (by decide +kernel) (by decide +kernel)
    (f4_range_join 26 6 32 7 13 (by decide +kernel) (by decide +kernel)
    (f4_range_join 26 3 29 3 6 (by decide +kernel) (by decide +kernel)
    (f4_range_join 26 1 27 2 3 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_26
    (f4_range_join 27 1 28 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_27
    f4_cyclic_row_28))
    (f4_range_join 29 1 30 2 3 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_29
    (f4_range_join 30 1 31 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_30
    f4_cyclic_row_31)))
    (f4_range_join 32 3 35 4 7 (by decide +kernel) (by decide +kernel)
    (f4_range_join 32 1 33 2 3 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_32
    (f4_range_join 33 1 34 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_33
    f4_cyclic_row_34))
    (f4_range_join 35 2 37 2 4 (by decide +kernel) (by decide +kernel)
    (f4_range_join 35 1 36 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_35
    f4_cyclic_row_36)
    (f4_range_join 37 1 38 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_37
    f4_cyclic_row_38))))
    (f4_range_join 39 6 45 7 13 (by decide +kernel) (by decide +kernel)
    (f4_range_join 39 3 42 3 6 (by decide +kernel) (by decide +kernel)
    (f4_range_join 39 1 40 2 3 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_39
    (f4_range_join 40 1 41 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_40
    f4_cyclic_row_41))
    (f4_range_join 42 1 43 2 3 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_42
    (f4_range_join 43 1 44 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_43
    f4_cyclic_row_44)))
    (f4_range_join 45 3 48 4 7 (by decide +kernel) (by decide +kernel)
    (f4_range_join 45 1 46 2 3 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_45
    (f4_range_join 46 1 47 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_46
    f4_cyclic_row_47))
    (f4_range_join 48 2 50 2 4 (by decide +kernel) (by decide +kernel)
    (f4_range_join 48 1 49 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_48
    f4_cyclic_row_49)
    (f4_range_join 50 1 51 1 2 (by decide +kernel) (by decide +kernel)
    f4_cyclic_row_50
    f4_cyclic_row_51))))))


end VOA.DeligneAudit.DeligneSector.F4
