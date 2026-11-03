import VOA.DeligneAudit.DeligneDivisorCheckRange
import VOA.DeligneAudit.E6DivisorColCheck00
import VOA.DeligneAudit.E6DivisorColCheck01
import VOA.DeligneAudit.E6DivisorColCheck02
import VOA.DeligneAudit.E6DivisorColCheck03
import VOA.DeligneAudit.E6DivisorColCheck04
import VOA.DeligneAudit.E6DivisorColCheck05
import VOA.DeligneAudit.E6DivisorColCheck06
import VOA.DeligneAudit.E6DivisorColCheck07
import VOA.DeligneAudit.E6DivisorColCheck08
import VOA.DeligneAudit.E6DivisorColCheck09
import VOA.DeligneAudit.E6DivisorColCheck10
import VOA.DeligneAudit.E6DivisorColCheck11
import VOA.DeligneAudit.E6DivisorColCheck12
import VOA.DeligneAudit.E6DivisorColCheck13
import VOA.DeligneAudit.E6DivisorColCheck14
import VOA.DeligneAudit.E6DivisorColCheck15
import VOA.DeligneAudit.E6DivisorColCheck16
import VOA.DeligneAudit.E6DivisorColCheck17
import VOA.DeligneAudit.E6DivisorColCheck18
import VOA.DeligneAudit.E6DivisorColCheck19


namespace VOA.DeligneAudit.DeligneDivisor.E6

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem colChecks_join_0_8 :
    (List.range' 0 8).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 0 4 8
    (by omega) (by omega) e6_colChecks_0 e6_colChecks_4

private theorem colChecks_join_12_20 :
    (List.range' 12 8).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 12 16 20
    (by omega) (by omega) e6_colChecks_12 e6_colChecks_16

private theorem colChecks_join_8_20 :
    (List.range' 8 12).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 8 12 20
    (by omega) (by omega) e6_colChecks_8 colChecks_join_12_20

private theorem colChecks_join_0_20 :
    (List.range' 0 20).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 0 8 20
    (by omega) (by omega) colChecks_join_0_8 colChecks_join_8_20

private theorem colChecks_join_20_28 :
    (List.range' 20 8).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 20 24 28
    (by omega) (by omega) e6_colChecks_20 e6_colChecks_24

private theorem colChecks_join_32_40 :
    (List.range' 32 8).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 32 36 40
    (by omega) (by omega) e6_colChecks_32 e6_colChecks_36

private theorem colChecks_join_28_40 :
    (List.range' 28 12).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 28 32 40
    (by omega) (by omega) e6_colChecks_28 colChecks_join_32_40

private theorem colChecks_join_20_40 :
    (List.range' 20 20).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 20 28 40
    (by omega) (by omega) colChecks_join_20_28 colChecks_join_28_40

private theorem colChecks_join_0_40 :
    (List.range' 0 40).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 0 20 40
    (by omega) (by omega) colChecks_join_0_20 colChecks_join_20_40

private theorem colChecks_join_40_48 :
    (List.range' 40 8).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 40 44 48
    (by omega) (by omega) e6_colChecks_40 e6_colChecks_44

private theorem colChecks_join_52_60 :
    (List.range' 52 8).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 52 56 60
    (by omega) (by omega) e6_colChecks_52 e6_colChecks_56

private theorem colChecks_join_48_60 :
    (List.range' 48 12).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 48 52 60
    (by omega) (by omega) e6_colChecks_48 colChecks_join_52_60

private theorem colChecks_join_40_60 :
    (List.range' 40 20).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 40 48 60
    (by omega) (by omega) colChecks_join_40_48 colChecks_join_48_60

private theorem colChecks_join_60_68 :
    (List.range' 60 8).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 60 64 68
    (by omega) (by omega) e6_colChecks_60 e6_colChecks_64

private theorem colChecks_join_72_78 :
    (List.range' 72 6).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 72 76 78
    (by omega) (by omega) e6_colChecks_72 e6_colChecks_76

private theorem colChecks_join_68_78 :
    (List.range' 68 10).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 68 72 78
    (by omega) (by omega) e6_colChecks_68 colChecks_join_72_78

private theorem colChecks_join_60_78 :
    (List.range' 60 18).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 60 68 78
    (by omega) (by omega) colChecks_join_60_68 colChecks_join_68_78

private theorem colChecks_join_40_78 :
    (List.range' 40 38).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 40 60 78
    (by omega) (by omega) colChecks_join_40_60 colChecks_join_60_78

private theorem colChecks_join_0_78 :
    (List.range' 0 78).all (fun x => colCheck br colE6 78 x) = true :=
  checkRange_join (fun x => colCheck br colE6 78 x) 0 40 78
    (by omega) (by omega) colChecks_join_0_40 colChecks_join_40_78

theorem e6_colChecks : colChecks = true := by
  apply List.all_eq_true.mpr
  intro x hx
  exact checkRange_mem (fun x => colCheck br colE6 78 x) 0 78 x colChecks_join_0_78
    (Nat.zero_le _) (List.mem_range.mp hx)

end VOA.DeligneAudit.DeligneDivisor.E6

#print axioms VOA.DeligneAudit.DeligneDivisor.E6.e6_colChecks
