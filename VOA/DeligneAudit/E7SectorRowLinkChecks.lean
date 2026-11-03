import VOA.DeligneAudit.DeligneDivisorCheckRange
import VOA.DeligneAudit.E7SectorRowLink000
import VOA.DeligneAudit.E7SectorRowLink003
import VOA.DeligneAudit.E7SectorRowLink006
import VOA.DeligneAudit.E7SectorRowLink009
import VOA.DeligneAudit.E7SectorRowLink012
import VOA.DeligneAudit.E7SectorRowLink015
import VOA.DeligneAudit.E7SectorRowLink018
import VOA.DeligneAudit.E7SectorRowLink021
import VOA.DeligneAudit.E7SectorRowLink024
import VOA.DeligneAudit.E7SectorRowLink027
import VOA.DeligneAudit.E7SectorRowLink030
import VOA.DeligneAudit.E7SectorRowLink033
import VOA.DeligneAudit.E7SectorRowLink036
import VOA.DeligneAudit.E7SectorRowLink039
import VOA.DeligneAudit.E7SectorRowLink042
import VOA.DeligneAudit.E7SectorRowLink045
import VOA.DeligneAudit.E7SectorRowLink048
import VOA.DeligneAudit.E7SectorRowLink051
import VOA.DeligneAudit.E7SectorRowLink054
import VOA.DeligneAudit.E7SectorRowLink057
import VOA.DeligneAudit.E7SectorRowLink060
import VOA.DeligneAudit.E7SectorRowLink063
import VOA.DeligneAudit.E7SectorRowLink066
import VOA.DeligneAudit.E7SectorRowLink069
import VOA.DeligneAudit.E7SectorRowLink072
import VOA.DeligneAudit.E7SectorRowLink075
import VOA.DeligneAudit.E7SectorRowLink078
import VOA.DeligneAudit.E7SectorRowLink081
import VOA.DeligneAudit.E7SectorRowLink084
import VOA.DeligneAudit.E7SectorRowLink087
import VOA.DeligneAudit.E7SectorRowLink090
import VOA.DeligneAudit.E7SectorRowLink093
import VOA.DeligneAudit.E7SectorRowLink096
import VOA.DeligneAudit.E7SectorRowLink099
import VOA.DeligneAudit.E7SectorRowLink102
import VOA.DeligneAudit.E7SectorRowLink105
import VOA.DeligneAudit.E7SectorRowLink108
import VOA.DeligneAudit.E7SectorRowLink111
import VOA.DeligneAudit.E7SectorRowLink114
import VOA.DeligneAudit.E7SectorRowLink117
import VOA.DeligneAudit.E7SectorRowLink120
import VOA.DeligneAudit.E7SectorRowLink123
import VOA.DeligneAudit.E7SectorRowLink126
import VOA.DeligneAudit.E7SectorRowLink129
import VOA.DeligneAudit.E7SectorRowLink130

/-! Opaque assembly of all 133 original E7 row comparisons from fixed
independently checked ranges. No full-range kernel decision is repeated. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.DeligneAudit.DeligneDivisor

private theorem rowLink_join000_006 :
    (List.range' 0 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 0 3 6 (by decide) (by decide)
    rowLink000_003 rowLink003_006

private theorem rowLink_join009_015 :
    (List.range' 9 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 9 12 15 (by decide) (by decide)
    rowLink009_012 rowLink012_015

private theorem rowLink_join006_015 :
    (List.range' 6 9).all rowLinkOK = true :=
  checkRange_join rowLinkOK 6 9 15 (by decide) (by decide)
    rowLink006_009 rowLink_join009_015

private theorem rowLink_join000_015 :
    (List.range' 0 15).all rowLinkOK = true :=
  checkRange_join rowLinkOK 0 6 15 (by decide) (by decide)
    rowLink_join000_006 rowLink_join006_015

private theorem rowLink_join018_024 :
    (List.range' 18 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 18 21 24 (by decide) (by decide)
    rowLink018_021 rowLink021_024

private theorem rowLink_join015_024 :
    (List.range' 15 9).all rowLinkOK = true :=
  checkRange_join rowLinkOK 15 18 24 (by decide) (by decide)
    rowLink015_018 rowLink_join018_024

private theorem rowLink_join027_033 :
    (List.range' 27 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 27 30 33 (by decide) (by decide)
    rowLink027_030 rowLink030_033

private theorem rowLink_join024_033 :
    (List.range' 24 9).all rowLinkOK = true :=
  checkRange_join rowLinkOK 24 27 33 (by decide) (by decide)
    rowLink024_027 rowLink_join027_033

private theorem rowLink_join015_033 :
    (List.range' 15 18).all rowLinkOK = true :=
  checkRange_join rowLinkOK 15 24 33 (by decide) (by decide)
    rowLink_join015_024 rowLink_join024_033

private theorem rowLink_join000_033 :
    (List.range' 0 33).all rowLinkOK = true :=
  checkRange_join rowLinkOK 0 15 33 (by decide) (by decide)
    rowLink_join000_015 rowLink_join015_033

private theorem rowLink_join033_039 :
    (List.range' 33 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 33 36 39 (by decide) (by decide)
    rowLink033_036 rowLink036_039

private theorem rowLink_join042_048 :
    (List.range' 42 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 42 45 48 (by decide) (by decide)
    rowLink042_045 rowLink045_048

private theorem rowLink_join039_048 :
    (List.range' 39 9).all rowLinkOK = true :=
  checkRange_join rowLinkOK 39 42 48 (by decide) (by decide)
    rowLink039_042 rowLink_join042_048

private theorem rowLink_join033_048 :
    (List.range' 33 15).all rowLinkOK = true :=
  checkRange_join rowLinkOK 33 39 48 (by decide) (by decide)
    rowLink_join033_039 rowLink_join039_048

private theorem rowLink_join051_057 :
    (List.range' 51 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 51 54 57 (by decide) (by decide)
    rowLink051_054 rowLink054_057

private theorem rowLink_join048_057 :
    (List.range' 48 9).all rowLinkOK = true :=
  checkRange_join rowLinkOK 48 51 57 (by decide) (by decide)
    rowLink048_051 rowLink_join051_057

private theorem rowLink_join060_066 :
    (List.range' 60 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 60 63 66 (by decide) (by decide)
    rowLink060_063 rowLink063_066

private theorem rowLink_join057_066 :
    (List.range' 57 9).all rowLinkOK = true :=
  checkRange_join rowLinkOK 57 60 66 (by decide) (by decide)
    rowLink057_060 rowLink_join060_066

private theorem rowLink_join048_066 :
    (List.range' 48 18).all rowLinkOK = true :=
  checkRange_join rowLinkOK 48 57 66 (by decide) (by decide)
    rowLink_join048_057 rowLink_join057_066

private theorem rowLink_join033_066 :
    (List.range' 33 33).all rowLinkOK = true :=
  checkRange_join rowLinkOK 33 48 66 (by decide) (by decide)
    rowLink_join033_048 rowLink_join048_066

private theorem rowLink_join000_066 :
    (List.range' 0 66).all rowLinkOK = true :=
  checkRange_join rowLinkOK 0 33 66 (by decide) (by decide)
    rowLink_join000_033 rowLink_join033_066

private theorem rowLink_join066_072 :
    (List.range' 66 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 66 69 72 (by decide) (by decide)
    rowLink066_069 rowLink069_072

private theorem rowLink_join075_081 :
    (List.range' 75 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 75 78 81 (by decide) (by decide)
    rowLink075_078 rowLink078_081

private theorem rowLink_join072_081 :
    (List.range' 72 9).all rowLinkOK = true :=
  checkRange_join rowLinkOK 72 75 81 (by decide) (by decide)
    rowLink072_075 rowLink_join075_081

private theorem rowLink_join066_081 :
    (List.range' 66 15).all rowLinkOK = true :=
  checkRange_join rowLinkOK 66 72 81 (by decide) (by decide)
    rowLink_join066_072 rowLink_join072_081

private theorem rowLink_join084_090 :
    (List.range' 84 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 84 87 90 (by decide) (by decide)
    rowLink084_087 rowLink087_090

private theorem rowLink_join081_090 :
    (List.range' 81 9).all rowLinkOK = true :=
  checkRange_join rowLinkOK 81 84 90 (by decide) (by decide)
    rowLink081_084 rowLink_join084_090

private theorem rowLink_join093_099 :
    (List.range' 93 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 93 96 99 (by decide) (by decide)
    rowLink093_096 rowLink096_099

private theorem rowLink_join090_099 :
    (List.range' 90 9).all rowLinkOK = true :=
  checkRange_join rowLinkOK 90 93 99 (by decide) (by decide)
    rowLink090_093 rowLink_join093_099

private theorem rowLink_join081_099 :
    (List.range' 81 18).all rowLinkOK = true :=
  checkRange_join rowLinkOK 81 90 99 (by decide) (by decide)
    rowLink_join081_090 rowLink_join090_099

private theorem rowLink_join066_099 :
    (List.range' 66 33).all rowLinkOK = true :=
  checkRange_join rowLinkOK 66 81 99 (by decide) (by decide)
    rowLink_join066_081 rowLink_join081_099

private theorem rowLink_join102_108 :
    (List.range' 102 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 102 105 108 (by decide) (by decide)
    rowLink102_105 rowLink105_108

private theorem rowLink_join099_108 :
    (List.range' 99 9).all rowLinkOK = true :=
  checkRange_join rowLinkOK 99 102 108 (by decide) (by decide)
    rowLink099_102 rowLink_join102_108

private theorem rowLink_join111_117 :
    (List.range' 111 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 111 114 117 (by decide) (by decide)
    rowLink111_114 rowLink114_117

private theorem rowLink_join108_117 :
    (List.range' 108 9).all rowLinkOK = true :=
  checkRange_join rowLinkOK 108 111 117 (by decide) (by decide)
    rowLink108_111 rowLink_join111_117

private theorem rowLink_join099_117 :
    (List.range' 99 18).all rowLinkOK = true :=
  checkRange_join rowLinkOK 99 108 117 (by decide) (by decide)
    rowLink_join099_108 rowLink_join108_117

private theorem rowLink_join120_126 :
    (List.range' 120 6).all rowLinkOK = true :=
  checkRange_join rowLinkOK 120 123 126 (by decide) (by decide)
    rowLink120_123 rowLink123_126

private theorem rowLink_join117_126 :
    (List.range' 117 9).all rowLinkOK = true :=
  checkRange_join rowLinkOK 117 120 126 (by decide) (by decide)
    rowLink117_120 rowLink_join120_126

private theorem rowLink_join129_133 :
    (List.range' 129 4).all rowLinkOK = true :=
  checkRange_join rowLinkOK 129 130 133 (by decide) (by decide)
    rowLink129_130 rowLink130_133

private theorem rowLink_join126_133 :
    (List.range' 126 7).all rowLinkOK = true :=
  checkRange_join rowLinkOK 126 129 133 (by decide) (by decide)
    rowLink126_129 rowLink_join129_133

private theorem rowLink_join117_133 :
    (List.range' 117 16).all rowLinkOK = true :=
  checkRange_join rowLinkOK 117 126 133 (by decide) (by decide)
    rowLink_join117_126 rowLink_join126_133

private theorem rowLink_join099_133 :
    (List.range' 99 34).all rowLinkOK = true :=
  checkRange_join rowLinkOK 99 117 133 (by decide) (by decide)
    rowLink_join099_117 rowLink_join117_133

private theorem rowLink_join066_133 :
    (List.range' 66 67).all rowLinkOK = true :=
  checkRange_join rowLinkOK 66 99 133 (by decide) (by decide)
    rowLink_join066_099 rowLink_join099_133

private theorem rowLink_join000_133 :
    (List.range' 0 133).all rowLinkOK = true :=
  checkRange_join rowLinkOK 0 66 133 (by decide) (by decide)
    rowLink_join000_066 rowLink_join066_133

/-- The complete original whole-row predicate, assembled from fixed small checks. -/
theorem rowLink_all_checked : (List.range' 0 133).all rowLinkOK = true :=
  rowLink_join000_133

/-- Every original row comparison follows from the opaque full-range certificate. -/
theorem rowLink_checked (a : ℕ) (ha : a < 133) : rowLinkOK a = true :=
  checkRange_mem rowLinkOK 0 133 a rowLink_all_checked (Nat.zero_le _) ha

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.rowLink_all_checked
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.rowLink_checked
