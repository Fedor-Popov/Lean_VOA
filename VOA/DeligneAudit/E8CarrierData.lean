/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8CarrierU3000
import VOA.DeligneAudit.E8CarrierU3001
import VOA.DeligneAudit.E8CarrierU3002
import VOA.DeligneAudit.E8CarrierU3003
import VOA.DeligneAudit.E8CarrierU3004
import VOA.DeligneAudit.E8CarrierU3005
import VOA.DeligneAudit.E8CarrierU3006
import VOA.DeligneAudit.E8CarrierU3007
import VOA.DeligneAudit.E8CarrierU3008
import VOA.DeligneAudit.E8CarrierU3009
import VOA.DeligneAudit.E8CarrierU3010
import VOA.DeligneAudit.E8CarrierU3011
import VOA.DeligneAudit.E8CarrierU3012
import VOA.DeligneAudit.E8CarrierU3013
import VOA.DeligneAudit.E8CarrierU3014
import VOA.DeligneAudit.E8CarrierU3015
import VOA.DeligneAudit.E8CarrierU3016
import VOA.DeligneAudit.E8CarrierU3017
import VOA.DeligneAudit.E8CarrierU3018
import VOA.DeligneAudit.E8CarrierU3019
import VOA.DeligneAudit.E8CarrierU3020
import VOA.DeligneAudit.E8CarrierU3021
import VOA.DeligneAudit.E8CarrierU3022
import VOA.DeligneAudit.E8CarrierU3023
import VOA.DeligneAudit.E8CarrierU3024
import VOA.DeligneAudit.E8CarrierU3025
import VOA.DeligneAudit.E8CarrierU3026
import VOA.DeligneAudit.E8CarrierU3027
import VOA.DeligneAudit.E8CarrierU3028
import VOA.DeligneAudit.E8CarrierU3029
import VOA.DeligneAudit.E8CarrierU3030
import VOA.DeligneAudit.E8CarrierU3031
import VOA.DeligneAudit.E8CarrierU3032
import VOA.DeligneAudit.E8CarrierU3033
import VOA.DeligneAudit.E8CarrierU3034
import VOA.DeligneAudit.E8CarrierU3035
import VOA.DeligneAudit.E8CarrierU3036
import VOA.DeligneAudit.E8CarrierU3037
import VOA.DeligneAudit.E8CarrierU3038
import VOA.DeligneAudit.E8CarrierU3039
import VOA.DeligneAudit.E8CarrierU3040
import VOA.DeligneAudit.E8CarrierU3041
import VOA.DeligneAudit.E8CarrierU3042
import VOA.DeligneAudit.E8CarrierU3043
import VOA.DeligneAudit.E8CarrierU3044
import VOA.DeligneAudit.E8CarrierU3045
import VOA.DeligneAudit.E8CarrierU3046
import VOA.DeligneAudit.E8CarrierU3047
import VOA.DeligneAudit.E8CarrierU3048
import VOA.DeligneAudit.E8CarrierU3049
import VOA.DeligneAudit.E8CarrierU3050
import VOA.DeligneAudit.E8CarrierU3051
import VOA.DeligneAudit.E8CarrierU3052
import VOA.DeligneAudit.E8CarrierU3053
import VOA.DeligneAudit.E8CarrierU3054
import VOA.DeligneAudit.E8CarrierU3055
import VOA.DeligneAudit.E8CarrierU3056
import VOA.DeligneAudit.E8CarrierU3057
import VOA.DeligneAudit.E8CarrierU3058
import VOA.DeligneAudit.E8CarrierU3059
import VOA.DeligneAudit.E8CarrierU3060
import VOA.DeligneAudit.E8CarrierU3061
import VOA.DeligneAudit.DeligneCarrierData
import VOA.DeligneAudit.A2Carrier

set_option linter.style.longLine false

/-!
# The E₈ type data for the carrier chain

`E8data : DeligneCarrierData` with `n = 248` (basis of `casimir_cert/cert_E8.json`), the 3875 relations of
`I₂ⁿˢ` (`E8CarrierTables`), the Casimir, and **U3 for all 248 currents, Lean-checked** by the sparse certificates
of `E8CarrierU3A..M` (reflection checker `E7Sparse`, no `ring`).
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E8

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E7Sparse VOA.DeligneAudit.E8Sparse

noncomputable section

/-- Sparse terms as an entry list over `Fin 248`. -/
def toEntries (l : List (ℕ × ℕ × ℤ)) : List (Fin 248 × Fin 248 × ℂ) :=
  l.map fun t => (Fin.ofNat 248 t.1, Fin.ofNat 248 t.2.1, ((t.2.2 : ℤ) : ℂ))

/-- The relations of `I₂ⁿˢ`. -/
def rel (r : Fin 3875) : Fin 248 × Fin 248 → ℂ := A2.entryMatrix (toEntries (relQ r))

/-- The Casimir. -/
def cas : Fin 248 × Fin 248 → ℂ := A2.entryMatrix (toEntries qQ)

theorem Xn_eq (i : ℕ) (hi : i < 248) : Xn 248 i = X (Fin.ofNat 248 i) := by
  rw [Xn, dif_pos hi]
  congr 1
  ext
  simp [Fin.ofNat, Nat.mod_eq_of_lt hi]

theorem Xn_fin (a : Fin 248) : Xn 248 a = X a := by
  rw [Xn, dif_pos a.2]

theorem quadraticRelation_toEntries (l : List (ℕ × ℕ × ℤ)) (hl : inRange248 l = true) :
    quadraticRelation (A2.entryMatrix (toEntries l)) = quadP 248 l := by
  rw [A2.quadraticRelation_entryMatrix, toEntries, List.map_map, quadP]
  congr 1
  apply List.map_congr_left
  intro t ht
  have h := List.all_eq_true.mp hl t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Function.comp_apply, Xn_eq _ h.1, Xn_eq _ h.2, smul_eq_C_mul]
  simp

theorem quadraticRelation_rel (r : Fin 3875) : quadraticRelation (rel r) = quadP 248 (relQ r) :=
  quadraticRelation_toEntries _ (List.all_eq_true.mp rel_inRange r (List.mem_range.mpr r.2))

theorem quadraticRelation_cas : quadraticRelation cas = quadP 248 qQ :=
  quadraticRelation_toEntries _ qQ_inRange

theorem relQ_mem (b : ℕ) (hb : b < 3875) : quadP 248 (relQ b) ∈ quadraticIdeal rel := by
  have := quadraticRelation_rel ⟨b, hb⟩
  rw [← this]
  exact Ideal.subset_span ⟨⟨b, hb⟩, rfl⟩

theorem u3_of_ok (a : Fin 248) (c : List ℕ) (h : u3OK a c = true) :
    X a * quadraticRelation cas ∈ quadraticIdeal rel := by
  simp only [u3OK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hL, hb⟩, hc⟩ := h
  have := mem_of_u3Check relQ (quadraticIdeal rel) qQ a _ hL _
    (fun t ht => relQ_mem _ (by simpa using List.all_eq_true.mp hb t ht)) hc
  rw [quadraticRelation_cas, ← Xn_fin]
  exact this

theorem u3_of_chain (a : Fin 248) (c : List ℕ) (hpre : certPre c = true)
    (hs : small (u3List a c) = true) (bs : List ℕ) (hch : BucketChain (u3List a c) (0 :: bs)) :
    X a * quadraticRelation cas ∈ quadraticIdeal rel := by
  simp only [certPre, Bool.and_eq_true, decide_eq_true_eq] at hpre
  obtain ⟨hL, hb⟩ := hpre
  have := mem_of_cubicP_zero relQ (quadraticIdeal rel) qQ a _ hL _
    (fun t ht => relQ_mem _ (by simpa using List.all_eq_true.mp hb t ht))
    (cubicP_eq_zero_of_chain _ hs bs hch)
  rw [quadraticRelation_cas, ← Xn_fin]
  exact this

/-- **The E₈ type data**: 248 currents, `I₂ⁿˢ = 3875`, the Casimir, U3 checked. -/
def E8data : DeligneCarrierData where
  n := 248
  ρ := Fin 3875
  rel := rel
  cas := cas
  u3 a := by
    fin_cases a
    · exact u3_of_chain _ _ cert0_pre cert0_small _ cert0_chain
    · exact u3_of_chain _ _ cert1_pre cert1_small _ cert1_chain
    · exact u3_of_chain _ _ cert2_pre cert2_small _ cert2_chain
    · exact u3_of_chain _ _ cert3_pre cert3_small _ cert3_chain
    · exact u3_of_chain _ _ cert4_pre cert4_small _ cert4_chain
    · exact u3_of_chain _ _ cert5_pre cert5_small _ cert5_chain
    · exact u3_of_chain _ _ cert6_pre cert6_small _ cert6_chain
    · exact u3_of_chain _ _ cert7_pre cert7_small _ cert7_chain
    · exact u3_of_chain _ _ cert8_pre cert8_small _ cert8_chain
    · exact u3_of_chain _ _ cert9_pre cert9_small _ cert9_chain
    · exact u3_of_chain _ _ cert10_pre cert10_small _ cert10_chain
    · exact u3_of_chain _ _ cert11_pre cert11_small _ cert11_chain
    · exact u3_of_chain _ _ cert12_pre cert12_small _ cert12_chain
    · exact u3_of_chain _ _ cert13_pre cert13_small _ cert13_chain
    · exact u3_of_chain _ _ cert14_pre cert14_small _ cert14_chain
    · exact u3_of_chain _ _ cert15_pre cert15_small _ cert15_chain
    · exact u3_of_chain _ _ cert16_pre cert16_small _ cert16_chain
    · exact u3_of_chain _ _ cert17_pre cert17_small _ cert17_chain
    · exact u3_of_chain _ _ cert18_pre cert18_small _ cert18_chain
    · exact u3_of_chain _ _ cert19_pre cert19_small _ cert19_chain
    · exact u3_of_chain _ _ cert20_pre cert20_small _ cert20_chain
    · exact u3_of_chain _ _ cert21_pre cert21_small _ cert21_chain
    · exact u3_of_chain _ _ cert22_pre cert22_small _ cert22_chain
    · exact u3_of_chain _ _ cert23_pre cert23_small _ cert23_chain
    · exact u3_of_chain _ _ cert24_pre cert24_small _ cert24_chain
    · exact u3_of_chain _ _ cert25_pre cert25_small _ cert25_chain
    · exact u3_of_chain _ _ cert26_pre cert26_small _ cert26_chain
    · exact u3_of_chain _ _ cert27_pre cert27_small _ cert27_chain
    · exact u3_of_chain _ _ cert28_pre cert28_small _ cert28_chain
    · exact u3_of_chain _ _ cert29_pre cert29_small _ cert29_chain
    · exact u3_of_chain _ _ cert30_pre cert30_small _ cert30_chain
    · exact u3_of_chain _ _ cert31_pre cert31_small _ cert31_chain
    · exact u3_of_chain _ _ cert32_pre cert32_small _ cert32_chain
    · exact u3_of_chain _ _ cert33_pre cert33_small _ cert33_chain
    · exact u3_of_chain _ _ cert34_pre cert34_small _ cert34_chain
    · exact u3_of_chain _ _ cert35_pre cert35_small _ cert35_chain
    · exact u3_of_chain _ _ cert36_pre cert36_small _ cert36_chain
    · exact u3_of_chain _ _ cert37_pre cert37_small _ cert37_chain
    · exact u3_of_chain _ _ cert38_pre cert38_small _ cert38_chain
    · exact u3_of_chain _ _ cert39_pre cert39_small _ cert39_chain
    · exact u3_of_chain _ _ cert40_pre cert40_small _ cert40_chain
    · exact u3_of_chain _ _ cert41_pre cert41_small _ cert41_chain
    · exact u3_of_chain _ _ cert42_pre cert42_small _ cert42_chain
    · exact u3_of_chain _ _ cert43_pre cert43_small _ cert43_chain
    · exact u3_of_chain _ _ cert44_pre cert44_small _ cert44_chain
    · exact u3_of_chain _ _ cert45_pre cert45_small _ cert45_chain
    · exact u3_of_chain _ _ cert46_pre cert46_small _ cert46_chain
    · exact u3_of_chain _ _ cert47_pre cert47_small _ cert47_chain
    · exact u3_of_chain _ _ cert48_pre cert48_small _ cert48_chain
    · exact u3_of_chain _ _ cert49_pre cert49_small _ cert49_chain
    · exact u3_of_chain _ _ cert50_pre cert50_small _ cert50_chain
    · exact u3_of_chain _ _ cert51_pre cert51_small _ cert51_chain
    · exact u3_of_chain _ _ cert52_pre cert52_small _ cert52_chain
    · exact u3_of_chain _ _ cert53_pre cert53_small _ cert53_chain
    · exact u3_of_chain _ _ cert54_pre cert54_small _ cert54_chain
    · exact u3_of_chain _ _ cert55_pre cert55_small _ cert55_chain
    · exact u3_of_chain _ _ cert56_pre cert56_small _ cert56_chain
    · exact u3_of_chain _ _ cert57_pre cert57_small _ cert57_chain
    · exact u3_of_chain _ _ cert58_pre cert58_small _ cert58_chain
    · exact u3_of_chain _ _ cert59_pre cert59_small _ cert59_chain
    · exact u3_of_chain _ _ cert60_pre cert60_small _ cert60_chain
    · exact u3_of_chain _ _ cert61_pre cert61_small _ cert61_chain
    · exact u3_of_chain _ _ cert62_pre cert62_small _ cert62_chain
    · exact u3_of_chain _ _ cert63_pre cert63_small _ cert63_chain
    · exact u3_of_chain _ _ cert64_pre cert64_small _ cert64_chain
    · exact u3_of_chain _ _ cert65_pre cert65_small _ cert65_chain
    · exact u3_of_chain _ _ cert66_pre cert66_small _ cert66_chain
    · exact u3_of_chain _ _ cert67_pre cert67_small _ cert67_chain
    · exact u3_of_chain _ _ cert68_pre cert68_small _ cert68_chain
    · exact u3_of_chain _ _ cert69_pre cert69_small _ cert69_chain
    · exact u3_of_chain _ _ cert70_pre cert70_small _ cert70_chain
    · exact u3_of_chain _ _ cert71_pre cert71_small _ cert71_chain
    · exact u3_of_chain _ _ cert72_pre cert72_small _ cert72_chain
    · exact u3_of_chain _ _ cert73_pre cert73_small _ cert73_chain
    · exact u3_of_chain _ _ cert74_pre cert74_small _ cert74_chain
    · exact u3_of_chain _ _ cert75_pre cert75_small _ cert75_chain
    · exact u3_of_chain _ _ cert76_pre cert76_small _ cert76_chain
    · exact u3_of_chain _ _ cert77_pre cert77_small _ cert77_chain
    · exact u3_of_chain _ _ cert78_pre cert78_small _ cert78_chain
    · exact u3_of_chain _ _ cert79_pre cert79_small _ cert79_chain
    · exact u3_of_chain _ _ cert80_pre cert80_small _ cert80_chain
    · exact u3_of_chain _ _ cert81_pre cert81_small _ cert81_chain
    · exact u3_of_chain _ _ cert82_pre cert82_small _ cert82_chain
    · exact u3_of_chain _ _ cert83_pre cert83_small _ cert83_chain
    · exact u3_of_chain _ _ cert84_pre cert84_small _ cert84_chain
    · exact u3_of_chain _ _ cert85_pre cert85_small _ cert85_chain
    · exact u3_of_chain _ _ cert86_pre cert86_small _ cert86_chain
    · exact u3_of_chain _ _ cert87_pre cert87_small _ cert87_chain
    · exact u3_of_chain _ _ cert88_pre cert88_small _ cert88_chain
    · exact u3_of_chain _ _ cert89_pre cert89_small _ cert89_chain
    · exact u3_of_chain _ _ cert90_pre cert90_small _ cert90_chain
    · exact u3_of_chain _ _ cert91_pre cert91_small _ cert91_chain
    · exact u3_of_chain _ _ cert92_pre cert92_small _ cert92_chain
    · exact u3_of_chain _ _ cert93_pre cert93_small _ cert93_chain
    · exact u3_of_chain _ _ cert94_pre cert94_small _ cert94_chain
    · exact u3_of_chain _ _ cert95_pre cert95_small _ cert95_chain
    · exact u3_of_chain _ _ cert96_pre cert96_small _ cert96_chain
    · exact u3_of_chain _ _ cert97_pre cert97_small _ cert97_chain
    · exact u3_of_chain _ _ cert98_pre cert98_small _ cert98_chain
    · exact u3_of_chain _ _ cert99_pre cert99_small _ cert99_chain
    · exact u3_of_chain _ _ cert100_pre cert100_small _ cert100_chain
    · exact u3_of_chain _ _ cert101_pre cert101_small _ cert101_chain
    · exact u3_of_chain _ _ cert102_pre cert102_small _ cert102_chain
    · exact u3_of_chain _ _ cert103_pre cert103_small _ cert103_chain
    · exact u3_of_chain _ _ cert104_pre cert104_small _ cert104_chain
    · exact u3_of_chain _ _ cert105_pre cert105_small _ cert105_chain
    · exact u3_of_chain _ _ cert106_pre cert106_small _ cert106_chain
    · exact u3_of_chain _ _ cert107_pre cert107_small _ cert107_chain
    · exact u3_of_chain _ _ cert108_pre cert108_small _ cert108_chain
    · exact u3_of_chain _ _ cert109_pre cert109_small _ cert109_chain
    · exact u3_of_chain _ _ cert110_pre cert110_small _ cert110_chain
    · exact u3_of_chain _ _ cert111_pre cert111_small _ cert111_chain
    · exact u3_of_chain _ _ cert112_pre cert112_small _ cert112_chain
    · exact u3_of_chain _ _ cert113_pre cert113_small _ cert113_chain
    · exact u3_of_chain _ _ cert114_pre cert114_small _ cert114_chain
    · exact u3_of_chain _ _ cert115_pre cert115_small _ cert115_chain
    · exact u3_of_chain _ _ cert116_pre cert116_small _ cert116_chain
    · exact u3_of_chain _ _ cert117_pre cert117_small _ cert117_chain
    · exact u3_of_chain _ _ cert118_pre cert118_small _ cert118_chain
    · exact u3_of_chain _ _ cert119_pre cert119_small _ cert119_chain
    · exact u3_of_chain _ _ cert120_pre cert120_small _ cert120_chain
    · exact u3_of_chain _ _ cert121_pre cert121_small _ cert121_chain
    · exact u3_of_chain _ _ cert122_pre cert122_small _ cert122_chain
    · exact u3_of_chain _ _ cert123_pre cert123_small _ cert123_chain
    · exact u3_of_chain _ _ cert124_pre cert124_small _ cert124_chain
    · exact u3_of_chain _ _ cert125_pre cert125_small _ cert125_chain
    · exact u3_of_chain _ _ cert126_pre cert126_small _ cert126_chain
    · exact u3_of_chain _ _ cert127_pre cert127_small _ cert127_chain
    · exact u3_of_chain _ _ cert128_pre cert128_small _ cert128_chain
    · exact u3_of_chain _ _ cert129_pre cert129_small _ cert129_chain
    · exact u3_of_chain _ _ cert130_pre cert130_small _ cert130_chain
    · exact u3_of_chain _ _ cert131_pre cert131_small _ cert131_chain
    · exact u3_of_chain _ _ cert132_pre cert132_small _ cert132_chain
    · exact u3_of_chain _ _ cert133_pre cert133_small _ cert133_chain
    · exact u3_of_chain _ _ cert134_pre cert134_small _ cert134_chain
    · exact u3_of_chain _ _ cert135_pre cert135_small _ cert135_chain
    · exact u3_of_chain _ _ cert136_pre cert136_small _ cert136_chain
    · exact u3_of_chain _ _ cert137_pre cert137_small _ cert137_chain
    · exact u3_of_chain _ _ cert138_pre cert138_small _ cert138_chain
    · exact u3_of_chain _ _ cert139_pre cert139_small _ cert139_chain
    · exact u3_of_chain _ _ cert140_pre cert140_small _ cert140_chain
    · exact u3_of_chain _ _ cert141_pre cert141_small _ cert141_chain
    · exact u3_of_chain _ _ cert142_pre cert142_small _ cert142_chain
    · exact u3_of_chain _ _ cert143_pre cert143_small _ cert143_chain
    · exact u3_of_chain _ _ cert144_pre cert144_small _ cert144_chain
    · exact u3_of_chain _ _ cert145_pre cert145_small _ cert145_chain
    · exact u3_of_chain _ _ cert146_pre cert146_small _ cert146_chain
    · exact u3_of_chain _ _ cert147_pre cert147_small _ cert147_chain
    · exact u3_of_chain _ _ cert148_pre cert148_small _ cert148_chain
    · exact u3_of_chain _ _ cert149_pre cert149_small _ cert149_chain
    · exact u3_of_chain _ _ cert150_pre cert150_small _ cert150_chain
    · exact u3_of_chain _ _ cert151_pre cert151_small _ cert151_chain
    · exact u3_of_chain _ _ cert152_pre cert152_small _ cert152_chain
    · exact u3_of_chain _ _ cert153_pre cert153_small _ cert153_chain
    · exact u3_of_chain _ _ cert154_pre cert154_small _ cert154_chain
    · exact u3_of_chain _ _ cert155_pre cert155_small _ cert155_chain
    · exact u3_of_chain _ _ cert156_pre cert156_small _ cert156_chain
    · exact u3_of_chain _ _ cert157_pre cert157_small _ cert157_chain
    · exact u3_of_chain _ _ cert158_pre cert158_small _ cert158_chain
    · exact u3_of_chain _ _ cert159_pre cert159_small _ cert159_chain
    · exact u3_of_chain _ _ cert160_pre cert160_small _ cert160_chain
    · exact u3_of_chain _ _ cert161_pre cert161_small _ cert161_chain
    · exact u3_of_chain _ _ cert162_pre cert162_small _ cert162_chain
    · exact u3_of_chain _ _ cert163_pre cert163_small _ cert163_chain
    · exact u3_of_chain _ _ cert164_pre cert164_small _ cert164_chain
    · exact u3_of_chain _ _ cert165_pre cert165_small _ cert165_chain
    · exact u3_of_chain _ _ cert166_pre cert166_small _ cert166_chain
    · exact u3_of_chain _ _ cert167_pre cert167_small _ cert167_chain
    · exact u3_of_chain _ _ cert168_pre cert168_small _ cert168_chain
    · exact u3_of_chain _ _ cert169_pre cert169_small _ cert169_chain
    · exact u3_of_chain _ _ cert170_pre cert170_small _ cert170_chain
    · exact u3_of_chain _ _ cert171_pre cert171_small _ cert171_chain
    · exact u3_of_chain _ _ cert172_pre cert172_small _ cert172_chain
    · exact u3_of_chain _ _ cert173_pre cert173_small _ cert173_chain
    · exact u3_of_chain _ _ cert174_pre cert174_small _ cert174_chain
    · exact u3_of_chain _ _ cert175_pre cert175_small _ cert175_chain
    · exact u3_of_chain _ _ cert176_pre cert176_small _ cert176_chain
    · exact u3_of_chain _ _ cert177_pre cert177_small _ cert177_chain
    · exact u3_of_chain _ _ cert178_pre cert178_small _ cert178_chain
    · exact u3_of_chain _ _ cert179_pre cert179_small _ cert179_chain
    · exact u3_of_chain _ _ cert180_pre cert180_small _ cert180_chain
    · exact u3_of_chain _ _ cert181_pre cert181_small _ cert181_chain
    · exact u3_of_chain _ _ cert182_pre cert182_small _ cert182_chain
    · exact u3_of_chain _ _ cert183_pre cert183_small _ cert183_chain
    · exact u3_of_chain _ _ cert184_pre cert184_small _ cert184_chain
    · exact u3_of_chain _ _ cert185_pre cert185_small _ cert185_chain
    · exact u3_of_chain _ _ cert186_pre cert186_small _ cert186_chain
    · exact u3_of_chain _ _ cert187_pre cert187_small _ cert187_chain
    · exact u3_of_chain _ _ cert188_pre cert188_small _ cert188_chain
    · exact u3_of_chain _ _ cert189_pre cert189_small _ cert189_chain
    · exact u3_of_chain _ _ cert190_pre cert190_small _ cert190_chain
    · exact u3_of_chain _ _ cert191_pre cert191_small _ cert191_chain
    · exact u3_of_chain _ _ cert192_pre cert192_small _ cert192_chain
    · exact u3_of_chain _ _ cert193_pre cert193_small _ cert193_chain
    · exact u3_of_chain _ _ cert194_pre cert194_small _ cert194_chain
    · exact u3_of_chain _ _ cert195_pre cert195_small _ cert195_chain
    · exact u3_of_chain _ _ cert196_pre cert196_small _ cert196_chain
    · exact u3_of_chain _ _ cert197_pre cert197_small _ cert197_chain
    · exact u3_of_chain _ _ cert198_pre cert198_small _ cert198_chain
    · exact u3_of_chain _ _ cert199_pre cert199_small _ cert199_chain
    · exact u3_of_chain _ _ cert200_pre cert200_small _ cert200_chain
    · exact u3_of_chain _ _ cert201_pre cert201_small _ cert201_chain
    · exact u3_of_chain _ _ cert202_pre cert202_small _ cert202_chain
    · exact u3_of_chain _ _ cert203_pre cert203_small _ cert203_chain
    · exact u3_of_chain _ _ cert204_pre cert204_small _ cert204_chain
    · exact u3_of_chain _ _ cert205_pre cert205_small _ cert205_chain
    · exact u3_of_chain _ _ cert206_pre cert206_small _ cert206_chain
    · exact u3_of_chain _ _ cert207_pre cert207_small _ cert207_chain
    · exact u3_of_chain _ _ cert208_pre cert208_small _ cert208_chain
    · exact u3_of_chain _ _ cert209_pre cert209_small _ cert209_chain
    · exact u3_of_chain _ _ cert210_pre cert210_small _ cert210_chain
    · exact u3_of_chain _ _ cert211_pre cert211_small _ cert211_chain
    · exact u3_of_chain _ _ cert212_pre cert212_small _ cert212_chain
    · exact u3_of_chain _ _ cert213_pre cert213_small _ cert213_chain
    · exact u3_of_chain _ _ cert214_pre cert214_small _ cert214_chain
    · exact u3_of_chain _ _ cert215_pre cert215_small _ cert215_chain
    · exact u3_of_chain _ _ cert216_pre cert216_small _ cert216_chain
    · exact u3_of_chain _ _ cert217_pre cert217_small _ cert217_chain
    · exact u3_of_chain _ _ cert218_pre cert218_small _ cert218_chain
    · exact u3_of_chain _ _ cert219_pre cert219_small _ cert219_chain
    · exact u3_of_chain _ _ cert220_pre cert220_small _ cert220_chain
    · exact u3_of_chain _ _ cert221_pre cert221_small _ cert221_chain
    · exact u3_of_chain _ _ cert222_pre cert222_small _ cert222_chain
    · exact u3_of_chain _ _ cert223_pre cert223_small _ cert223_chain
    · exact u3_of_chain _ _ cert224_pre cert224_small _ cert224_chain
    · exact u3_of_chain _ _ cert225_pre cert225_small _ cert225_chain
    · exact u3_of_chain _ _ cert226_pre cert226_small _ cert226_chain
    · exact u3_of_chain _ _ cert227_pre cert227_small _ cert227_chain
    · exact u3_of_chain _ _ cert228_pre cert228_small _ cert228_chain
    · exact u3_of_chain _ _ cert229_pre cert229_small _ cert229_chain
    · exact u3_of_chain _ _ cert230_pre cert230_small _ cert230_chain
    · exact u3_of_chain _ _ cert231_pre cert231_small _ cert231_chain
    · exact u3_of_chain _ _ cert232_pre cert232_small _ cert232_chain
    · exact u3_of_chain _ _ cert233_pre cert233_small _ cert233_chain
    · exact u3_of_chain _ _ cert234_pre cert234_small _ cert234_chain
    · exact u3_of_chain _ _ cert235_pre cert235_small _ cert235_chain
    · exact u3_of_chain _ _ cert236_pre cert236_small _ cert236_chain
    · exact u3_of_chain _ _ cert237_pre cert237_small _ cert237_chain
    · exact u3_of_chain _ _ cert238_pre cert238_small _ cert238_chain
    · exact u3_of_chain _ _ cert239_pre cert239_small _ cert239_chain
    · exact u3_of_chain _ _ cert240_pre cert240_small _ cert240_chain
    · exact u3_of_chain _ _ cert241_pre cert241_small _ cert241_chain
    · exact u3_of_chain _ _ cert242_pre cert242_small _ cert242_chain
    · exact u3_of_chain _ _ cert243_pre cert243_small _ cert243_chain
    · exact u3_of_chain _ _ cert244_pre cert244_small _ cert244_chain
    · exact u3_of_chain _ _ cert245_pre cert245_small _ cert245_chain
    · exact u3_of_chain _ _ cert246_pre cert246_small _ cert246_chain
    · exact u3_of_chain _ _ cert247_pre cert247_small _ cert247_chain

end

end VOA.DeligneAudit.DeligneCarrier.E8

section AxiomAudit
open VOA.DeligneAudit.DeligneCarrier.E8
#print axioms E8data
end AxiomAudit
