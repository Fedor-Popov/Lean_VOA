/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7CarrierU3A
import VOA.DeligneAudit.E7CarrierU3B
import VOA.DeligneAudit.E7CarrierU3C
import VOA.DeligneAudit.E7CarrierU3D
import VOA.DeligneAudit.E7CarrierU3E
import VOA.DeligneAudit.E7CarrierU3F
import VOA.DeligneAudit.E7CarrierU3G
import VOA.DeligneAudit.E7CarrierU3H
import VOA.DeligneAudit.E7CarrierU3I
import VOA.DeligneAudit.E7CarrierU3J
import VOA.DeligneAudit.E7CarrierU3K
import VOA.DeligneAudit.E7CarrierU3L
import VOA.DeligneAudit.E7CarrierU3M
import VOA.DeligneAudit.E7CarrierU3N
import VOA.DeligneAudit.E7CarrierU3O
import VOA.DeligneAudit.E7CarrierU3P
import VOA.DeligneAudit.E7CarrierU3Q
import VOA.DeligneAudit.E7CarrierU3R
import VOA.DeligneAudit.E7CarrierU3S
import VOA.DeligneAudit.E7CarrierU3T
import VOA.DeligneAudit.E7CarrierU3U
import VOA.DeligneAudit.E7CarrierU3V
import VOA.DeligneAudit.E7CarrierU3W
import VOA.DeligneAudit.DeligneCarrierData
import VOA.DeligneAudit.A2Carrier

set_option linter.style.longLine false

/-!
# The E₇ type data for the carrier chain

`E7data : DeligneCarrierData` with `n = 133` (basis of `casimir_cert/cert_E7.json`), the 1539 relations of
`I₂ⁿˢ` (`E7CarrierTables`), the Casimir, and **U3 for all 133 currents, Lean-checked** by the sparse certificates
of `E7CarrierU3A..M` (reflection checker `E7Sparse`, no `ring`).
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E7

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E7Sparse

noncomputable section

/-- Sparse terms as an entry list over `Fin 133`. -/
def toEntries (l : List (ℕ × ℕ × ℤ)) : List (Fin 133 × Fin 133 × ℂ) :=
  l.map fun t => (Fin.ofNat 133 t.1, Fin.ofNat 133 t.2.1, ((t.2.2 : ℤ) : ℂ))

/-- The relations of `I₂ⁿˢ`. -/
def rel (r : Fin 1539) : Fin 133 × Fin 133 → ℂ := A2.entryMatrix (toEntries (relQ r))

/-- The Casimir. -/
def cas : Fin 133 × Fin 133 → ℂ := A2.entryMatrix (toEntries qQ)

theorem Xn_eq (i : ℕ) (hi : i < 133) : Xn 133 i = X (Fin.ofNat 133 i) := by
  rw [Xn, dif_pos hi]
  congr 1
  ext
  simp [Fin.ofNat, Nat.mod_eq_of_lt hi]

theorem Xn_fin (a : Fin 133) : Xn 133 a = X a := by
  rw [Xn, dif_pos a.2]

theorem quadraticRelation_toEntries (l : List (ℕ × ℕ × ℤ)) (hl : inRange133 l = true) :
    quadraticRelation (A2.entryMatrix (toEntries l)) = quadP 133 l := by
  rw [A2.quadraticRelation_entryMatrix, toEntries, List.map_map, quadP]
  congr 1
  apply List.map_congr_left
  intro t ht
  have h := List.all_eq_true.mp hl t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Function.comp_apply, Xn_eq _ h.1, Xn_eq _ h.2, smul_eq_C_mul]
  simp

theorem quadraticRelation_rel (r : Fin 1539) : quadraticRelation (rel r) = quadP 133 (relQ r) :=
  quadraticRelation_toEntries _ (List.all_eq_true.mp rel_inRange r (List.mem_range.mpr r.2))

theorem quadraticRelation_cas : quadraticRelation cas = quadP 133 qQ :=
  quadraticRelation_toEntries _ qQ_inRange

theorem relQ_mem (b : ℕ) (hb : b < 1539) : quadP 133 (relQ b) ∈ quadraticIdeal rel := by
  have := quadraticRelation_rel ⟨b, hb⟩
  rw [← this]
  exact Ideal.subset_span ⟨⟨b, hb⟩, rfl⟩

theorem u3_of_ok (a : Fin 133) (c : List ℕ) (h : u3OK a c = true) :
    X a * quadraticRelation cas ∈ quadraticIdeal rel := by
  simp only [u3OK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hL, hb⟩, hc⟩ := h
  have := mem_of_u3Check relQ (quadraticIdeal rel) qQ a _ hL _
    (fun t ht => relQ_mem _ (by simpa using List.all_eq_true.mp hb t ht)) hc
  rw [quadraticRelation_cas, ← Xn_fin]
  exact this

/-- **The E₇ type data**: 133 currents, `I₂ⁿˢ = 1539`, the Casimir, U3 checked. -/
def E7data : DeligneCarrierData where
  n := 133
  ρ := Fin 1539
  rel := rel
  cas := cas
  u3 a := by
    fin_cases a
    · exact u3_of_ok _ _ cert0_ok
    · exact u3_of_ok _ _ cert1_ok
    · exact u3_of_ok _ _ cert2_ok
    · exact u3_of_ok _ _ cert3_ok
    · exact u3_of_ok _ _ cert4_ok
    · exact u3_of_ok _ _ cert5_ok
    · exact u3_of_ok _ _ cert6_ok
    · exact u3_of_ok _ _ cert7_ok
    · exact u3_of_ok _ _ cert8_ok
    · exact u3_of_ok _ _ cert9_ok
    · exact u3_of_ok _ _ cert10_ok
    · exact u3_of_ok _ _ cert11_ok
    · exact u3_of_ok _ _ cert12_ok
    · exact u3_of_ok _ _ cert13_ok
    · exact u3_of_ok _ _ cert14_ok
    · exact u3_of_ok _ _ cert15_ok
    · exact u3_of_ok _ _ cert16_ok
    · exact u3_of_ok _ _ cert17_ok
    · exact u3_of_ok _ _ cert18_ok
    · exact u3_of_ok _ _ cert19_ok
    · exact u3_of_ok _ _ cert20_ok
    · exact u3_of_ok _ _ cert21_ok
    · exact u3_of_ok _ _ cert22_ok
    · exact u3_of_ok _ _ cert23_ok
    · exact u3_of_ok _ _ cert24_ok
    · exact u3_of_ok _ _ cert25_ok
    · exact u3_of_ok _ _ cert26_ok
    · exact u3_of_ok _ _ cert27_ok
    · exact u3_of_ok _ _ cert28_ok
    · exact u3_of_ok _ _ cert29_ok
    · exact u3_of_ok _ _ cert30_ok
    · exact u3_of_ok _ _ cert31_ok
    · exact u3_of_ok _ _ cert32_ok
    · exact u3_of_ok _ _ cert33_ok
    · exact u3_of_ok _ _ cert34_ok
    · exact u3_of_ok _ _ cert35_ok
    · exact u3_of_ok _ _ cert36_ok
    · exact u3_of_ok _ _ cert37_ok
    · exact u3_of_ok _ _ cert38_ok
    · exact u3_of_ok _ _ cert39_ok
    · exact u3_of_ok _ _ cert40_ok
    · exact u3_of_ok _ _ cert41_ok
    · exact u3_of_ok _ _ cert42_ok
    · exact u3_of_ok _ _ cert43_ok
    · exact u3_of_ok _ _ cert44_ok
    · exact u3_of_ok _ _ cert45_ok
    · exact u3_of_ok _ _ cert46_ok
    · exact u3_of_ok _ _ cert47_ok
    · exact u3_of_ok _ _ cert48_ok
    · exact u3_of_ok _ _ cert49_ok
    · exact u3_of_ok _ _ cert50_ok
    · exact u3_of_ok _ _ cert51_ok
    · exact u3_of_ok _ _ cert52_ok
    · exact u3_of_ok _ _ cert53_ok
    · exact u3_of_ok _ _ cert54_ok
    · exact u3_of_ok _ _ cert55_ok
    · exact u3_of_ok _ _ cert56_ok
    · exact u3_of_ok _ _ cert57_ok
    · exact u3_of_ok _ _ cert58_ok
    · exact u3_of_ok _ _ cert59_ok
    · exact u3_of_ok _ _ cert60_ok
    · exact u3_of_ok _ _ cert61_ok
    · exact u3_of_ok _ _ cert62_ok
    · exact u3_of_ok _ _ cert63_ok
    · exact u3_of_ok _ _ cert64_ok
    · exact u3_of_ok _ _ cert65_ok
    · exact u3_of_ok _ _ cert66_ok
    · exact u3_of_ok _ _ cert67_ok
    · exact u3_of_ok _ _ cert68_ok
    · exact u3_of_ok _ _ cert69_ok
    · exact u3_of_ok _ _ cert70_ok
    · exact u3_of_ok _ _ cert71_ok
    · exact u3_of_ok _ _ cert72_ok
    · exact u3_of_ok _ _ cert73_ok
    · exact u3_of_ok _ _ cert74_ok
    · exact u3_of_ok _ _ cert75_ok
    · exact u3_of_ok _ _ cert76_ok
    · exact u3_of_ok _ _ cert77_ok
    · exact u3_of_ok _ _ cert78_ok
    · exact u3_of_ok _ _ cert79_ok
    · exact u3_of_ok _ _ cert80_ok
    · exact u3_of_ok _ _ cert81_ok
    · exact u3_of_ok _ _ cert82_ok
    · exact u3_of_ok _ _ cert83_ok
    · exact u3_of_ok _ _ cert84_ok
    · exact u3_of_ok _ _ cert85_ok
    · exact u3_of_ok _ _ cert86_ok
    · exact u3_of_ok _ _ cert87_ok
    · exact u3_of_ok _ _ cert88_ok
    · exact u3_of_ok _ _ cert89_ok
    · exact u3_of_ok _ _ cert90_ok
    · exact u3_of_ok _ _ cert91_ok
    · exact u3_of_ok _ _ cert92_ok
    · exact u3_of_ok _ _ cert93_ok
    · exact u3_of_ok _ _ cert94_ok
    · exact u3_of_ok _ _ cert95_ok
    · exact u3_of_ok _ _ cert96_ok
    · exact u3_of_ok _ _ cert97_ok
    · exact u3_of_ok _ _ cert98_ok
    · exact u3_of_ok _ _ cert99_ok
    · exact u3_of_ok _ _ cert100_ok
    · exact u3_of_ok _ _ cert101_ok
    · exact u3_of_ok _ _ cert102_ok
    · exact u3_of_ok _ _ cert103_ok
    · exact u3_of_ok _ _ cert104_ok
    · exact u3_of_ok _ _ cert105_ok
    · exact u3_of_ok _ _ cert106_ok
    · exact u3_of_ok _ _ cert107_ok
    · exact u3_of_ok _ _ cert108_ok
    · exact u3_of_ok _ _ cert109_ok
    · exact u3_of_ok _ _ cert110_ok
    · exact u3_of_ok _ _ cert111_ok
    · exact u3_of_ok _ _ cert112_ok
    · exact u3_of_ok _ _ cert113_ok
    · exact u3_of_ok _ _ cert114_ok
    · exact u3_of_ok _ _ cert115_ok
    · exact u3_of_ok _ _ cert116_ok
    · exact u3_of_ok _ _ cert117_ok
    · exact u3_of_ok _ _ cert118_ok
    · exact u3_of_ok _ _ cert119_ok
    · exact u3_of_ok _ _ cert120_ok
    · exact u3_of_ok _ _ cert121_ok
    · exact u3_of_ok _ _ cert122_ok
    · exact u3_of_ok _ _ cert123_ok
    · exact u3_of_ok _ _ cert124_ok
    · exact u3_of_ok _ _ cert125_ok
    · exact u3_of_ok _ _ cert126_ok
    · exact u3_of_ok _ _ cert127_ok
    · exact u3_of_ok _ _ cert128_ok
    · exact u3_of_ok _ _ cert129_ok
    · exact u3_of_ok _ _ cert130_ok
    · exact u3_of_ok _ _ cert131_ok
    · exact u3_of_ok _ _ cert132_ok

end

end VOA.DeligneAudit.DeligneCarrier.E7

section AxiomAudit
open VOA.DeligneAudit.DeligneCarrier.E7
#print axioms E7data
end AxiomAudit
