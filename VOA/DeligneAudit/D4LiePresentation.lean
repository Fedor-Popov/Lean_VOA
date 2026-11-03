/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LiePresentationSteps
import VOA.DeligneAudit.A2CarrierUpperBound
import VOA.DeligneAudit.A2CurrentJetSurjectivity

/-!
# The explicit `D₄` presentation of `L_{-2}(𝔰𝔬₈)`

* `cls4_Q_all`: all 105 relations `P_r` of `DeligneCarrierD4` (spanning `I₂ⁿˢ = 35_v ⊕ 35_s ⊕ 35_c`)
  vanish in the `C₂` algebra of `L_{-2}(𝔰𝔬₈)`: the three highest from the singular vectors
  (`cls4_Q0..2`), the rest by the propagation steps (`D4LiePresentationSteps`).
* `I2ns_le_ker4`: `I₂ⁿˢ ⊆ ker`.
* `explicitPresentation4 : CurrentC2Presentation .D4 W4` with ideal `I₂ⁿˢ = D4data.I`, its
  `CurrentJetSurjectivity`, and its `GeometricCarrierEmbedding` with the literal carrier of the
  `D₄` relations.
* **`explicit_classicallyFree_of_char`**: the `D₄` Deligne case on `L_{-2}(𝔰𝔬₈)` (cert basis),
  with `ker = I₂ⁿˢ`, from the single remaining input `OrdinaryCarrierCharacter` for that carrier
  (equivalently `QuadraticCarrierUpperBound`, `explicit_classicallyFree_of_upperBound`).
-/

namespace VOA.DeligneAudit.D4Lie

open MvPolynomial VOA.AffineGeneral VOA.DeligneHigherRankConditionalCapstone
  VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.CarrierEmbedding

noncomputable section

set_option maxHeartbeats 4000000 in -- 102 propagation steps in one proof
/-- **All 105 relations vanish in the `C₂` algebra of `L_{-2}(𝔰𝔬₈)`.** -/
theorem cls4_Q_all (r : Fin 105) : cls4 (Q r) = 0 := by
  have h0 := cls4_Q0
  have h1 := cls4_Q1
  have h2 := cls4_Q2
  have h3 : cls4 (Q 3) = 0 := cls4_stepq (by norm_num) step3 h0
  have h6 : cls4 (Q 6) = 0 := cls4_stepq (by norm_num) step6 h0
  have h13 : cls4 (Q 13) = 0 := cls4_stepq (by norm_num) step13 h0
  have h12 : cls4 (Q 12) = 0 := cls4_stepq (by norm_num) step12 h0
  have h21 : cls4 (Q 21) = 0 := cls4_stepq (by norm_num) step21 h0
  have h33 : cls4 (Q 33) = 0 := cls4_stepq (by norm_num) step33 h0
  have h4 : cls4 (Q 4) = 0 := cls4_stepq (by norm_num) step4 h1
  have h8 : cls4 (Q 8) = 0 := cls4_stepq (by norm_num) step8 h1
  have h17 : cls4 (Q 17) = 0 := cls4_stepq (by norm_num) step17 h1
  have h15 : cls4 (Q 15) = 0 := cls4_stepq (by norm_num) step15 h1
  have h26 : cls4 (Q 26) = 0 := cls4_stepq (by norm_num) step26 h1
  have h39 : cls4 (Q 39) = 0 := cls4_stepq (by norm_num) step39 h1
  have h5 : cls4 (Q 5) = 0 := cls4_stepq (by norm_num) step5 h2
  have h11 : cls4 (Q 11) = 0 := cls4_stepq (by norm_num) step11 h2
  have h20 : cls4 (Q 20) = 0 := cls4_stepq (by norm_num) step20 h2
  have h19 : cls4 (Q 19) = 0 := cls4_stepq (by norm_num) step19 h2
  have h32 : cls4 (Q 32) = 0 := cls4_stepq (by norm_num) step32 h2
  have h44 : cls4 (Q 44) = 0 := cls4_stepq (by norm_num) step44 h2
  have h7 : cls4 (Q 7) = 0 := cls4_stepq (by norm_num) step7 h3
  have h14 : cls4 (Q 14) = 0 := cls4_stepq (by norm_num) step14 h3
  have h23 : cls4 (Q 23) = 0 := cls4_stepq (by norm_num) step23 h3
  have h22 : cls4 (Q 22) = 0 := cls4_stepq (by norm_num) step22 h3
  have h34 : cls4 (Q 34) = 0 := cls4_stepq (by norm_num) step34 h3
  have h45 : cls4 (Q 45) = 0 := cls4_stepq (by norm_num) step45 h3
  have h9 : cls4 (Q 9) = 0 := cls4_stepq (by norm_num) step9 h4
  have h16 : cls4 (Q 16) = 0 := cls4_stepq (by norm_num) step16 h4
  have h28 : cls4 (Q 28) = 0 := cls4_stepq (by norm_num) step28 h4
  have h25 : cls4 (Q 25) = 0 := cls4_stepq (by norm_num) step25 h4
  have h38 : cls4 (Q 38) = 0 := cls4_stepq (by norm_num) step38 h4
  have h53 : cls4 (Q 53) = 0 := cls4_stepq (by norm_num) step53 h4
  have h10 : cls4 (Q 10) = 0 := cls4_stepq (by norm_num) step10 h5
  have h18 : cls4 (Q 18) = 0 := cls4_stepq (by norm_num) step18 h5
  have h31 : cls4 (Q 31) = 0 := cls4_stepq (by norm_num) step31 h5
  have h30 : cls4 (Q 30) = 0 := cls4_stepq (by norm_num) step30 h5
  have h43 : cls4 (Q 43) = 0 := cls4_stepq (by norm_num) step43 h5
  have h59 : cls4 (Q 59) = 0 := cls4_stepq (by norm_num) step59 h5
  have h24 : cls4 (Q 24) = 0 := cls4_stepq (by norm_num) step24 h6
  have h36 : cls4 (Q 36) = 0 := cls4_stepq (by norm_num) step36 h6
  have h35 : cls4 (Q 35) = 0 := cls4_stepq (by norm_num) step35 h6
  have h60 : cls4 (Q 60) = 0 := cls4_stepq (by norm_num) step60 h6
  have h61 : cls4 (Q 61) = 0 := cls4_stepq (by norm_num) step61 h7
  have h27 : cls4 (Q 27) = 0 := cls4_stepq (by norm_num) step27 h8
  have h40 : cls4 (Q 40) = 0 := cls4_stepq (by norm_num) step40 h8
  have h37 : cls4 (Q 37) = 0 := cls4_stepq (by norm_num) step37 h8
  have h65 : cls4 (Q 65) = 0 := cls4_stepq (by norm_num) step65 h8
  have h67 : cls4 (Q 67) = 0 := cls4_stepq (by norm_num) step67 h9
  have h71 : cls4 (Q 71) = 0 := cls4_stepq (by norm_num) step71 h10
  have h29 : cls4 (Q 29) = 0 := cls4_stepq (by norm_num) step29 h11
  have h42 : cls4 (Q 42) = 0 := cls4_stepq (by norm_num) step42 h11
  have h41 : cls4 (Q 41) = 0 := cls4_stepq (by norm_num) step41 h11
  have h69 : cls4 (Q 69) = 0 := cls4_stepq (by norm_num) step69 h11
  have h47 : cls4 (Q 47) = 0 := cls4_stepq (by norm_num) step47 h12
  have h62 : cls4 (Q 62) = 0 := cls4_stepq (by norm_num) step62 h12
  have h72 : cls4 (Q 72) = 0 := cls4_stepq (by norm_num) step72 h12
  have h49 : cls4 (Q 49) = 0 := cls4_stepq (by norm_num) step49 h13
  have h63 : cls4 (Q 63) = 0 := cls4_stepq (by norm_num) step63 h13
  have h73 : cls4 (Q 73) = 0 := cls4_stepq (by norm_num) step73 h13
  have h46 : cls4 (Q 46) = 0 := cls4_stepq (by norm_num) step46 h14
  have h74 : cls4 (Q 74) = 0 := cls4_stepq (by norm_num) step74 h14
  have h50 : cls4 (Q 50) = 0 := cls4_stepq (by norm_num) step50 h15
  have h64 : cls4 (Q 64) = 0 := cls4_stepq (by norm_num) step64 h15
  have h76 : cls4 (Q 76) = 0 := cls4_stepq (by norm_num) step76 h15
  have h52 : cls4 (Q 52) = 0 := cls4_stepq (by norm_num) step52 h16
  have h78 : cls4 (Q 78) = 0 := cls4_stepq (by norm_num) step78 h16
  have h54 : cls4 (Q 54) = 0 := cls4_stepq (by norm_num) step54 h17
  have h66 : cls4 (Q 66) = 0 := cls4_stepq (by norm_num) step66 h17
  have h79 : cls4 (Q 79) = 0 := cls4_stepq (by norm_num) step79 h17
  have h58 : cls4 (Q 58) = 0 := cls4_stepq (by norm_num) step58 h18
  have h82 : cls4 (Q 82) = 0 := cls4_stepq (by norm_num) step82 h18
  have h55 : cls4 (Q 55) = 0 := cls4_stepq (by norm_num) step55 h19
  have h68 : cls4 (Q 68) = 0 := cls4_stepq (by norm_num) step68 h19
  have h80 : cls4 (Q 80) = 0 := cls4_stepq (by norm_num) step80 h19
  have h57 : cls4 (Q 57) = 0 := cls4_stepq (by norm_num) step57 h20
  have h70 : cls4 (Q 70) = 0 := cls4_stepq (by norm_num) step70 h20
  have h83 : cls4 (Q 83) = 0 := cls4_stepq (by norm_num) step83 h20
  have h75 : cls4 (Q 75) = 0 := cls4_stepq (by norm_num) step75 h21
  have h84 : cls4 (Q 84) = 0 := cls4_stepq (by norm_num) step84 h21
  have h85 : cls4 (Q 85) = 0 := cls4_stepq (by norm_num) step85 h22
  have h86 : cls4 (Q 86) = 0 := cls4_stepq (by norm_num) step86 h23
  have h87 : cls4 (Q 87) = 0 := cls4_stepq (by norm_num) step87 h25
  have h77 : cls4 (Q 77) = 0 := cls4_stepq (by norm_num) step77 h26
  have h88 : cls4 (Q 88) = 0 := cls4_stepq (by norm_num) step88 h26
  have h89 : cls4 (Q 89) = 0 := cls4_stepq (by norm_num) step89 h28
  have h90 : cls4 (Q 90) = 0 := cls4_stepq (by norm_num) step90 h30
  have h92 : cls4 (Q 92) = 0 := cls4_stepq (by norm_num) step92 h31
  have h81 : cls4 (Q 81) = 0 := cls4_stepq (by norm_num) step81 h32
  have h91 : cls4 (Q 91) = 0 := cls4_stepq (by norm_num) step91 h32
  have h93 : cls4 (Q 93) = 0 := cls4_stepq (by norm_num) step93 h33
  have h94 : cls4 (Q 94) = 0 := cls4_stepq (by norm_num) step94 h34
  have h48 : cls4 (Q 48) = 0 := cls4_stepq (by norm_num) step48 h35
  have h51 : cls4 (Q 51) = 0 := cls4_stepq (by norm_num) step51 h37
  have h95 : cls4 (Q 95) = 0 := cls4_stepq (by norm_num) step95 h38
  have h96 : cls4 (Q 96) = 0 := cls4_stepq (by norm_num) step96 h39
  have h56 : cls4 (Q 56) = 0 := cls4_stepq (by norm_num) step56 h41
  have h97 : cls4 (Q 97) = 0 := cls4_stepq (by norm_num) step97 h43
  have h98 : cls4 (Q 98) = 0 := cls4_stepq (by norm_num) step98 h44
  have h99 : cls4 (Q 99) = 0 := cls4_stepq (by norm_num) step99 h45
  have h100 : cls4 (Q 100) = 0 := cls4_stepq (by norm_num) step100 h52
  have h101 : cls4 (Q 101) = 0 := cls4_stepq (by norm_num) step101 h58
  have h102 : cls4 (Q 102) = 0 := cls4_stepq (by norm_num) step102 h61
  have h103 : cls4 (Q 103) = 0 := cls4_stepq (by norm_num) step103 h67
  have h104 : cls4 (Q 104) = 0 := cls4_stepq (by norm_num) step104 h71
  match r with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | 5 => exact h5
  | 6 => exact h6
  | 7 => exact h7
  | 8 => exact h8
  | 9 => exact h9
  | 10 => exact h10
  | 11 => exact h11
  | 12 => exact h12
  | 13 => exact h13
  | 14 => exact h14
  | 15 => exact h15
  | 16 => exact h16
  | 17 => exact h17
  | 18 => exact h18
  | 19 => exact h19
  | 20 => exact h20
  | 21 => exact h21
  | 22 => exact h22
  | 23 => exact h23
  | 24 => exact h24
  | 25 => exact h25
  | 26 => exact h26
  | 27 => exact h27
  | 28 => exact h28
  | 29 => exact h29
  | 30 => exact h30
  | 31 => exact h31
  | 32 => exact h32
  | 33 => exact h33
  | 34 => exact h34
  | 35 => exact h35
  | 36 => exact h36
  | 37 => exact h37
  | 38 => exact h38
  | 39 => exact h39
  | 40 => exact h40
  | 41 => exact h41
  | 42 => exact h42
  | 43 => exact h43
  | 44 => exact h44
  | 45 => exact h45
  | 46 => exact h46
  | 47 => exact h47
  | 48 => exact h48
  | 49 => exact h49
  | 50 => exact h50
  | 51 => exact h51
  | 52 => exact h52
  | 53 => exact h53
  | 54 => exact h54
  | 55 => exact h55
  | 56 => exact h56
  | 57 => exact h57
  | 58 => exact h58
  | 59 => exact h59
  | 60 => exact h60
  | 61 => exact h61
  | 62 => exact h62
  | 63 => exact h63
  | 64 => exact h64
  | 65 => exact h65
  | 66 => exact h66
  | 67 => exact h67
  | 68 => exact h68
  | 69 => exact h69
  | 70 => exact h70
  | 71 => exact h71
  | 72 => exact h72
  | 73 => exact h73
  | 74 => exact h74
  | 75 => exact h75
  | 76 => exact h76
  | 77 => exact h77
  | 78 => exact h78
  | 79 => exact h79
  | 80 => exact h80
  | 81 => exact h81
  | 82 => exact h82
  | 83 => exact h83
  | 84 => exact h84
  | 85 => exact h85
  | 86 => exact h86
  | 87 => exact h87
  | 88 => exact h88
  | 89 => exact h89
  | 90 => exact h90
  | 91 => exact h91
  | 92 => exact h92
  | 93 => exact h93
  | 94 => exact h94
  | 95 => exact h95
  | 96 => exact h96
  | 97 => exact h97
  | 98 => exact h98
  | 99 => exact h99
  | 100 => exact h100
  | 101 => exact h101
  | 102 => exact h102
  | 103 => exact h103
  | 104 => exact h104
  | ⟨n + 105, h⟩ => exact absurd h (by omega)

/-- **`I₂ⁿˢ ⊆ ker`** on `L_{-2}(𝔰𝔬₈)`. -/
theorem I2ns_le_ker4 : DeligneCarrier.D4.D4data.I ≤ RingHom.ker
    (MvPolynomial.aeval fun i => liDegreeZeroClass W4 1 ⟨gen4 i, gen4_weight_one i⟩).toRingHom := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨r, rfl⟩
  exact RingHom.mem_ker.mpr (cls4_Q_all r)

/-- **The explicit `D₄` presentation**: the 28 cert currents of `L_{-2}(𝔰𝔬₈)`, ideal `I₂ⁿˢ`. -/
def explicitPresentation4 : CurrentC2Presentation .D4 W4 where
  gen := gen4
  gen_weight_one := gen4_weight_one
  ideal := DeligneCarrier.D4.D4data.I
  relations := I2ns_le_ker4

theorem explicitPresentation4_ideal :
    explicitPresentation4.ideal = quadraticIdeal DeligneCarrier.D4.rel := rfl

/-- `CurrentJetSurjectivity` (the current-word spanning proof does not look at the ideal). -/
theorem explicitCurrentJetSurjectivity4 :
    CurrentJetSurjectivity .D4 W4 explicitPresentation4 :=
  DeligneAudit.currentJetSurjectivity_of_genWordSpan explicitPresentation4
    (Deligne.genWordsSpan .D4 d4CertData (-2) hk4)

/-- The geometric carrier embedding, with the literal carrier of the `D₄` relations. -/
def explicitGeometricCarrierEmbedding4 :
    GeometricCarrierEmbedding .D4 W4 explicitPresentation4 (Carrier DeligneCarrier.D4.rel) :=
  geometricCarrierEmbedding_of_quadraticIdeal explicitPresentation4 DeligneCarrier.D4.rel rfl

/-- **The `D₄` Deligne case on `L_{-2}(𝔰𝔬₈)` with the explicit ideal `I₂ⁿˢ`**, conditional only on
the character input for the literal carrier.  It also yields `ker = I₂ⁿˢ`. -/
theorem explicit_classicallyFree_of_char
    (hchar : OrdinaryCarrierCharacter W4 (Carrier DeligneCarrier.D4.rel)) :
    CaseClassicallyFree .D4 W4 explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W4 1 ⟨explicitPresentation4.gen i,
          explicitPresentation4.gen_weight_one i⟩).toRingHom = explicitPresentation4.ideal :=
  caseClassicallyFree_of_explicit_inputs .D4 W4 explicitPresentation4 _
    explicitCurrentJetSurjectivity4 explicitGeometricCarrierEmbedding4 hchar

/-- The same from the carrier upper bound (`QuadraticCarrierUpperBound`, the form fed by the
carrier chain `DeligneCarrierD4Chain`). -/
theorem explicit_classicallyFree_of_upperBound
    (hbound : QuadraticCarrierUpperBound DeligneCarrier.D4.rel W4) :
    CaseClassicallyFree .D4 W4 explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W4 1 ⟨explicitPresentation4.gen i,
          explicitPresentation4.gen_weight_one i⟩).toRingHom = explicitPresentation4.ideal :=
  caseClassicallyFree_of_quadraticCarrierUpperBound explicitPresentation4 DeligneCarrier.D4.rel rfl
    explicitCurrentJetSurjectivity4 hbound

end

end VOA.DeligneAudit.D4Lie

section AxiomAudit
open VOA.DeligneAudit.D4Lie
#print axioms cls4_Q_all
#print axioms I2ns_le_ker4
#print axioms explicitCurrentJetSurjectivity4
#print axioms explicit_classicallyFree_of_char
#print axioms explicit_classicallyFree_of_upperBound
end AxiomAudit
