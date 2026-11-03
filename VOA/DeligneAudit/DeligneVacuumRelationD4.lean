/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneVacuumRelationAffine
import VOA.DeligneAudit.D4LiePresentation
import VOA.DeligneAudit.DeligneMLDETypes

/-!
# `D₄`: the vacuum quartic relation of `L_{-2}(𝔰𝔬₈)` (`κ = (h∨+1)(5h∨-6) = 168`)

The generic `vacuumQuarticRelation_affine_of_relations` applies to `W4 = L_{-2}(𝔰𝔬₈)` in the cert
basis (`d4CertData`):
* relation symbols: the three highest relations `Q 0, Q 1, Q 2` by `sym_singular` from the
  singular vectors `sv r` (`simpleProjection_sv`) plus two integer shadow checks
  (`hw_bracket_shadow`, `hw_form_shadow`, kernel `decide` on 3×28 small sums); the other 102 by
  the propagation steps (`step_s`) through `sym_step`;
* U3: `D4data.u3` (`X a · Qd ∈ (I₂ⁿˢ)`), with `casPoly = Qd` (`casPoly_eq`).

`D4Lie.vacuumQuarticRelation4 : VacuumQuarticRelation W4 168` and
`D4Lie.targetLowerBoundQ4 : TargetLowerBoundQ W4 (mldeCoeff 6)`.
-/

namespace VOA.DeligneAudit.D4Lie

open MvPolynomial VOA VOA.AffineGeneral VOA.DeligneAudit.VacuumRelation
  VOA.DeligneAudit.DeligneMLDE VOA.QuadraticJetCoefficientPairing

noncomputable section

/-- The square-bracket current data of `L_{-2}(𝔰𝔬₈)`. -/
abbrev E4 : SqCurrentData W4 (Fin 28) := affineCurrentData d4CertData (-2) hk4

theorem kappaInv4 (a c : Fin 28) : d4CertData.kappaInv a c = (Gi2 a c : ℂ) / 2 := by
  unfold LieData.kappaInv LieData.coordinates LieData.dualGenerator
  rw [d4CertData_def]
  show bB.repr (dualx a) c = _
  rw [dualx, repr_sum]

theorem hw_bracket_shadowZ : ∀ (r : Fin 3) (e : Fin 28),
    ∑ i, cz r i * sZ (ta r i) (tb r i) e = 0 := by decide +kernel

theorem hw_form_shadowZ : ∀ r : Fin 3, ∑ i, cz r i * Gz (ta r i) (tb r i) = 0 := by
  decide +kernel

theorem sym4_hw (r : Fin 3) :
    E4.sym (∑ i, (cz r i : ℂ) • (X (ta r i) * X (tb r i))) = 0 := by
  refine sym_singular d4CertData (-2) hk4 (fun i => (cz r i : ℂ)) (ta r) (tb r) ?_ ?_ ?_
  · have h := simpleProjection_sv r
    rw [sv] at h
    simpa [w2] using h
  · intro e
    have h := hw_bracket_shadowZ r e
    simp only [structureConstant_eq]
    exact_mod_cast h
  · have h := hw_form_shadowZ r
    simp only [formTable_eq]
    exact_mod_cast h

theorem sym4_Q0 : E4.sym (Q 0) = 0 := by rw [Q_hw0]; exact sym4_hw 0
theorem sym4_Q1 : E4.sym (Q 1) = 0 := by rw [Q_hw1]; exact sym4_hw 1
theorem sym4_Q2 : E4.sym (Q 2) = 0 := by rw [Q_hw2]; exact sym4_hw 2

theorem sym4_stepq {b : Fin 28} {r s : Fin 105} {p q : ℂ} (hp : p ≠ 0)
    (h : q • ad4 b (Q r) = p • Q s) (hr : E4.sym (Q r) = 0) : E4.sym (Q s) = 0 :=
  sym_step d4CertData (-2) hk4 hp h hr

theorem sym4_Q_all (r : Fin 105) : E4.sym (Q r) = 0 := by
  have h0 := sym4_Q0
  have h1 := sym4_Q1
  have h2 := sym4_Q2
  have h3 : E4.sym (Q 3) = 0 := sym4_stepq (by norm_num) step3 h0
  have h6 : E4.sym (Q 6) = 0 := sym4_stepq (by norm_num) step6 h0
  have h13 : E4.sym (Q 13) = 0 := sym4_stepq (by norm_num) step13 h0
  have h12 : E4.sym (Q 12) = 0 := sym4_stepq (by norm_num) step12 h0
  have h21 : E4.sym (Q 21) = 0 := sym4_stepq (by norm_num) step21 h0
  have h33 : E4.sym (Q 33) = 0 := sym4_stepq (by norm_num) step33 h0
  have h4 : E4.sym (Q 4) = 0 := sym4_stepq (by norm_num) step4 h1
  have h8 : E4.sym (Q 8) = 0 := sym4_stepq (by norm_num) step8 h1
  have h17 : E4.sym (Q 17) = 0 := sym4_stepq (by norm_num) step17 h1
  have h15 : E4.sym (Q 15) = 0 := sym4_stepq (by norm_num) step15 h1
  have h26 : E4.sym (Q 26) = 0 := sym4_stepq (by norm_num) step26 h1
  have h39 : E4.sym (Q 39) = 0 := sym4_stepq (by norm_num) step39 h1
  have h5 : E4.sym (Q 5) = 0 := sym4_stepq (by norm_num) step5 h2
  have h11 : E4.sym (Q 11) = 0 := sym4_stepq (by norm_num) step11 h2
  have h20 : E4.sym (Q 20) = 0 := sym4_stepq (by norm_num) step20 h2
  have h19 : E4.sym (Q 19) = 0 := sym4_stepq (by norm_num) step19 h2
  have h32 : E4.sym (Q 32) = 0 := sym4_stepq (by norm_num) step32 h2
  have h44 : E4.sym (Q 44) = 0 := sym4_stepq (by norm_num) step44 h2
  have h7 : E4.sym (Q 7) = 0 := sym4_stepq (by norm_num) step7 h3
  have h14 : E4.sym (Q 14) = 0 := sym4_stepq (by norm_num) step14 h3
  have h23 : E4.sym (Q 23) = 0 := sym4_stepq (by norm_num) step23 h3
  have h22 : E4.sym (Q 22) = 0 := sym4_stepq (by norm_num) step22 h3
  have h34 : E4.sym (Q 34) = 0 := sym4_stepq (by norm_num) step34 h3
  have h45 : E4.sym (Q 45) = 0 := sym4_stepq (by norm_num) step45 h3
  have h9 : E4.sym (Q 9) = 0 := sym4_stepq (by norm_num) step9 h4
  have h16 : E4.sym (Q 16) = 0 := sym4_stepq (by norm_num) step16 h4
  have h28 : E4.sym (Q 28) = 0 := sym4_stepq (by norm_num) step28 h4
  have h25 : E4.sym (Q 25) = 0 := sym4_stepq (by norm_num) step25 h4
  have h38 : E4.sym (Q 38) = 0 := sym4_stepq (by norm_num) step38 h4
  have h53 : E4.sym (Q 53) = 0 := sym4_stepq (by norm_num) step53 h4
  have h10 : E4.sym (Q 10) = 0 := sym4_stepq (by norm_num) step10 h5
  have h18 : E4.sym (Q 18) = 0 := sym4_stepq (by norm_num) step18 h5
  have h31 : E4.sym (Q 31) = 0 := sym4_stepq (by norm_num) step31 h5
  have h30 : E4.sym (Q 30) = 0 := sym4_stepq (by norm_num) step30 h5
  have h43 : E4.sym (Q 43) = 0 := sym4_stepq (by norm_num) step43 h5
  have h59 : E4.sym (Q 59) = 0 := sym4_stepq (by norm_num) step59 h5
  have h24 : E4.sym (Q 24) = 0 := sym4_stepq (by norm_num) step24 h6
  have h36 : E4.sym (Q 36) = 0 := sym4_stepq (by norm_num) step36 h6
  have h35 : E4.sym (Q 35) = 0 := sym4_stepq (by norm_num) step35 h6
  have h60 : E4.sym (Q 60) = 0 := sym4_stepq (by norm_num) step60 h6
  have h61 : E4.sym (Q 61) = 0 := sym4_stepq (by norm_num) step61 h7
  have h27 : E4.sym (Q 27) = 0 := sym4_stepq (by norm_num) step27 h8
  have h40 : E4.sym (Q 40) = 0 := sym4_stepq (by norm_num) step40 h8
  have h37 : E4.sym (Q 37) = 0 := sym4_stepq (by norm_num) step37 h8
  have h65 : E4.sym (Q 65) = 0 := sym4_stepq (by norm_num) step65 h8
  have h67 : E4.sym (Q 67) = 0 := sym4_stepq (by norm_num) step67 h9
  have h71 : E4.sym (Q 71) = 0 := sym4_stepq (by norm_num) step71 h10
  have h29 : E4.sym (Q 29) = 0 := sym4_stepq (by norm_num) step29 h11
  have h42 : E4.sym (Q 42) = 0 := sym4_stepq (by norm_num) step42 h11
  have h41 : E4.sym (Q 41) = 0 := sym4_stepq (by norm_num) step41 h11
  have h69 : E4.sym (Q 69) = 0 := sym4_stepq (by norm_num) step69 h11
  have h47 : E4.sym (Q 47) = 0 := sym4_stepq (by norm_num) step47 h12
  have h62 : E4.sym (Q 62) = 0 := sym4_stepq (by norm_num) step62 h12
  have h72 : E4.sym (Q 72) = 0 := sym4_stepq (by norm_num) step72 h12
  have h49 : E4.sym (Q 49) = 0 := sym4_stepq (by norm_num) step49 h13
  have h63 : E4.sym (Q 63) = 0 := sym4_stepq (by norm_num) step63 h13
  have h73 : E4.sym (Q 73) = 0 := sym4_stepq (by norm_num) step73 h13
  have h46 : E4.sym (Q 46) = 0 := sym4_stepq (by norm_num) step46 h14
  have h74 : E4.sym (Q 74) = 0 := sym4_stepq (by norm_num) step74 h14
  have h50 : E4.sym (Q 50) = 0 := sym4_stepq (by norm_num) step50 h15
  have h64 : E4.sym (Q 64) = 0 := sym4_stepq (by norm_num) step64 h15
  have h76 : E4.sym (Q 76) = 0 := sym4_stepq (by norm_num) step76 h15
  have h52 : E4.sym (Q 52) = 0 := sym4_stepq (by norm_num) step52 h16
  have h78 : E4.sym (Q 78) = 0 := sym4_stepq (by norm_num) step78 h16
  have h54 : E4.sym (Q 54) = 0 := sym4_stepq (by norm_num) step54 h17
  have h66 : E4.sym (Q 66) = 0 := sym4_stepq (by norm_num) step66 h17
  have h79 : E4.sym (Q 79) = 0 := sym4_stepq (by norm_num) step79 h17
  have h58 : E4.sym (Q 58) = 0 := sym4_stepq (by norm_num) step58 h18
  have h82 : E4.sym (Q 82) = 0 := sym4_stepq (by norm_num) step82 h18
  have h55 : E4.sym (Q 55) = 0 := sym4_stepq (by norm_num) step55 h19
  have h68 : E4.sym (Q 68) = 0 := sym4_stepq (by norm_num) step68 h19
  have h80 : E4.sym (Q 80) = 0 := sym4_stepq (by norm_num) step80 h19
  have h57 : E4.sym (Q 57) = 0 := sym4_stepq (by norm_num) step57 h20
  have h70 : E4.sym (Q 70) = 0 := sym4_stepq (by norm_num) step70 h20
  have h83 : E4.sym (Q 83) = 0 := sym4_stepq (by norm_num) step83 h20
  have h75 : E4.sym (Q 75) = 0 := sym4_stepq (by norm_num) step75 h21
  have h84 : E4.sym (Q 84) = 0 := sym4_stepq (by norm_num) step84 h21
  have h85 : E4.sym (Q 85) = 0 := sym4_stepq (by norm_num) step85 h22
  have h86 : E4.sym (Q 86) = 0 := sym4_stepq (by norm_num) step86 h23
  have h87 : E4.sym (Q 87) = 0 := sym4_stepq (by norm_num) step87 h25
  have h77 : E4.sym (Q 77) = 0 := sym4_stepq (by norm_num) step77 h26
  have h88 : E4.sym (Q 88) = 0 := sym4_stepq (by norm_num) step88 h26
  have h89 : E4.sym (Q 89) = 0 := sym4_stepq (by norm_num) step89 h28
  have h90 : E4.sym (Q 90) = 0 := sym4_stepq (by norm_num) step90 h30
  have h92 : E4.sym (Q 92) = 0 := sym4_stepq (by norm_num) step92 h31
  have h81 : E4.sym (Q 81) = 0 := sym4_stepq (by norm_num) step81 h32
  have h91 : E4.sym (Q 91) = 0 := sym4_stepq (by norm_num) step91 h32
  have h93 : E4.sym (Q 93) = 0 := sym4_stepq (by norm_num) step93 h33
  have h94 : E4.sym (Q 94) = 0 := sym4_stepq (by norm_num) step94 h34
  have h48 : E4.sym (Q 48) = 0 := sym4_stepq (by norm_num) step48 h35
  have h51 : E4.sym (Q 51) = 0 := sym4_stepq (by norm_num) step51 h37
  have h95 : E4.sym (Q 95) = 0 := sym4_stepq (by norm_num) step95 h38
  have h96 : E4.sym (Q 96) = 0 := sym4_stepq (by norm_num) step96 h39
  have h56 : E4.sym (Q 56) = 0 := sym4_stepq (by norm_num) step56 h41
  have h97 : E4.sym (Q 97) = 0 := sym4_stepq (by norm_num) step97 h43
  have h98 : E4.sym (Q 98) = 0 := sym4_stepq (by norm_num) step98 h44
  have h99 : E4.sym (Q 99) = 0 := sym4_stepq (by norm_num) step99 h45
  have h100 : E4.sym (Q 100) = 0 := sym4_stepq (by norm_num) step100 h52
  have h101 : E4.sym (Q 101) = 0 := sym4_stepq (by norm_num) step101 h58
  have h102 : E4.sym (Q 102) = 0 := sym4_stepq (by norm_num) step102 h61
  have h103 : E4.sym (Q 103) = 0 := sym4_stepq (by norm_num) step103 h67
  have h104 : E4.sym (Q 104) = 0 := sym4_stepq (by norm_num) step104 h71
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

set_option maxHeartbeats 8000000 in -- a 28 × 28 explicit sum
theorem casPoly_eq4 : E4.casPoly = DeligneCarrier.D4.Qd := by
  simp only [SqCurrentData.casPoly, E4, affineCurrentData, kappaInv4]
  simp [Fin.sum_univ_succ, Gi2, DeligneCarrier.D4.Qd]
  try simp only [one_div]
  have hc : (MvPolynomial.C (2⁻¹ : ℂ) : MvPolynomial (Fin 28) ℂ) * 2 = 1 := by
    rw [← map_ofNat (MvPolynomial.C (σ := Fin 28) (R := ℂ)) 2, ← map_mul]; norm_num
  have h2 : (MvPolynomial.C (2 : ℂ) : MvPolynomial (Fin 28) ℂ) = 2 := map_ofNat _ 2
  have h4 : (MvPolynomial.C (4 / 2 : ℂ) : MvPolynomial (Fin 28) ℂ) = 2 := by
    rw [show (4 / 2 : ℂ) = 2 by norm_num]; exact h2
  linear_combination (X 0 * X 2 + X 0 * X 3 + X 2 * X 3) * hc + X 1 ^ 2 * h2
    + X 1 ^ 2 * h4 - X 1 ^ 2 * h2

/-- **The vacuum quartic relation of `L_{-2}(𝔰𝔬₈)`.** -/
theorem vacuumQuarticRelation4 : VacuumQuarticRelation W4 168 := by
  have h := vacuumQuarticRelation_affine_of_relations d4CertData (-2) hk4 Q sym4_Q_all
    (fun i => by
      have := DeligneCarrier.D4.D4data.u3 i
      change X i * quadraticRelation DeligneCarrier.D4.cas ∈ quadraticIdeal DeligneCarrier.D4.rel
        at this
      rw [DeligneCarrier.D4.cas_eq] at this
      change X i * E4.casPoly ∈ _
      rw [casPoly_eq4]
      exact this)
  convert h using 1
  rw [simple_centralCharge', d4CertData_h]
  norm_num

/-- **The `D₄` target lower bound** `dim (L_{-2}(𝔰𝔬₈))_N ≥ mldeCoeff 6 N`. -/
theorem targetLowerBoundQ4 : DeligneCharacter.TargetLowerBoundQ W4 (DeligneCharacter.mldeCoeff 6) :=
  d4_targetLowerBoundQ_of_quartic W4
    (by rw [simple_centralCharge', d4CertData_h]; norm_num)
    (simple_vacuum_ne_zero' d4CertData (-2) hk4) vacuumQuarticRelation4

end

end VOA.DeligneAudit.D4Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.D4Lie.sym4_Q_all
#print axioms VOA.DeligneAudit.D4Lie.vacuumQuarticRelation4
#print axioms VOA.DeligneAudit.D4Lie.targetLowerBoundQ4
end AxiomAudit
