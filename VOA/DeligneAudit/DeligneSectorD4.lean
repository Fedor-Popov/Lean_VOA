/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorD4Rel
import VOA.DeligneAudit.DeligneSectorD4Cyc
import VOA.DeligneAudit.DeligneSectorChain
import VOA.DeligneAudit.DeligneCarrierD4Chain

/-!
# D₄ as sector data

`D4sector : DeligneSectorData` with carrier part `D4data` and the `so₈` structure constants of
`DeligneSectorD4Table`.  Every field is checked in Lean:

* Jacobi, ad-stability of `I₂ = I₂ⁿˢ ⊕ ℂQ`, weight homogeneity, the raising/Cartan tables and the
  coadjoint cyclicity are kernel checks of integer certificates (`decide +kernel`), transported to
  `ℂ` by the soundness lemmas of `DeligneSectorSparse`;
* `δ = δ₂₇` (the `-θ` root vector), `θ(H_i) = (0, 1, 0, 0)`, lowering operators `F_1..F_4 =
  19, 18, 17, 16` with exponents `θ(H_i)`, fusion operators the negative root vectors `16..27`,
  cyclicity depth `10`;
* `lowering_noweight` from the functional `ℓ_i = ht ∘ s_i` (`noweight_of_functional`).

The headline `D4_sectorFusionBound` gives `SectorFusionBound D4data F` from U5 for D₄ and the D₄
divisor comparison; `d4_carrierDim_le_demazureSum_of_sector` feeds it into the D₄ carrier chain.
-/

namespace VOA.DeligneAudit.DeligneSector.D4

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.QuadraticJetCoefficientPairing
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneCarrier
open VOA.DeligneAudit.DeligneCarrier.D4 (D4data d4_carrierDim_le_demazureSum)
open VOA.DeligneAudit.DeligneCharacter (demazureSumCoeff d4DemazureHilb)

noncomputable section

/-- The `so₈` structure constants. -/
abbrev fD4 : Fin 28 → Fin 28 → Fin 28 → ℂ := fC 28 br

theorem d4_jacobi : JacobiCoord fD4 := jacobiCoord_of_check d4_rangeCheck d4_jacCheck

/-! ## The relations as sparse forms -/

set_option maxHeartbeats 2000000 in
theorem relTable_eq (r : Fin 105) :
    VOA.DeligneAudit.DeligneCarrier.D4.relTable r = castL 28 (relZ r) := by
  fin_cases r <;> simp [VOA.DeligneAudit.DeligneCarrier.D4.relTable, castL, relZ, relT] <;> rfl

theorem casEntries_eq : VOA.DeligneAudit.DeligneCarrier.D4.casEntries = castL 28 (relZ 105) := by
  simp [VOA.DeligneAudit.DeligneCarrier.D4.casEntries, castL, relZ, relT]
  rfl

/-- Relation labels as indices (`none` = Casimir = `105`). -/
def idx : Option (Fin 105) → ℕ
  | none => 105
  | some r => r

/-- Indices as relation labels. -/
def lab (s : ℕ) : Option (Fin 105) := if h : s < 105 then some ⟨s, h⟩ else none

theorem idx_lab {s : ℕ} (hs : s < 106) : idx (lab s) = s := by
  unfold lab
  split_ifs with h
  · rfl
  · simp [idx]; omega

theorem idx_lt (r : Option (Fin 105)) : idx r < 106 := by
  cases r with
  | none => simp [idx]
  | some r => simp only [idx]; omega

theorem fullMatrix_eq (r : Option (Fin 105)) :
    D4data.fullMatrix r = VOA.DeligneAudit.A2.entryMatrix (castL 28 (relZ (idx r))) := by
  cases r with
  | none =>
      show VOA.DeligneAudit.DeligneCarrier.D4.cas = _
      rw [VOA.DeligneAudit.DeligneCarrier.D4.cas, casEntries_eq]; rfl
  | some r =>
      show VOA.DeligneAudit.DeligneCarrier.D4.rel r = _
      rw [VOA.DeligneAudit.DeligneCarrier.D4.rel, relTable_eq]; rfl

theorem relZ_range {k : ℕ} (hk : k < 106) : ∀ t ∈ relZ k, t.1 < 28 ∧ t.2.1 < 28 := by
  have h := d4_relRange
  simp only [relRange, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h k hk

theorem quadraticRelation_fullMatrix (r : Option (Fin 105)) :
    quadraticRelation (D4data.fullMatrix r) = qpoly 28 (relZ (idx r)) := by
  rw [fullMatrix_eq]
  exact quadraticRelation_castL (n := 28) _ (relZ_range (idx_lt r))

/-! ## Ad-stability -/

/-- **The D₄ relations `I₂ = I₂ⁿˢ ⊕ ℂQ` are `ad`-stable.** -/
theorem d4_relationsStable : RelationsStable fD4 D4data.fullMatrix := by
  intro x r
  rw [fullMatrix_eq, quadraticRelation_adMatrix_castL d4_rangeCheck x _ (relZ_range (idx_lt r))]
  set k := idx r with hk
  have hk106 : k < 106 := idx_lt r
  have h := d4_stabCheck x
  simp only [stabCheckX, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨hN, hμ⟩, hz⟩ := h k hk106
  have h0 := qpoly_eq_zero_of_check (n := 28) hz
  rw [stabDefect, qpoly_append, qpoly_smulQ, qpoly_flatMap] at h0
  set A := qpoly 28 (adQ br x (relZ k))
  set Sμ := ((cert x k).2.map fun p => qpoly 28 (smulQ (-p.2) (relZ p.1))).sum
  have hNA : ((((cert x k).1 : ℤ)) : ℂ) • A = -Sμ := eq_neg_of_add_eq_zero_left h0
  have hN' : (((cert x k).1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hN
  have : A = ((((cert x k).1 : ℤ)) : ℂ)⁻¹ • (-Sμ) := by
    rw [← hNA, smul_smul, inv_mul_cancel₀ hN', one_smul]
  rw [this]
  refine Submodule.smul_mem _ _ (Submodule.neg_mem _ ?_)
  refine list_sum_mem fun z hz' => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz'
  rw [qpoly_smulQ]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨lab p.1, ?_⟩)
  exact (quadraticRelation_fullMatrix (lab p.1)).trans (by rw [idx_lab (hμ p hp)])

/-! ## The lowest-weight vector and the local Weyl tables -/

theorem d4_diag (r : Option (Fin 105)) : D4data.fullMatrix r ((27 : Fin 28), (27 : Fin 28)) = 0 := by
  rw [fullMatrix_eq]
  refine entryMatrix_castL_diag _ (relZ_range (idx_lt r)) 27 ?_
  have h : ∀ k < 106, (relZ k).all (fun t => !(t.1 = 27 ∧ t.2.1 = 27)) = true := by
    decide +kernel
  exact h _ (idx_lt r)

/-- The coroot values `θ(H_i)`. -/
def thetaD4 (h : Fin 28) : ℕ := if h.val = 1 then 1 else 0

theorem d4_raising_table (e : Fin 28) (he : 4 ≤ e.val ∧ e.val < 16) (y : Fin 28) :
    fD4 e y 27 = 0 := by
  simp only [fD4, fC]
  show ((fZ br e y 27 : ℤ) : ℂ) = 0
  rw [d4_raisingCheck e y he.1 he.2, Int.cast_zero]

theorem d4_cartan_table (h : Fin 28) (hh : h.val < 4) (y : Fin 28) :
    fD4 h y 27 = if y = 27 then -(thetaD4 h : ℂ) else 0 := by
  simp only [fD4, fC]
  have := d4_cartanCheck h y hh
  rw [show ((27 : Fin 28) : ℕ) = 27 from rfl] at *
  rw [this]
  have hy : (y.val = 27) ↔ y = 27 := ⟨fun e => Fin.ext e, fun e => by subst e; rfl⟩
  by_cases h1 : y = 27
  · rw [if_pos (hy.mpr h1), if_pos h1]
    unfold thetaD4
    split_ifs <;> simp
  · rw [if_neg (fun e => h1 (hy.mp e)), if_neg h1]; simp

/-! ## Weights -/

/-- The weights in simple-root coordinates. -/
def wtD4 (c : Fin 28) : Fin 4 → ℤ := fun i => wtZ c i

theorem d4_table_wt (x y c : Fin 28) (h : wtD4 c ≠ wtD4 x + wtD4 y) : fD4 x y c = 0 := by
  by_contra hf
  have hs : sget (br x y) c ≠ 0 := by
    intro h0; apply hf; simp [fD4, fC, fZ, h0]
  obtain ⟨p, hp, hpc⟩ := exists_of_sget_ne_zero hs
  have hw := d4_wtCheck
  simp only [wtCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at hw
  apply h
  funext i
  have := hw x x.2 y y.2 p hp i i.2
  rw [hpc] at this
  simpa [wtD4] using this

/-- The functional `ℓ_i = ht ∘ s_i` for the lowering operator `i`. -/
def ellD4 (i : Fin 28) : Fin 4 → ℤ :=
  if i.val = 19 then ![-1, 2, 1, 1] else if i.val = 18 then ![2, -1, 2, 2]
  else if i.val = 17 then ![1, 2, -1, 1] else ![1, 2, 1, -1]

/-- Lowering exponents `θ(H_i)` for `F_1..F_4 = 19, 18, 17, 16`. -/
def lowExpD4 (i : Fin 28) : ℕ := if i.val = 18 then 1 else 0

theorem ell_sum (i c : Fin 28) :
    ∑ k, ellD4 i k * wtD4 c k =
      ellD4 i 0 * wtZ c 0 + ellD4 i 1 * wtZ c 1 + ellD4 i 2 * wtZ c 2 + ellD4 i 3 * wtZ c 3 := by
  rw [Fin.sum_univ_four]; rfl

theorem ell_bound : ∀ i c : Fin 28, 16 ≤ i.val → i.val < 20 →
    -5 ≤ ellD4 i 0 * wtZ c 0 + ellD4 i 1 * wtZ c 1 + ellD4 i 2 * wtZ c 2 + ellD4 i 3 * wtZ c 3 := by
  decide +kernel

theorem ell_c0 : ∀ i : Fin 28, 16 ≤ i.val → i.val < 20 →
    ellD4 i 0 * wtZ 27 0 + ellD4 i 1 * wtZ 27 1 + ellD4 i 2 * wtZ 27 2 + ellD4 i 3 * wtZ 27 3 =
      -5 + (lowExpD4 i : ℤ) := by
  decide +kernel

theorem ell_i : ∀ i : Fin 28, 16 ≤ i.val → i.val < 20 →
    ellD4 i 0 * wtZ i 0 + ellD4 i 1 * wtZ i 1 + ellD4 i 2 * wtZ i 2 + ellD4 i 3 * wtZ i 3 = 1 := by
  decide +kernel

theorem d4_lowering_noweight (i : Fin 28) (hi : 16 ≤ i.val ∧ i.val < 20) (m : ℕ)
    (t : Fin m → Fin 28) :
    ∑ j, wtD4 (t j) ≠ m • wtD4 27 - (m * lowExpD4 i + 1) • wtD4 i := by
  refine noweight_of_functional wtD4 (ellD4 i) 27 i (lowExpD4 i) (-5) (fun c => ?_) ?_ ?_ m t
  · rw [ell_sum]; exact ell_bound i c hi.1 hi.2
  · rw [ell_sum]; exact ell_c0 i hi.1 hi.2
  · rw [ell_sum]; exact ell_i i hi.1 hi.2

/-! ## Coadjoint cyclicity -/

theorem d4_cyclic (c : Fin 28) : (Pi.single c 1 : Fin 28 → ℂ) ∈ slotWords fD4 27 10 := by
  have h := d4_cycCheck
  simp only [cycCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨hN, hw⟩, hz⟩ := h c c.2
  exact single_mem_slotWords_of_check (br := br) 27 10 c (cyc c).1 (cyc c).2 hN
    (fun p hp => ⟨(hw p hp).1, (hw p hp).2⟩) hz

/-! ## The sector data -/

/-- **D₄ as sector data.** -/
def D4sector : DeligneSectorData where
  n := D4data.n
  ρ := D4data.ρ
  rel := D4data.rel
  cas := D4data.cas
  u3 := D4data.u3
  ρFin := inferInstanceAs (Fintype (Fin 105))
  f := fD4
  jacobi := d4_jacobi
  stable := d4_relationsStable
  c₀ := (27 : Fin 28)
  diag := d4_diag
  raising e := 4 ≤ e.val ∧ e.val < 16
  raising_table := d4_raising_table
  cartan h := h.val < 4
  thetaH := thetaD4
  cartan_table := d4_cartan_table
  hθ := (1 : Fin 28)
  hθ_cartan := by decide
  hθ_ne := by decide
  lowering i := 16 ≤ i.val ∧ i.val < 20
  lowExp := lowExpD4
  R := 4
  wt := wtD4
  table_wt := d4_table_wt
  lowering_noweight := d4_lowering_noweight
  fusion x := 16 ≤ x.val
  depth := 10
  cyclic := d4_cyclic

theorem D4sector_carrier : D4sector.toDeligneCarrierData = D4data := rfl

/-- **The D₄ sector fusion bound**, from U5 for D₄ and the D₄ divisor comparison. -/
theorem D4_sectorFusionBound (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBoundG D4sector F)
    (hD : DivisorComparisonG D4sector) : SectorFusionBound D4data F :=
  sectorFusionBoundG D4sector F hU5 hD

/-- **D₄ carrier side through the sector chain**: `Σ_p dim Carrier p N ≤ D_N`, from U5, the divisor
comparison and U6 for D₄. -/
theorem d4_carrierDim_le_demazureSum_of_sector (F : ℕ → PowerSeries ℚ)
    (hU5 : FusionModuleBoundG D4sector F) (hD : DivisorComparisonG D4sector)
    (hU6 : MixedFusionRecursion F (hilbSeries d4DemazureHilb))
    (N : ℕ) :
    carrierDim D4data N ≤ demazureSumCoeff d4DemazureHilb N :=
  d4_carrierDim_le_demazureSum F (D4_sectorFusionBound F hU5 hD) hU6 N

end

end VOA.DeligneAudit.DeligneSector.D4

section AxiomAudit
open VOA.DeligneAudit.DeligneSector.D4
#print axioms d4_jacobi
#print axioms d4_relationsStable
#print axioms d4_cyclic
#print axioms d4_lowering_noweight
#print axioms D4sector
#print axioms D4_sectorFusionBound
#print axioms d4_carrierDim_le_demazureSum_of_sector
end AxiomAudit
