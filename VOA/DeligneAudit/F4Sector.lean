/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorChecks

/-!
# F4: carrier data and sector data

* **`F4data : DeligneCarrierData`**: `n = 52` (the basis of `f4T`), the 324 relations of `I₂ⁿˢ` (the
  irreducible component of `Sym² 𝔤` other than `V(2θ)` and `ℂQ`), the Casimir, and **U3 checked**
  (`E6Sparse.mem_of_u3Check` certificates).
* **`F4sector : DeligneSectorData`** with `F4sector.toDeligneCarrierData = F4data` (rfl):
  Jacobi from the `f4Checks` (`jacobiCoord_of_checks`), ad-stability from the generators (Cartan basis,
  `E_i`, `F_i`; `relationsStable_of_generators`), `c₀ = 45` (`-θ`), raising the positive roots, Cartan basis
  [0, 1, 2, 3] with `θ`-values [2, 1, 0, -1] (`cartan` for `θ(h) ≥ 0`, `cartanN` for `θ(h) < 0`), lowering `F_i = [26, 13, 46, 47]` with
  exponents `⟨θ, α_i^∨⟩ = [0, 0, 0, 1]`, fusion the negative roots, cyclicity depth 22.
-/

namespace VOA.DeligneAudit.DeligneSector.F4

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.QuadraticJetCoefficientPairing
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneCarrier VOA.DeligneAudit.DeligneDivisor

noncomputable section

/-! ## Carrier data -/

theorem relZ_range {k : ℕ} (hk : k < 325) : ∀ t ∈ relZ k, t.1 < 52 ∧ t.2.1 < 52 := by
  have h := relRange_ok
  simp only [relRange, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h k hk

/-- The relations of `I₂ⁿˢ`. -/
def rel (r : Fin 324) : Fin 52 × Fin 52 → ℂ := VOA.DeligneAudit.A2.entryMatrix (castL 52 (relQ r))

/-- The Casimir. -/
def cas : Fin 52 × Fin 52 → ℂ := VOA.DeligneAudit.A2.entryMatrix (castL 52 qQ)

theorem quadP_eq (l : List (ℕ × ℕ × ℤ)) :
    VOA.DeligneAudit.E6Sparse.quadP 52 l = qpoly 52 l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [VOA.DeligneAudit.E6Sparse.quadP, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, qpoly_cons, MvPolynomial.smul_eq_C_mul]
    simp only [VOA.DeligneAudit.E6Sparse.Xn, Xn, map_intCast]

theorem rel_poly (r : Fin 324) : quadraticRelation (rel r) = qpoly 52 (relQ r) := by
  have := relZ_range (k := r) (by omega)
  simp only [relZ, r.2, if_true] at this
  exact quadraticRelation_castL _ this

theorem cas_poly : quadraticRelation cas = qpoly 52 qQ := by
  have := relZ_range (k := 324) (by omega)
  simp only [relZ, lt_irrefl, if_false] at this
  exact quadraticRelation_castL _ this

theorem u3_mem (a : Fin 52) : X a * quadraticRelation cas ∈ quadraticIdeal rel := by
  have h := u3_ok
  simp only [List.all_eq_true, List.mem_range] at h
  have ha := h a a.2
  simp only [u3OK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ha
  obtain ⟨⟨hL, hb⟩, hc⟩ := ha
  have := VOA.DeligneAudit.E6Sparse.mem_of_u3Check relQ (quadraticIdeal rel) qQ a _ hL _
    (fun t ht => by
      have hlt : t.2.2 < 324 := by simpa using hb t ht
      rw [quadP_eq, ← rel_poly ⟨t.2.2, hlt⟩]
      exact Ideal.subset_span ⟨⟨t.2.2, hlt⟩, rfl⟩) hc
  rw [quadP_eq, ← cas_poly] at this
  simpa [VOA.DeligneAudit.E6Sparse.Xn, a.2] using this

/-- **The F4 type data**: 52 currents, `I₂ⁿˢ` (324 relations), the Casimir, U3 checked. -/
def F4data : DeligneCarrierData where
  n := 52
  ρ := Fin 324
  rel := rel
  cas := cas
  u3 := u3_mem

/-! ## Structure constants -/

/-- The `f4` structure constants (the `f4T`). -/
abbrev fF4 : Fin 52 → Fin 52 → Fin 52 → ℂ := fC 52 br

theorem jacobi : JacobiCoord fF4 :=
  VOA.DeligneAudit.E6SectorSparse.jacobiCoord_of_checks VOA.AffineGeneral.SCLie.f4Checks

theorem cover : ∀ c < 52, c ∈ gensL ++ genT.map (·.1) := by
  have h := cover_ok
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h

/-! ## Relations -/

/-- Relation labels as indices (`none` = Casimir = `324`). -/
def idx : Option (Fin 324) → ℕ
  | none => 324
  | some r => r

/-- Indices as relation labels. -/
def lab (s : ℕ) : Option (Fin 324) := if h : s < 324 then some ⟨s, h⟩ else none

theorem idx_lab {s : ℕ} (hs : s < 325) : idx (lab s) = s := by
  unfold lab
  split_ifs with h
  · rfl
  · simp [idx]; omega

theorem idx_lt (r : Option (Fin 324)) : idx r < 325 := by
  cases r with
  | none => simp [idx]
  | some r => simp only [idx]; omega

theorem fullMatrix_eq (r : Option (Fin 324)) :
    F4data.fullMatrix r = VOA.DeligneAudit.A2.entryMatrix (castL 52 (relZ (idx r))) := by
  cases r with
  | none => rfl
  | some r =>
      show rel r = _
      simp only [idx, relZ, r.2, if_true]
      rfl

theorem quadraticRelation_fullMatrix (r : Option (Fin 324)) :
    quadraticRelation (F4data.fullMatrix r) = qpoly 52 (relZ (idx r)) := by
  rw [fullMatrix_eq]
  exact quadraticRelation_castL (n := 52) _ (relZ_range (idx_lt r))

theorem gen_stab : ∀ g ∈ gensL, ∀ (hg : g < 52), ∀ r,
    quadraticRelation (adMatrix fF4 ⟨g, hg⟩ (F4data.fullMatrix r)) ∈ Sp F4data.fullMatrix := by
  intro g hgG hg r
  rw [fullMatrix_eq, quadraticRelation_adMatrix_castL range_ok _ _ (relZ_range (idx_lt r))]
  set i := gensL.idxOf g
  have hi : i < gensL.length := List.idxOf_lt_length_of_mem hgG
  have hgi : gensL.getD i 0 = g := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_idxOf hi
  have h := stab_ok
  simp only [stabChecks, List.all_eq_true, List.mem_range] at h
  have h1 := h i (by simpa using hi) (idx r) (idx_lt r)
  simp only [stabCheck] at h1
  rw [hgi] at h1
  split at h1
  · rw [show (⟨g, hg⟩ : Fin 52).val = g from rfl, qpoly_eq_zero_of_qzeroSortSym (by norm_num) h1]
    exact Submodule.zero_mem _
  · rename_i N ps _
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h1
    obtain ⟨⟨hN, hps⟩, hz⟩ := h1
    have h0 := qpoly_eq_zero_of_qzeroSortSym (n := 52) (by norm_num) hz
    rw [qpoly_append, qpoly_smulQ, qpoly_flatMap] at h0
    have hN' : ((N : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hN
    have e : qpoly 52 (adQ br g (relZ (idx r))) = ((N : ℤ) : ℂ)⁻¹ •
        -(ps.map fun p => qpoly 52 (smulQ (-p.2) (relZ p.1))).sum := by
      rw [← eq_neg_of_add_eq_zero_left h0, smul_smul, inv_mul_cancel₀ hN', one_smul]
    rw [show (⟨g, hg⟩ : Fin 52).val = g from rfl, e]
    refine Submodule.smul_mem (Sp F4data.fullMatrix) _ (Submodule.neg_mem _ (list_sum_mem fun z hz' => ?_))
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz'
    rw [qpoly_smulQ]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨lab p.1, ?_⟩)
    exact (quadraticRelation_fullMatrix (lab p.1)).trans (by rw [idx_lab (hps p hp)])

theorem stable : RelationsStable fF4 F4data.fullMatrix :=
  relationsStable_of_generators F4data.fullMatrix jacobi gensL genT gen_ok cover gen_stab

/-! ## Local Weyl data -/

theorem diag (r : Option (Fin 324)) : F4data.fullMatrix r ((45 : Fin 52), (45 : Fin 52)) = 0 := by
  rw [fullMatrix_eq]
  refine entryMatrix_castL_diag _ (relZ_range (idx_lt r)) 45 ?_
  have h := diag_ok
  simp only [List.all_eq_true, List.mem_range] at h
  exact List.all_eq_true.mpr (h _ (idx_lt r))

/-- `θ(h) ≥ 0` on the Cartan basis. -/
def thetaH (h : Fin 52) : ℕ := if h.val = 0 then 2 else if h.val = 1 then 1 else if h.val = 2 then 0 else 0

/-- `-θ(h) > 0` on the Cartan basis. -/
def thetaN (h : Fin 52) : ℕ := if h.val = 3 then 1 else 0

theorem raising_table (e : Fin 52) (he : e.val ∈ posL) (y : Fin 52) : fF4 e y 45 = 0 := by
  show ((fZ br e y 45 : ℤ) : ℂ) = 0
  rw [raising_ok e y he, Int.cast_zero]

theorem cartan_table (h : Fin 52) (hh : h.val ∈ ([0, 1, 2] : List ℕ)) (y : Fin 52) :
    fF4 h y 45 = if y = 45 then -(thetaH h : ℂ) else 0 := by
  show ((fZ br h y 45 : ℤ) : ℂ) = _
  have hc := cartan_ok y
  obtain ⟨hv, hlt⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl
  · rw [hc.1]
    simp only [thetaH]
    split_ifs <;> simp_all [Fin.ext_iff]
  · rw [hc.2.1]
    simp only [thetaH]
    split_ifs <;> simp_all [Fin.ext_iff]
  · rw [hc.2.2.1]
    simp only [thetaH]
    split_ifs <;> simp_all [Fin.ext_iff]

theorem cartanN_table (h : Fin 52) (hh : h.val ∈ ([3] : List ℕ)) (y : Fin 52) :
    fF4 h y 45 = if y = 45 then (thetaN h : ℂ) else 0 := by
  show ((fZ br h y 45 : ℤ) : ℂ) = _
  have hc := cartan_ok y
  obtain ⟨hv, hlt⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl
  · rw [hc.2.2.2]
    simp only [thetaN]
    split_ifs <;> simp_all [Fin.ext_iff]

/-- The weights in simple-root coordinates. -/
def wtS (c : Fin 52) : Fin 4 → ℤ := fun i => wtZ c i

theorem table_wt (x y c : Fin 52) (h : wtS c ≠ wtS x + wtS y) : fF4 x y c = 0 := by
  by_contra hf
  have hs : sget (br x y) c ≠ 0 := by
    intro h0; apply hf; simp [fF4, fC, fZ, h0]
  obtain ⟨p, hp, hpc⟩ := exists_of_sget_ne_zero hs
  have hw := wt_ok
  simp only [wtCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at hw
  apply h
  funext i
  have := hw x x.2 y y.2 p hp i i.2
  rw [hpc] at this
  simpa [wtS] using this

/-- `ℓ_i = ht ∘ s_i` (coefficients `1 - ⟨α_j, α_i^∨⟩`). -/
def ellS (i : Fin 52) : Fin 4 → ℤ := if i.val = 26 then ![-1, 1, 2, 2] else if i.val = 13 then ![1, -1, 2, 1] else if i.val = 46 then ![3, 2, -1, 1] else if i.val = 47 then ![2, 1, 1, -1] else ![0, 0, 0, 0]

/-- Lowering exponents `⟨θ, α_i^∨⟩`. -/
def lowExpS (i : Fin 52) : ℕ := if i.val = 26 then 0 else if i.val = 13 then 0 else if i.val = 46 then 0 else if i.val = 47 then 1 else 0

theorem ell_sum (i c : Fin 52) : ∑ k, ellS i k * wtS c k = ellS i 0 * wtZ c 0 + ellS i 1 * wtZ c 1 + ellS i 2 * wtZ c 2 + ellS i 3 * wtZ c 3 := by
  simp [Fin.sum_univ_succ, wtS, add_assoc]

theorem ell_bound : ∀ i c : Fin 52, i.val ∈ ([26, 13, 46, 47] : List ℕ) → -11 ≤ ellS i 0 * wtZ c 0 + ellS i 1 * wtZ c 1 + ellS i 2 * wtZ c 2 + ellS i 3 * wtZ c 3 := by
  decide +kernel

theorem ell_c0 : ∀ i : Fin 52, i.val ∈ ([26, 13, 46, 47] : List ℕ) → ellS i 0 * wtZ 45 0 + ellS i 1 * wtZ 45 1 + ellS i 2 * wtZ 45 2 + ellS i 3 * wtZ 45 3 = -11 + (lowExpS i : ℤ) := by
  decide +kernel

theorem ell_i : ∀ i : Fin 52, i.val ∈ ([26, 13, 46, 47] : List ℕ) → ellS i 0 * wtZ i 0 + ellS i 1 * wtZ i 1 + ellS i 2 * wtZ i 2 + ellS i 3 * wtZ i 3 = 1 := by
  decide +kernel

theorem lowering_noweight (i : Fin 52) (hi : i.val ∈ ([26, 13, 46, 47] : List ℕ)) (m : ℕ) (t : Fin m → Fin 52) :
    ∑ j, wtS (t j) ≠ m • wtS 45 - (m * lowExpS i + 1) • wtS i := by
  refine noweight_of_functional wtS (ellS i) 45 i (lowExpS i) (-11) (fun c => ?_) ?_ ?_ m t
  · rw [ell_sum]; exact ell_bound i c hi
  · rw [ell_sum]; exact ell_c0 i hi
  · rw [ell_sum]; exact ell_i i hi

theorem cyclic (c : Fin 52) : (Pi.single c 1 : Fin 52 → ℂ) ∈ slotWords fF4 45 22 := by
  have hn : ∀ i, 0 < i → i < vecR.length → cycNodeCheck rows vecs cpar 52 i = true := by
    intro i h0 h1
    have h := cycNodes_ok
    simp only [cycNodes, List.all_eq_true, List.mem_range'] at h
    exact h i ⟨i - 1, by omega, by omega⟩
  have h := cyc_ok
  simp only [cycCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨hK, hw⟩, hz⟩ := h c c.2
  exact single_mem_slotWords_of_tree (br := br) (vecs := vecs) (cpar := cpar) (fun x _ => rfl) 45
    cycRoot_ok.1 cycRoot_ok.2 vecR.length hn 22 c (cyc c).1 (cyc c).2 hK (fun p hp => hw p hp) hz

/-! ## The sector data -/

/-- **F4 as sector data.** -/
def F4sector : DeligneSectorData where
  n := F4data.n
  ρ := F4data.ρ
  rel := F4data.rel
  cas := F4data.cas
  u3 := F4data.u3
  ρFin := inferInstanceAs (Fintype (Fin 324))
  f := fF4
  jacobi := jacobi
  stable := stable
  c₀ := (45 : Fin 52)
  diag := diag
  raising e := e.val ∈ posL
  raising_table := raising_table
  cartan h := h.val ∈ ([0, 1, 2] : List ℕ)
  thetaH := thetaH
  cartan_table := cartan_table
  hθ := (0 : Fin 52)
  hθ_cartan := by decide
  hθ_ne := by decide
  lowering i := i.val ∈ ([26, 13, 46, 47] : List ℕ)
  lowExp := lowExpS
  R := 4
  wt := wtS
  table_wt := table_wt
  lowering_noweight := lowering_noweight
  fusion x := x.val ∈ negL
  depth := 22
  cyclic := cyclic
  cartanN h := h.val ∈ ([3] : List ℕ)
  thetaN := thetaN
  cartanN_table := cartanN_table

theorem F4sector_carrier : F4sector.toDeligneCarrierData = F4data := rfl

theorem F4sector_n : F4sector.n = 52 := rfl

end

end VOA.DeligneAudit.DeligneSector.F4

section AxiomAudit
open VOA.DeligneAudit.DeligneSector.F4
#print axioms F4data
#print axioms F4sector
end AxiomAudit
