/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2SectorChecks

/-!
# G2: carrier data and sector data

* **`G2data : DeligneCarrierData`**: `n = 14` (the basis of `g2T`), the 27 relations of `I₂ⁿˢ` (the
  irreducible component of `Sym² 𝔤` other than `V(2θ)` and `ℂQ`), the Casimir, and **U3 checked**
  (`E6Sparse.mem_of_u3Check` certificates).
* **`G2sector : DeligneSectorData`** with `G2sector.toDeligneCarrierData = G2data` (rfl):
  Jacobi from the `g2Checks` (`jacobiCoord_of_checks`), ad-stability from the generators (Cartan basis,
  `E_i`, `F_i`; `relationsStable_of_generators`), `c₀ = 12` (`-θ`), raising the positive roots, Cartan basis
  [0, 1] with `θ`-values [3, -1] (`cartan` for `θ(h) ≥ 0`, `cartanN` for `θ(h) < 0`), lowering `F_i = [4, 13]` with
  exponents `⟨θ, α_i^∨⟩ = [0, 1]`, fusion the negative roots, cyclicity depth 10.
-/

namespace VOA.DeligneAudit.DeligneSector.G2

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.QuadraticJetCoefficientPairing
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneCarrier VOA.DeligneAudit.DeligneDivisor

noncomputable section

/-! ## Carrier data -/

theorem relZ_range {k : ℕ} (hk : k < 28) : ∀ t ∈ relZ k, t.1 < 14 ∧ t.2.1 < 14 := by
  have h := relRange_ok
  simp only [relRange, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h k hk

/-- The relations of `I₂ⁿˢ`. -/
def rel (r : Fin 27) : Fin 14 × Fin 14 → ℂ := VOA.DeligneAudit.A2.entryMatrix (castL 14 (relQ r))

/-- The Casimir. -/
def cas : Fin 14 × Fin 14 → ℂ := VOA.DeligneAudit.A2.entryMatrix (castL 14 qQ)

theorem quadP_eq (l : List (ℕ × ℕ × ℤ)) :
    VOA.DeligneAudit.E6Sparse.quadP 14 l = qpoly 14 l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [VOA.DeligneAudit.E6Sparse.quadP, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, qpoly_cons, MvPolynomial.smul_eq_C_mul]
    simp only [VOA.DeligneAudit.E6Sparse.Xn, Xn, map_intCast]

theorem rel_poly (r : Fin 27) : quadraticRelation (rel r) = qpoly 14 (relQ r) := by
  have := relZ_range (k := r) (by omega)
  simp only [relZ, r.2, if_true] at this
  exact quadraticRelation_castL _ this

theorem cas_poly : quadraticRelation cas = qpoly 14 qQ := by
  have := relZ_range (k := 27) (by omega)
  simp only [relZ, lt_irrefl, if_false] at this
  exact quadraticRelation_castL _ this

theorem u3_mem (a : Fin 14) : X a * quadraticRelation cas ∈ quadraticIdeal rel := by
  have h := u3_ok
  simp only [List.all_eq_true, List.mem_range] at h
  have ha := h a a.2
  simp only [u3OK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ha
  obtain ⟨⟨hL, hb⟩, hc⟩ := ha
  have := VOA.DeligneAudit.E6Sparse.mem_of_u3Check relQ (quadraticIdeal rel) qQ a _ hL _
    (fun t ht => by
      have hlt : t.2.2 < 27 := by simpa using hb t ht
      rw [quadP_eq, ← rel_poly ⟨t.2.2, hlt⟩]
      exact Ideal.subset_span ⟨⟨t.2.2, hlt⟩, rfl⟩) hc
  rw [quadP_eq, ← cas_poly] at this
  simpa [VOA.DeligneAudit.E6Sparse.Xn, a.2] using this

/-- **The G2 type data**: 14 currents, `I₂ⁿˢ` (27 relations), the Casimir, U3 checked. -/
def G2data : DeligneCarrierData where
  n := 14
  ρ := Fin 27
  rel := rel
  cas := cas
  u3 := u3_mem

/-! ## Structure constants -/

/-- The `g2` structure constants (the `g2T`). -/
abbrev fG2 : Fin 14 → Fin 14 → Fin 14 → ℂ := fC 14 br

theorem jacobi : JacobiCoord fG2 :=
  VOA.DeligneAudit.E6SectorSparse.jacobiCoord_of_checks VOA.AffineGeneral.SCLie.g2Checks

theorem cover : ∀ c < 14, c ∈ gensL ++ genT.map (·.1) := by
  have h := cover_ok
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h

/-! ## Relations -/

/-- Relation labels as indices (`none` = Casimir = `27`). -/
def idx : Option (Fin 27) → ℕ
  | none => 27
  | some r => r

/-- Indices as relation labels. -/
def lab (s : ℕ) : Option (Fin 27) := if h : s < 27 then some ⟨s, h⟩ else none

theorem idx_lab {s : ℕ} (hs : s < 28) : idx (lab s) = s := by
  unfold lab
  split_ifs with h
  · rfl
  · simp [idx]; omega

theorem idx_lt (r : Option (Fin 27)) : idx r < 28 := by
  cases r with
  | none => simp [idx]
  | some r => simp only [idx]; omega

theorem fullMatrix_eq (r : Option (Fin 27)) :
    G2data.fullMatrix r = VOA.DeligneAudit.A2.entryMatrix (castL 14 (relZ (idx r))) := by
  cases r with
  | none => rfl
  | some r =>
      show rel r = _
      simp only [idx, relZ, r.2, if_true]
      rfl

theorem quadraticRelation_fullMatrix (r : Option (Fin 27)) :
    quadraticRelation (G2data.fullMatrix r) = qpoly 14 (relZ (idx r)) := by
  rw [fullMatrix_eq]
  exact quadraticRelation_castL (n := 14) _ (relZ_range (idx_lt r))

theorem gen_stab : ∀ g ∈ gensL, ∀ (hg : g < 14), ∀ r,
    quadraticRelation (adMatrix fG2 ⟨g, hg⟩ (G2data.fullMatrix r)) ∈ Sp G2data.fullMatrix := by
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
  · rw [show (⟨g, hg⟩ : Fin 14).val = g from rfl, qpoly_eq_zero_of_qzeroSortSym (by norm_num) h1]
    exact Submodule.zero_mem _
  · rename_i N ps _
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h1
    obtain ⟨⟨hN, hps⟩, hz⟩ := h1
    have h0 := qpoly_eq_zero_of_qzeroSortSym (n := 14) (by norm_num) hz
    rw [qpoly_append, qpoly_smulQ, qpoly_flatMap] at h0
    have hN' : ((N : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hN
    have e : qpoly 14 (adQ br g (relZ (idx r))) = ((N : ℤ) : ℂ)⁻¹ •
        -(ps.map fun p => qpoly 14 (smulQ (-p.2) (relZ p.1))).sum := by
      rw [← eq_neg_of_add_eq_zero_left h0, smul_smul, inv_mul_cancel₀ hN', one_smul]
    rw [show (⟨g, hg⟩ : Fin 14).val = g from rfl, e]
    refine Submodule.smul_mem (Sp G2data.fullMatrix) _ (Submodule.neg_mem _ (list_sum_mem fun z hz' => ?_))
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz'
    rw [qpoly_smulQ]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨lab p.1, ?_⟩)
    exact (quadraticRelation_fullMatrix (lab p.1)).trans (by rw [idx_lab (hps p hp)])

theorem stable : RelationsStable fG2 G2data.fullMatrix :=
  relationsStable_of_generators G2data.fullMatrix jacobi gensL genT gen_ok cover gen_stab

/-! ## Local Weyl data -/

theorem diag (r : Option (Fin 27)) : G2data.fullMatrix r ((12 : Fin 14), (12 : Fin 14)) = 0 := by
  rw [fullMatrix_eq]
  refine entryMatrix_castL_diag _ (relZ_range (idx_lt r)) 12 ?_
  have h := diag_ok
  simp only [List.all_eq_true, List.mem_range] at h
  exact List.all_eq_true.mpr (h _ (idx_lt r))

/-- `θ(h) ≥ 0` on the Cartan basis. -/
def thetaH (h : Fin 14) : ℕ := if h.val = 0 then 3 else 0

/-- `-θ(h) > 0` on the Cartan basis. -/
def thetaN (h : Fin 14) : ℕ := if h.val = 1 then 1 else 0

theorem raising_table (e : Fin 14) (he : e.val ∈ posL) (y : Fin 14) : fG2 e y 12 = 0 := by
  show ((fZ br e y 12 : ℤ) : ℂ) = 0
  rw [raising_ok e y he, Int.cast_zero]

theorem cartan_table (h : Fin 14) (hh : h.val ∈ ([0] : List ℕ)) (y : Fin 14) :
    fG2 h y 12 = if y = 12 then -(thetaH h : ℂ) else 0 := by
  show ((fZ br h y 12 : ℤ) : ℂ) = _
  have hc := cartan_ok y
  obtain ⟨hv, hlt⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl
  · rw [hc.1]
    simp only [thetaH]
    split_ifs <;> simp_all [Fin.ext_iff]

theorem cartanN_table (h : Fin 14) (hh : h.val ∈ ([1] : List ℕ)) (y : Fin 14) :
    fG2 h y 12 = if y = 12 then (thetaN h : ℂ) else 0 := by
  show ((fZ br h y 12 : ℤ) : ℂ) = _
  have hc := cartan_ok y
  obtain ⟨hv, hlt⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl
  · rw [hc.2]
    simp only [thetaN]
    split_ifs <;> simp_all [Fin.ext_iff]

/-- The weights in simple-root coordinates. -/
def wtS (c : Fin 14) : Fin 2 → ℤ := fun i => wtZ c i

theorem table_wt (x y c : Fin 14) (h : wtS c ≠ wtS x + wtS y) : fG2 x y c = 0 := by
  by_contra hf
  have hs : sget (br x y) c ≠ 0 := by
    intro h0; apply hf; simp [fG2, fC, fZ, h0]
  obtain ⟨p, hp, hpc⟩ := exists_of_sget_ne_zero hs
  have hw := wt_ok
  simp only [wtCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at hw
  apply h
  funext i
  have := hw x x.2 y y.2 p hp i i.2
  rw [hpc] at this
  simpa [wtS] using this

/-- `ℓ_i = ht ∘ s_i` (coefficients `1 - ⟨α_j, α_i^∨⟩`). -/
def ellS (i : Fin 14) : Fin 2 → ℤ := if i.val = 4 then ![-1, 4] else if i.val = 13 then ![2, -1] else ![0, 0]

/-- Lowering exponents `⟨θ, α_i^∨⟩`. -/
def lowExpS (i : Fin 14) : ℕ := if i.val = 4 then 0 else if i.val = 13 then 1 else 0

theorem ell_sum (i c : Fin 14) : ∑ k, ellS i k * wtS c k = ellS i 0 * wtZ c 0 + ellS i 1 * wtZ c 1 := by
  simp [Fin.sum_univ_succ, wtS, add_assoc]

theorem ell_bound : ∀ i c : Fin 14, i.val ∈ ([4, 13] : List ℕ) → -5 ≤ ellS i 0 * wtZ c 0 + ellS i 1 * wtZ c 1 := by
  decide +kernel

theorem ell_c0 : ∀ i : Fin 14, i.val ∈ ([4, 13] : List ℕ) → ellS i 0 * wtZ 12 0 + ellS i 1 * wtZ 12 1 = -5 + (lowExpS i : ℤ) := by
  decide +kernel

theorem ell_i : ∀ i : Fin 14, i.val ∈ ([4, 13] : List ℕ) → ellS i 0 * wtZ i 0 + ellS i 1 * wtZ i 1 = 1 := by
  decide +kernel

theorem lowering_noweight (i : Fin 14) (hi : i.val ∈ ([4, 13] : List ℕ)) (m : ℕ) (t : Fin m → Fin 14) :
    ∑ j, wtS (t j) ≠ m • wtS 12 - (m * lowExpS i + 1) • wtS i := by
  refine noweight_of_functional wtS (ellS i) 12 i (lowExpS i) (-5) (fun c => ?_) ?_ ?_ m t
  · rw [ell_sum]; exact ell_bound i c hi
  · rw [ell_sum]; exact ell_c0 i hi
  · rw [ell_sum]; exact ell_i i hi

theorem cyclic (c : Fin 14) : (Pi.single c 1 : Fin 14 → ℂ) ∈ slotWords fG2 12 10 := by
  have hn : ∀ i, 0 < i → i < vecR.length → cycNodeCheck rows vecs cpar 14 i = true := by
    intro i h0 h1
    have h := cycNodes_ok
    simp only [cycNodes, List.all_eq_true, List.mem_range'] at h
    exact h i ⟨i - 1, by omega, by omega⟩
  have h := cyc_ok
  simp only [cycCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨hK, hw⟩, hz⟩ := h c c.2
  exact single_mem_slotWords_of_tree (br := br) (vecs := vecs) (cpar := cpar) (fun x _ => rfl) 12
    cycRoot_ok.1 cycRoot_ok.2 vecR.length hn 10 c (cyc c).1 (cyc c).2 hK (fun p hp => hw p hp) hz

/-! ## The sector data -/

/-- **G2 as sector data.** -/
def G2sector : DeligneSectorData where
  n := G2data.n
  ρ := G2data.ρ
  rel := G2data.rel
  cas := G2data.cas
  u3 := G2data.u3
  ρFin := inferInstanceAs (Fintype (Fin 27))
  f := fG2
  jacobi := jacobi
  stable := stable
  c₀ := (12 : Fin 14)
  diag := diag
  raising e := e.val ∈ posL
  raising_table := raising_table
  cartan h := h.val ∈ ([0] : List ℕ)
  thetaH := thetaH
  cartan_table := cartan_table
  hθ := (0 : Fin 14)
  hθ_cartan := by decide
  hθ_ne := by decide
  lowering i := i.val ∈ ([4, 13] : List ℕ)
  lowExp := lowExpS
  R := 2
  wt := wtS
  table_wt := table_wt
  lowering_noweight := lowering_noweight
  fusion x := x.val ∈ negL
  depth := 10
  cyclic := cyclic
  cartanN h := h.val ∈ ([1] : List ℕ)
  thetaN := thetaN
  cartanN_table := cartanN_table

theorem G2sector_carrier : G2sector.toDeligneCarrierData = G2data := rfl

theorem G2sector_n : G2sector.n = 14 := rfl

end

end VOA.DeligneAudit.DeligneSector.G2

section AxiomAudit
open VOA.DeligneAudit.DeligneSector.G2
#print axioms G2data
#print axioms G2sector
end AxiomAudit
