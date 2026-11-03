import VOA.DeligneAudit.SL4TSecondLeviOrbitClosure
import Mathlib.Data.Finset.Max

/-! Dimension bounds from quotient layers in finite fibers with a finite set of supported layers. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Adding a subspace increases dimension by its image in the quotient. -/
theorem submodule_finrank_sup_eq (S N : Submodule ℂ V) :
    Module.finrank ℂ ↥(S ⊔ N) = Module.finrank ℂ N + Module.finrank ℂ (S.map N.mkQ) := by
  let f := N.mkQ.comp S.subtype
  have hr : LinearMap.range f = S.map N.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : Module.finrank ℂ (LinearMap.ker f) = Module.finrank ℂ ↥(S ⊓ N) := by
    rw [← Submodule.finrank_map_subtype_eq S (LinearMap.ker f)]
    rw [show LinearMap.ker f = N.comap S.subtype by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ], Submodule.map_comap_subtype]
  have hd := f.finrank_range_add_finrank_ker
  rw [hr, hk] at hd
  have hs := S.finrank_sup_add_finrank_inf_eq N
  omega

/-- Enlarging the relation subspace decreases the dimension of a quotient image. -/
theorem quotientImage_finrank_antitone (S N P : Submodule ℂ V) (hNP : N ≤ P) :
    Module.finrank ℂ (S.map P.mkQ) ≤ Module.finrank ℂ (S.map N.mkQ) := by
  let f := Submodule.mapQ N P LinearMap.id hNP
  have he : (S.map N.mkQ).map f = S.map P.mkQ := by
    rw [← Submodule.map_comp]
    rfl
  rw [← he]
  exact Submodule.finrank_map_le _ _

/-- Summing quotient bounds along any finite strictly ordered filtration bounds the total span. -/
theorem finiteFiltration_finrank_le {ι : Type v} [DecidableEq ι]
    (S N : ι → Submodule ℂ V) (ord : ι → ℤ) (c : ι → ℕ) (t : Finset ι)
    (hN : ∀ i ∈ t, N i ≤ ⨆ j ∈ t, ⨆ (_ : ord j < ord i), S j)
    (hc : ∀ i ∈ t, Module.finrank ℂ ((S i).map (N i).mkQ) ≤ c i) :
    Module.finrank ℂ ↥(⨆ i ∈ t, S i) ≤ ∑ i ∈ t, c i := by
  induction t using Finset.induction_on_max_value ord with
  | empty => simp
  | insert a t ha hmax ih =>
    have hn : N a ≤ ⨆ j ∈ t, S j := by
      refine (hN a (Finset.mem_insert_self _ _)).trans ?_
      apply iSup_le
      intro j
      apply iSup_le
      intro hj
      apply iSup_le
      intro ho
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact False.elim (lt_irrefl _ ho)
      · exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)
    have hnt : ∀ i ∈ t, N i ≤ ⨆ j ∈ t, ⨆ (_ : ord j < ord i), S j := by
      intro i hi
      refine (hN i (Finset.mem_insert_of_mem hi)).trans ?_
      apply iSup_le
      intro j
      apply iSup_le
      intro hj
      apply iSup_le
      intro ho
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact False.elim ((not_lt_of_ge (hmax i hi)) ho)
      · exact le_iSup_of_le j (le_iSup_of_le hj (le_iSup_of_le ho le_rfl))
    have ht := ih hnt (fun i hi => hc i (Finset.mem_insert_of_mem hi))
    have hb := (quotientImage_finrank_antitone (S a) (N a) (⨆ j ∈ t, S j) hn).trans
      (hc a (Finset.mem_insert_self _ _))
    rw [Finset.sum_insert ha, Finset.iSup_insert, submodule_finrank_sup_eq]
    omega

/-- Finite fibers and finite support turn local quotient bounds into a global dimension bound. -/
theorem finiteFiberFiltration_finrank_le {ι : Type v} [DecidableEq ι]
    (S N : ι → Submodule ℂ V) (fiber : ι → Finset ι) (ord : ι → ℤ)
    (c : ι → ℕ) (support : Finset ι)
    (hself : ∀ i, i ∈ fiber i)
    (hfiber : ∀ i j, j ∈ fiber i → fiber j = fiber i)
    (hN : ∀ i, N i ≤ ⨆ j ∈ fiber i, ⨆ (_ : ord j < ord i), S j)
    (hc : ∀ i, Module.finrank ℂ ((S i).map (N i).mkQ) ≤ c i)
    (hzero : ∀ i, i ∉ support → c i = 0) :
    Module.finrank ℂ ↥(⨆ i, S i) ≤ ∑ i ∈ support, c i := by
  classical
  have hfg : (⨆ i, S i).FG := Module.Finite.iff_fg.mp inferInstance
  obtain ⟨t, ht⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
    (Submodule ℂ V) ((Submodule.fg_iff_compact _).mp hfg) S le_rfl
  let s := t.biUnion fiber
  have hts : t ⊆ s := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨i, hi, hself i⟩
  have he : (⨆ i, S i) = ⨆ i ∈ s, S i := by
    apply le_antisymm
    · exact ht.trans (iSup_le fun i => iSup_le fun hi =>
        le_iSup_of_le i (le_iSup_of_le (hts hi) le_rfl))
    · exact iSup_le fun i => iSup_le fun _ => le_iSup S i
  have hclosed : ∀ i ∈ s, fiber i ⊆ s := by
    intro i hi j hj
    obtain ⟨k, hk, hki⟩ := Finset.mem_biUnion.mp hi
    rw [hfiber k i hki] at hj
    exact Finset.mem_biUnion.mpr ⟨k, hk, hj⟩
  have hb := finiteFiltration_finrank_le S N ord c s (fun i hi =>
    (hN i).trans (iSup_le fun j => iSup_le fun hj => iSup_le fun ho =>
      le_iSup_of_le j (le_iSup_of_le (hclosed i hi hj) (le_iSup_of_le ho le_rfl))))
    (fun i _ => hc i)
  have hs : (∑ i ∈ s, c i) = ∑ i ∈ s ∩ support, c i := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro i _ hi
    apply hzero
    intro his
    exact hi (Finset.mem_inter.mpr ⟨by assumption, his⟩)
  rw [he]
  exact hb.trans (hs.trans_le (Finset.sum_le_sum_of_subset Finset.inter_subset_right))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.submodule_finrank_sup_eq
#print axioms VOA.DeligneAudit.SL4T.quotientImage_finrank_antitone
#print axioms VOA.DeligneAudit.SL4T.finiteFiltration_finrank_le
#print axioms VOA.DeligneAudit.SL4T.finiteFiberFiltration_finrank_le
