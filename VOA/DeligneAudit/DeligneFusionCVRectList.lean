import VOA.DeligneAudit.DeligneFusionCVRectCount
import VOA.DeligneAudit.DeligneFusionCVRectIntegrationOrder

/-! # Maximal-site extraction and permutation invariance for the actual count -/

namespace VOA.DeligneAudit.A2.CVRectList

open CVRectCount CVRectIntegrationOrder

/-- Select a maximal capacity, retaining all multiplicities by an explicit
list permutation. Zero capacities are allowed. -/
theorem exists_max_cons (two : List ℕ) (hne : two ≠ []) :
    ∃ K ks, two.Perm (K :: ks) ∧ ∀ k ∈ ks, k ≤ K := by
  refine ⟨two.max hne, two.erase (two.max hne), List.perm_cons_erase (List.max_mem hne), ?_⟩
  intro k hk
  exact List.le_max_of_mem (List.mem_of_mem_erase hk)

theorem excess_perm {ks ls : List ℕ} (h : ks.Perm ls) (t : ℕ) :
    excess ks t = excess ls t := by
  exact (h.map (fun k => t - k)).sum_eq

theorem familyWeight_perm {two two' one one' : List ℕ}
    (ht : two.Perm two') (ho : one.Perm one') :
    familyWeight two one = familyWeight two' one' := by
  simp only [familyWeight, (ht.map rectangleWeight).prod_eq,
    (ho.map (fun k => k + 1)).prod_eq]

theorem complexity_perm {two two' one one' : List ℕ}
    (ht : two.Perm two') (ho : one.Perm one') :
    complexity two one = complexity two' one' := by
  simp only [complexity, ht.sum_eq, ho.sum_eq, ht.length_eq, ho.length_eq]

/-- Numerical parameter identities for moving the selected site first. -/
theorem max_cons_parameters {two ks : List ℕ} {K : ℕ} (h : two.Perm (K :: ks)) :
    two.length = ks.length + 1 ∧ two.sum = K + ks.sum := by
  exact ⟨by simpa using h.length_eq, by simpa using h.sum_eq⟩

end VOA.DeligneAudit.A2.CVRectList

#print axioms VOA.DeligneAudit.A2.CVRectList.exists_max_cons
#print axioms VOA.DeligneAudit.A2.CVRectList.familyWeight_perm
#print axioms VOA.DeligneAudit.A2.CVRectList.complexity_perm
