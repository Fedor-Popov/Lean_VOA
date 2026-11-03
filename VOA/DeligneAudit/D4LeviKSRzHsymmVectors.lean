import VOA.DeligneAudit.D4LeviKSRzOrbitKernel

/-! The complete homogeneous polynomial as a sum over mode vectors. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

noncomputable instance rzModeVectorFintype (k s : ℕ) :
    Fintype {e : Fin k → ℕ // ∑ i, e i = s} :=
  Fintype.ofEquiv (Sym (Fin k) s)
    (Sym.equivNatSumOfFintype (Fin k) s)

theorem rz_hsymm_eq_sum_vectors (k s : ℕ) :
    hsymm (Fin k) ℂ s =
      ∑ e : {e : Fin k → ℕ // ∑ i, e i = s},
        ∏ i : Fin k, X i ^ e.1 i := by
  classical
  unfold hsymm
  apply Fintype.sum_equiv (Sym.equivNatSumOfFintype (Fin k) s)
  intro t
  rw [Finset.prod_multiset_map_count]
  rw [Finset.prod_subset (Finset.subset_univ _) (by
    intro i hi hnot
    have hzero : (t : Multiset (Fin k)).count i = 0 :=
      Multiset.count_eq_zero_of_notMem (by
        simpa only [Multiset.mem_toFinset] using hnot)
    simp [hzero])]
  simp

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_hsymm_eq_sum_vectors
