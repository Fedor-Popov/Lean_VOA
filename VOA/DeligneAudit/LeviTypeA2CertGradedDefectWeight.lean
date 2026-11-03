import VOA.DeligneAudit.LeviTypeA2CertGradedDefectWords

/-! The sorted word of a monomial retains both parts of its weight. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl

theorem a2_lst_length (f : ℕ →₀ ℕ) :
    (VOA.DeligneAudit.CLAssembly.lst f).length = (Finsupp.weight om f).1 := by
  rw [VOA.DeligneAudit.CLAssembly.length_lst]
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum,
    Prod.fst_sum, om]

theorem a2_lst_sum (f : ℕ →₀ ℕ) :
    (VOA.DeligneAudit.CLAssembly.lst f).sum = (Finsupp.weight om f).2 := by
  rw [← Multiset.sum_coe, VOA.DeligneAudit.CLAssembly.lst_coe,
    Finsupp.toMultiset_apply, Finsupp.multiset_sum_sum]
  simp [Finsupp.weight_apply, Finsupp.sum, Prod.snd_sum, om]
  apply Finset.sum_congr rfl
  intro x _
  change Multiset.sumAddMonoidHom (f x • ({x} : Multiset ℕ)) = f x * x
  rw [map_nsmul]
  simp [nsmul_eq_mul]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_lst_length
#print axioms VOA.DeligneAudit.A3Sector.a2_lst_sum
