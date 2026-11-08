import VOA.Moonshine.MoonshineLRHecke
import VOA.Moonshine.MoonshineCNGenusZeroCritical

/-!
# Property P, unconditionally

`exists_mem_symmetryGroup_smul_eq` proves property P (equal values of `f_k` come from the
symmetry group) under the single hypothesis `PrimeHeckeIdentity F k`.
`ReplicableFamily_primeHeckeIdentity` discharges it, so property P holds for every member of every
replicable family of positive period.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open UpperHalfPlane

/-- **Property P, unconditionally.** If `f_k(z) = f_k(w)` then `γ • z = w` for some `γ` in the
symmetry group of `f_k`. -/
theorem ReplicableFamily_exists_mem_symmetryGroup_smul_eq {N : ℕ} (hN : 0 < N)
    (F : ReplicableFamily N) (k : ℕ) {z w : ℍ}
    (hzw : qSeriesFun (F.c k) z = qSeriesFun (F.c k) w) :
    ∃ γ ∈ symmetryGroup (qSeriesFun (F.c k)), γ • z = w :=
  exists_mem_symmetryGroup_smul_eq hN F k (ReplicableFamily_primeHeckeIdentity F k) hzw

end VOA.Moonshine.ConwayNorton.M8
