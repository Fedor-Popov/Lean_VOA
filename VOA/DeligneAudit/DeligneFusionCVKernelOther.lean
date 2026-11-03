import VOA.DeligneAudit.DeligneFusionCVFamily
import VOA.DeligneAudit.DeligneFusionCVCrossRoot

/-!
# The other simple-root relations of the first A₂ CV kernel generator

For the zero-epsilon three-level CV family, let
`u = f₁(ν₁+ρ₁+j−1) w`, with `j ≥ 2`. This file proves its second-root
linear truncation and all quadratic coefficient relations needed by the
first kernel source presentation. They follow from the source CV relations,
not from any assumed target presentation or dimension bound.
-/

namespace VOA.DeligneAudit.A2.CVKernelOther

open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart

noncomputable section

section Coefficients

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- At sufficiently high total degree, a quadratic coefficient may omit its
low modes: their partners already annihilate the vector. -/
theorem Q_two_eq_QFrom (F : ℕ → Module.End ℂ V)
    (hFF : ∀ k l, F k * F l = F l * F k) {u : V} (B L s : ℕ)
    (htr : ∀ k, L ≤ k → F k u = 0) (hs : B + L ≤ s) :
    Q F 2 s u = QFrom F (B + 1) 2 s u := by
  have htwo (G : ℕ → Module.End ℂ V) :
      Q G 2 s = ∑ x ∈ Finset.antidiagonal s, G x.1 * G x.2 := by
    rw [Q_succ]
    simp only [Q_one]
  rw [htwo, QFrom, htwo]
  simp only [LinearMap.coe_sum, Finset.sum_apply, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxs : x.1 + x.2 = s := Finset.mem_antidiagonal.mp hx
  by_cases h1 : B + 1 ≤ x.1
  · by_cases h2 : B + 1 ≤ x.2
    · simp only [fromMode, if_pos h1, if_pos h2]
    · simp only [fromMode, if_pos h1, if_neg h2, LinearMap.zero_apply, map_zero]
      rw [← Module.End.mul_apply, hFF, Module.End.mul_apply,
        htr x.1 (by omega), map_zero]
  · simp only [fromMode, if_neg h1, LinearMap.zero_apply]
    rw [htr x.2 (by omega), map_zero]

end Coefficients

section CurrentModule

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVCrossRoot

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ν ϱ : Weight} {j : ℕ}

/-- A cutoff second-root current commutes through a first-root mode on the
common kernel of sufficiently high highest-root modes. -/
theorem f1_QFrom_second (R : CurrentModule bracketTable V) {w : V} {L a p : ℕ}
    (hap : L ≤ a + p) (htheta : ∀ k, L ≤ k → R.op 5 k w = 0) (r s : ℕ) :
    R.op 3 a (QFrom (R.op 4) p r s w) =
      QFrom (R.op 4) p r s (R.op 3 a w) := by
  apply Q_commute_on (fromMode (R.op 4) p) (R.op 3 a) (thetaKernel R L)
  · intro k v hv
    by_cases hk : p ≤ k
    · simpa only [fromMode, if_pos hk] using thetaKernel_f2 R L k hv
    · simp only [fromMode, if_neg hk, LinearMap.zero_apply]
      exact (thetaKernel R L).zero_mem
  · intro k v hv
    by_cases hk : p ≤ k
    · simp only [fromMode, if_pos hk]
      exact (f2_f1_commute_on R (by omega) hv).symm
    · simp only [fromMode, if_neg hk, LinearMap.zero_apply, map_zero]
  · exact htheta

/-- The first kernel generator has the second-root linear truncation of its
proposed source partition. -/
theorem second_trunc (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j)
    (q : ℕ) (hq : ν.2 + ϱ.2 + j ≤ q) :
    R.op 4 q (R.op 3 (ν.1 + ϱ.1 + j - 1) w) = 0 := by
  have hq0 : R.op 4 q w = 0 := by
    apply trunc_of_cvrel h.second q
    simp only [parts_length]
    omega
  have htheta : R.op 5 (q + (ν.1 + ϱ.1 + j - 1)) w = 0 :=
    theta_trunc h _ (by omega)
  rw [comm_apply 4 3]
  simp [Fin.sum_univ_eight, bracketTable, hq0, htheta]

/-- The source cutoff relation at `B+1`, at exactly the new quadratic threshold. -/
theorem second_cutoff_two (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j)
    (s : ℕ) (hs : 2 * (ν.2 + ϱ.2) + j ≤ s) :
    QFrom (R.op 4) (ν.2 + ϱ.2 + 1) 2 s w = 0 := by
  apply cvrel_cutoff (CVRoots.sl2_second R).hFF h.second
    (ν.2 + ϱ.2 + 1) 2 s (by omega)
  have ht : T (ν.2 + ϱ.2 + 1) (parts ϱ.2 ν.2 (0 + j)) = j - 1 := by
    simp only [parts, T_append, T_replicate,
      List.length_append, List.length_replicate]
    omega
  rw [ht]
  omega

/-- All target second-root quadratic relations hold on the first kernel generator. -/
theorem second_quadratic (h : CV3Rel R w (0, 0) ν ϱ j) (hj : 2 ≤ j)
    (s : ℕ) (hs : 2 * (ν.2 + ϱ.2) + j ≤ s) :
    Q (R.op 4) 2 s (R.op 3 (ν.1 + ϱ.1 + j - 1) w) = 0 := by
  rw [Q_two_eq_QFrom (R.op 4) (CVRoots.sl2_second R).hFF
    (ν.2 + ϱ.2) (ν.2 + ϱ.2 + j) s (second_trunc h hj) (by omega)]
  have hc := f1_QFrom_second R
    (L := (ν.1 + ϱ.1) + (ν.2 + ϱ.2) + j)
    (a := ν.1 + ϱ.1 + j - 1) (p := ν.2 + ϱ.2 + 1)
    (by omega) (theta_trunc h) 2 s
  rw [← hc, second_cutoff_two h hj s hs, map_zero]

end CurrentModule

end

end VOA.DeligneAudit.A2.CVKernelOther

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.CVKernelOther.Q_two_eq_QFrom
#print axioms VOA.DeligneAudit.A2.CVKernelOther.second_trunc
#print axioms VOA.DeligneAudit.A2.CVKernelOther.second_quadratic
end AxiomAudit
