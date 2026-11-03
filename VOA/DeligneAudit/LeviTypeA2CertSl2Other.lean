import VOA.DeligneAudit.LeviTypeA2CertOtherWeight

/-! Stability of a local Weyl lowering orbit under an extra Cartan current. -/

namespace VOA.DeligneAudit.CVsl2

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- An extra Cartan current preserving the lowering currents preserves
their cyclic orbit when its positive modes kill the generator. -/
theorem fspan_other_cartan_stable
    (F K : ℕ → Module.End ℂ V)
    (hKF : ∀ s k, K s * F k - F k * K s = F (s + k))
    (y : V) (hKy0 : ∃ c : ℂ, K 0 y = c • y)
    (hKyp : ∀ s, 0 < s → K s y = 0) :
    ∀ s, Fspan F y ≤ (Fspan F y).comap (K s) := by
  intro s
  rw [Fspan, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  induction l with
  | nil =>
      simp only [ECalc.Fw, Module.End.one_apply]
      change K s y ∈ Fspan F y
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · obtain ⟨c, hc⟩ := hKy0
        rw [hc]
        exact Submodule.smul_mem _ _ (self_mem y)
      · rw [hKyp s hs]
        exact (Fspan F y).zero_mem
  | cons k l ih =>
      have hc := congrArg (fun T : Module.End ℂ V => T (ECalc.Fw F l y))
        (hKF s k)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
      change K s (F k (ECalc.Fw F l y)) ∈ Fspan F y
      rw [sub_eq_iff_eq_add.mp hc]
      exact (Fspan F y).add_mem (Fw_mem y ((s + k) :: l))
        (Fspan_F y k ih)

end VOA.DeligneAudit.CVsl2

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl
open VOA.AffineSl3

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V)

/-- The other Cartan current acts on `f₂` as weight one. -/
theorem a2_other_f2_comm (s k : ℕ) :
    ρ.op 6 s * ρ.op 4 k - ρ.op 4 k * ρ.op 6 s =
      ρ.op 4 (s + k) := by
  rw [op_comm_end]
  simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.CVsl2.fspan_other_cartan_stable
#print axioms VOA.DeligneAudit.A3Sector.a2_other_f2_comm
