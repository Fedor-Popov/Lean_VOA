import VOA.DeligneAudit.LeviTypeA2CertBoxDefect

/-! The graded first-colour box with commuting spectators. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A commuting spectator preserves the length and mode-degree box bound. -/
theorem a2_span_box_graded_spectator (F : ℕ → Module.End ℂ V)
    (hFF : ∀ i j, F i * F j = F j * F i)
    (B : Module.End ℂ V) (hBF : ∀ i, B * F i = F i * B)
    (w : V) (m : ℕ)
    (hk : ∀ r s, 1 ≤ r → m + 1 ≤ r + s →
      (PowerSeries.coeff s (VOA.DeligneAudit.Garland.Fs F ^ r)) w = 0)
    {P : R} {n : ℕ × ℕ}
    (hp : MvPolynomial.IsWeightedHomogeneous om P n) :
    Sl2Weyl.evAlg F hFF P (B w) ∈
      Submodule.span ℂ {v | ∃ f, BoxP m f ∧ Finsupp.weight om f = n ∧
        v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) (B w)} := by
  let S : Submodule ℂ V :=
    Submodule.span ℂ {v | ∃ f, BoxP m f ∧ Finsupp.weight om f = n ∧
      v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) (B w)}
  have hmap : ∀ v ∈ Submodule.span ℂ {v | ∃ f, BoxP m f ∧
      Finsupp.weight om f = n ∧
      v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) w}, B v ∈ S := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨f, hf, hw, rfl⟩ := hv
        have hc := a2_evAlg_comm_spectator F hFF B hBF
          (MvPolynomial.monomial f 1)
        rw [← Module.End.mul_apply, hc, Module.End.mul_apply]
        exact Submodule.subset_span ⟨f, hf, hw, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using S.add_mem hx hy
    | smul c x _ hx => simpa only [map_smul] using S.smul_mem c hx
  have h := hmap _ (span_box_graded F hFF w m hk hp)
  have hc := a2_evAlg_comm_spectator F hFF B hBF P
  rwa [← Module.End.mul_apply, hc, Module.End.mul_apply] at h

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_span_box_graded_spectator
