import VOA.DeligneAudit.DeligneFusionGrade
import VOA.DeligneAudit.DeligneFusionDemazure
import VOA.DeligneAudit.DeligneFusionInverse
import VOA.DeligneAudit.DeligneFusionGarlandSl3
import VOA.DeligneAudit.DeligneFusionFinite

/-!
# A₂ classical freeness from the named fusion inputs

The graded characters `Mchar a b` of the universal modules `U_{a,b}` (`DeligneFusionUniv`) satisfy
the `FusionSqueezeInputs`:

* `nonneg` — they are graded dimensions;
* `rec_le` — Ravinder's exact sequence, proved here (`DeligneFusionGrade.finrank_step`) from the
  named input `RavinderKernelTrunc` (Garland identities);
* `total_le` — the named input `FusionTotalBound` (Feigin; Fourier–Littelmann) at `a = 0`;
* `dem_le` — from the named input `DemazureRealization n` (U7, the `dem_le_of_realization`).

The squeeze then gives U5 for `fusionF`, and with it the A₂ case.
-/

namespace VOA.DeligneAudit.A2

open PowerSeries SectorWeyl VOA.AffineSl3 VOA.DeligneGaussian VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-- **All degree pieces of all `U_{a,b}` are finite-dimensional.** -/
theorem univ_fd (hF : FusionTotalBound) (hR : RavinderKernelRel) :
    ∀ a b N, FiniteDimensional ℂ (cycDeg (univRep a b) (SectorWeyl.wU a b) N)
  | 0, b, N =>
      (hF b _ (univRep 0 b) (SectorWeyl.wU 0 b) ((mabRel_zero_iff _ _ _).mp (univ_mabRel 0 b))).1 N
  | a + 1, b, N => by
      haveI := univ_fd hF hR a (b + 1) N
      haveI := univ_fd hF hR a b (N - (2 * a + b + 1))
      exact SectorWeyl.fd_step a b hR N

/-- **The universal bound for `Mchar`** (the body of the `MabUniversalBound Mchar`): every
cyclic module with the relations of `M_{a,b}` is bounded degree by degree by `Mchar a b`. -/
theorem Mchar_universalBound (hF : FusionTotalBound) (hR : RavinderKernelRel) :
    ∀ (a b : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V)
      (w : V), MabRel ρ w a b → ∀ N, (Module.finrank ℂ (cycDeg ρ w N) : ℚ) ≤ coeff N (Mchar a b) := by
  intro a b V _ _ ρ w h N
  haveI := univ_fd hF hR a b N
  simp only [Mchar, coeff_mk]
  exact_mod_cast finrank_cycDeg_le_univ h N

theorem Mchar_rec_le (hF : FusionTotalBound) (hR : RavinderKernelRel) (a b : ℕ) :
    CoeffLe (Mchar (a + 1) b) (Mchar a (b + 1) + X ^ (2 * a + b + 1) * Mchar a b) := by
  intro N
  haveI := univ_fd hF hR a (b + 1) N
  haveI := univ_fd hF hR a b (N - (2 * a + b + 1))
  have h := finrank_step a b hR N
  rw [map_add, coeff_X_pow_mul']
  simp only [Mchar, coeff_mk]
  split_ifs with hN
  · rw [if_pos hN] at h; exact_mod_cast h
  · rw [if_neg hN, add_zero] at h; rw [add_zero]; exact_mod_cast h

theorem Mchar_total_le (hF : FusionTotalBound) (m B : ℕ) :
    ∑ N ∈ Finset.range B, coeff N (Mchar 0 m) ≤ 8 ^ m := by
  have := (hF m _ (univRep 0 m) (SectorWeyl.wU 0 m) ((mabRel_zero_iff _ _ _).mp (univ_mabRel 0 m))).2 B
  simp only [Mchar, coeff_mk]
  exact_mod_cast this

/-- `Mchar_universalBound` in the `MabUniversalBound` form. -/
theorem mabUniversalBound_Mchar (hF : FusionTotalBound) (hR : RavinderKernelRel) :
    MabUniversalBound Mchar :=
  Mchar_universalBound hF hR

/-- **The squeeze inputs for the universal characters**, from the three named inputs. -/
theorem fusionSqueezeInputs_Mchar (hF : FusionTotalBound) (hR : RavinderKernelRel)
    (hD : ∀ n, DemazureRealization n) : FusionSqueezeInputs Mchar where
  nonneg := Mchar_nonneg
  rec_le := Mchar_rec_le hF hR
  dem_le n := dem_le_of_realization (mabUniversalBound_Mchar hF hR) (hD n)
  total_le := Mchar_total_le hF

/-- **U5 for `fusionF`** from `FusionTotalBound`, `RavinderKernelTrunc` and the Demazure
realizations (U7). -/
theorem fusionModuleBound_of_named (hF : FusionTotalBound) (hT : RavinderKernelTrunc)
    (hD : ∀ n, DemazureRealization n) : FusionModuleBound fusionF := by
  have hR := ravinderKernelRel_of_trunc hT
  exact fusionModuleBound_of_realizations (mabUniversalBound_Mchar hF hR) hD Mchar_nonneg
    (Mchar_rec_le hF hR) (Mchar_total_le hF)

/-- **A₂ Deligne classical freeness from the named fusion inputs**: `FusionTotalBound`
(F4: Feigin; Fourier–Littelmann), `RavinderKernelTrunc` (F4′: Ravinder Thm. 1 / Garland) and
`DemazureRealization` (U7). -/
theorem classicallyFree_of_realizations (hF : FusionTotalBound) (hT : RavinderKernelTrunc)
    (hD : ∀ n, DemazureRealization n) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_fusionBound (fusionModuleBound_of_named hF hT hD)

/-- **A₂ Deligne classical freeness from `FusionTotalBound` and U7 alone**: `RavinderKernelTrunc`
is a theorem (`SectorWeyl.ravinderKernelTrunc`, Garland identity with `P(u) = 1`). -/
theorem classicallyFree_of_totalBound (hF : FusionTotalBound) (hD : ∀ n, DemazureRealization n) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_realizations hF ravinderKernelTrunc hD

/-- **A₂ Deligne classical freeness from the bare dimension bound `FusionTotalDim` and U7**:
the finiteness clause of `FusionTotalBound` is a theorem (`cycDeg_finiteDimensional`). -/
theorem classicallyFree_of_totalDim (hF : FusionTotalDim) (hD : ∀ n, DemazureRealization n) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_totalBound (fusionTotalBound_of_dim hF) hD

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.Mchar_universalBound
#print axioms VOA.DeligneAudit.A2.fusionSqueezeInputs_Mchar
#print axioms VOA.DeligneAudit.A2.fusionModuleBound_of_named
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_realizations
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_totalBound
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_totalDim
end AxiomAudit
