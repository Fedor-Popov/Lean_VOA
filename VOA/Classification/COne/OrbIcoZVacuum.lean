import VOA.Classification.COne.OrbIcoZZeroFiber
import VOA.Classification.COne.OrbIcoZVacuumLow
import VOA.Classification.COne.OrbIcoZSpan

/-! Intrinsic vacuum-fiber uniqueness for the actual A5 orbifold.
No strong-rationality or module-exhaustion input is used. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbZhu OrbSpan OrbPrim OrbIco OrbIcoS OrbIcoT OrbB5 PlusUnitary

theorem sixth_remainder :
    Wi.smul Xico 35 Xico - icoSixthCoupling • Xico ∈ lowerDesc Wi 36 := by
  have h := average_lowerDesc ico ico_sixth_channel
  rw [map_sub, map_smul] at h
  have ha : OrbC2.average ico ((V2m 1 le_rfl).smul
      (Xico : VOA.LatGen.LatModuleGen (VOA.LatGen.Triplet.latP 1)) 35 Xico) =
      Wi.smul Xico 35 Xico := by
    exact OrbC2.average_fixed (G := ico) (Wi.smul Xico 35 Xico)
  rw [ha, OrbC2.average_fixed] at h
  exact h

/-- Every projection killing the conformal image also kills the actual A5 primary. -/
theorem Xico_zeroFiber {T : Type*} [AddCommGroup T] [Module ℂ T]
    (f : A Wi →ₗ[ℂ] T) (hf : ∀ z, f (omegaL Wi z) = 0) :
    f (mk Wi Xico) = 0 := by
  have h := zeroFiber_lowerDesc36 f hf sixth_remainder
  rw [map_sub, map_smul, map_sub, map_smul] at h
  have hmode : f (mk Wi (Wi.smul Xico 35 Xico)) = 0 :=
    self35_zeroFiber f hf
  rw [hmode, zero_sub, neg_eq_zero] at h
  exact (smul_eq_zero.mp h).resolve_left icoSixthCoupling_ne_zero

/-- The sole non-vacuum tower is genuinely divisible by the conformal class. -/
theorem icoVacuumFiber_holds : ∃ z : A Wi, omegaL Wi z = mk Wi Xico := by
  let P := LinearMap.range (omegaL Wi)
  have h := Xico_zeroFiber P.mkQ (fun z =>
    (Submodule.Quotient.mk_eq_zero P).mpr (LinearMap.mem_range_self (omegaL Wi) z))
  exact (Submodule.Quotient.mk_eq_zero P).mp h

theorem Xico_zeroBottom {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wi M) (hl : IsLowestWeight N 0) :
    actA N hl (mk Wi Xico) = 0 := by
  apply Xico_zeroFiber
  intro z
  have h := actA_omegaL_pow N hl 1 z
  simpa using h

private abbrev adj := adjointModule Wi
private theorem adj_low : IsLowestWeight adj 0 := isLowestWeight_adjoint Wi

/-- Every Zhu class has the same scalar action on a zero bottom and on the vacuum bottom. -/
theorem ico_zeroBottom_scalar {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wi M) (hl : IsLowestWeight N 0) (z : A Wi) :
    ∃ c : ℂ, actA N hl z = c • 1 ∧ actA adj (h := 0) adj_low z = c • 1 := by
  let S := pairedScalars (actA N hl) (actA adj (h := 0) adj_low)
    (1 : Module.End ℂ (N.weight 0)) (1 : Module.End ℂ (adj.weight 0))
  have hs (b : Bool) : mk Wi (icoSeeds b) ∈ S := by
    cases b
    · exact ⟨1, by simpa only [icoSeeds, Bool.false_eq_true, if_false, one_smul]
          using actA_one N hl,
        by simpa only [icoSeeds, Bool.false_eq_true, if_false, one_smul]
          using actA_one adj adj_low⟩
    · exact ⟨0, by simpa only [icoSeeds, if_true, zero_smul] using Xico_zeroBottom N hl,
        by simpa only [icoSeeds, if_true, zero_smul] using Xico_zeroBottom adj adj_low⟩
  have hp (n : ℕ) {a : A Wi} (ha : a ∈ S) : (omegaL Wi ^ n) a ∈ S := by
    obtain ⟨c, hc, hc'⟩ := ha
    exact ⟨(0 : ℂ) ^ n * c, by rw [actA_omegaL_pow, hc, smul_smul],
      by rw [actA_omegaL_pow, hc', smul_smul]⟩
  have htop : (⊤ : Submodule ℂ (A Wi)) ≤ S := by
    rw [← ico_zhuTowerSpan_eq_top]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨b, n⟩, rfl⟩
    exact hp n (hs b)
  exact htop (Submodule.mem_top : z ∈ ⊤)

private theorem ico_simple : Wi.IsSimple :=
  @exceptionalOrbifold_isSimple ico ico_finite

/-- A realized lowest weight zero in an actual irreducible module identifies the vacuum module. -/
theorem ico_vacuum_of_lowest_zero {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wi M) (hi : N.IsIrreducible)
    (hl : IsLowestWeight N 0) (hne : N.weight 0 ≠ ⊥) :
    Nonempty (ModuleEquiv Wi N (adjointModule Wi)) := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply nonempty_moduleEquiv_adjoint_of_vacuumTop ico_simple N hi hl hx hx0
  intro k hk a ha
  obtain ⟨c, hc, hc'⟩ := ico_zeroBottom_scalar N hl (mk Wi a)
  have hc0 : c = 0 := by
    have hh := congrArg (fun f : Module.End ℂ (adj.weight 0) =>
      (f ⟨Wi.vacuum, vacuum_mem_adjoint_weight Wi⟩).val) hc'
    change ((actA adj (h := 0) adj_low (mk Wi a)
      ⟨Wi.vacuum, vacuum_mem_adjoint_weight Wi⟩ : adj.weight 0) : _) = c • Wi.vacuum at hh
    rw [actA_mk_apply_coe, oMod_adjoint_vacuum Wi hk ha] at hh
    exact (smul_eq_zero.mp hh.symm).resolve_right ico_simple.vacuum_ne_zero
  have hh := congrArg (fun f : Module.End ℂ (N.weight 0) => (f ⟨x, hx⟩).val) hc
  change ((actA N hl (mk Wi a) ⟨x, hx⟩ : N.weight 0) : M) = c • x at hh
  rwa [actA_mk_apply_coe, hc0, zero_smul] at hh

end VOA.Classification.COne.OrbIcoZ
