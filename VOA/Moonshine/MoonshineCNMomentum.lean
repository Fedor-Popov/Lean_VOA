import VOA.Moonshine.MoonshineCNRealization

/-!
# Momentum decomposition and momentum addition by vertex modes

The lattice momentum is independent of oscillator weight. Each sector is a
copy of the whole polynomial Fock space. All reconstructed modes add momenta.
-/

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct Classical
open Module (End)
open IntegralLattice HeisenbergN LatGen

noncomputable def latticeMomentumGrading (L : IntegralLattice) (α : L.carrier) :
    Submodule ℂ (LatModuleGen L) := ⨆ w : ℤ, bigradα L (w, α)

theorem latticeMomentumGrading_eq_range (L : IntegralLattice) (α : L.carrier) :
    latticeMomentumGrading L α = LinearMap.range (mkEα L α) := by
  simp only [latticeMomentumGrading, bigradα]
  rw [← Submodule.map_iSup, gradingZN_iSup_eq_top, Submodule.map_top]

theorem latticeMomentumGrading_eq_fiber (L : IntegralLattice) (α : L.carrier) :
    latticeMomentumGrading L α = ⨆ p ∈ {p : ℤ × L.carrier | p.2 = α}, bigradα L p := by
  apply le_antisymm
  · exact iSup_le fun w => le_biSup (bigradα L) (show (w, α).2 = α from rfl)
  · refine iSup_le fun p => iSup_le fun hp => ?_
    obtain ⟨w, β⟩ := p
    change β = α at hp
    subst β
    exact le_iSup (fun w => bigradα L (w, α)) w

theorem latticeMomentumGrading_complement (L : IntegralLattice) (α : L.carrier) :
    (⨆ (β : L.carrier) (_ : β ≠ α), latticeMomentumGrading L β) =
      ⨆ p ∈ {p : ℤ × L.carrier | p.2 ≠ α}, bigradα L p := by
  apply le_antisymm
  · refine iSup_le fun β => iSup_le fun hβ => iSup_le fun w => ?_
    exact le_biSup (bigradα L) (show (w, β).2 ≠ α from hβ)
  · refine iSup_le fun p => iSup_le fun hp => ?_
    exact (le_iSup (fun w => bigradα L (w, p.2)) p.1).trans
      ((le_iSup (fun _ : p.2 ≠ α => latticeMomentumGrading L p.2) hp).trans
        (le_iSup (fun β => ⨆ (_ : β ≠ α), latticeMomentumGrading L β) p.2))

theorem latticeMomentumGrading_isInternal (L : IntegralLattice) :
    DirectSum.IsInternal (latticeMomentumGrading L) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro α
    rw [latticeMomentumGrading_eq_fiber, latticeMomentumGrading_complement]
    apply (bigradα_iSupIndep L).disjoint_biSup_biSup
    rw [Set.disjoint_left]
    exact fun _ he hn => hn he
  · apply top_unique
    rw [← bigradα_iSup_eq_top L]
    exact iSup_le fun p =>
      (le_iSup (fun w => bigradα L (w, p.2)) p.1).trans
        (le_iSup (latticeMomentumGrading L) p.2)

theorem latState_mem_momentum (L : IntegralLattice) (p : FockN (rank L)) (α : L.carrier) :
    latStateGen L p α ∈ latticeMomentumGrading L α := by
  rw [latticeMomentumGrading_eq_range]
  exact ⟨p, rfl⟩

/-- A field of momentum `α` adds `α` to the momentum of its argument. -/
def HasLatticeMomentum {L : IntegralLattice}
    (A : FormalDist (End ℂ (LatModuleGen L))) (α : L.carrier) : Prop :=
  ∀ (t : ℤ) (β : L.carrier) (v : LatModuleGen L), v ∈ latticeMomentumGrading L β →
    A t v ∈ latticeMomentumGrading L (α + β)

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

theorem canonicalChargedField_momentum (α : L.carrier) :
    HasLatticeMomentum (canonicalChargedField F α) α := by
  intro t β v hv
  rw [latticeMomentumGrading_eq_range] at hv
  obtain ⟨p, rfl⟩ := hv
  change canonicalChargedField F α t (latStateGen L p β) ∈ _
  rw [canonicalChargedField_tmul]
  exact Submodule.smul_mem _ _ (latState_mem_momentum L _ _)

theorem frameCurrent_momentum (a : Fin (rank L)) :
    HasLatticeMomentum (frameCurrent F a) 0 := by
  intro t β v hv
  rw [zero_add]
  rw [latticeMomentumGrading_eq_range] at hv
  obtain ⟨p, rfl⟩ := hv
  change frameCurrent F a t (latStateGen L p β) ∈ _
  rw [frameCurrent_tmul]
  apply Submodule.add_mem
  · exact latState_mem_momentum L _ _
  · split_ifs
    · exact Submodule.smul_mem _ _ (latState_mem_momentum L _ _)
    · exact Submodule.zero_mem _

theorem HasLatticeMomentum.derivative {A : FormalDist (End ℂ (LatModuleGen L))}
    {α : L.carrier} (hA : HasLatticeMomentum A α) : HasLatticeMomentum (deriv A) α := by
  intro t β v hv
  rw [deriv_apply, ← Int.cast_smul_eq_zsmul ℂ, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (hA (t + 1) β v hv)

theorem HasLatticeMomentum.scalar {A : FormalDist (End ℂ (LatModuleGen L))}
    {α : L.carrier} (hA : HasLatticeMomentum A α) (c : ℂ) :
    HasLatticeMomentum (c • A) α := by
  intro t β v hv
  exact Submodule.smul_mem _ c (hA t β v hv)

theorem frameDerivativeCurrent_momentum (a : Fin (rank L)) (i : ℕ) :
    HasLatticeMomentum (frameDerivativeCurrent F a i) 0 := by
  have hd : ∀ j : ℕ, HasLatticeMomentum (deriv^[j] (frameCurrent F a)) 0 := by
    intro j
    induction j with
    | zero => exact frameCurrent_momentum F a
    | succ j ih =>
      rw [Function.iterate_succ', Function.comp_apply]
      exact ih.derivative
  exact (hd i).scalar _

theorem HasLatticeMomentum.normalProduct {A B : FormalDist (End ℂ (LatModuleGen L))}
    (hAf : IsField A) (hBf : IsField B) {α β : L.carrier}
    (hA : HasLatticeMomentum A α) (hB : HasLatticeMomentum B β) :
    HasLatticeMomentum (nprod hAf hBf) (α + β) := by
  intro t γ v hv
  rw [nprod_apply]
  refine finsum_lattice_submodule L _ _ (normalOrdered_diag_support_finite hAf hBf t v) ?_
  intro m
  rw [normalOrdered_apply]
  split_ifs
  · simpa only [Module.End.mul_apply, add_assoc] using hA m (β + γ) (B (t - m) v) (hB _ _ _ hv)
  · have h := hB (t - m) (α + γ) (A m v) (hA _ _ _ hv)
    simpa only [Module.End.mul_apply, show β + (α + γ) = α + β + γ by abel] using h

theorem frameWordField_momentum (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    HasLatticeMomentum (frameWordField F l α) α := by
  induction l with
  | nil => exact canonicalChargedField_momentum F α
  | cons ia rest ih =>
    rw [frameWordField_cons]
    simpa only [zero_add] using
      HasLatticeMomentum.normalProduct
        (frameDerivativeCurrent_isField F ia.2 ia.1) (frameWordField_isField F rest α)
        (frameDerivativeCurrent_momentum F ia.2 ia.1) ih

/-- Every fixed momentum sector is spanned by its oscillator words. -/
theorem momentumSector_le_wordSpan (α : L.carrier) :
    latticeMomentumGrading L α ≤
      Submodule.span ℂ (Set.range (fun l => frameWordState L l α)) := by
  rw [latticeMomentumGrading_eq_range]
  rintro _ ⟨p, rfl⟩
  change p ⊗ₜ[ℂ] eGen L α ∈ _
  rw [← MvPolynomial.support_sum_monomial_coeff p, TensorProduct.sum_tmul]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [show MvPolynomial.monomial d (MvPolynomial.coeff d p) =
      (MvPolynomial.coeff d p) • MvPolynomial.monomial d (1 : ℂ) by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], ← TensorProduct.smul_tmul']
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨monoWordN d, by simp only [frameWordState_eq, wordStateN_monoWordN]⟩

theorem frameStateField_momentum (hEven : L.Even) (α : L.carrier)
    (u : LatModuleGen L) (hu : u ∈ latticeMomentumGrading L α) :
    HasLatticeMomentum (frameStateField F hEven u) α := by
  have hspan : u ∈ Submodule.span ℂ (Set.range (fun l => frameWordState L l α)) :=
    momentumSector_le_wordSpan α hu
  clear hu
  induction hspan using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, rfl⟩ := hu
    rw [frameStateField_word]
    exact frameWordField_momentum F l α
  | zero =>
    intro t β v hv
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  | add u w _ _ ihu ihw =>
    intro t β v hv
    rw [map_add]
    exact Submodule.add_mem _ (ihu t β v hv) (ihw t β v hv)
  | smul c u _ ihu =>
    rw [map_smul]
    exact ihu.scalar c

theorem lorentzianNearVOA_momentum (α β : lorentzianLattice.carrier)
    (u v : LorentzianFockSpace) (hu : u ∈ latticeMomentumGrading lorentzianLattice α)
    (hv : v ∈ latticeMomentumGrading lorentzianLattice β) (n : ℤ) :
    mode (lorentzianNearVOA.Y u) n v ∈ latticeMomentumGrading lorentzianLattice (α + β) :=
  frameStateField_momentum lorentzianComplexFrame lorentzian_even α u hu (-n - 1) β v hv

end VOA.Moonshine.ConwayNorton
