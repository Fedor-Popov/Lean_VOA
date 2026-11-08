import VOA.Moonshine.MoonshineCNExponential

/-!
# Charged fields on an indefinite lattice Fock space

The creation and annihilation exponentials are formal fields. Their normally
ordered product and the cocycle-weighted momentum shift define `chargedField`.
Every coefficient sum is finite on a fixed vector. The creation exponential
itself generally has infinitely many nonzero coefficients on the vacuum.

The proofs adapt `LatticeGenVertex` and the lower-truncation argument of
`LatticeGenReconstruct`, with an arbitrary complex frame and cocycle function.
Locality is not asserted in this module.
-/

set_option maxHeartbeats 800000

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct
open Module (End)
open IntegralLattice HeisenbergN LatGen

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)
variable (ε : L.carrier → L.carrier → ℂ)

noncomputable def creationField (α : L.carrier) : FormalDist (End ℂ (FockN (rank L))) :=
  fun t => if 0 ≤ t then creationOperator F α t.toNat else 0

@[simp] theorem creationField_apply (α : L.carrier) (t : ℤ) :
    creationField F α t = if 0 ≤ t then creationOperator F α t.toNat else 0 := rfl

theorem creationField_neg (α : L.carrier) {t : ℤ} (ht : t < 0) : creationField F α t = 0 := by
  rw [creationField_apply, if_neg (by omega)]

theorem creationField_isField (α : L.carrier) : IsField (creationField F α) := by
  intro x
  exact ⟨0, fun n hn => by rw [creationField_neg F α hn, LinearMap.zero_apply]⟩


noncomputable def annihilationField (α : L.carrier) : FormalDist (End ℂ (FockN (rank L))) :=
  fun t => if t ≤ 0 then annihilationCoefficient F α (-t).toNat else 0

@[simp] theorem annihilationField_apply (α : L.carrier) (t : ℤ) :
    annihilationField F α t = if t ≤ 0 then annihilationCoefficient F α (-t).toNat else 0 := rfl

theorem annihilationField_nonpos (α : L.carrier) {t : ℤ} (ht : t ≤ 0) :
    annihilationField F α t = annihilationCoefficient F α (-t).toNat := by
  rw [annihilationField_apply, if_pos ht]

theorem annihilationField_isField (α : L.carrier) : IsField (annihilationField F α) := by
  classical
  intro x
  obtain ⟨cc, rfl⟩ := (HeisenbergN.gradingWN_isInternal (rank L)).2 x
  obtain ⟨W, hW⟩ := Finset.exists_le cc.support
  refine ⟨-(W : ℤ), fun n hn => ?_⟩
  have hn0 : n ≤ 0 := by omega
  rw [annihilationField_nonpos F α hn0, DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun w hw => ?_
  have hwW : (w : ℤ) ≤ (W : ℤ) := by exact_mod_cast hW w hw
  have hmem := annihilationCoefficient_mem_gradingZN F α (-n).toNat (cc w).2
  rw [HeisenbergN.gradingZN_of_neg (by omega : (w : ℤ) - ((-n).toNat : ℤ) < 0),
    Submodule.mem_bot] at hmem
  exact hmem


noncomputable def dressingField (α : L.carrier) : FormalDist (End ℂ (FockN (rank L))) :=
  nprod (creationField_isField F α) (annihilationField_isField F α)

theorem dressingField_isField (α : L.carrier) : IsField (dressingField F α) :=
  IsField.nprod (creationField_isField F α) (annihilationField_isField F α)



theorem creationField_vacuum (α : L.carrier) (t : ℤ) :
    creationField F α t (vacuumN (rank L)) = if 0 ≤ t then creationCoefficient F α t.toNat else 0 := by
  rw [creationField_apply]; split_ifs with h
  · rw [creationOperator_vacuum]
  · rfl

theorem annihilationField_vacuum (α : L.carrier) (t : ℤ) :
    annihilationField F α t (vacuumN (rank L)) = if t = 0 then vacuumN (rank L) else 0 := by
  rw [annihilationField_apply]
  by_cases h : t ≤ 0
  · rw [if_pos h, annihilationCoefficient_vacuum]
    by_cases h0 : t = 0
    · rw [if_pos (by omega : (-t).toNat = 0), if_pos h0]
    · rw [if_neg (by omega : ¬ (-t).toNat = 0), if_neg h0]
  · rw [if_neg h, if_neg (by omega : ¬ t = 0), LinearMap.zero_apply]


theorem dressingField_vacuum (α : L.carrier) (t : ℤ) :
    dressingField F α t (vacuumN (rank L)) = if 0 ≤ t then creationCoefficient F α t.toNat else 0 := by
  classical
  have hsupp : ∀ m : ℤ, m ≠ t →
      normalOrdered (creationField F α) (annihilationField F α) m (t - m) (vacuumN (rank L)) = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, Module.End.mul_apply, annihilationField_vacuum F α, if_neg (by omega)]
      exact map_zero _
    · rw [if_neg h0, Module.End.mul_apply, creationField_neg F α (by omega : m < 0)]
      simp
  rw [dressingField, nprod_apply, finsum_eq_single _ t hsupp, normalOrdered_apply]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, if_pos ht, Module.End.mul_apply, show t - t = (0 : ℤ) from by ring,
      annihilationField_vacuum F α, if_pos rfl, creationField_vacuum, if_pos ht]
  · rw [if_neg ht, if_neg ht, Module.End.mul_apply, creationField_vacuum, if_neg ht]
    exact map_zero _




noncomputable def chargedFieldSectorMap (α : L.carrier) (t : ℤ) (β : L.carrier) :
    ℂ →ₗ[ℂ] (FockN (rank L) →ₗ[ℂ] LatModuleGen L) :=
  LinearMap.toSpanSingleton ℂ (FockN (rank L) →ₗ[ℂ] LatModuleGen L)
    (ε α β •
      (((TensorProduct.mk ℂ (FockN (rank L)) (L.carrier →₀ ℂ)).flip (eGen L (α + β))).comp
        (dressingField F α (t - L.form α β))))


noncomputable def chargedField (α : L.carrier) (t : ℤ) : LatModuleGen L →ₗ[ℂ] LatModuleGen L :=
  TensorProduct.lift (Finsupp.lsum ℂ (chargedFieldSectorMap F ε α t)).flip


theorem chargedField_tmul (α β : L.carrier) (t : ℤ) (p : FockN (rank L)) :
    chargedField F ε α t (latStateGen L p β)
      = ε α β • latStateGen L (dressingField F α (t - L.form α β) p) (α + β) := by
  rw [latStateGen, chargedField, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (chargedFieldSectorMap F ε α t)) (eGen L β) p = _
  rw [eGen, Finsupp.lsum_single, chargedFieldSectorMap, LinearMap.toSpanSingleton_apply, one_smul,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    latStateGen, eGen]


theorem chargedField_vacuum (hε : ∀ α, ε α 0 = 1) (α : L.carrier) (t : ℤ) :
    chargedField F ε α t (latVacuumGen L)
      = if 0 ≤ t then latStateGen L (creationCoefficient F α t.toNat) α else 0 := by
  rw [latVacuumGen, chargedField_tmul, hε, one_smul,
    show L.form α 0 = 0 from by simp, sub_zero, add_zero]
  rw [latStateGen, dressingField_vacuum]
  split_ifs with ht
  · rfl
  · rw [TensorProduct.zero_tmul]


theorem chargedField_creation_z0 (hε : ∀ α, ε α 0 = 1) (α : L.carrier) : chargedField F ε α 0 (latVacuumGen L) = latChargeGen L α := by
  rw [chargedField_vacuum F ε hε, if_pos le_rfl, Int.toNat_zero, creationCoefficient_zero]
  rfl


theorem chargedField_creation_nonneg (hε : ∀ α, ε α 0 = 1) (α : L.carrier) {n : ℤ} (hn : 0 ≤ n) :
    mode (chargedField F ε α) n (latVacuumGen L) = 0 := by
  rw [mode_apply, chargedField_vacuum F ε hε, if_neg (by omega)]

theorem chargedField_mode_neg_one_vacuum (hε : ∀ α, ε α 0 = 1) (α : L.carrier) :
    mode (chargedField F ε α) (-1) (latVacuumGen L) = latChargeGen L α := by
  rw [mode_apply, show -(-1 : ℤ) - 1 = 0 from by ring, chargedField_creation_z0 F ε hε]

theorem chargedField_isField (α : L.carrier) : IsField (chargedField F ε α) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => (chargedField F ε α n).map_zero⟩
  | add x y hx hy =>
      obtain ⟨Bx, hBx⟩ := hx
      obtain ⟨By, hBy⟩ := hy
      refine ⟨min Bx By, fun n hn => ?_⟩
      rw [map_add (chargedField F ε α n) x y, hBx n (lt_of_lt_of_le hn (min_le_left _ _)),
        hBy n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => exact ⟨0, fun n _ => by erw [TensorProduct.tmul_zero]; exact (chargedField F ε α n).map_zero⟩
      | add g1 g2 h1 h2 =>
          obtain ⟨B1, hB1⟩ := h1
          obtain ⟨B2, hB2⟩ := h2
          refine ⟨min B1 B2, fun n hn => ?_⟩
          erw [TensorProduct.tmul_add]
          simp only [map_add]
          rw [hB1 n (lt_of_lt_of_le hn (min_le_left _ _)),
            hB2 n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]
      | single β a =>
          obtain ⟨Bp, hBp⟩ := dressingField_isField F α p
          refine ⟨Bp + L.form α β, fun n hn => ?_⟩
          rw [(Finsupp.smul_single_one β a).symm,
            show (Finsupp.single β (1 : ℂ) : L.carrier →₀ ℂ) = eGen L β from rfl]
          erw [TensorProduct.tmul_smul, map_smul,
            show p ⊗ₜ[ℂ] eGen L β = latStateGen L p β from rfl, chargedField_tmul,
            hBp (n - L.form α β) (by omega), latStateGen, TensorProduct.zero_tmul,
            smul_zero]


/-- Finite support of the coefficient convolution on each Fock vector. -/
theorem dressingField_coefficient_finite (α : L.carrier) (t : ℤ)
    (p : FockN (rank L)) :
    (Function.support (fun m =>
      normalOrdered (creationField F α) (annihilationField F α) m (t - m) p)).Finite :=
  normalOrdered_diag_support_finite (creationField_isField F α)
    (annihilationField_isField F α) t p

/-- The leading product of two charged ground states, with its actual cocycle. -/
theorem chargedField_charge_leading (α β : L.carrier) :
    mode (chargedField F ε α) (-L.form α β - 1) (latChargeGen L β) =
      ε α β • latChargeGen L (α + β) := by
  rw [mode_apply, latChargeGen, chargedField_tmul,
    show -(-L.form α β - 1) - 1 - L.form α β = 0 by ring,
    dressingField_vacuum, if_pos le_rfl, Int.toNat_zero, creationCoefficient_zero]
  rfl

theorem chargedField_charge_higher_modes (α β : L.carrier) (n : ℤ)
    (hn : -L.form α β - 1 < n) :
    mode (chargedField F ε α) n (latChargeGen L β) = 0 := by
  rw [mode_apply, latChargeGen, chargedField_tmul, dressingField_vacuum,
    if_neg (by omega), latStateGen, TensorProduct.zero_tmul, smul_zero]

theorem chargedField_regularity (α : L.carrier) (v : LatModuleGen L) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (chargedField F ε α) n v = 0 := by
  obtain ⟨B, hB⟩ := chargedField_isField F ε α v
  exact ⟨-B, fun n hn => hB (-n - 1) (by omega)⟩

/-- Charged fields using the fixed isotropic-coordinate cocycle. -/
noncomputable def lorentzianChargedField (α : lorentzianLattice.carrier) :
    FormalDist (End ℂ LorentzianFockSpace) :=
  chargedField lorentzianComplexFrame standardLorentzianCocycle α

/-- The same construction with the chosen-basis cocycle required by the old target. -/
noncomputable def lorentzianTargetChargedField (α : lorentzianLattice.carrier) :
    FormalDist (End ℂ LorentzianFockSpace) :=
  chargedField lorentzianComplexFrame (latticeCocycle lorentzianLattice) α

theorem lorentzianChargedField_isField (α : lorentzianLattice.carrier) :
    IsField (lorentzianChargedField α) :=
  chargedField_isField _ _ α

theorem lorentzianChargedField_creation (α : lorentzianLattice.carrier) :
    mode (lorentzianChargedField α) (-1) lorentzianVacuum = lorentzianChargeState α ∧
      ∀ n : ℤ, 0 ≤ n → mode (lorentzianChargedField α) n lorentzianVacuum = 0 :=
  ⟨chargedField_mode_neg_one_vacuum _ _
      (fun x => (standardLorentzianCocycle_normalized x).2) α,
    fun _ hn => chargedField_creation_nonneg _ _
      (fun x => (standardLorentzianCocycle_normalized x).2) α hn⟩

theorem lorentzianChargedField_charge_leading (α β : lorentzianLattice.carrier) :
    mode (lorentzianChargedField α) (-lorentzianLattice.form α β - 1)
      (lorentzianChargeState β) =
        (-1 : ℂ) ^ (α 1 * β 0) • lorentzianChargeState (α + β) :=
  chargedField_charge_leading _ _ α β

theorem lorentzianTargetChargedField_charge_leading (α β : lorentzianLattice.carrier) :
    mode (lorentzianTargetChargedField α) (-lorentzianLattice.form α β - 1)
      (lorentzianChargeState β) =
        latticeCocycle lorentzianLattice α β • lorentzianChargeState (α + β) :=
  chargedField_charge_leading _ _ α β

end VOA.Moonshine.ConwayNorton
