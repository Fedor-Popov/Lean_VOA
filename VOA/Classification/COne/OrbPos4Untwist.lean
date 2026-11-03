import VOA.Classification.COne.OrbPos4Charges
import VOA.Huang.LiRegularLeft

/-!
# Constructing an ordinary untwist from a lattice energy realization

An energy-compatible linear equivalence suffices for the precise untwist
target. We construct the ordinary module, its grading, and its irreducibility.
The universal existence of such equivalences is OPEN. This is a lossless
reformulation, not a proof of twisted-sector classification or a full Li twist.
-/

namespace VOA.Classification.COne.OrbPos4
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 LatMod

section Transport
variable {V M F : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup F] [Module ℂ F]
  {W : VertexOperatorAlgebra V}

/-- Ordinary transport includes finite-dimensional grading and a lower bound. -/
noncomputable def transportOrdinary (A : OrdVModule W F) (e : M ≃ₗ[ℂ] F) :
    OrdVModule W M where
  toWeakModule := Huang.LiRegular.WeakModule.transport A.toWeakModule e
  weight α := (A.weight α).map e.symm.toLinearMap
  isInternal := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact LinearMap.iSupIndep_map _ e.symm.injective A.isInternal.submodule_iSupIndep
    · rw [← Submodule.map_iSup, A.isInternal.submodule_iSup_eq_top,
        Submodule.map_top, LinearMap.range_eq_top.mpr e.symm.surjective]
  L0_weight α x hx := by
    obtain ⟨y, hy, rfl⟩ := hx
    change e.symm (mode (A.YM W.conformalVector) 1 (e (e.symm y))) = _
    rw [e.apply_symm_apply, A.L0_weight α y hy, map_smul]
    rfl
  finrank α := by
    haveI := A.finrank α
    infer_instance
  boundedBelow := by
    obtain ⟨B, hB⟩ := A.boundedBelow
    refine ⟨B, fun α hα => hB α ?_⟩
    intro h
    apply hα
    rw [h, Submodule.map_bot]

theorem transportOrdinary_mode (A : OrdVModule W F) (e : M ≃ₗ[ℂ] F)
    (v : V) (k : ℤ) (x : M) :
    mode ((transportOrdinary A e).YM v) k x = e.symm (mode (A.YM v) k (e x)) := rfl

theorem transportOrdinary_irreducible (A : OrdVModule W F) (e : M ≃ₗ[ℂ] F)
    (hA : A.IsIrreducible) : (transportOrdinary A e).IsIrreducible := by
  letI := hA.1
  refine ⟨e.symm.injective.nontrivial, fun S => ?_⟩
  let T : WeakModule.Submodule' A.toWeakModule :=
    { carrier := S.carrier.map e.toLinearMap
      act_mem := by
        intro v k y hy
        obtain ⟨x, hx, rfl⟩ := hy
        refine ⟨(transportOrdinary A e).toWeakModule.act v k x, S.act_mem v k hx, ?_⟩
        change e (e.symm (mode (A.YM v) k (e x))) = _
        exact e.apply_symm_apply _ }
  have hc : S.carrier = T.carrier.comap e.toLinearMap :=
    (Submodule.comap_map_eq_of_injective e.injective S.carrier).symm
  rcases hA.2 T with h | h
  · left
    rw [hc, h, Submodule.comap_bot, LinearMap.ker_eq_bot.mpr e.injective]
  · right
    rw [hc, h, Submodule.comap_top]

end Transport

section Lattice
variable {M : Type} [AddCommGroup M] [Module ℂ M]

/-- A concrete ordinary module on the given carrier, obtained from one integral
coset label. The equivalence is extra input, not extracted from dimension alone. -/
noncomputable def latticeUntwist (j : ℤ) (e : M ≃ₗ[ℂ] Space) :
    OrdVModule (V2m 1 le_rfl) M := transportOrdinary (latticeModule 1 le_rfl j) e

theorem latticeUntwist_irreducible (j : ℤ) (e : M ≃ₗ[ℂ] Space) :
    (latticeUntwist j e).IsIrreducible :=
  transportOrdinary_irreducible _ e (latticeModule_isIrreducible 1 le_rfl j)

theorem latticeUntwist_energy (n : ℕ) (a j : ℤ) (e : M ≃ₗ[ℂ] Space) (x : M) :
    e (shiftedL0 (mode ((latticeUntwist j e).YM (V2m 1 le_rfl).conformalVector) 1)
      (ordinaryRootZero (latticeUntwist j e)) ((a : ℂ) / (2*n)) x) =
      energyOperator n a j (e x) := by
  apply map_shiftedL0 e.toLinearMap
  · intro y
    exact e.apply_symm_apply _
  · intro y
    rw [ordinaryRootZero, LinearMap.smul_apply, map_smul, charge_eq_root_zeroMode,
      LinearMap.smul_apply]
    congr 1
    exact e.apply_symm_apply _

/-- The explicit shifted-lattice realization required at a fixed angle.
It controls the entire energy operator with multiplicities, not only its spectrum.
No intertwining of other twisted modes is required by this predicate. -/
def LatticeEnergyRealization {g : Aut (V2m 1 le_rfl)} {n : ℕ}
    (P : TwistedModule g n M) (a : ℤ) : Prop :=
  ∃ (j : ℤ) (e : M ≃ₗ[ℂ] Space), ∀ x,
    e (P.YM (V2m 1 le_rfl).conformalVector n x) = energyOperator n a j (e x)

/-- From an energy realization we actually construct the ordinary irreducible
untwist and prove the conformal-mode identity on every vector. -/
theorem ordinaryUntwist_of_latticeEnergyRealization
    {g : Aut (V2m 1 le_rfl)} {n : ℕ} (P : TwistedModule g n M) (a : ℤ)
    (h : LatticeEnergyRealization P a) :
    ∃ A : OrdVModule (V2m 1 le_rfl) M, A.IsIrreducible ∧
      ∀ x, P.YM (V2m 1 le_rfl).conformalVector n x =
        shiftedL0 (mode (A.YM (V2m 1 le_rfl).conformalVector) 1) (ordinaryRootZero A)
          ((a : ℂ) / (2*n)) x := by
  obtain ⟨j, e, hE⟩ := h
  refine ⟨latticeUntwist j e, latticeUntwist_irreducible j e, fun x => ?_⟩
  apply e.injective
  rw [hE, latticeUntwist_energy]

/-- Lossless: ordinary lattice classification proves the converse as well. -/
theorem ordinaryUntwist_iff_latticeEnergyRealization
    {g : Aut (V2m 1 le_rfl)} {n : ℕ} (P : TwistedModule g n M) (a : ℤ) :
    (∃ A : OrdVModule (V2m 1 le_rfl) M, A.IsIrreducible ∧
      ∀ x, P.YM (V2m 1 le_rfl).conformalVector n x =
        shiftedL0 (mode (A.YM (V2m 1 le_rfl).conformalVector) 1) (ordinaryRootZero A)
          ((a : ℂ) / (2*n)) x) ↔ LatticeEnergyRealization P a := by
  refine ⟨?_, ordinaryUntwist_of_latticeEnergyRealization P a⟩
  rintro ⟨A, hA, hL⟩
  obtain ⟨j, ⟨e₀⟩⟩ := exists_latticeModule_equiv_int A hA
  let e := e₀.symm
  refine ⟨j, e.toLinearEquiv, fun x => ?_⟩
  rw [hL]
  apply map_shiftedL0 e.toLinearEquiv.toLinearMap
  · intro y
    exact e.map_act _ 1 y
  · intro y
    rw [ordinaryRootZero, LinearMap.smul_apply, map_smul, charge_eq_root_zeroMode,
      LinearMap.smul_apply]
    exact congrArg (chargeCoord (latP 1) (1 : ℤ) (a0 1) • ·) (e.map_act _ 0 y)

end Lattice

/-- OPEN: classification of the energies of arbitrary irreducible torus-twisted
modules by explicit shifted lattice carriers. Equivalent to the old target. -/
def V2TorusLatticeEnergyRealization : Prop :=
  ∀ (u : ℂˣ) (n : ℕ), 0 < n → orderOf (charU 1 le_rfl u) = n →
    charU 1 le_rfl u ≠ 1 →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M]
      (P : TwistedModule (charU 1 le_rfl u) n M), TwistedIrreducible P →
      ∃ a : ℤ, 0 < a ∧ a < n ∧ LatticeEnergyRealization P a

theorem v2TorusOrdinaryUntwist_iff_latticeEnergyRealization :
    V2TorusOrdinaryUntwist ↔ V2TorusLatticeEnergyRealization := by
  constructor
  · intro h u n hn ho hu M _ _ P hi
    obtain ⟨a, ha, han, hA⟩ := h u n hn ho hu M P hi
    exact ⟨a, ha, han, (ordinaryUntwist_iff_latticeEnergyRealization P a).mp hA⟩
  · intro h u n hn ho hu M _ _ P hi
    obtain ⟨a, ha, han, hE⟩ := h u n hn ho hu M P hi
    exact ⟨a, ha, han, ordinaryUntwist_of_latticeEnergyRealization P a hE⟩

theorem exceptionalOrbifoldPositiveWeightsFact_of_drx_latticeEnergy
    (hDRX : ExceptionalDRXEmbedding) (hE : V2TorusLatticeEnergyRealization) :
    ExceptionalOrbifoldPositiveWeightsFact :=
  exceptionalOrbifoldPositiveWeightsFact_of_drx_untwist hDRX
    (v2TorusOrdinaryUntwist_iff_latticeEnergyRealization.mpr hE)

end VOA.Classification.COne.OrbPos4
