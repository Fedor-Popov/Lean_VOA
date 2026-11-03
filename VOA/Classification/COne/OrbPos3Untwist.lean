import VOA.Classification.COne.OrbPos3Energy
import VOA.Classification.COne.OrbPos3Conjugate

/-!
# Reduction to an ordinary inverse twist, with the actual conformal-mode identity

`V2TorusOrdinaryUntwist` is an OPEN proposition, not a theorem. It requires an
actual irreducible ordinary V₂-module on the same vector space, and the Li
identity for the actual conformal and root-current modes. The untwisted
classification and the complete shifted-operator spectral calculation then
prove the unchanged `V2InnerTwistedSpectrum` statement at every finite order.

Li q-alg/9504022, Proposition 5.4 and Remark 5.5 supply a mathematical route
through weak modules. Ordinary grading of the inverse twist must additionally
be justified; this file does not silently infer it from weak irreducibility.
-/

namespace VOA.Classification.COne.OrbPos3
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 LatMod

section Maps
variable {M T : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T]

theorem map_shiftedL0 (f : M →ₗ[ℂ] T) (L H : Module.End ℂ M)
    (L' H' : Module.End ℂ T) (t : ℂ)
    (hL : ∀ x, f (L x) = L' (f x)) (hH : ∀ x, f (H x) = H' (f x)) (x : M) :
    f (shiftedL0 L H t x) = shiftedL0 L' H' t (f x) := by
  simp only [shiftedL0, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_add, map_sub, map_smul, hL, hH]

end Maps

/-- Root-normalized Heisenberg zero mode of an actual ordinary V₂-module. -/
noncomputable def ordinaryRootZero {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : OrdVModule (V2m 1 le_rfl) M) : Module.End ℂ M :=
  chargeCoord (latP 1) (1 : ℤ) (a0 1) • mode (A.YM (hVec (latP 1) (a0 1))) 0

/-- An actual ordinary untwist and its conformal identity suffice for all
realized twisted weights. No twisted-field construction is assumed implicitly. -/
theorem twisted_spectrum_of_ordinary_untwist
    {g : Aut (V2m 1 le_rfl)} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (P : TwistedModule g n M) (A : OrdVModule (V2m 1 le_rfl) M)
    (hA : A.IsIrreducible) (a : ℤ)
    (hL : ∀ x, P.YM (V2m 1 le_rfl).conformalVector n x =
      shiftedL0 (mode (A.YM (V2m 1 le_rfl).conformalVector) 1) (ordinaryRootZero A)
        ((a : ℂ) / (2 * n)) x) :
    ∃ ε : ℤ, (ε = 0 ∨ ε = 1) ∧ ∀ α : ℂ, P.weight α ≠ ⊥ →
      ∃ (k : ℤ) (r : ℕ), α = (innerEnergy n a ε k r : ℂ) := by
  obtain ⟨j, ⟨e₀⟩⟩ := exists_latticeModule_equiv_int A hA
  let e := e₀.symm
  have hε : j % 2 = 0 ∨ j % 2 = 1 := by omega
  refine ⟨j % 2, hε, ?_⟩
  intro α hα
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  have hmap (x : M) :
      e.toLinearEquiv (P.YM (V2m 1 le_rfl).conformalVector n x) =
        energyOperator n a j (e.toLinearEquiv x) := by
    rw [hL]
    apply map_shiftedL0 e.toLinearEquiv.toLinearMap
    · intro y
      exact e.map_act _ 1 y
    · intro y
      rw [ordinaryRootZero, LinearMap.smul_apply, map_smul, charge_eq_root_zeroMode,
        LinearMap.smul_apply]
      exact congrArg (chargeCoord (latP 1) (1 : ℤ) (a0 1) • ·) (e.map_act _ 0 y)
  have he : e.toLinearEquiv x ∈ Module.End.eigenspace (energyOperator n a j) α := by
    rw [Module.End.mem_eigenspace_iff, ← hmap, P.L0_weight α x hx, map_smul]
  have hne : Module.End.eigenspace (energyOperator n a j) α ≠ ⊥ := by
    intro hz
    rw [hz, Submodule.mem_bot] at he
    exact hx0 (e.toLinearEquiv.injective (he.trans (map_zero _).symm))
  obtain ⟨k, r, hr⟩ := energyOperator_spectrum n a j hne
  exact ⟨k + j / 2, r, hr.trans (congrArg (fun q : ℚ => (q : ℂ))
    (innerEnergy_normalize n a j k r))⟩

/-- OPEN: inverse Li twisting in torus sectors, retaining ordinary grading.
Only its conformal identity is needed below; existence of the module and its
irreducibility are genuine extra obligations, not scalar spectral assumptions. -/
def V2TorusOrdinaryUntwist : Prop :=
  ∀ (u : ℂˣ) (n : ℕ), 0 < n → orderOf (charU 1 le_rfl u) = n →
    charU 1 le_rfl u ≠ 1 →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M]
      (P : TwistedModule (charU 1 le_rfl u) n M), TwistedIrreducible P →
      ∃ a : ℤ, 0 < a ∧ a < n ∧
        ∃ A : OrdVModule (V2m 1 le_rfl) M, A.IsIrreducible ∧
          ∀ x, P.YM (V2m 1 le_rfl).conformalVector n x =
            shiftedL0 (mode (A.YM (V2m 1 le_rfl).conformalVector) 1) (ordinaryRootZero A)
              ((a : ℂ) / (2 * n)) x

/-- The unchanged all-orders spectral target follows from the explicit ordinary untwist. -/
theorem v2InnerTwistedSpectrum_of_torusOrdinaryUntwist
    (h : V2TorusOrdinaryUntwist) : V2InnerTwistedSpectrum := by
  intro g n hn ho hg M _ _ P hi
  obtain ⟨u, Q, horder, hQ, hw⟩ := v2_twisted_torus_reduction hn ho P hi
  have hu : charU 1 le_rfl u ≠ 1 := by
    intro he
    have hn1 : n = 1 := by simpa only [he, orderOf_one] using horder.symm
    exact hg (orderOf_eq_one_iff.mp (ho.trans hn1))
  obtain ⟨a, ha, han, A, hA, hL⟩ := h u n hn horder hu M Q hQ
  obtain ⟨ε, hε, hs⟩ := twisted_spectrum_of_ordinary_untwist Q A hA a hL
  refine ⟨a, ε, ha, han, hε, ?_⟩
  intro α hα
  exact hs α (by rwa [hw])

/-- Conditional B5 endpoint; neither DRX nor the ordinary untwist is asserted. -/
theorem exceptionalOrbifoldPositiveWeightsFact_of_drx_untwist
    (hDRX : ExceptionalDRXEmbedding) (hLi : V2TorusOrdinaryUntwist) :
    ExceptionalOrbifoldPositiveWeightsFact :=
  exceptionalOrbifoldPositiveWeightsFact_of_drx_li hDRX
    (v2InnerTwistedSpectrum_of_torusOrdinaryUntwist hLi)

end VOA.Classification.COne.OrbPos3
