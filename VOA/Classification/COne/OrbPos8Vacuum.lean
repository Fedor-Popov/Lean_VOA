import VOA.Classification.COne.OrbPos8Charges
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! # Nonzero Heisenberg vacuum eigenvectors in arbitrary twisted modules

Finite-dimensional conformal weight spaces, together with the actual vacuum
energy identity, provide a charge eigenvector. No lattice charge quantization
or exhaustion of the shifted modules is assumed or asserted.
-/

namespace VOA.Classification.COne.OrbPos8
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet HeisenbergN
open OrbPos2 DMCOne LatMod

variable {M : Type} [AddCommGroup M] [Module ℂ M] {u : ℂˣ} {n : ℕ}

/-- The actual current zero mode preserves the conformal weight spaces. -/
theorem torus_zero_mem_weight (P : TwistedModule (charU 1 le_rfl u) n M) (hn : 0 < n)
    {α : ℂ} {x : M} (hx : x ∈ P.weight α) : P.YM (hb 1) 0 x ∈ P.weight α := by
  let H : (orbifold (Subgroup.zpowers (charU 1 le_rfl u))).carrier :=
    ⟨hb 1, (mem_orbifold_zpowers_iff _ _).mpr (charU_hb u)⟩
  have hh : H ∈ (orbifoldVOA (Subgroup.zpowers (charU 1 le_rfl u))).grading 1 :=
    hb_mem_grading 1 le_rfl
  have hm := mode_mem_weight (cyclicRestriction P hn) hh hx 0
  simpa only [cyclicRestriction, restrictedOrdModule, restrictedWeakModule,
    mode_restrictedFields, mul_zero, Int.cast_one, Int.cast_zero, sub_zero,
    add_sub_cancel_right] using hm

/-- The Heisenberg vacuum space is stable under the actual conformal mode. -/
theorem torus_L0_mem_vac (P : TwistedModule (charU 1 le_rfl u) n M) (hn : 0 < n)
    {x : M} (hx : x ∈ (torusHeisenberg P hn).vac) :
    P.YM (V2m 1 le_rfl).conformalVector n x ∈ (torusHeisenberg P hn).vac := by
  rw [torus_L0_on_vac P hn hx]
  apply Submodule.smul_mem
  have ha : (torusHeisenberg P hn).a 0 = P.YM (hb 1) 0 := by simp
  rw [← ha]
  exact (torusHeisenberg P hn).a_zero_mem_vac
    ((torusHeisenberg P hn).a_zero_mem_vac hx)

/-- Every nonzero torus-twisted module has a nonzero homogeneous Heisenberg
vacuum vector. Irreducibility is not needed. -/
theorem torus_vac_weight_ne_bot (P : TwistedModule (charU 1 le_rfl u) n M)
    (hn : 0 < n) [Nontrivial M] :
    ∃ α : ℂ, (torusHeisenberg P hn).vac ⊓ P.weight α ≠ ⊥ := by
  classical
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (twisted_vac_ne_bot P hn (V2m_isHeisVector 1 le_rfl) (charU_hb u))
  letI : DirectSum.Decomposition P.weight := P.isInternal.chooseDecomposition
  let f := DirectSum.decompose P.weight x
  have hsum : (∑ α ∈ f.support, (f α : M)) = x :=
    DirectSum.sum_support_decompose P.weight x
  have hmem : ∀ α ∈ f.support, (f α : M) ∈ (torusHeisenberg P hn).vac := by
    apply mem_of_sum_eigen (P.YM (V2m 1 le_rfl).conformalVector n)
      (torusHeisenberg P hn).vac (fun _ hy => torus_L0_mem_vac P hn hy)
      f.support (fun α => (f α : M))
      (fun α _ => P.L0_weight α _ (f α).property)
    rwa [hsum]
  by_contra h
  push Not at h
  apply hx0
  rw [← hsum]
  apply Finset.sum_eq_zero
  intro α hα
  have hz : (f α : M) ∈ (torusHeisenberg P hn).vac ⊓ P.weight α :=
    ⟨hmem α hα, (f α).property⟩
  rwa [h α, Submodule.mem_bot] at hz

/-- Every nonzero ordinary torus-twisted V₂-module has a nonzero Heisenberg
vacuum eigenvector. Its actual conformal energy is half the charge square. -/
theorem torus_vac_eigen_exists (P : TwistedModule (charU 1 le_rfl u) n M)
    (hn : 0 < n) [Nontrivial M] :
    ∃ (μ : ℂ) (x : M), x ≠ 0 ∧ x ∈ (torusHeisenberg P hn).vac ∧
      P.YM (hb 1) 0 x = μ • x ∧
      P.YM (V2m 1 le_rfl).conformalVector n x = (μ ^ 2 / 2) • x := by
  obtain ⟨α, hα⟩ := torus_vac_weight_ne_bot P hn
  let S := (torusHeisenberg P hn).vac ⊓ P.weight α
  haveI : FiniteDimensional ℂ (P.weight α) := P.finrank α
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  haveI : Nontrivial S := ⟨⟨⟨y, hy⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  have hpres : ∀ y ∈ S, P.YM (hb 1) 0 y ∈ S := by
    intro y hy
    refine ⟨?_, torus_zero_mem_weight P hn hy.2⟩
    simpa using (torusHeisenberg P hn).a_zero_mem_vac hy.1
  let T : Module.End ℂ S := (P.YM (hb 1) 0).restrict hpres
  obtain ⟨μ, hμ⟩ := T.exists_eigenvalue
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have he : P.YM (hb 1) 0 x.val = μ • x.val := congrArg Subtype.val hx.apply_eq_smul
  exact ⟨μ, x.val, fun hz => hx.2 (Subtype.ext hz), x.property.1, he,
    torus_vac_energy P hn x.property.1 he⟩

end VOA.Classification.COne.OrbPos8
