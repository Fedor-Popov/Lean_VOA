/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesKoszulInvariants
import VOA.Examples.TwoSeriesLeeYang

/-!
# Sanity check: the invariant-count form of the general theorem at `n = 1`

At `n = 1` (Lee–Yang, `k = -4/3`) both inputs of `twoSeries_gradedUnitary_of_affine_invariants`
are supplied by the existing proofs, with `coeff = gapTwoCoefficient`:

* `leeYang_affineInvariants_rank_le` — (I) for the actual invariant space
  `(gr_r L_{-4/3}(sl₂) ⊗ L_1(sl₂))^{g[t]}_N`: its rank is at most `gapTwoCoefficient N r`. This is
  the proved cyclic-dual / Heisenberg-separation bound (`finrank_le_of_heisenberg`) applied to every
  finite-dimensional subspace, so it also shows the invariant space is finite-dimensional;
* (II) is the proved Lee–Yang PBW character.

`leeYang_gradedUnitary_of_affine_viaInvariants` — Lee–Yang GU recovered from the
invariant-count theorem, conditional only on `hA`. So hypothesis (I) is not vacuous at `n = 1`.
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.LeeYangTransferAssembly VOA.LeeYangShortcut
open VOA.SymbolModel VOA.KoszulResidual VOA.KoszulConcrete VOA.CyclicEval VOA.LevelOneHeis
open VOA.AdamovicSymbol GradedUnitaryCohomology
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 20000

noncomputable section

/-- A space all of whose finite-dimensional subspaces have dimension `≤ g` has rank `≤ g`. -/
theorem rank_le_of_finiteDimensional_subspaces {V : Type*} [AddCommGroup V] [Module ℂ V]
    {g : ℕ} (h : ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → Module.finrank ℂ W ≤ g) :
    Module.rank ℂ V ≤ g := by
  apply rank_le
  intro s hs
  rw [← finrank_span_finset_eq_card hs]
  exact h _ inferInstance

/-- The proved level-one cyclic dual vectors on `gr_r L_{-4/3}(sl₂)`. -/
def levelOneGrCyclicVector (r : ℕ) : GrCyclicVector r :=
  grCyclicVectors (fun r => (grJetStrict_of_leadingSymbol_product
    (jetLeadingSymbols_of_descends fun r => Desc.wordSymbolDescends (r + 2))
    (VOA.JetProduct.jetProductBound_of_lower VOA.JetFermionic.jetFermionicLower)
    r).toGrCyclicVector) r

/-- **(I) at `n = 1`**: the invariant space of `gr_r L_{-4/3}(sl₂) ⊗ L_1(sl₂)` at weight `N`
has rank at most `gapTwoCoefficient N r`. -/
theorem leeYang_affineInvariants_rank_le (N : ℤ) (r : ℕ) :
    Module.rank ℂ (affineInvariants (twoSeriesLevels 1) r N) ≤ gapTwoCoefficient N r := by
  apply rank_le_of_finiteDimensional_subspaces
  intro W _
  exact finrank_le_of_heisenberg ((levelOneGrCyclicVector r).toCyclicDual (grZero_comm r))
    ((levelOneHeisenbergSeparation_of_singular levelOneBottomDetected
      levelOneHeisenbergSingular).toSep r) N
    ((affineInvariants (twoSeriesLevels 1) r N).subtype ∘ₗ W.subtype)
    (Subtype.val_injective.comp Subtype.val_injective)
    (fun v => ((mem_affineInvariants (twoSeriesLevels 1) r N _).mp v.1.2).2)
    (fun v => ((mem_affineInvariants (twoSeriesLevels 1) r N _).mp v.1.2).1)

/-- **Sanity check.** The invariant-count form of the general `(2, 2n+3)` theorem at `n = 1`,
with (I) and (II) supplied by the existing proofs, is the Lee–Yang theorem, conditional only on
`hA`. -/
theorem leeYang_gradedUnitary_of_affine_viaInvariants
    (hA : GradedUnitary LeeYangTransferAssembly.affineForm
      LeeYangTransferAssembly.affineRealStructure LeeYangTransferAssembly.affineFlag) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  twoSeries_gradedUnitary_of_affine_invariants 1 hA gapTwoCoefficient
    leeYang_affineInvariants_rank_le
    (fun N p => by
      rw [← sum_evenCoeff]
      exact (twoSeriesSqueezeInput_one hA).pbwLower N p)

end

end VOA.TwoSeries
