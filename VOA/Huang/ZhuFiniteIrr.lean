/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.AModBridge
import VOA.Modularity.StronglyRationalFamily
import VOA.Modularity.ZhuAlgebraFinite

/-!
# Finitely many irreducible modules when `A(V)` is finite-dimensional and semisimple

This replaces the literature
input "Dong–Li–Mason finiteness" in the `IModData` bridge for `C₂`-cofinite `V`:

* `A(V)` finite-dimensional (free from `C₂`: `finiteDimensional_A_of_C2Cofinite`) and semisimple
  decomposes as a *finite* independent family of simple left ideals (`s.Finite` from
  Noetherianity);
* every simple `A(V)`-module `U` is a quotient of `A(V)` (`a ↦ a·u`), so it is isomorphic to one of
  those left ideals (Schur, `LinearMap.bijective_of_ne_zero`);
* the bottom of an irreducible module is simple (`isSimpleAMod_of_irreducible_of_semisimple`), and
  Zhu's correspondence is injective (`zhuBijective`), so `Φ V` injects into the finite family.

## Main results

* `finite_Φ_of_semisimple` : `Pr`, `dim A(V) < ∞`, `A(V)` semisimple ⟹ `Finite (Φ V)`.
* `finite_Φ_of_C2Cofinite` : the `C₂`-cofinite form.

`#print axioms`: Lean's three. `Pr` (the PBW bottom datum) is an explicit hypothesis.
-/

namespace VOA.Huang.ZhuFiniteIrr

open VOA VOA.VHat VOA.VHat.DLM3

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- An `A(V)`-linear equivalence of bundled `AMod`s is an `AModEquiv`. -/
noncomputable def amodEquivOfLinearEquiv {U U' : AMod W}
    (e : letI := instRingA W; letI := U.moduleA; letI := U'.moduleA;
      U.carrier ≃ₗ[A W] U'.carrier) : AModEquiv W U U' :=
  letI := instRingA W
  letI := U.moduleA
  letI := U'.moduleA
  { toLinearEquiv :=
      { toFun := e
        invFun := e.symm
        map_add' := e.map_add
        map_smul' := fun c x => by
          have h := e.map_smul (c • (1 : A W)) x
          rw [AMod.smul_comm_C U c (1 : A W) x, one_smul, AMod.smul_comm_C U' c (1 : A W),
            one_smul] at h
          exact h
        left_inv := e.left_inv
        right_inv := e.right_inv }
    map_ρ := fun a x => e.map_smul a x }

/-- Every simple `AMod` is `A(V)`-isomorphic to one member of a family of simple left ideals whose
supremum is `A(V)`. -/
theorem exists_mem_linearEquiv
    (s : letI := instRingA W; Set (Submodule (A W) (A W)))
    (htop : letI := instRingA W; sSup s = ⊤)
    (hsimp : letI := instRingA W; ∀ m ∈ s, IsSimpleModule (A W) m)
    (U : AMod W) (hU : IsSimpleAMod U) :
    letI := instRingA W
    letI := U.moduleA
    ∃ I ∈ s, Nonempty (I ≃ₗ[A W] U.carrier) := by
  letI := instRingA W
  letI := U.moduleA
  haveI hUm : IsSimpleModule (A W) U.carrier := (isSimpleAMod_iff_isSimpleModule U).1 hU
  haveI : Nontrivial U.carrier := hU.1
  obtain ⟨u, hu⟩ := exists_ne (0 : U.carrier)
  let f : A W →ₗ[A W] U.carrier := LinearMap.toSpanSingleton (A W) U.carrier u
  have hex : ∃ I ∈ s, f.comp I.subtype ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : sSup s ≤ LinearMap.ker f := by
      refine sSup_le fun I hI => ?_
      intro a ha
      have := congrArg (fun g => g ⟨a, ha⟩) (hcon I hI)
      simpa [f] using this
    rw [htop] at hle
    have h1 : (1 : A W) ∈ LinearMap.ker f := hle Submodule.mem_top
    rw [LinearMap.mem_ker] at h1
    apply hu
    simpa [f] using h1
  obtain ⟨I, hI, hne⟩ := hex
  haveI := hsimp I hI
  exact ⟨I, hI, ⟨LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hne)⟩⟩

/-- `canonicalIrrFamily_bottomSeparated` with the PBW datum as a hypothesis instead of `VOA.pbw`:
distinct classes have non-isomorphic bottoms. -/
theorem canonicalIrrFamily_bottomSeparated_of_Pr
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) {j k : Φ W} (hjk : j ≠ k) :
    IsEmpty (AModEquiv W
      (lowestAMod (canonicalIrrFamily_hasConformalWeight (W := W) j).2)
      (lowestAMod (canonicalIrrFamily_hasConformalWeight (W := W) k).2)) := by
  constructor
  intro e
  let Pj : IrrLWModule W :=
    ⟨canonicalIrrLWModule (W := W) j, canonicalIrrLWModule_irreducible j⟩
  let Pk : IrrLWModule W :=
    ⟨canonicalIrrLWModule (W := W) k, canonicalIrrLWModule_irreducible k⟩
  have hforward : forwardMapIrr W
      (Quotient.mk (IrrLWModule.setoid W) Pj) =
      forwardMapIrr W (Quotient.mk (IrrLWModule.setoid W) Pk) := by
    rw [forwardMapIrr_mk, forwardMapIrr_mk]
    exact Quotient.sound ⟨e⟩
  have hclasses := (zhuBijective Pr).1 hforward
  have hforget := congrArg (forgetClass W) hclasses
  apply hjk
  change (canonicalIrrModule j).toΦ = (canonicalIrrModule k).toΦ at hforget
  simpa using hforget

/-- **Finitely many irreducible modules** when `A(V)` is finite-dimensional and semisimple
(given the PBW datum `Pr`). -/
theorem finite_Φ_of_semisimple
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    (hss : letI := instRingA W; IsSemisimpleRing (A W)) : Finite (Φ W) := by
  classical
  letI := instRingA W
  letI := instAlgebraA W
  haveI : IsSemisimpleRing (A W) := hss
  obtain ⟨s, hind, htop, hsimp⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (A W) (A W)
  haveI : IsNoetherian ℂ (A W) := IsNoetherian.iff_fg.mpr hfd
  haveI : IsNoetherian (A W) (A W) := isNoetherian_of_tower ℂ inferInstance
  have hsfin : s.Finite := WellFoundedGT.finite_of_sSupIndep hind
  haveI := hsfin.to_subtype
  have hUs : ∀ c : Φ W, IsSimpleAMod
      (lowestAMod (canonicalIrrFamily_hasConformalWeight (W := W) c).2) := fun c =>
    isSimpleAMod_of_irreducible_of_semisimple Pr hss (canonicalIrrLWModule c)
      (canonicalIrrLWModule_irreducible c)
  have hex := fun c => exists_mem_linearEquiv s htop hsimp _ (hUs c)
  choose I hIs hIe using hex
  refine Finite.of_injective (fun c => (⟨I c, hIs c⟩ : s)) ?_
  intro j k hjk
  have hI : I j = I k := congrArg Subtype.val hjk
  by_contra hne
  obtain ⟨ej⟩ := hIe j
  obtain ⟨ek⟩ := hIe k
  exact (canonicalIrrFamily_bottomSeparated_of_Pr Pr hne).false
    (amodEquivOfLinearEquiv (ej.symm.trans ((LinearEquiv.ofEq _ _ hI).trans ek)))

/-- The `C₂`-cofinite form: `dim A(V) < ∞` is free. -/
theorem finite_Φ_of_C2Cofinite
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hC2 : C2Cofinite W) (hss : letI := instRingA W; IsSemisimpleRing (A W)) :
    Finite (Φ W) :=
  finite_Φ_of_semisimple Pr (finiteDimensional_A_of_C2Cofinite W hC2) hss

end VOA.Huang.ZhuFiniteIrr
