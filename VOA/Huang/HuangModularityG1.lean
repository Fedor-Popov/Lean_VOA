/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangModularitySymm

/-!
# (G1) with the vacuum eigenvalue made explicit

`GenusOneG1d.vacuumChannelTransport_of_inputs` proves `S · B = diag(Ω) · S` with an EXISTENTIAL
`Ω`; inside its proof `Ω_x = e^{2πi h_b} Ω^A_x / μ`, where `Ω^A` is the A-cycle scalar
(`IsACycleScalar`, with `Ω^A_{v0} = e^{−2πi h_{v0}}`, `aCycleScalar_vacuum`) and `μ` is the
constant of the conjugation identity, which in turn is the constant of the trace skew-symmetry,
i.e. of `Y^π = μ Ω₀(Y^ε)` (`piInt_eq_smul_skew`). The existential packaging of
`ConjugationInput`/`TraceSkew` loses `μ`; this file re-runs the two proofs with `μ` explicit:

* `conjugation_explicit` — the conjugation identity with the GIVEN skew constant `μ`
  (verbatim proof of `GenusOneG1e.conjugationInput_of_skew`, explicit witness);
* `vacuumRow_explicit` — for the vacuum row:
  `μ Σ_y S_{v0 y} B_{yz} = e^{2πi h_b} e^{−2πi h_{v0}} S_{v0 z}`, for any vacuum retraction `π`
  (`η ≫ π = 𝟙`) and the `μ` with `Y^π = μ Ω₀(Y^ε)`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HuangModularity

open VOA VOA.Huang Complex VOA.Huang.GenusOneG1d VOA.Huang.GenusOneG1e VOA.Huang.VerlindeFusion
  VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.TensorCat
  VOA.Huang.VerlindeTransport VOA.Huang.GenusOneG1c CategoryTheory
open VOA.Huang.GenusOne (sqL traceFunction)
open VOA.Huang.GenusOne.IntCoord (bracketModes NormalizedIntertwinerSubstitution
  transportedModes_weight vacuum_traceFunction_eq)
open VOA.Huang.GenusTwoPoint (vacuumLW)
open scoped BigOperators MatrixGroups

universe u w

section Explicit

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **The conjugation identity with the given skew constant `μ`** (the proof of
`GenusOneG1e.conjugationInput_of_skew`, with the witness kept explicit). -/
theorem conjugation_explicit (F : FusionChoice W) (hV : StronglyRational W)
    (D : VOA.ModularData W ι) (hZ : ZhuModularityAnalytic D) {a b : ι} (hv : W.vacuum ≠ 0)
    (c : TransferChoice F D a b) (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject)
    {σ : ι → ι} (hP : ∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0) (μ : ℂ)
    (hsk : ∀ (n : ℂ) (wa : (lwOf D a).carrier) (wb : (lwOf D b).carrier) (x : ι)
      (τ : UpperHalfPlane),
      traceFun D.Mfam D.h x
          (bracketModes (P := lwOf D b) (Q := lwOf D a) (N := vacuumLW W hv) (piInt F π) n wb wa)
          τ =
        μ * exp ((Real.pi : ℂ) * I * (-n - 1)) * traceFun D.Mfam D.h x
          (bracketModes (P := lwOf D a) (Q := lwOf D b) (N := vacuumLW W hv) (epsInt F c) n wa wb)
          τ)
    (hsub : NormalizedIntertwinerSubstitution (P := lwOf D a) (Q := lwOf D b)
      (N := vacuumLW W hv) (epsInt F c)) (ins : Insertion D a b) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re → ∀ z,
      revF F hv π ins z τ u = μ * exp (-((Real.pi : ℂ) * I * ins.κ)) * vacF F hv c ins (σ z) τ u := by
  have iQ : (vacuumLW W hv).IsIrreducibleLW :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hV.simple
  obtain ⟨N0, hal0, hal1⟩ := ins_align D ins
  by_cases hnd : (∑ i, ins.wa i) ≠ 0 ∧ (∑ j, ins.wb j) ≠ 0
  · have hal := hal1 hnd.1 hnd.2
    have halr : ∀ j i, ins.wb j ≠ 0 → ins.wa i ≠ 0 →
        ∃ Dn : ℕ, ins.κ - ins.αb j - ins.αa i + N0 = Dn := by
      intro j i hj hi
      obtain ⟨Dn, h⟩ := hal i j hi hj
      exact ⟨Dn, by rw [← h]; ring⟩
    have hvac := fun x : ι => sum_laurent hV (lwOf_irreducible D a) (lwOf_irreducible D b)
      (lwOf_irreducible D x) iQ (moduleIntertwiner (lwOf D x).isMod) (epsInt F c)
      ins.wa ins.αa ins.hwa ins.wb ins.αb ins.hwb ins.κ N0 hal τ
    have hrev := fun x : ι => sum_laurent hV (lwOf_irreducible D b) (lwOf_irreducible D a)
      (lwOf_irreducible D x) iQ (moduleIntertwiner (lwOf D x).isMod) (piInt F π)
      ins.wb ins.αb ins.hwb ins.wa ins.αa ins.hwa ins.κ N0 halr τ
    choose δ1 hδ1 h1 using hvac
    choose δ2 hδ2 h2 using hrev
    obtain ⟨δa, hδa, hlea⟩ := exists_pos_le_fintype δ1 hδ1
    obtain ⟨δb, hδb, hleb⟩ := exists_pos_le_fintype δ2 hδ2
    refine ⟨min δa δb, lt_min hδa hδb, fun u hu hre z => ?_⟩
    have hA := h1 (σ z) u (lt_of_lt_of_le hu ((min_le_left _ _).trans (hlea _))) hre
    have hB := h2 z u (lt_of_lt_of_le hu ((min_le_right _ _).trans (hleb _))) hre
    unfold revF vacF
    rw [Finset.sum_comm, ← hB.tsum_eq, ← hA.tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun s => ?_
    have hw : sqL (adjointModule W) 0 (bracketModes (P := lwOf D a) (Q := lwOf D b)
        (N := vacuumLW W hv) (epsInt F c) (ins.κ - 1 - 0 - ((s : ℂ) - N0))
          (∑ i, ins.wa i) (∑ j, ins.wb j)) = ((s : ℂ) - N0) • bracketModes
          (P := lwOf D a) (Q := lwOf D b) (N := vacuumLW W hv) (epsInt F c)
          (ins.κ - 1 - 0 - ((s : ℂ) - N0)) (∑ i, ins.wa i) (∑ j, ins.wb j) := by
      rw [hsub]
      erw [transportedModes_weight (N := vacuumLW W hv) (epsInt F c) ins.hsqa ins.hsqb]
      congr 1
      unfold Insertion.κ
      ring
    have hps := parity_step D hZ hv hP ins.κ N0 s _ hw z τ
    have hsk' := hsk (ins.κ - 1 - 0 - ((s : ℂ) - N0)) (∑ i, ins.wa i) (∑ j, ins.wb j) z τ
    change exp (((0 : ℂ) - ins.κ - N0) * log u) * u ^ s * traceFunction
        (moduleIntertwiner (lwOf D z).isMod) (lwOf D z).h (bracketModes (P := lwOf D b)
          (Q := lwOf D a) (N := vacuumLW W hv) (piInt F π) (ins.κ - 1 - 0 - ((s : ℂ) - N0))
          (∑ j, ins.wb j) (∑ i, ins.wa i)) τ =
      μ * exp (-((Real.pi : ℂ) * I * ins.κ)) * (exp (((0 : ℂ) - ins.κ - N0) * log u) * u ^ s *
        traceFunction (moduleIntertwiner (lwOf D (σ z)).isMod) (lwOf D (σ z)).h
          (bracketModes (P := lwOf D a) (Q := lwOf D b) (N := vacuumLW W hv) (epsInt F c)
            (ins.κ - 1 - 0 - ((s : ℂ) - N0)) (∑ i, ins.wa i) (∑ j, ins.wb j)) τ)
    rw [vacuum_traceFunction_eq, vacuum_traceFunction_eq, hsk', mul_assoc μ, hps]
    ring
  · have halr : ∀ j i, ins.wb j ≠ 0 → ins.wa i ≠ 0 →
        ∃ Dn : ℕ, (D.h a + D.h b) - ins.αb j - ins.αa i + N0 = Dn := by
      intro j i hj hi
      obtain ⟨Dn, h⟩ := hal0 i j hi hj
      exact ⟨Dn, by rw [← h]; ring⟩
    have hvac := fun x : ι => sum_laurent hV (lwOf_irreducible D a) (lwOf_irreducible D b)
      (lwOf_irreducible D x) iQ (moduleIntertwiner (lwOf D x).isMod) (epsInt F c)
      ins.wa ins.αa ins.hwa ins.wb ins.αb ins.hwb (D.h a + D.h b) N0 hal0 τ
    have hrev := fun x : ι => sum_laurent hV (lwOf_irreducible D b) (lwOf_irreducible D a)
      (lwOf_irreducible D x) iQ (moduleIntertwiner (lwOf D x).isMod) (piInt F π)
      ins.wb ins.αb ins.hwb ins.wa ins.αa ins.hwa (D.h a + D.h b) N0 halr τ
    choose δ1 hδ1 h1 using hvac
    choose δ2 hδ2 h2 using hrev
    obtain ⟨δa, hδa, hlea⟩ := exists_pos_le_fintype δ1 hδ1
    obtain ⟨δb, hδb, hleb⟩ := exists_pos_le_fintype δ2 hδ2
    refine ⟨min δa δb, lt_min hδa hδb, fun u hu hre z => ?_⟩
    have hA := h1 (σ z) u (lt_of_lt_of_le hu ((min_le_left _ _).trans (hlea _))) hre
    have hB := h2 z u (lt_of_lt_of_le hu ((min_le_right _ _).trans (hleb _))) hre
    rw [not_and_or, not_not, not_not] at hnd
    have hz1 : ∀ n : ℂ, bracketModes (P := lwOf D a) (Q := lwOf D b) (N := vacuumLW W hv)
        (epsInt F c) n (∑ i, ins.wa i) (∑ j, ins.wb j) = 0 := by
      intro n
      rcases hnd with h0 | h0
      · rw [h0, map_zero, LinearMap.zero_apply]
      · rw [h0, map_zero]
    have hz2 : ∀ n : ℂ, bracketModes (P := lwOf D b) (Q := lwOf D a) (N := vacuumLW W hv)
        (piInt F π) n (∑ j, ins.wb j) (∑ i, ins.wa i) = 0 := by
      intro n
      rcases hnd with h0 | h0
      · rw [h0, map_zero]
      · rw [h0, map_zero, LinearMap.zero_apply]
    simp only [hz1, hz2, traceFunction_zero, mul_zero] at hA hB
    have hvacF : vacF F hv c ins (σ z) τ u = 0 := hA.unique hasSum_zero
    have hrevF : revF F hv π ins z τ u = 0 := by
      unfold revF
      rw [Finset.sum_comm]
      exact hB.unique hasSum_zero
    rw [hvacF, hrevF, mul_zero]

/-- **(G1) on the vacuum row, with the eigenvalue explicit**:
`μ Σ_y S_{v0 y} B_{yz} = e^{2πi h_b} e^{2πi(h_b − h_{v0} − h_b)} S_{v0 z}`, where `μ` is the
constant of the conjugation identity for the vacuum retraction `π`. -/
theorem vacuumRow_explicit (F : FusionChoice W) (H : OrdinaryFourPointInput F)
    {D : VOA.ModularData W ι} {a b : ι}
    (hNice : Nice W) (hZ : ZhuModularityAnalytic D)
    (hirr : Irredundant D.Mfam) (hcomp : Complete D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)))
    (c : TransferChoice F D a b) {β : ∀ x, Fin (c.r x) → ℂ} (hβ : IsTransferScalar F H c β)
    (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject) (hπ : c.η ≫ π = 𝟙 _) (μ : ℂ)
    (hS : ∀ hv : W.vacuum ≠ 0, VacuumSCovariance F hv c)
    (hconj : ∀ (hv : W.vacuum ≠ 0) (σ : ι → ι),
      (∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0) →
      ∀ (ins : Insertion D a b) (τ : UpperHalfPlane), ∃ δ : ℝ, 0 < δ ∧
        ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re → ∀ z,
          revF F hv π ins z τ u = μ * exp (-((Real.pi : ℂ) * I * ins.κ)) * vacF F hv c ins (σ z) τ u)
    (hstab : ∀ η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b),
      η' ≫ c.ε = 𝟙 _ → ChannelSStability F η' c.η)
    (hind : ∀ (hv : W.vacuum ≠ 0)
      (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)),
      η' ≫ c.ε = 𝟙 _ → ChannelIndependence F hv c η') (z : ι) :
    μ * ∑ y, D.repS v0 y * transferMatrix c β y z =
      exp (2 * (Real.pi : ℂ) * I * D.h b) *
        exp (2 * (Real.pi : ℂ) * I * (D.h b - D.h v0 - D.h b)) * D.repS v0 z := by
  have hV : StronglyRational W := hNice.1
  have hv : W.vacuum ≠ 0 := hV.toStronglyFinite.vacuum_ne_zero
  obtain ⟨σ, T, hσσ, hTS, -, hTσ, hdual, -⟩ :=
    rho_setup VerlindeRho.rhoNegOneInput_pbw hNice D hZ hirr hcomp v0 hv0
  obtain ⟨σ₂, hP₂, hdual₂⟩ := VerlindeVacuum.chargeConjugationInput_of_rhoNegOne
    VerlindeRho.rhoNegOneInput_pbw 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  have hσeq : σ₂ = σ := by
    funext x
    have h1 := hdual x (σ₂ x)
    rw [hdual₂ x (σ₂ x), if_pos rfl] at h1
    by_contra hne
    rw [if_neg hne] at h1
    exact one_ne_zero h1
  have hP : ∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0 := by rw [← hσeq]; exact hP₂
  have hTS' : ∀ w z, ∑ y, T w y * D.repS y z = if w = z then 1 else 0 := by
    intro w z
    have := congrFun (congrFun hTS w) z
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa only [Matrix.of_apply] using this
  obtain ⟨r, lab, i, p, htot⟩ :=
    exists_split hNice.1 D hcomp (tensorObj F (famObj D b) (famObj D a))
  obtain ⟨η', hη'⟩ := exists_vacuumSection F hNice hcomp v0 hv0 c.ε c.ε_ne
  obtain ⟨r', lab', i', p', htot'⟩ :=
    exists_split hNice.1 D hcomp (tensorObj F (famObj D a) (famObj D b))
  obtain ⟨Ω, hΩ⟩ := exists_aCycleScalar F H c η' (D.h b)
  have hΩv := aCycleScalar_vacuum F H hirr v0 hv0 c hη' hΩ
  have hrel : ∀ x, relCoef F c β σ Ω μ x = 0 := fun x =>
    hind hv η' hη' _ (relation_mem_Rspan F H hV hv c hβ hπ lab i p htot hη' hΩ lab' i' p' htot'
      (hS hv) hσσ (hconj hv σ hP) (hstab η' hη') hTS' hTσ x)
  have h := congrFun (hrel v0) (σ z)
  simp only [relCoef, hσσ, Pi.zero_apply] at h
  rw [hΩv] at h
  linear_combination -h

end Explicit

end VOA.Huang.HuangModularity
