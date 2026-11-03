import VOA.Huang.GenusOneG1eStability
import VOA.Huang.GenusOneIntCoordVacuumTrace

/-!
# (N1) and (N3) from ONE coordinate-change input

Step (5b) of the proof of (G1). The vacuum channel is the iterate channel
with inner module `V` (`vacuumLW`), inner intertwiner `epsInt F c` and outer intertwiner the
module vertex operator `Y_{M_x}`; its one-point functions are Zhu's `traceFun`
(`IntCoord.vacuum_traceFunction_eq`), and `L[0]` of the adjoint module is Zhu's `Lsq W 0`
(`sqL_adjoint_zero`). So the sharp vacuum bracket expansion `VacuumChannelBracketSharp` (which
gives (N1) through the proved `vacuumSCovariance_of_sharp`) is the instance `Q = V` of
`InnerBracketSharp`.

* `sqL_adjoint_zero` — `sqL (adjointModule W) 0 = Lsq W 0` pointwise;
* `vacuumChannelBracketSharp_of_inner`, `vacuumBracketSharpInput_of_channel`;
* `fusionEigenInput_of_channelBracket : ChannelBracketSharpInput → ConjugationInputAll →
  ChannelIndependenceInput → FusionEigenInput` — Huang's Thm 5.2 with (N1) and (N3) both
  discharged from the single coordinate-change input.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1e

open VOA VOA.Huang VOA.Huang.TensorCat VOA.Huang.FusionProduct VOA.Huang.FusionUnit
  VOA.Huang.VerlindeTransport VOA.Huang.VerlindeFusion VOA.Huang.GenusOneG1c
  VOA.Huang.GenusOneG1d CategoryTheory Complex VOA.Classification.COne VOA.Huang.ZhuModData
open VOA.Huang.GenusOne (sqL traceFunction)
open VOA.Huang.GenusTwoPoint (vacuumLW)
open scoped BigOperators

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- `L[0]` of the adjoint module is Zhu's `L[0]`. -/
theorem sqL_adjoint_zero (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) :
    sqL (adjointModule W) 0 x = Lsq W 0 x := by
  rw [Lsq_apply, sqBracketCoeffZ_vacuum_of_ne (0 + 1) (by norm_num), mul_zero, zero_smul,
    sub_zero]
  simp only [sqL, if_neg (show (0 : ℤ) ≠ -2 by norm_num), zero_smul, sub_zero]
  rfl

/-- **The sharp vacuum bracket expansion is the `Q = V` instance of `InnerBracketSharp`.** -/
theorem vacuumChannelBracketSharp_of_inner (F : FusionChoice W) {D : VOA.ModularData W ι}
    {a b : ι} (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
    (hB : InnerBracketSharp D (vacuumLW W hv) (epsInt F c)) :
    VacuumChannelBracketSharp F hv c := by
  intro ins
  obtain ⟨coef, v, β, hsq, hβ, hE⟩ := hB ins
  choose n hn using hβ
  have hn0 : ∀ m, β m = (n m : ℂ) := fun m => by
    rw [hn m]; change (0 : ℂ) + _ = _; rw [zero_add]
  refine ⟨coef, v, n, fun m => ?_, fun τ => ?_⟩
  · rw [mem_sqWeightSpace_iff, ← sqL_adjoint_zero, ← hn0 m]
    exact hsq m
  · choose δx hδx hx using fun x : ι => hE x (moduleIntertwiner (lwOf D x).isMod) τ
    obtain ⟨δ, hδ, hle⟩ := exists_pos_le_fintype δx hδx
    refine ⟨δ, hδ, fun x u hu hre => ?_⟩
    obtain ⟨hs, heq⟩ := hx x u (lt_of_lt_of_le hu (hle x)) hre
    have hterm : ∀ m, coef m * exp ((β m - ins.κ) * log u) *
        traceFunction (moduleIntertwiner (lwOf D x).isMod) (D.h x) (v m) τ =
          coef m * exp (((n m : ℂ) - ins.κ) * log u) * traceFun D.Mfam D.h x (v m) τ := by
      intro m
      rw [hn0 m]
      congr 1
      exact GenusOne.IntCoord.vacuum_traceFunction_eq D x (v m) τ
    refine ⟨hs.congr hterm, ?_⟩
    unfold vacF bracketChannel
    rw [heq]
    exact tsum_congr hterm

/-- **`VacuumBracketSharpInput` from the coordinate-change input.** -/
theorem vacuumBracketSharpInput_of_channel (h : ChannelBracketSharpInput.{u, w}) :
    VacuumBracketSharpInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp F a b c hv
  have iQ : (vacuumLW W hv).IsIrreducibleLW :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hNice.1.simple
  exact vacuumChannelBracketSharp_of_inner F hv c
    (h 𝒱 W hNice ι D hZ hirr hcomp a b (vacuumLW W hv) iQ (epsInt F c))

/-- **Huang's Theorem 5.2 from the coordinate-change input, (N2) and (N4).** (N1) and (N3)
are both discharged from `ChannelBracketSharpInput`. -/
theorem fusionEigenInput_of_channelBracket (h : ChannelBracketSharpInput.{u, w})
    (h2 : ConjugationInputAll.{u, w}) (h4 : ChannelIndependenceInput.{u, w}) :
    VerlindeEigen.FusionEigenInput.{u, w} :=
  fusionEigenInput_of_bracket (vacuumBracketSharpInput_of_channel h) h2
    (channelSStabilityInput_of_bracket h) h4

end VOA.Huang.GenusOneG1e
