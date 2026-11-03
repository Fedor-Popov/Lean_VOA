/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLUUniversal
import VOA.Modules.ZhuVermaAnArchLU

/-!
# DJ Theorem 4.13 (second half), specialized to an irreducible target — toward `realizesIrr`.

`ZhuVermaAnArchLUUniversal` proved the induced map `φ̄ = oLevUnivMap A L U φ … : M(U) → M` is a
weak-module map for any `A(𝒱)`-equivariant bottom embedding `φ : U → Ω(M)`.  This file specializes it
to `M = P` an **irreducible** lowest-weight `𝒱`-module, `U =` the bottom `Ω(P)` as an `A₀(𝒱)`-module,
and `φ =` the bottom inclusion — the setup DJ Thm 4.13 uses to realize every irreducible `P` as the
irreducible quotient `L(P.bottom)` of `M(P.bottom)`.

## The setup

For `P : LWModule W`: `A := P.isMod.toWeakModule`, `L := admLevOfLowestWeight`, `U := Ω(P).toAmModZero`
(the bottom `P.weight h` as an `A₀(𝒱)`-module through `lowestAMod`), and `φ := Ω(P) ↪ P` the inclusion.
The bottom `A(𝒱)`-action `actA` *is* the zero mode `o(a)` on `Ω(P)` (`actA_mk_apply_coe`), which is
exactly `oLevW P.isMod.toWeakModule 0 a` (`oLevW_zero_eq_oMod`); so `φ` is `A(𝒱)`-equivariant (`hφact`)
and `φ̄ := pPhiBar P : M(Ω(P)) → P` is a weak-module map (`pPhiBar_intertwine`).

The construction of `pPhiBar` and its intertwining is proof-term `#print axioms`-clean,
`sorry`-free, and `pbw`-free. The later bottom-triviality/kernel declarations explicitly carry the
`regularAMod` `BottomProjection` hypothesis `Pr`; the project-level witness is supplied by
`voaPBWBottomProjection`, from the generic relative-induction field of the theorem
`VOA.pbw : PBWPrinciple`. (Downstream: surjectivity onto
irreducible `P` + `ker φ̄ = J` ⟹ `P ≅ L(Ω(P))` = `realizesIrr`.)

## References
Dong–Jiang math/0601626 Thm 4.13; DLM3 §4.  `ZhuVermaAnArchLUUniversal` (`oLevUnivMap`,
`oLevUnivMap_intertwine`), `ZhuVermaAnArchLU` (`AMod.toAmModZero`), `ZhuModule`
(`lowestAMod`, `actA`, `actA_mk_apply_coe`), `ZhuVermaAnArchGate` (`admLevOfLowestWeight`,
`oLevW_zero_eq_oMod`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra
open VHat VHat.DLM3

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section
variable {W : VertexOperatorAlgebra 𝒱}

/-- **The bottom `Ω(P)` of an irreducible lowest-weight module, as an `A₀(𝒱)`-module.** -/
noncomputable def pBotAmMod (P : LWModule W) : AmMod W 0 :=
  (lowestAMod P.isLow).toAmModZero

/-- **`P` as a non-negatively levelled weak module** (`admLevOfLowestWeight`). -/
noncomputable def pAdmLev (P : LWModule W) : AdmLev W P.isMod.toWeakModule :=
  admLevOfLowestWeight P.isMod P.isLow

/-- **The bottom inclusion** `Ω(P) ↪ P`. -/
noncomputable def pBotIncl (P : LWModule W) : (pBotAmMod P).carrier →ₗ[ℂ] P.carrier :=
  (P.isMod.weight P.h).subtype

/-- The bottom inclusion lands in the level-0 piece `Ω(P) = L.lev 0`. -/
theorem pBotIncl_lev (P : LWModule W) (u : (pBotAmMod P).carrier) :
    pBotIncl P u ∈ (pAdmLev P).lev 0 := by
  have hlev : (pAdmLev P).lev 0 = P.isMod.weight P.h := by
    show (if (0 : ℤ) ≤ 0 then P.isMod.weight (P.h + ((0 : ℤ) : ℂ)) else ⊥) = P.isMod.weight P.h
    rw [if_pos le_rfl, Int.cast_zero, add_zero]
  rw [hlev]
  exact u.2

/-- **`A(𝒱)`-equivariance of the bottom inclusion**: `φ([a]·u) = o(a)·φ(u)`.  The bottom action `actA`
is the zero mode `o(a)` on `Ω(P)` (`actA_mk_apply_coe`), i.e. `oLevW A 0 a` (`oLevW_zero_eq_oMod`). -/
theorem pBotIncl_act (P : LWModule W) (a : 𝒱) (u : (pBotAmMod P).carrier) :
    pBotIncl P ((pBotAmMod P).ρ (mkAnFull W 0 a) u)
      = oLevW P.isMod.toWeakModule (0 : ℤ) a (pBotIncl P u) := by
  rw [oLevW_zero_eq_oMod]
  exact actA_mk_apply_coe P.isMod P.isLow a u

/-- **DJ's induced map `φ̄ : M(Ω(P)) → P`** for an irreducible target — a `𝒱`-module map. -/
noncomputable def pPhiBar (P : LWModule W) :
    DJCarrier W (pBotAmMod P) →ₗ[ℂ] P.carrier :=
  oLevUnivMap P.isMod.toWeakModule (pAdmLev P) (pBotAmMod P) (pBotIncl P)
    (pBotIncl_lev P) (pBotIncl_act P)

/-- **`φ̄` is a weak-module map** (`oLevUnivMap_intertwine` specialized). -/
theorem pPhiBar_intertwine (P : LWModule W) (p : ℤ) (a : 𝒱) (x : DJCarrier W (pBotAmMod P)) :
    pPhiBar P (djModeZero W (pBotAmMod P) p a x)
      = P.isMod.toWeakModule.act a p (pPhiBar P x) :=
  oLevUnivMap_intertwine (pAdmLev P) (pBotAmMod P) (pBotIncl P)
    (pBotIncl_lev P) (pBotIncl_act P) p a x

/-! ## Surjectivity onto an irreducible target

`φ̄`'s image is a `𝒱`-submodule of `P` (act-closed by `pPhiBar_intertwine`), and it is nonzero — it
contains the bottom, because on the level-0 generator `𝟙 ⊗ u` the map is `o_{0,0}(𝟙)·φ(u) = φ(u) = u`
(`o(𝟙) = id`, `oMod_vacuum`).  For an *irreducible* `P` a nonzero submodule is everything, so `φ̄` is
onto. -/

/-- **The bottom witness**: on the level-0 generator `𝟙 ⊗ u`, `φ̄` returns the bottom vector `u`.
`φ̄(𝟙 ⊗ u) = o_{0,0}(𝟙)·φ(u) = φ(u) = ↑u`, using `o(𝟙) = id` (`oMod_vacuum`). -/
theorem pPhiBar_bottom (P : LWModule W) (u : (pBotAmMod P).carrier) :
    pPhiBar P (DJCarrier.incl W (pBotAmMod P) 0
        (mkDJPiece W (pBotAmMod P) 0 (mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] u)))
      = pBotIncl P u := by
  simp only [pPhiBar, oLevUnivMap_incl, oLevPieceMap_mk, Nat.cast_zero, sub_zero,
    oLevW_zero_eq_oMod, oMod_vacuum, LinearMap.id_coe, id_eq]

/-- **The image of `φ̄` as a `𝒱`-submodule of `P`** — act-closed because `φ̄` intertwines the action
(`pPhiBar_intertwine`): `aₚ·φ̄(y) = φ̄(aₚ·y) ∈ range`. -/
noncomputable def pPhiBarRange (P : LWModule W) : WeakModule.Submodule' P.isMod.toWeakModule where
  carrier := LinearMap.range (pPhiBar P)
  act_mem u n x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact LinearMap.mem_range.mpr ⟨djModeZero W (pBotAmMod P) n u y, pPhiBar_intertwine P n u y⟩

/-- **`φ̄` is onto an irreducible `P`.**  Its image `pPhiBarRange` is a nonzero submodule (it contains
the nonzero bottom vector, `pPhiBar_bottom` + `P.realized`); irreducibility forces it to be all of `P`. -/
theorem pPhiBar_surjective (P : LWModule W) (hP : P.IsIrreducibleLW) :
    Function.Surjective (pPhiBar P) := by
  have hne : (pPhiBarRange P).carrier ≠ ⊥ := by
    obtain ⟨x, hx, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.realized
    have hmem : x ∈ (pPhiBarRange P).carrier :=
      LinearMap.mem_range.mpr
        ⟨DJCarrier.incl W (pBotAmMod P) 0
          (mkDJPiece W (pBotAmMod P) 0
            (mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] (⟨x, hx⟩ : (pBotAmMod P).carrier))),
          pPhiBar_bottom P ⟨x, hx⟩⟩
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    exact hxne hmem
  rcases hP.2 (pPhiBarRange P) with h | h
  · exact absurd h hne
  · exact LinearMap.range_eq_top.mp h

/-! ## The kernel of `φ̄` is maximal (surjectivity + irreducibility)

For `djJ_unique` (`ZhuVermaAnArchLU`) the kernel of `φ̄` must be (i) *bottom-trivial* and (ii)
*maximal* among proper weak submodules.  Maximality is pure surjectivity + irreducibility, gate-free:
the image of any `Q ⊇ ker φ̄` is a submodule of the irreducible `P`, hence `⊥` (then `Q = ker φ̄`) or
`⊤` (then `Q = ⊤`, using `ker φ̄ ⊆ Q` and surjectivity). -/

/-- **The kernel of `φ̄` as a `𝒱`-submodule of `M(U)`** — act-closed by `pPhiBar_intertwine`
(`aₚ·x ↦ φ̄(aₚ·x) = aₚ·φ̄(x) = aₚ·0 = 0`). -/
noncomputable def pPhiBarKer (P : LWModule W) :
    WeakModule.Submodule' (djCarrierWeak W (pBotAmMod P)) where
  carrier := LinearMap.ker (pPhiBar P)
  act_mem u n x hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [djCarrierWeak_act, pPhiBar_intertwine, hx, WeakModule.act_def, map_zero]

/-- **The image of `Q` under `φ̄`, as a `𝒱`-submodule of `P`** — act-closed by `pPhiBar_intertwine`. -/
noncomputable def pPhiBarImage (P : LWModule W)
    (Q : WeakModule.Submodule' (djCarrierWeak W (pBotAmMod P))) :
    WeakModule.Submodule' P.isMod.toWeakModule where
  carrier := Submodule.map (pPhiBar P) Q.carrier
  act_mem u n x hx := by
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨(djCarrierWeak W (pBotAmMod P)).act u n q, Q.act_mem u n hq, ?_⟩
    rw [djCarrierWeak_act, pPhiBar_intertwine]

/-- **`ker φ̄` is maximal among proper weak submodules** of `M(U)` — the second hypothesis of
`djJ_unique`.  Gate-free (surjectivity + irreducibility of `P`). -/
theorem pPhiBarKer_maximal (P : LWModule W) (hP : P.IsIrreducibleLW)
    (Q : WeakModule.Submodule' (djCarrierWeak W (pBotAmMod P)))
    (hQ : (pPhiBarKer P).carrier ≤ Q.carrier) :
    Q.carrier = (pPhiBarKer P).carrier ∨ Q.carrier = ⊤ := by
  rcases hP.2 (pPhiBarImage P Q) with hbot | htop
  · left
    have hbot' : Submodule.map (pPhiBar P) Q.carrier = ⊥ := hbot
    have hQker : Q.carrier ≤ (pPhiBarKer P).carrier := by
      intro z hz
      rw [show (pPhiBarKer P).carrier = LinearMap.ker (pPhiBar P) from rfl, LinearMap.mem_ker]
      have hzm : pPhiBar P z ∈ Submodule.map (pPhiBar P) Q.carrier := Submodule.mem_map_of_mem hz
      rw [hbot'] at hzm
      exact (Submodule.mem_bot ℂ).mp hzm
    exact le_antisymm hQker hQ
  · right
    rw [eq_top_iff]
    intro x _
    have hmem : pPhiBar P x ∈ Submodule.map (pPhiBar P) Q.carrier := by
      rw [show Submodule.map (pPhiBar P) Q.carrier = (pPhiBarImage P Q).carrier from rfl, htop]
      exact Submodule.mem_top
    obtain ⟨q, hq, hqx⟩ := Submodule.mem_map.mp hmem
    have hdiff : x - q ∈ (pPhiBarKer P).carrier := by
      rw [show (pPhiBarKer P).carrier = LinearMap.ker (pPhiBar P) from rfl, LinearMap.mem_ker,
        map_sub, hqx, sub_self]
    have hxq : x - q ∈ Q.carrier := hQ hdiff
    have hx : x = (x - q) + q := by abel
    rw [hx]
    exact Q.carrier.add_mem hxq hq

/-! ## The kernel of `φ̄` is bottom-trivial, hence equals `J(U)`

`φ̄` is injective on the bottom `M(U)(0)`: conditional on the independent `BottomProjection`
assumption, the bottom isomorphism
`e : M(U)(0) ≅ U` (`djCarrierWeak_bottom_equiv`, defeq `degMEquiv W 0`), every bottom vector is a
vacuum tensor `𝟙 ⊗ w = e⁻¹ w` (`degMEquiv_symm_eq_vacTensor`), on which `φ̄` is the injective bottom
inclusion `φ = pBotIncl` (`pPhiBar_bottom`).  So `ker φ̄ ⊓ M(U)(0) = ⊥`, and with `pPhiBarKer_maximal`
Dong–Jiang's `djJ_unique` identifies `ker φ̄ = J(U)`. -/

/-- **`φ̄` meets the bottom trivially** — the first hypothesis of `djJ_unique`. Carries the
explicit `BottomProjection` assumption `Pr` (the gate `M(U)(0) ≅ U`). The project-level witness
`voaPBWBottomProjection` is supplied from the generic relative-induction field of the theorem
`VOA.pbw : PBWPrinciple`. -/
theorem pPhiBar_bottom_trivial (P : LWModule W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    (pPhiBarKer P).carrier ⊓ DJCarrier.deg W (pBotAmMod P) 0 = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzker, hzdeg⟩ := Submodule.mem_inf.mp hz
  rw [Submodule.mem_bot]
  have hpz : pPhiBar P z = 0 := hzker
  let w : (pBotAmMod P).carrier := djCarrierWeak_bottom_equiv Pr (pBotAmMod P) ⟨z, hzdeg⟩
  have hsymm : (djCarrierWeak_bottom_equiv Pr (pBotAmMod P)).symm w = ⟨z, hzdeg⟩ :=
    LinearEquiv.symm_apply_apply _ _
  have hvac : (((djCarrierWeak_bottom_equiv Pr (pBotAmMod P)).symm w :
      DJCarrier.deg W (pBotAmMod P) 0) : DJCarrier W (pBotAmMod P))
      = djVacTensor W (pBotAmMod P) w :=
    degMEquiv_symm_eq_vacTensor
      (djAnnEqAn_zero_of_gate (gate_le_of_pbwDatum Pr)) (pBotAmMod P) w
  rw [hsymm] at hvac
  have hzv : z = djVacTensor W (pBotAmMod P) w := hvac
  rw [hzv, djVacTensor_def, pPhiBar_bottom] at hpz
  have hinj : Function.Injective (pBotIncl P) :=
    LinearMap.ker_eq_bot.mp (by simp only [pBotIncl]; exact Submodule.ker_subtype _)
  have hw0 : w = 0 := hinj (by rw [hpz, map_zero])
  have hζ0 : (⟨z, hzdeg⟩ : DJCarrier.deg W (pBotAmMod P) 0) = 0 := by
    rw [← hsymm, hw0, map_zero]
  exact congrArg Subtype.val hζ0

/-- **`ker φ̄ = J(U)`** — Dong–Jiang's `djJ_unique` fed by bottom-triviality
(`pPhiBar_bottom_trivial`) and maximality (`pPhiBarKer_maximal`).  Hence `M(U)/ker φ̄ = L(U)`. -/
theorem pPhiBarKer_eq_djJ (P : LWModule W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hU : Nontrivial (pBotAmMod P).carrier)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W (pBotAmMod P)), x ∈ DJCarrier.deg W (pBotAmMod P) n →
      djModeZero W (pBotAmMod P) 1 W.conformalVector x = (P.h + n) • x)
    (hP : P.IsIrreducibleLW) :
    (pPhiBarKer P).carrier = (djJ Pr (pBotAmMod P) hU P.h hL0).carrier :=
  djJ_unique Pr (pBotAmMod P) hU P.h hL0 (pPhiBarKer P)
    (pPhiBar_bottom_trivial P Pr) (pPhiBarKer_maximal P hP)

end

end VOA
