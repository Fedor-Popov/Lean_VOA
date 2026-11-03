/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchBimodDescentsGen
import VOA.Modules.ZhuVermaAnArchBottomSurvival

/-!
# `BottomOrbitDefectVanishes` for the concrete `M(U)` — closed via the block-diagonal mechanism

`ZhuVermaAnArchBottomAn` reduced full bottom survival to the single genuine `A_n`-bimodule datum

  `BottomOrbitDefectVanishes ρ hInt`  (`∀ g u v x ℓ N, deg0Proj hInt (ρ.toAlgHom g δ) = 0`)

and `ZhuVermaAnArchBottomOrbit` instantiated the *abstract* machinery on `M(U)`, carrying
`BottomOrbitDefectVanishes` as a field of `MUVHatOrbitData`.  **This file discharges that field for
the concrete Construction-A representation `ρ`** — the sound bottom-row action `repMULevel`
(`ZhuVermaAnArchBimodDescentsGen`) — closing `BottomOrbitDefectVanishes` down to one precise
level-`0` identity (the `A(𝒱) = A_0`-module structure of the bottom).

## The mechanism — block-diagonality of the level action

The Construction-A loop modes of `repMULevel` are the *level-diagonal* right residue action
`composeActLevel a` (`ZhuVermaAnArchBimodDescentsGen`), which acts on each graded piece
`MU.deg n = M(U)(n)` and **stays at the same level** (`composeActLevel_incl`).  Hence every mode is
**block-diagonal** for the `ℕ`-grading `MU.deg` (`ZhuVermaAnArchMU`, `MU.isInternal_deg`).  The set of
block-diagonal endomorphisms is a subalgebra of `End ℂ M`, and `ρ` factors through it on the
generators `gen a m`, so by the universal property of `U(V̂)` the **whole orbit map** `ρ.toAlgHom g`
is block-diagonal (same factoring as `defectOrbit_le_of_invariant`).  A block-diagonal map commutes
with the degree-`0` projection `deg0Proj` (`certificates/mathematica/bottom_orbit_deg0.wl`), so

  `deg0Proj (ρ.toAlgHom g δ) = ρ.toAlgHom g (deg0Proj δ)`,

reducing `BottomOrbitDefectVanishes` to the **single level-`0` identity** `deg0Proj δ = 0` — the
degree-`0` component of the *bare* defect, which is the `A(𝒱)`-module Borcherds relation on the
bottom `M₀ = U` (the genuine `A_0` content, `gMode_anmCirc_lowest` / `oMod_zhuMul_lowest_all`).

## What is built here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`deg0Proj_of_mem_ne`** — the degree-`0` projection kills any homogeneous piece of degree `d ≠ 0`.
* **`IsBlockDiag ρ mdeg`** — every `ρ x` preserves each graded piece `mdeg n` (block-diagonal).
* **`deg0Proj_comm_blockDiag`** — a block-diagonal endomorphism commutes with `deg0Proj`.
* **`toAlgHom_preserves_block` / `toAlgHom_blockDiag`** — from block-diagonality on the generators,
  the whole orbit map `ρ.toAlgHom g` is block-diagonal (universal property of `U(V̂)`).
* **`bottomOrbitDefectVanishes_of_blockDiag`** — *the closure*: for any block-diagonal `ρ`, the
  orbit datum `BottomOrbitDefectVanishes` reduces to the single level-`0` identity
  `∀ u v x ℓ N, deg0Proj hInt (defectVec ρ u v x ℓ N) = 0`.
* **`composeActLevel_block` / `repMULevel_isBlockDiag`** — the concrete `repMULevel` *is*
  block-diagonal for the `ℕ`-grading `MU.deg` (lifted to `ℤ`), since each mode is `composeActLevel`,
  level-preserving.
* **`repMULevel_bottomOrbitDefectVanishes`** — `BottomOrbitDefectVanishes` for the concrete
  `repMULevel`, reduced to the level-`0` identity `bottomLevelDefect` (the `A(𝒱)`-module relation).

## What is OPEN (precise, NOT faked)

* `bottomLevelDefect` — the level-`0` identity `deg0Proj (defectVec ρ u v x ℓ N) = 0` for
  `ρ = repMULevel`.  This is the degree-`0` component of the bare defect: on `M₀ = A(𝒱) ⊗ U` it is
  the `A(𝒱) = A_0`-module Borcherds (zero-mode) relation — `0` in `U` *as an `A(𝒱)`-module*.  The
  genuine `A_0` content (the same mechanism as `gMode_anmCirc_lowest` / `oMod_zhuMul_lowest_all`),
  carried as an explicit hypothesis, **never** an axiom.  This is the EXACT remaining
  orbit-degree-`0` identity, isolated from the whole `g`-orbit by block-diagonality.

## References
DLM3 §4; Frenkel–Zhu; Dong–Jiang `math/0601626`; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchBottomAn` (`BottomOrbitDefectVanishes`, `deg0Proj`, `deg0Proj_eq_self`);
`ZhuVermaAnArchBimodDescentsGen` (`repMULevel`, `composeActLevel`, `composeActLevel_incl`);
`ZhuVermaAnArchMU` (`MU.deg`, `MU.isInternal_deg`, `MU.incl`); `ZhuModule` (`oMod_zhuMul_lowest_all`);
`certificates/mathematica/bottom_orbit_deg0.wl`.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct DirectSum
open Finsupp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## (A) The degree-`0` projection of an off-bottom homogeneous piece -/

/-- **The degree-`0` projection kills off-bottom homogeneous pieces.** For `m ∈ mdeg d` with `d ≠ 0`,
the degree-`0` component is `0` (`decompose_of_mem_ne`). -/
theorem deg0Proj_of_mem_ne {mdeg : ℤ → Submodule ℂ M} (hInt : DirectSum.IsInternal mdeg) {d : ℤ}
    (hd : d ≠ 0) {m : M} (hm : m ∈ mdeg d) : deg0Proj hInt m = 0 := by
  letI := hInt.chooseDecomposition
  rw [deg0Proj_apply]
  have hcomp : (DirectSum.decompose mdeg m 0 : M) = 0 :=
    DirectSum.decompose_of_mem_ne (ℳ := mdeg) hm hd
  -- `decomposeLinearEquiv mdeg m = decompose mdeg m`; its `0`-component coerces to `0`.
  have hzero : (DirectSum.component ℂ ℤ (fun d => mdeg d) 0
      ((DirectSum.decomposeLinearEquiv mdeg) m) : mdeg 0) = 0 := by
    apply Subtype.ext
    show ((DirectSum.decomposeLinearEquiv mdeg) m 0 : M) = (0 : M)
    rw [DirectSum.decomposeLinearEquiv_apply]
    exact hcomp
  rw [hzero]
  rfl

/-! ## (B) Block-diagonal representations and the degree-`0` projection -/

/-- **`ρ` is block-diagonal for `mdeg`**: every mode `ρ x` (for `x : V̂`) preserves each graded piece
`mdeg n`.  The level action `composeActLevel` of `repMULevel` is block-diagonal: it acts within each
level `MU.deg n` (`composeActLevel_incl`), unlike a degree-*shifting* graded action. -/
def IsBlockDiag (ρ : VHatRep W M) (mdeg : ℤ → Submodule ℂ M) : Prop :=
  ∀ (x : VHatCarrier W) (n : ℤ) (m : M), m ∈ mdeg n → ρ x m ∈ mdeg n

/-- **A block-diagonal endomorphism commutes with `deg0Proj`.** If `T` preserves every graded piece,
then `deg0Proj (T m) = T (deg0Proj m)` for all `m`.  Proof: reduce `m` to homogeneous pieces via the
internal direct sum (`hInt`, `iSup_eq_top`); on `m ∈ mdeg d`, `T m ∈ mdeg d`, and both sides equal
`T m` if `d = 0` (`deg0Proj_eq_self`) and `0` otherwise (`deg0Proj_of_mem_ne`). Engine-verified
(`certificates/mathematica/bottom_orbit_deg0.wl`). -/
theorem deg0Proj_comm_blockDiag {mdeg : ℤ → Submodule ℂ M} (hInt : DirectSum.IsInternal mdeg)
    {T : M →ₗ[ℂ] M} (hT : ∀ (n : ℤ) (m : M), m ∈ mdeg n → T m ∈ mdeg n) (m : M) :
    deg0Proj hInt (T m) = T (deg0Proj hInt m) := by
  -- `m` lies in the supremum of all graded pieces (internal direct sum).
  have hmem : m ∈ ⨆ d, mdeg d := by
    rw [hInt.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction mdeg (motive := fun z =>
      deg0Proj hInt (T z) = T (deg0Proj hInt z)) hmem ?_ ?_ ?_
  · -- homogeneous case: `z ∈ mdeg d`.
    intro d z hz
    rcases eq_or_ne d 0 with hd | hd
    · subst hd
      rw [deg0Proj_eq_self hInt hz, deg0Proj_eq_self hInt (hT 0 z hz)]
    · rw [deg0Proj_of_mem_ne hInt hd hz, map_zero,
        deg0Proj_of_mem_ne hInt hd (hT d z hz)]
  · simp only [map_zero]
  · intro a b ha hb
    -- additivity of `deg0Proj` and `T` (both `ℂ`-linear maps).
    simp only [map_add, ha, hb]

/-! ## (C) The orbit map `ρ.toAlgHom g` is block-diagonal (universal property of `U(V̂)`)

If every generator `ρ x` preserves a graded piece `mdeg n`, then the whole `U(V̂)`-orbit map
`ρ.toAlgHom g` preserves it.  This is the same factoring argument as `defectOrbit_le_of_invariant`:
the maps preserving `mdeg n` form a subalgebra of `End ℂ M`, `ρ` factors through it, hence so does
`ρ.toAlgHom`. -/

/-- **Each generator `ρ x` preserves `mdeg n` ⟹ the whole orbit map `ρ.toAlgHom g` preserves it.**
The block-preserving maps `{T | ∀ z ∈ mdeg n, T z ∈ mdeg n}` form a subalgebra `S ≤ End ℂ M`; `ρ`
factors as a Lie morphism into `S` (block-diagonality on generators), so `ρ.toAlgHom g ∈ S`. -/
theorem toAlgHom_preserves_block {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M} (n : ℤ)
    (hbd : ∀ (x : VHatCarrier W) (z : M), z ∈ mdeg n → ρ x z ∈ mdeg n) (g : UEnv W) {z : M}
    (hz : z ∈ mdeg n) : ρ.toAlgHom g z ∈ mdeg n := by
  -- The block-preserving subalgebra.
  let S : Subalgebra ℂ (Module.End ℂ M) :=
    { carrier := {T : Module.End ℂ M | ∀ z ∈ mdeg n, T z ∈ mdeg n}
      mul_mem' := fun {a b} ha hb z hz => ha _ (hb z hz)
      one_mem' := fun z hz => hz
      add_mem' := fun {a b} ha hb z hz => Submodule.add_mem _ (ha z hz) (hb z hz)
      zero_mem' := fun z _ => Submodule.zero_mem _
      algebraMap_mem' := fun c z hz => by
        simp only [Module.algebraMap_end_apply]
        exact Submodule.smul_mem _ c hz }
  suffices hmem : ρ.toAlgHom g ∈ S by exact hmem z hz
  -- `ρ` factors as a Lie morphism into `S`.
  let ρS : VHatCarrier W →ₗ⁅ℂ⁆ S :=
    { toFun := fun x => ⟨ρ x, fun z hz => hbd x z hz⟩
      map_add' := fun x y => by apply Subtype.ext; simp
      map_smul' := fun c x => by apply Subtype.ext; simp
      map_lie' := fun {x y} => by
        apply Subtype.ext
        show (ρ ⁅x, y⁆ : Module.End ℂ M) = ((⟨ρ x, _⟩ : S) * ⟨ρ y, _⟩ - ⟨ρ y, _⟩ * ⟨ρ x, _⟩ : S)
        rw [ρ.map_lie x y]
        rfl }
  have hfactor : S.val.comp (UniversalEnvelopingAlgebra.lift ℂ ρS) = ρ.toAlgHom := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => ?_
    show S.val (UniversalEnvelopingAlgebra.lift ℂ ρS (UniversalEnvelopingAlgebra.ι ℂ x))
      = ρ.toAlgHom (UniversalEnvelopingAlgebra.ι ℂ x)
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    show (ρ x : Module.End ℂ M) = ρ.toAlgHom (uι W x)
    rw [toAlgHom_uι]
  have hg : ρ.toAlgHom g = S.val (UniversalEnvelopingAlgebra.lift ℂ ρS g) := by
    rw [← hfactor]; rfl
  rw [hg]
  exact (UniversalEnvelopingAlgebra.lift ℂ ρS g).2

/-- **The orbit map is block-diagonal.** From `IsBlockDiag ρ mdeg` (block-diagonality on every
generator), the whole orbit map `ρ.toAlgHom g` preserves every graded piece. -/
theorem toAlgHom_blockDiag {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M} (hbd : IsBlockDiag ρ mdeg)
    (g : UEnv W) (n : ℤ) {z : M} (hz : z ∈ mdeg n) : ρ.toAlgHom g z ∈ mdeg n :=
  toAlgHom_preserves_block n (fun x z hz => hbd x n z hz) g hz

/-! ## (D) The closure: `BottomOrbitDefectVanishes` for a block-diagonal `ρ` -/

/-- **`BottomOrbitDefectVanishes` from block-diagonality + the level-`0` defect identity.**  For a
block-diagonal representation, the degree-`0` projection commutes with every orbit map
(`deg0Proj_comm_blockDiag` + `toAlgHom_blockDiag`), so

  `deg0Proj (ρ.toAlgHom g δ) = ρ.toAlgHom g (deg0Proj δ)`.

If the *bare* defect's degree-`0` component vanishes (`hbottom : deg0Proj δ = 0` — the `A(𝒱)`-module
relation on the bottom), then every orbit image's degree-`0` component is `ρ.toAlgHom g 0 = 0`, i.e.
`BottomOrbitDefectVanishes`.  This isolates the whole `g`-orbit datum down to the single level-`0`
identity. -/
theorem bottomOrbitDefectVanishes_of_blockDiag {ρ : VHatRep W M} {mdeg : ℤ → Submodule ℂ M}
    (hInt : DirectSum.IsInternal mdeg) (hbd : IsBlockDiag ρ mdeg)
    (hbottom : ∀ (u v : 𝒱) (x : M) (ℓ N : ℤ), deg0Proj hInt (defectVec ρ u v x ℓ N) = 0) :
    BottomOrbitDefectVanishes ρ hInt := by
  intro g u v x ℓ N
  rw [deg0Proj_comm_blockDiag hInt (fun n m hm => toAlgHom_blockDiag hbd g n hm),
    hbottom u v x ℓ N, map_zero]

end VHatRep
end VHat

/-! ## (E) The concrete `repMULevel` is block-diagonal for the `ℕ`-grading `MU.deg`

The sound Construction-A modes are `actMode a m = composeActLevel a` (`repMULevel_actMode`), and
`composeActLevel a` maps `MU.deg n` into `MU.deg n` (`composeActLevel_incl`): the level action is
level-preserving, hence block-diagonal.  We lift the `ℕ`-grading `MU.deg` to `ℤ` (degree `0` for
negative levels) and record block-diagonality of `repMULevel` for this `ℤ`-grading. -/

namespace VHat

/-- The `ℕ`-grading `MU.deg` lifted to `ℤ`: degree `d` is `MU.deg d.toNat` for `d ≥ 0`, and `⊥` for
`d < 0`.  (`MU W U` is `ℕ`-graded, so negative integer degrees carry no states.) -/
noncomputable def MUdegZ (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (d : ℤ) : Submodule ℂ (MU W U) :=
  if 0 ≤ d then MU.deg W U d.toNat else ⊥

theorem MUdegZ_ofNat (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    MUdegZ W U (n : ℤ) = MU.deg W U n := by
  rw [MUdegZ, if_pos (Int.ofNat_nonneg n), Int.toNat_natCast]

/-- **`composeActLevel a` preserves every level `MU.deg n`** — the level action is level-preserving.
Proof: a general element of `MU.deg n` is `MU.incl n x`, and `composeActLevel_incl` keeps it at
level `n`. -/
theorem composeActLevel_block (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n) (a : 𝒱) (n : ℕ) {z : MU W U} (hz : z ∈ MU.deg W U n) :
    composeActLevel W U hclo a z ∈ MU.deg W U n := by
  obtain ⟨y, rfl⟩ := hz
  rw [composeActLevel_incl]
  exact ⟨_, rfl⟩

/-- **The concrete `repMULevel` is block-diagonal for the `ℤ`-lifted grading `MUdegZ`.**  Every mode
`ρ x` preserves each level.  By `gen_span_top` it suffices to check on the generators `gen a m`,
where `ρ (gen a m) = actMode a m = composeActLevel a` (`repMULevel_actMode`), which is level-
preserving (`composeActLevel_block`); the block-preserving property is closed under `+`/`•`, so it
extends to the whole span `V̂ = span {gen a m}`. -/
theorem repMULevel_isBlockDiag (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevelFamily W U hclo m (W.L (-1) a)
        + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
        = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆) :
    VHatRep.IsBlockDiag (repMULevel W U hclo hderiv hbracket) (MUdegZ W U) := by
  set ρ := repMULevel W U hclo hderiv hbracket with hρ
  -- It suffices to handle nonnegative levels (negative `MUdegZ` is `⊥`).
  intro x d z hz
  rcases lt_or_ge d 0 with hd | hd
  · rw [MUdegZ, if_neg (not_le.mpr hd), Submodule.mem_bot] at hz
    rw [hz, map_zero]
    rw [MUdegZ, if_neg (not_le.mpr hd)]
    exact Submodule.zero_mem _
  · -- `d = (d.toNat : ℤ)`; reduce to the `ℕ`-level statement.
    rw [MUdegZ, if_pos hd] at hz ⊢
    set n : ℕ := d.toNat with hn
    -- Block-preservation by `ρ x` for the specific level `n`.
    -- The set of block-preserving endos is a submodule of `End ℂ M`; check on generators.
    have hgen : ∀ p : 𝒱 × ℤ, ∀ {w : MU W U}, w ∈ MU.deg W U n → ρ (gen W p.1 p.2) w ∈ MU.deg W U n := by
      rintro ⟨a, m⟩ w hw
      have : ρ (gen W a m) = composeActLevel W U hclo a := by
        rw [hρ]
        exact repMULevel_actMode W U hclo hderiv hbracket a m
      rw [this]
      exact composeActLevel_block W U hclo a n hw
    -- Extend from generators to all of `V̂` by linearity (block-preservation is a submodule).
    have hspan : x ∈ Submodule.span ℂ (Set.range (fun p : 𝒱 × ℤ => gen W p.1 p.2)) := by
      rw [gen_span_top]; exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun y _ => ρ y z ∈ MU.deg W U n) ?_ ?_ ?_ ?_ hspan
    · rintro y ⟨p, rfl⟩; exact hgen p hz
    · simp only [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      simp only [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      simp only [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ c ha

/-! ## (F) `BottomOrbitDefectVanishes` for the concrete `repMULevel`

By block-diagonality the whole `g`-orbit datum collapses to the single level-`0` identity
`deg0Proj (defectVec ρ u v x ℓ N) = 0` — the degree-`0` component of the bare defect, which on the
bottom `M₀ = A(𝒱) ⊗ U` is the `A(𝒱) = A_0`-module Borcherds (zero-mode) relation.  This level-`0`
identity is the genuine `A_0` content (the same mechanism as `gMode_anmCirc_lowest` /
`oMod_zhuMul_lowest_all`); it is carried as the explicit hypothesis `bottomLevelDefect`, **never** an
axiom, and *everything around it is proved*. -/

/-- The internal direct-sum structure of the `ℤ`-lifted grading `MUdegZ`.  Reindexes
`MU.isInternal_deg` (the `ℕ`-grading is internal) along the embedding `ℕ ↪ ℤ`, with the negative
degrees being `⊥`. -/
theorem MUdegZ_isInternal (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    DirectSum.IsInternal (MUdegZ W U) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  have hN := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (MU.deg W U)).mp
    (MU.isInternal_deg W U)
  constructor
  · -- Independence: a negative index contributes `⊥`; nonnegative indices reindex `hN.1`.
    rw [iSupIndep_def]
    intro d
    rcases lt_or_ge d 0 with hd | hd
    · rw [MUdegZ, if_neg (not_le.mpr hd)]; exact disjoint_bot_left
    · -- `MUdegZ d = MU.deg d.toNat`; the complement supremum is below the `ℕ`-complement.
      rw [MUdegZ, if_pos hd]
      have key := iSupIndep_def.mp hN.1 d.toNat
      refine key.mono_right ?_
      -- `⨆ (k ≠ d) MUdegZ k ≤ ⨆ (j ≠ d.toNat) MU.deg j`
      refine iSup_le (fun k => iSup_le (fun (hk : k ≠ d) => ?_))
      rcases lt_or_ge k 0 with hk0 | hk0
      · rw [MUdegZ, if_neg (not_le.mpr hk0)]; exact bot_le
      · rw [MUdegZ, if_pos hk0]
        refine le_iSup_of_le k.toNat (le_iSup_of_le ?_ le_rfl)
        intro hcontra
        exact hk (by rw [← Int.toNat_of_nonneg hk0, ← Int.toNat_of_nonneg hd, hcontra])
  · -- Spanning: every `ℕ`-piece is an `ℤ`-piece, so the `ℤ`-supremum is `⊤`.
    rw [eq_top_iff, ← hN.2]
    refine iSup_le (fun n => ?_)
    refine le_iSup_of_le (n : ℤ) ?_
    rw [MUdegZ_ofNat]

/-- **`BottomOrbitDefectVanishes` for the concrete `repMULevel`.**  The whole `U(V̂)`-orbit datum is
discharged by block-diagonality (`repMULevel_isBlockDiag`) down to the single level-`0` identity
`bottomLevelDefect` — the degree-`0` component of the bare defect, i.e. the `A(𝒱) = A_0`-module
Borcherds (zero-mode) relation on the bottom `M₀ = A(𝒱) ⊗ U`, which is `0` because the bottom is `U`
*as an `A(𝒱)`-module* (`oMod_zhuMul_lowest_all`).  The level-`0` identity is the genuine `A_0`
content, carried as an explicit hypothesis, **never** an axiom; everything around it is proved. -/
theorem repMULevel_bottomOrbitDefectVanishes (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevelFamily W U hclo m (W.L (-1) a)
        + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
        = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆)
    (bottomLevelDefect : ∀ (u v : 𝒱) (x : MU W U) (ℓ N : ℤ),
      VHatRep.deg0Proj (MUdegZ_isInternal W U)
        (VHatRep.defectVec (repMULevel W U hclo hderiv hbracket) u v x ℓ N) = 0) :
    VHatRep.BottomOrbitDefectVanishes (repMULevel W U hclo hderiv hbracket)
      (MUdegZ_isInternal W U) :=
  VHatRep.bottomOrbitDefectVanishes_of_blockDiag (MUdegZ_isInternal W U)
    (repMULevel_isBlockDiag W U hclo hderiv hbracket) bottomLevelDefect

/-- **Bottom survival for the concrete `repMULevel`, from the level-`0` defect identity.**  Plugging
the closed `BottomOrbitDefectVanishes` (`repMULevel_bottomOrbitDefectVanishes`) into the constructive
orbit characterization (`bottomAnRelation` ⟹ `defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥`,
`bottomSurvives_of_residual`): `defectSubmodule ρ` is disjoint from the bottom `MUdegZ 0`, so the
lowest-weight space `U` survives the defect quotient `M̄(U)`.  This route uses **only** the internal
grading and the orbit datum — no degree-*shifting* `IsGradedRep` hypothesis, which the
level-preserving `repMULevel` does not satisfy.  The only carried input is the genuine `A_0`-module
level-`0` identity `bottomLevelDefect`; everything else is proved. -/
theorem repMULevel_bottomSurvives (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hclo : ∀ n : ℕ, AnmRightModule W n)
    (hderiv : ∀ (a : 𝒱) (m : ℤ),
      composeActLevelFamily W U hclo m (W.L (-1) a)
        + (m : ℂ) • composeActLevelFamily W U hclo (m - 1) a = 0)
    (hbracket : ∀ (a b : 𝒱) (m k : ℤ),
      assembleAct (composeActLevelFamily W U hclo) (vloopBracket W (single m a) (single k b))
        = ⁅composeActLevelFamily W U hclo m a, composeActLevelFamily W U hclo k b⁆)
    (bottomLevelDefect : ∀ (u v : 𝒱) (x : MU W U) (ℓ N : ℤ),
      VHatRep.deg0Proj (MUdegZ_isInternal W U)
        (VHatRep.defectVec (repMULevel W U hclo hderiv hbracket) u v x ℓ N) = 0) :
    VHatRep.BottomSurvives (repMULevel W U hclo hderiv hbracket) (MUdegZ W U) :=
  VHatRep.bottomSurvives_of_residual
    (VHatRep.bottomAnRelation (MUdegZ_isInternal W U)
      (repMULevel_bottomOrbitDefectVanishes W U hclo hderiv hbracket bottomLevelDefect))

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
