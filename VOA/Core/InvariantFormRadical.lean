/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.SingularVector
import VOA.Core.RigidityBridge

/-!
# Li's theorem: the radical of the invariant form **is** the maximal proper graded ideal

H.-S. Li, *Symmetric invariant bilinear forms on vertex operator algebras*,
J. Pure Appl. Algebra **96** (1994) 279–297, Theorem 3.1 / Corollary 3.2 (see also
Frenkel–Huang–Lepowsky, *On axiomatic approaches to VOAs and modules*, §5.3, and
Dong–Li–Mason).  For a VOA `V` of CFT type (`V₀ = ℂ𝟙`, `Vₙ = 0` for `n < 0`) carrying a
normalised invariant bilinear form,

  `rad (·|·)  =  the maximal proper (graded) ideal of V`,

so `V` is simple iff the form is nondegenerate.  The point of the theorem is **computational**:
it converts the abstract supremum `QuotVOA.maxGradedIdeal W = sSup (ProperGradedIdeals W)` into
something a Gram matrix can see, level by level.

## What was already here, and what this file adds

Already present, and used unchanged:

* `Core.BilinearForm`: `InvariantForm` (carrying Virasoro-adjointness), the full
  generating-function invariance `InvariantForm.IsFullyInvariant`, the normalisation
  `InvariantForm.Normalized` = `(𝟙|𝟙) = 1`, the left radical
  `InvariantForm.leftRadical B = ker B.form`, `InvariantForm.radical_isIdeal`,
  `InvariantForm.orthogonal_of_ne`.
* `Core.InvariantFormCanonical` … `Core.InvariantFormFHL2`: the *concrete* form
  `canBilin` and `canonicalInvariantForm hne hqp`, proved fully invariant and normalised
  unconditionally given `𝟙 ≠ 0` and `L₁𝒱₁ = 0`.  So Li part (i) — existence of the canonical
  invariant form — **already existed**; this file assumes it and does not rebuild it.
* `Core.SingularVector`: `SingVec.rightRadical`, `SingVec.rightRadical_isIdeal`,
  `SingVec.vacuum_not_mem_{left,right}Radical`.
* `Core.QuotientVOA`: `QuotVOA.maxGradedIdeal = sSup (ProperGradedIdeals W)`,
  `QuotVOA.le_maxGradedIdeal'`, `QuotVOA.isGradedIdeal_of_isIdeal` (every ideal is graded),
  `QuotVOA.absorbsLeft_of_isIdeal` (ideals are two-sided), `QuotVOA.inf_grading_zero_eq_bot`.
* `Examples/LeeYangKac.mem_radBil_of_mem_properIdeal` — the **top-mode** half at fixed level:
  a homogeneous element of a proper ideal lies in `radBil (RigidBridge.shapForm W hvac k)`.
  Its own docstring records that the **converse** is missing and "is what needs Li's theorem
  for the FHL invariant form".

What was missing, and is supplied here: **no statement anywhere related any radical to
`QuotVOA.maxGradedIdeal`.**  This file proves Li part (ii) — the equality — for the abstract
invariant form (hence for `canonicalInvariantForm`), plus the level-by-level restatement and
the converse of `mem_radBil_of_mem_properIdeal` for quasi-primary vectors.

## Main results

* `leftRadical_eq_maxGradedIdeal` — **Li's theorem**: for *any* fully invariant normalised
  form `B` on `W`, `InvariantForm.leftRadical B = QuotVOA.maxGradedIdeal W`.
* `rightRadical_eq_maxGradedIdeal` — the same for the right radical; hence
  `leftRadical_eq_rightRadical` (a radical-level shadow of the symmetry of `B`).
* `le_leftRadical` / `le_rightRadical` — the substantive half: **every** proper ideal sits
  inside both radicals.  (`IsIdeal` in this repo is right-slot absorption; the left-radical
  statement needs the two-sidedness `QuotVOA.absorbsLeft_of_isIdeal`.)
* `mem_maxGradedIdeal_iff_grading` — **the level-by-level form**: for homogeneous
  `x ∈ 𝒱ₙ`, `x ∈ maxGradedIdeal W ↔ ∀ y ∈ 𝒱ₙ, (x|y) = 0`.  Packaged as
  `ker_gradedForm` and `maxGradedIdeal_inf_grading`: the degree-`n` part of `maxGradedIdeal`
  **is** the radical of the Gram matrix of `B` restricted to `𝒱ₙ`.  This is what lets a
  determinant computation touch `maxGradedIdeal`.
* `isSimple_iff_leftRadical_eq_bot` — `W` simple ⟺ the form is nondegenerate.
* `…_FHL` corollaries: everything above instantiated at the concrete
  `canonicalInvariantForm hne hqp` of `Core.InvariantFormFHL2`, which is unconditionally
  fully invariant and normalised given `𝟙 ≠ 0` and `L₁𝒱₁ = 0`.

## Hypotheses actually needed

CFT type is **free** here: `vacuum_grade : 𝒱₀ = ℂ𝟙` and `positivity : 𝒱_{<0} = ⊥` are
structure fields of `VertexOperatorAlgebra`.  The theorem itself needs only
`B.IsFullyInvariant` and `B.Normalized` (`(𝟙|𝟙) = 1`); `𝟙 ≠ 0` is a
*consequence* of `Normalized` (`vacuum_ne_zero_of_normalized`), not an extra hypothesis.
Li's `L₁𝒱₁ = 0` is needed only to *construct* such a `B`, i.e. it enters through
`canonicalInvariantForm`, not through this file's arguments.

## Proof

Both halves are short once the right repo lemmas are in hand.

* `rad ≤ maxGradedIdeal`: the radical is an ideal (`InvariantForm.radical_isIdeal`) and it is
  proper because `(𝟙|𝟙) = 1 ≠ 0` (`SingVec.vacuum_not_mem_leftRadical`), so
  `QuotVOA.le_maxGradedIdeal'` applies.
* `maxGradedIdeal ≤ rad` (the substantive half): let `I` be any proper ideal.  First,
  `(𝟙|z) = 0` for every `z ∈ I` — split `z` into homogeneous pieces (`I` is automatically
  graded, `QuotVOA.isGradedIdeal_of_isIdeal`); pieces of degree `≠ 0` are orthogonal to
  `𝟙 ∈ 𝒱₀` (`InvariantForm.orthogonal_of_ne`), and the degree-`0` piece lies in
  `I ⊓ 𝒱₀ = ⊥` (`QuotVOA.inf_grading_zero_eq_bot`, using `𝟙 ∉ I`).  Now for homogeneous
  `x ∈ I ∩ 𝒱ₚ` write `x = x₍₋₁₎𝟙` and apply full invariance:
  `(x|b) = (−1)^p ∑_j (1/j!) (𝟙 | (L₁ʲx)₍₂ₚ₋₁₋ⱼ₎ b)`.
  Every `L₁ʲx` is again in `I`, so every `(L₁ʲx)₍ₘ₎b` is in `I` (two-sidedness), and each
  term dies by the previous step.  For the right radical the same expansion with the roles of
  `x` and `b` exchanged uses only right-slot absorption.

## Validation (checked, not committed — it would need `Examples` imports in `Core`)

At `c = −22/5` on `V(c,0) = virasoroVOA leeYangC`, with `hne = leeYang_vacuum_ne_zero` and
`hqp = virasoroVOA_qp`:

* `mem_maxGradedIdeal_of_mem_radBil_shapForm` applied to `Examples/LeeYangRigidity`'s
  `leeYangSingular_mem_radBil` (and `L₁s = 0`, from `leeYangSingular_isSingular.annihilated 1`)
  reproves `leeYangSingular ∈ maxGradedIdeal` — a statement `Examples/LeeYangProper` obtains by
  a completely different route.  The two agree definitionally.
* `maxGradedIdeal_inf_grading_canonical … 4` together with
  `LeeYangKac.finrank_maxIdealVir_leeYang_inf_grading_four = 1` gives
  `finrank ℂ (ker (gradedForm (canonicalInvariantForm hne hqp) 4)) = 1`, against
  `finrank ℂ 𝒱₄ = 2` (`VirDefLow.finrank_gradingVir_four`).  **This matches the independent
  ground truth**: `dim V(−22/5,0)₄ = 2`, `dim L(−22/5,0)₄ = 1`, so the level-4 radical is a line.

## Status

Hole-free.  No `sorry`, no `admit`, no `native_decide`, no `unsafe`, no new axiom, and
`VOA.pbw` is not used.  `#print axioms` = `[propext, Classical.choice, Quot.sound]` on
every declaration in this file (and on the validation theorems above).

⚠ Not proved here, and not claimed: (i) that `B` is symmetric (only the equality of its two
radicals, `leftRadical_eq_rightRadical`, which is weaker); (ii) any identification of
`gradedForm B n` with `RigidBridge.shapForm W hvac n` off the quasi-primary locus — the
existing `RigidBridge.invariantForm_eq_shapForm` needs `L₁s = 0`, and on `V(c,0)` the weight
spaces are *not* all quasi-primary (`L₁L₋₄|0⟩ = 5L₋₃|0⟩ ≠ 0`), so the shapForm bridge below
covers quasi-primary vectors only; (iii) anything at all about levels beyond what a caller
supplies a Gram matrix for.
-/

namespace VOA

open VOA.VertexOperatorAlgebra

namespace LiRadical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## Preliminaries -/

/-- A normalised form forces a nonzero vacuum: `(𝟙|𝟙) = 1 ≠ 0`.  So `𝟙 ≠ 0` is never an
extra hypothesis below. -/
theorem vacuum_ne_zero_of_normalized {B : InvariantForm W} (hn : B.Normalized) :
    W.vacuum ≠ 0 := by
  intro h
  have hv : B.form W.vacuum W.vacuum = 1 := hn
  rw [h, map_zero] at hv
  norm_num at hv

/-- An ideal is stable under every Virasoro mode `Lₙ = ω₍ₙ₊₁₎` (right-slot absorption at
`u = ω`). -/
theorem L_mem_of_isIdeal {I : Submodule ℂ 𝒱} (hI : W.IsIdeal I) (n : ℤ) {x : 𝒱}
    (hx : x ∈ I) : W.L n x ∈ I := by
  have h : W.L n x = W.smul W.conformalVector (n + 1) x := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]
  rw [h]
  exact hI _ _ _ hx

/-- An ideal is stable under every iterate `L₁ʲ` — the operators appearing in the
`e^{zL₁}` tower of the invariance identity. -/
theorem L_one_pow_mem_of_isIdeal {I : Submodule ℂ 𝒱} (hI : W.IsIdeal I) :
    ∀ (j : ℕ) {x : 𝒱}, x ∈ I → ((W.L 1) ^ j) x ∈ I := by
  intro j
  induction j with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
    intro x hx
    have h : ((W.L 1) ^ (k + 1)) x = W.L 1 (((W.L 1) ^ k) x) := by
      rw [pow_succ', Module.End.mul_apply]
    rw [h]
    exact L_mem_of_isIdeal hI 1 (ih hx)

/-! ## The vacuum pairs to zero against a proper ideal

This is where `V₀ = ℂ𝟙` (CFT type, a structure field here) does its work. -/

/-- For `z` homogeneous inside a proper ideal `I`, `(𝟙|z) = 0`: either `z` has degree `≠ 0`
and is orthogonal to `𝟙 ∈ 𝒱₀`, or `z ∈ I ⊓ 𝒱₀ = ⊥` and `z = 0`. -/
theorem form_vacuum_eq_zero_of_mem_ideal_homog {B : InvariantForm W} {I : Submodule ℂ 𝒱}
    (hv : W.vacuum ∉ I) {k : ℤ} {z : 𝒱} (hzI : z ∈ I) (hzk : z ∈ W.grading k) :
    B.form W.vacuum z = 0 := by
  by_cases hk : k = 0
  · subst hk
    have hmem : z ∈ I ⊓ W.grading 0 := ⟨hzI, hzk⟩
    rw [QuotVOA.inf_grading_zero_eq_bot hv, Submodule.mem_bot] at hmem
    rw [hmem, map_zero]
  · exact InvariantForm.orthogonal_of_ne B (Ne.symm hk) W.vacuum_mem hzk

/-- For **any** `z` in a proper ideal `I`, `(𝟙|z) = 0`.  Every ideal of a VOA is graded
(`QuotVOA.isGradedIdeal_of_isIdeal`), so `z` decomposes into homogeneous pieces of `I`. -/
theorem form_vacuum_eq_zero_of_mem_ideal {B : InvariantForm W} {I : Submodule ℂ 𝒱}
    (hI : W.IsIdeal I) (hv : W.vacuum ∉ I) {z : 𝒱} (hz : z ∈ I) :
    B.form W.vacuum z = 0 := by
  have hgr : I = ⨆ n : ℤ, I ⊓ W.grading n := QuotVOA.isGradedIdeal_of_isIdeal hI
  have hz' : z ∈ ⨆ n : ℤ, I ⊓ W.grading n := hgr ▸ hz
  refine Submodule.iSup_induction (fun n : ℤ => I ⊓ W.grading n)
    (motive := fun z => B.form W.vacuum z = 0) hz' ?_ ?_ ?_
  · intro n y hy
    exact form_vacuum_eq_zero_of_mem_ideal_homog hv hy.1 hy.2
  · exact map_zero _
  · intro y y' hy hy'; rw [map_add, hy, hy', add_zero]

/-! ## The substantive half of Li's theorem: every proper ideal is inside both radicals -/

/-- The homogeneous core of `le_leftRadical`.  For `x ∈ I ∩ 𝒱ₚ`, write `x = x₍₋₁₎𝟙` and apply
full invariance: `(x|b) = (−1)^p ∑_j (1/j!) (𝟙 | (L₁ʲx)₍₂ₚ₋₁₋ⱼ₎b)`.  Each `L₁ʲx` stays in `I`,
so — by two-sidedness of VOA ideals (`QuotVOA.absorbsLeft_of_isIdeal`) — each
`(L₁ʲx)₍ₘ₎b` stays in `I`, and pairs to zero against `𝟙`. -/
theorem form_eq_zero_of_mem_ideal_homog {B : InvariantForm W} (hB : B.IsFullyInvariant)
    {I : Submodule ℂ 𝒱} (hI : W.IsIdeal I) (hv : W.vacuum ∉ I) {p : ℤ} {x : 𝒱}
    (hxI : x ∈ I) (hxp : x ∈ W.grading p) (b : 𝒱) :
    B.form x b = 0 := by
  have key := hB p x hxp (-1) W.vacuum b
  rw [PreVertexAlgebra.smul_vacuum_neg_one] at key
  rw [key, Finset.sum_eq_zero, smul_zero]
  intro j _
  have hLI : ((W.L 1) ^ j) x ∈ I := L_one_pow_mem_of_isIdeal hI j hxI
  have hmem : W.smul (((W.L 1) ^ j) x) (2 * p - (-1) - 2 - (j : ℤ)) b ∈ I :=
    QuotVOA.absorbsLeft_of_isIdeal hI _ _ _ hLI
  rw [form_vacuum_eq_zero_of_mem_ideal hI hv hmem, smul_zero]

/-- **Every proper ideal lies in the left radical.**  (Li, JPAA 96 (1994), Thm 3.1.) -/
theorem le_leftRadical {B : InvariantForm W} (hB : B.IsFullyInvariant) {I : Submodule ℂ 𝒱}
    (hI : W.IsIdeal I) (hv : W.vacuum ∉ I) : I ≤ InvariantForm.leftRadical B := by
  intro x hx
  have hgr : I = ⨆ n : ℤ, I ⊓ W.grading n := QuotVOA.isGradedIdeal_of_isIdeal hI
  have hx' : x ∈ ⨆ n : ℤ, I ⊓ W.grading n := hgr ▸ hx
  rw [InvariantForm.mem_leftRadical]
  refine LinearMap.ext fun b => ?_
  simp only [LinearMap.zero_apply]
  refine Submodule.iSup_induction (fun n : ℤ => I ⊓ W.grading n)
    (motive := fun x => ∀ c : 𝒱, B.form x c = 0) hx' ?_ ?_ ?_ b
  · intro n y hy c
    exact form_eq_zero_of_mem_ideal_homog hB hI hv hy.1 hy.2 c
  · intro c; rw [map_zero, LinearMap.zero_apply]
  · intro y y' hy hy' c
    rw [map_add, LinearMap.add_apply, hy c, hy' c, add_zero]

/-- The homogeneous core of `le_rightRadical`: the same expansion with the roles exchanged,
`(b|x) = (−1)^q ∑_j (1/j!) (𝟙 | (L₁ʲb)₍₂q₋₁₋ⱼ₎x)`.  Here `x ∈ I` sits in the **right** slot of
every mode, so plain right-slot absorption (`IsIdeal`) suffices — no two-sidedness needed. -/
theorem form_eq_zero_of_mem_ideal_homog' {B : InvariantForm W} (hB : B.IsFullyInvariant)
    {I : Submodule ℂ 𝒱} (hI : W.IsIdeal I) (hv : W.vacuum ∉ I) {q : ℤ} {b : 𝒱}
    (hb : b ∈ W.grading q) {x : 𝒱} (hxI : x ∈ I) :
    B.form b x = 0 := by
  have key := hB q b hb (-1) W.vacuum x
  rw [PreVertexAlgebra.smul_vacuum_neg_one] at key
  rw [key, Finset.sum_eq_zero, smul_zero]
  intro j _
  have hmem : W.smul (((W.L 1) ^ j) b) (2 * q - (-1) - 2 - (j : ℤ)) x ∈ I := hI _ _ _ hxI
  rw [form_vacuum_eq_zero_of_mem_ideal hI hv hmem, smul_zero]

/-- **Every proper ideal lies in the right radical.** -/
theorem le_rightRadical {B : InvariantForm W} (hB : B.IsFullyInvariant) {I : Submodule ℂ 𝒱}
    (hI : W.IsIdeal I) (hv : W.vacuum ∉ I) : I ≤ SingVec.rightRadical B := by
  intro x hx
  rw [SingVec.mem_rightRadical]
  intro a
  have hatop : a ∈ ⨆ i : ℤ, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun a => B.form a x = 0) hatop ?_ ?_ ?_
  · intro q y hy
    exact form_eq_zero_of_mem_ideal_homog' hB hI hv hy hx
  · change B.form 0 x = 0
    simp
  · intro y y' hy hy'; rw [map_add, LinearMap.add_apply, hy, hy', add_zero]

/-! ## Li's theorem -/

/-- **Li's theorem** (Li, JPAA **96** (1994) 279–297, Thm 3.1/Cor 3.2; FHL §5.3):
for any fully invariant normalised bilinear form `B` on a VOA `W`,
**the radical of `B` is the maximal proper graded ideal**.

`≤`: the radical is an ideal and is proper because `(𝟙|𝟙) = 1 ≠ 0`.
`≥`: `le_leftRadical` applied to `maxGradedIdeal W`, which is a proper ideal.

CFT type — `𝒱₀ = ℂ𝟙` and `𝒱_{<0} = ⊥` — is built into `VertexOperatorAlgebra` here, so it is
not a hypothesis; and `𝟙 ≠ 0` follows from `Normalized`. -/
theorem leftRadical_eq_maxGradedIdeal {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) :
    InvariantForm.leftRadical B = QuotVOA.maxGradedIdeal W :=
  le_antisymm
    (QuotVOA.le_maxGradedIdeal' (InvariantForm.radical_isIdeal hB)
      (SingVec.vacuum_not_mem_leftRadical hn))
    (le_leftRadical hB (QuotVOA.maxGradedIdeal_isIdeal W)
      (QuotVOA.vacuum_not_mem_maxGradedIdeal W (vacuum_ne_zero_of_normalized hn)))

/-- **Li's theorem, right-radical form.** -/
theorem rightRadical_eq_maxGradedIdeal {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) :
    SingVec.rightRadical B = QuotVOA.maxGradedIdeal W :=
  le_antisymm
    (QuotVOA.le_maxGradedIdeal' (SingVec.rightRadical_isIdeal hB)
      (SingVec.vacuum_not_mem_rightRadical hn))
    (le_rightRadical hB (QuotVOA.maxGradedIdeal_isIdeal W)
      (QuotVOA.vacuum_not_mem_maxGradedIdeal W (vacuum_ne_zero_of_normalized hn)))

/-- The two radicals of a fully invariant normalised form agree — the radical-level shadow of
the symmetry of `B` (which is *not* proved in the repo; this consequence of it is). -/
theorem leftRadical_eq_rightRadical {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) :
    InvariantForm.leftRadical B = SingVec.rightRadical B := by
  rw [leftRadical_eq_maxGradedIdeal hB hn, rightRadical_eq_maxGradedIdeal hB hn]

/-- Membership form of Li's theorem. -/
theorem mem_maxGradedIdeal_iff {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) {x : 𝒱} :
    x ∈ QuotVOA.maxGradedIdeal W ↔ ∀ b : 𝒱, B.form x b = 0 := by
  rw [← leftRadical_eq_maxGradedIdeal hB hn, InvariantForm.leftRadical, LinearMap.mem_ker,
    LinearMap.ext_iff]
  simp only [LinearMap.zero_apply]

/-- **Simplicity ⟺ nondegeneracy** (Li, Cor 3.2; Gannon 5.1.11b).  Unlike
`InvariantForm.invariantForm_nondegenerate`, which derives nondegeneracy *from* simplicity,
this is an equivalence. -/
theorem isSimple_iff_leftRadical_eq_bot {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) :
    W.IsSimple ↔ InvariantForm.leftRadical B = ⊥ := by
  have hvac : W.vacuum ≠ 0 := vacuum_ne_zero_of_normalized hn
  have htne : (⊤ : Submodule ℂ 𝒱) ≠ ⊥ := by
    intro htb
    exact hvac (by simpa using (htb ▸ Submodule.mem_top : W.vacuum ∈ (⊥ : Submodule ℂ 𝒱)))
  rw [leftRadical_eq_maxGradedIdeal hB hn]
  constructor
  · intro hs
    rcases hs.2 _ (QuotVOA.maxGradedIdeal_isIdeal W) with h | h
    · exact h
    · exact absurd (h ▸ Submodule.mem_top)
        (QuotVOA.vacuum_not_mem_maxGradedIdeal W hvac)
  · intro h
    refine ⟨htne, fun J hJ => ?_⟩
    by_cases hvJ : W.vacuum ∈ J
    · exact Or.inr (QuotVOA.eq_top_of_vacuum_mem hJ hvJ)
    · exact Or.inl (le_bot_iff.mp (h ▸ QuotVOA.le_maxGradedIdeal' hJ hvJ))

/-! ## The level-by-level form — the point of the whole theorem

`maxGradedIdeal` is a supremum over a *set of submodules*; the Gram matrix of `B` on `𝒱ₙ` is a
finite matrix.  The next three statements say they are the same object in degree `n`, which is
what makes a Kac-determinant computation able to decide membership in `maxGradedIdeal`. -/

/-- **The level-`n` criterion.**  For homogeneous `x ∈ 𝒱ₙ`,
`x ∈ maxGradedIdeal W  ↔  x ⟂ 𝒱ₙ`.  Only the *finite-dimensional* pairing on `𝒱ₙ` is tested:
pairings against other degrees vanish for free by `InvariantForm.orthogonal_of_ne`. -/
theorem mem_maxGradedIdeal_iff_grading {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) {n : ℤ} {x : 𝒱} (hx : x ∈ W.grading n) :
    x ∈ QuotVOA.maxGradedIdeal W ↔ ∀ y ∈ W.grading n, B.form x y = 0 := by
  rw [mem_maxGradedIdeal_iff hB hn]
  constructor
  · intro h y _; exact h y
  · intro h b
    have hbtop : b ∈ ⨆ i : ℤ, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading (motive := fun b => B.form x b = 0) hbtop ?_ ?_ ?_
    · intro q y hy
      by_cases hq : n = q
      · subst hq; exact h y hy
      · exact InvariantForm.orthogonal_of_ne B hq hx hy
    · exact map_zero _
    · intro y y' hy hy'; rw [map_add, hy, hy', add_zero]

variable (B : InvariantForm W) in
/-- The **level-`n` Gram form**: `B` restricted to `𝒱ₙ × 𝒱ₙ`.  Its matrix in any basis of `𝒱ₙ`
is the level-`n` Gram matrix whose determinant the Kac formula computes. -/
def gradedForm (n : ℤ) : LinearMap.BilinForm ℂ (W.grading n) :=
  B.form.compl₁₂ (W.grading n).subtype (W.grading n).subtype

@[simp] theorem gradedForm_apply (B : InvariantForm W) (n : ℤ) (a b : W.grading n) :
    gradedForm B n a b = B.form (a : 𝒱) (b : 𝒱) := rfl

/-- **The degree-`n` part of `maxGradedIdeal` is the radical of the level-`n` Gram form.**
Stated as an equality of submodules of `𝒱ₙ`. -/
theorem ker_gradedForm {B : InvariantForm W} (hB : B.IsFullyInvariant) (hn : B.Normalized)
    (n : ℤ) :
    LinearMap.ker (gradedForm B n) = (QuotVOA.maxGradedIdeal W).comap (W.grading n).subtype := by
  ext a
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
    mem_maxGradedIdeal_iff_grading hB hn a.2, LinearMap.ext_iff]
  constructor
  · intro h y hy
    have := h ⟨y, hy⟩
    rwa [LinearMap.zero_apply, gradedForm_apply] at this
  · intro h y
    rw [LinearMap.zero_apply, gradedForm_apply]
    exact h (y : 𝒱) y.2

/-- **The same equality, pushed back into `𝒱`**: `maxGradedIdeal W ⊓ 𝒱ₙ` is the image of the
radical of the level-`n` Gram form.  A Gram determinant on `𝒱ₙ` therefore computes exactly the
degree-`n` piece of the maximal ideal — e.g. `maxGradedIdeal W ⊓ 𝒱ₙ = ⊥` iff that determinant
is nonzero (`𝒱ₙ` finite-dimensional). -/
theorem maxGradedIdeal_inf_grading {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) (n : ℤ) :
    QuotVOA.maxGradedIdeal W ⊓ W.grading n
      = (LinearMap.ker (gradedForm B n)).map (W.grading n).subtype := by
  rw [ker_gradedForm hB hn n]
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨hxI, hxn⟩
    exact ⟨⟨x, hxn⟩, hxI, rfl⟩
  · rintro ⟨⟨y, hy⟩, hmem, rfl⟩
    exact ⟨hmem, hy⟩

/-- **The Gram-determinant criterion, level by level.**  `maxGradedIdeal W` has nothing in
degree `n` exactly when the level-`n` Gram form is nondegenerate.  On a finite-dimensional `𝒱ₙ`
the right-hand side is `det ≠ 0` for the Gram matrix in any basis — so a Kac-determinant
computation decides the left-hand side. -/
theorem maxGradedIdeal_inf_grading_eq_bot_iff {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) (n : ℤ) :
    QuotVOA.maxGradedIdeal W ⊓ W.grading n = ⊥ ↔ LinearMap.ker (gradedForm B n) = ⊥ := by
  rw [maxGradedIdeal_inf_grading hB hn n]
  constructor
  · intro h
    refine eq_bot_iff.mpr fun a ha => ?_
    have hmem : (a : 𝒱) ∈
        (LinearMap.ker (gradedForm B n)).map (W.grading n).subtype := ⟨a, ha, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact Submodule.mem_bot _ |>.mpr (Subtype.ext hmem)
  · intro h; rw [h, Submodule.map_bot]

/-- The radical of a fully invariant normalised form is a **graded** submodule — immediate from
Li's theorem, since `maxGradedIdeal` is graded by construction. -/
theorem isGradedIdeal_leftRadical {B : InvariantForm W} (hB : B.IsFullyInvariant)
    (hn : B.Normalized) : QuotVOA.IsGradedIdeal W (InvariantForm.leftRadical B) := by
  rw [leftRadical_eq_maxGradedIdeal hB hn]
  exact QuotVOA.maxGradedIdeal_isGradedIdeal W

/-! ## Instantiation at the concrete canonical form

`Core.InvariantFormFHL2.canonicalInvariantForm hne hqp` is unconditionally fully invariant and
normalised under `hne : 𝟙 ≠ 0` and Li's `hqp : L₁𝒱₁ = 0`, so every statement above applies to
it with no further hypotheses. -/

section Canonical

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- **Li's theorem for the canonical invariant form.**  `rad (canonicalInvariantForm) =
maxGradedIdeal W`, under only `𝟙 ≠ 0` and `L₁𝒱₁ = 0`. -/
theorem leftRadical_canonical_eq_maxGradedIdeal (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) :
    InvariantForm.leftRadical (canonicalInvariantForm hne hqp) = QuotVOA.maxGradedIdeal W :=
  leftRadical_eq_maxGradedIdeal (canonicalInvariantForm_isFullyInvariant hne hqp)
    (canonicalInvariantForm_normalized hne hqp)

/-- Right-radical version for the canonical form. -/
theorem rightRadical_canonical_eq_maxGradedIdeal (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) :
    SingVec.rightRadical (canonicalInvariantForm hne hqp) = QuotVOA.maxGradedIdeal W :=
  rightRadical_eq_maxGradedIdeal (canonicalInvariantForm_isFullyInvariant hne hqp)
    (canonicalInvariantForm_normalized hne hqp)

/-- **Simplicity ⟺ nondegeneracy of the canonical form.** -/
theorem isSimple_iff_canonical_nondegenerate (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) :
    W.IsSimple ↔ InvariantForm.leftRadical (canonicalInvariantForm hne hqp) = ⊥ :=
  isSimple_iff_leftRadical_eq_bot (canonicalInvariantForm_isFullyInvariant hne hqp)
    (canonicalInvariantForm_normalized hne hqp)

/-- **Level-`n` criterion for the canonical form.**  For homogeneous `x ∈ 𝒱ₙ`,
`x ∈ maxGradedIdeal W ↔ (x|y) = 0` for every `y ∈ 𝒱ₙ`. -/
theorem mem_maxGradedIdeal_iff_grading_canonical (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {n : ℤ} {x : V} (hx : x ∈ W.grading n) :
    x ∈ QuotVOA.maxGradedIdeal W ↔
      ∀ y ∈ W.grading n, (canonicalInvariantForm hne hqp).form x y = 0 :=
  mem_maxGradedIdeal_iff_grading (canonicalInvariantForm_isFullyInvariant hne hqp)
    (canonicalInvariantForm_normalized hne hqp) hx

/-- **The degree-`n` part of `maxGradedIdeal` is the radical of the canonical Gram form
on `𝒱ₙ`.** -/
theorem maxGradedIdeal_inf_grading_canonical (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (n : ℤ) :
    QuotVOA.maxGradedIdeal W ⊓ W.grading n
      = (LinearMap.ker (gradedForm (canonicalInvariantForm hne hqp) n)).map
          (W.grading n).subtype :=
  maxGradedIdeal_inf_grading (canonicalInvariantForm_isFullyInvariant hne hqp)
    (canonicalInvariantForm_normalized hne hqp) n

/-- **Gram-determinant criterion for the canonical form.** -/
theorem maxGradedIdeal_inf_grading_eq_bot_iff_canonical (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (n : ℤ) :
    QuotVOA.maxGradedIdeal W ⊓ W.grading n = ⊥ ↔
      LinearMap.ker (gradedForm (canonicalInvariantForm hne hqp) n) = ⊥ :=
  maxGradedIdeal_inf_grading_eq_bot_iff (canonicalInvariantForm_isFullyInvariant hne hqp)
    (canonicalInvariantForm_normalized hne hqp) n

/-! ### Bridge to the level-`k` Shapovalov (top-mode) form

`Core.RigidityBridge.shapForm W hvac k ⟨a,b⟩ = ε(a₍₂ₖ₋₁₎b)` is the **top-mode** form, the one
whose Gram matrix the explicit computations of `Examples/LeeYangGram`,
`Examples/AffineSl2Singular`, … produce.  `RigidBridge.invariantForm_eq_shapForm` identifies it
with the canonical invariant form up to the sign `(−1)^k` — but **only on quasi-primary
vectors** (`L₁s = 0`), because the `e^{zL₁}` tower of the invariance identity collapses to its
`j = 0` term only there.  Composing that with Li's theorem gives the statement below, and
its quasi-primarity hypothesis is inherited from that limitation, not from Li's theorem.

⚠ Two cautions carried over from the sources, *not* removed here.  (i) The identification is
`B(s,y) = (−1)^k⟨s,y⟩ₖ`, so `shapForm` is the contravariant form only up to that sign, and
only on quasi-primaries.  (ii) `Examples/LeeYangGram.shapForm_leeYang_level4_eq_kac` (the claim
that the level-4 matrix is `21×` the textbook Kac matrix) holds **only at `c = −22/5` and
`c = 0`** and must not be extrapolated in `c`. -/

/-- **A quasi-primary vector lies in the maximal graded ideal iff it lies in the radical of
the level-`k` Shapovalov form.**  This is the sentence that lets a level-`k` Gram/Kac
determinant certify membership in `QuotVOA.maxGradedIdeal` — the connection that did not exist
before.  Hypothesis `hL1 : L₁s = 0` is automatic for singular vectors. -/
theorem mem_maxGradedIdeal_iff_mem_radBil_shapForm (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {k : ℤ} {s : V} (hs : s ∈ W.grading k)
    (hL1 : W.L 1 s = 0) :
    s ∈ QuotVOA.maxGradedIdeal W ↔
      (⟨s, hs⟩ : W.grading k) ∈ DefForm.radBil (RigidBridge.shapForm W hne k) :=
  (mem_maxGradedIdeal_iff_grading_canonical hne hqp hs).trans
    (RigidBridge.mem_radBil_iff_invariantForm hne hqp hs hL1).symm

/-- One-directional convenience form: a quasi-primary vector in the Shapovalov radical is in the
maximal graded ideal, hence dies in the simple quotient `W ⧸ maxGradedIdeal W`. -/
theorem mem_maxGradedIdeal_of_mem_radBil_shapForm (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {k : ℤ} {s : V} (hs : s ∈ W.grading k)
    (hL1 : W.L 1 s = 0)
    (hrad : (⟨s, hs⟩ : W.grading k) ∈ DefForm.radBil (RigidBridge.shapForm W hne k)) :
    s ∈ QuotVOA.maxGradedIdeal W :=
  (mem_maxGradedIdeal_iff_mem_radBil_shapForm hne hqp hs hL1).mpr hrad

end Canonical

end LiRadical

end VOA
