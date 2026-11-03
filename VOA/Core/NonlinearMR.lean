/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.NPExtension

/-!
# The full De Sole–Kac ideal `M(R)`, over the `NPExtension` interface

De Sole–Kac Definition 3.4 ([DK] = Comm. Math. Phys. **254** (2005) 659–694) sets

  `M(R) = span_ℂ { A ⊗ ((b⊗c - p(b,c)·c⊗b) ⊗ D - N(∫₋ᵀ⁰[b_λ c]dλ, D)) | b,c ∈ R, A,D ∈ T(R) }`.

`Core.NonlinearConformal` §7 could only build the `D = 1` slice (`MRbot`), because the
normally ordered product `N` on composites did not exist there.  With the `NPExtension`
interface of `Core.NPExtension`, the *full* generator can be written down:

  `relDF NP p q : B ↦ gv p * gv q * B - p(p,q)·(gv q * gv p * B) - N(∫₋ᵀ⁰[p_λ q]dλ, B)`,

linear in the `D`-slot, and `MRfullCar NP` is the span of its left multiples over basis
words.  At `B = 1` the generator is the old `rel` (`relDF_one`), so the whole §7–§8
quotient machinery of `Core.NonlinearConformal` (`UR`, `vacU`, `creHalf`, `wstU`, `aug`,
`GenFields`) applies to these quotients unchanged, through `NMIdeal.toMIdeal`.

## The left-ideal subtlety, honored

⚠ De Sole–Kac (and the review [DSK-rev] = Japan. J. Math. **1** (2006), §3) are explicit
that in the conformal case `M(R)` is only a **left** ideal of the associative algebra
`T(R)`: the quotient is *not* an associative algebra.  What the vertex structure needs is
closure under the **extended `N`/`P` actions on both sides**, which in [DK] is
Corollary 4.5 (its ten inclusions, source labels `b1`–`b10`) — proved there by an
induction that *uses the Jacobi axiom* (Lie conformal data).  Over the bare interface that closure can therefore only be
**stated**, as the `Prop` bundle `NPClosure`; proving it here would be both impossible
and precisely the naive-two-sidedness trap the `MIdeal` docstring warns against.

## Compatibility with the linear layer

For a **linear** datum (`OPEData.IsLinear`: every OPE value in `ℂ·1 ⊕ span gv`), `N`
degenerates to concatenation on the left arguments that actually occur (`N_linSub` —
an immediate consequence of [DK] (3.1)–(3.2): for `a ∈ R ⊕ ℂ1` the only instances of `N`
are `a ⊗ B`), and

  `MRfullCar_eq_MRtwoCar : MRfullCar NP = MRtwoCar D`,

reconciling this file with `Core.NonlinearVirasoro` §4: `MRtwo` really was `M(R)` for
linear data, and for linear data `MRfullCar` is independent of the choice of interface
(`MRfullCar_indep`).

⚠ **The chain to `ker PhiVir` is available but has NOT been performed.**  Both halves
exist — `MRfull_virasoro` here and `Examples.NonlinearVirasoroGenuine.MRtwo_eq_ker_PhiVir`
there — but no Lean declaration anywhere composes them, and nothing in the repository
imports this file except the `Core.lean` umbrella and the axiom probe.  The composite
`MRfullCar NP = LinearMap.ker (PhiVir c)` is therefore *prose*, not a theorem.
It cannot live here: `Core` may not import `Examples`.  Stating it requires a new
`Examples/` module (one `Eq.trans`); it is not claimed as an established result.
⚠ The theorem is **parametric in `NP`**: no `NPExtension` instance is constructed in the
library, so the Virasoro corollary `MRfull_virasoro` is conditional on an
interface term, as it must be.  No stub instance is
manufactured anywhere.

## Non-vacuity, graded

Under `OPEData.IsConformal` and the `NPGraded` mixin (a **named hypothesis**, pending
the [DK] recursion), every generator of `MRfullCar` is a sum of words of positive weight
(`MRfull_le_grPos`), so the augmentation kills the ideal (`aug_MRfull`) and the vacuum
survives the quotient (`vacU_ne_zero_MRfull`) — the graded upgrade of `aug_MRbot`, with
no PBW anywhere.

No `sorry`, no `admit`, no `native_decide`, no new axiom; `VOA.pbw` is not used.
-/

namespace VOA.NonlinearConformal

open Module (End)
open NPExtension

set_option maxRecDepth 4000

universe u

variable {ι : Type u}

/-! ## §1  The full Definition 3.4 generator -/

section RelDF

variable {D : OPEData ι} (NP : NPExtension D)

/-- **The full De Sole–Kac Definition 3.4 generator**, linear in the `D`-slot:

  `relDF NP p q B = p⊗q⊗B - p(p,q)·q⊗p⊗B - N(∫₋ᵀ⁰[p_λ q]dλ, B)`.

At `B = 1` this is the old `rel` (`relDF_one`); for `B` a basis word it is the honest
`D ≠ 1` generator that `Core.NonlinearConformal` §7 could not write down without `N`. -/
noncomputable def relDF (p q : GenIdx ι) : TR ι →ₗ[ℂ] TR ι where
  toFun B := gv p * gv q * B - koszul (D.par p.1) (D.par q.1) • (gv q * gv p * B)
    - NP.N (opeInt D p q) B
  map_add' B C := by
    rw [mul_add, mul_add, map_add, smul_add]
    abel
  map_smul' c B := by
    rw [RingHom.id_apply, mul_smul_comm, mul_smul_comm, map_smul, smul_sub, smul_sub,
      smul_comm (koszul (D.par p.1) (D.par q.1)) c]

/-- Unfolding `relDF`. -/
theorem relDF_apply (p q : GenIdx ι) (B : TR ι) :
    relDF NP p q B = gv p * gv q * B - koszul (D.par p.1) (D.par q.1) • (gv q * gv p * B)
      - NP.N (opeInt D p q) B := rfl

/-- The Definition 3.4 generator against a basis word — `relD p q w`. -/
noncomputable def relD (p q : GenIdx ι) (w : FreeMonoid (GenIdx ι)) : TR ι :=
  relDF NP p q (wbasis ι w)

/-- **The `D = 1` slice of the full generator is the old relation**: `N(X, 1) = X`
collapses the third term to `∫₋ᵀ⁰[p_λ q]dλ`.  This is the bridge through which the
entire §7–§8 quotient machinery of `Core.NonlinearConformal` applies unchanged. -/
theorem relDF_one (p q : GenIdx ι) : relDF NP p q (1 : TR ι) = rel D p q := by
  rw [relDF_apply, NP.N_one_right, mul_one, mul_one, rel]

/-- `relD` at the empty word is the old relation. -/
theorem relD_one (p q : GenIdx ι) : relD NP p q 1 = rel D p q := by
  rw [relD, wbasis_one, relDF_one]

/-- **`T` acts on the full generators by the Leibniz rule** — the generalization of
`Ttr_rel` that makes `MRfullCar` `T`-stable.  The proof consumes `Ttr_N` (the
`T`-derivation law of the interface) and `Ttr_opeInt`. -/
theorem Ttr_relDF (p q : GenIdx ι) (B : TR ι) :
    Ttr (relDF NP p q B)
      = ((p.2 : ℂ) + 1) • relDF NP (p.1, p.2 + 1) q B
        + ((q.2 : ℂ) + 1) • relDF NP p (q.1, q.2 + 1) B
        + relDF NP p q (Ttr B) := by
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  -- `T` on the two quadratic prefixes
  have hpref : ∀ a b : GenIdx ι, Ttr (gv a * gv b * B)
      = gv a * gv b * Ttr B
        + ((a.2 : ℂ) + 1) • (gv (a.1, a.2 + 1) * gv b * B)
        + ((b.2 : ℂ) + 1) • (gv a * gv (b.1, b.2 + 1) * B) := by
    intro a b
    rw [Ttr_mul, Ttr_mul, Ttr_gv, Ttr_gv, add_mul, smul_mul_assoc, smul_mul_assoc,
      mul_smul_comm, smul_mul_assoc]
    push_cast
    abel
  -- `T` on the `N` term
  have hN : Ttr (NP.N (opeInt D (i, k) (j, l)) B)
      = ((k : ℂ) + 1) • NP.N (opeInt D (i, k + 1) (j, l)) B
        + ((l : ℂ) + 1) • NP.N (opeInt D (i, k) (j, l + 1)) B
        + NP.N (opeInt D (i, k) (j, l)) (Ttr B) := by
    rw [NP.Ttr_N, ← Ttr_opeInt D (i, k) (j, l), map_add, map_smul, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  simp only [relDF_apply, map_sub, map_smul, hpref, hN]
  simp only [smul_sub, smul_add, smul_smul, mul_comm (koszul (D.par i) (D.par j))]
  abel

end RelDF

/-! ## §2  The span `MRfullCar` — the full `M(R)`, over the interface -/

section MRfull

variable {D : OPEData ι} (NP : NPExtension D)

/-- **The full De Sole–Kac `M(R)`**, over the interface: the span of the left
multiples of the Definition 3.4 generators, `A · relDF p q (wbasis w)`.
⚠ A **left** ideal only — see the module docstring. -/
noncomputable def MRfullCar : Submodule ℂ (TR ι) :=
  Submodule.span ℂ (Set.range
    (fun z : TR ι × GenIdx ι × GenIdx ι × FreeMonoid (GenIdx ι) =>
      z.1 * relDF NP z.2.1 z.2.2.1 (wbasis ι z.2.2.2)))

theorem mem_MRfullCar (A : TR ι) (p q : GenIdx ι) (w : FreeMonoid (GenIdx ι)) :
    A * relDF NP p q (wbasis ι w) ∈ MRfullCar NP :=
  Submodule.subset_span ⟨(A, p, q, w), rfl⟩

/-- The generator against an **arbitrary** second slot stays in the span: `relDF` is
linear in that slot and the words are a basis. -/
theorem mul_relDF_mem_MRfullCar (A : TR ι) (p q : GenIdx ι) (B : TR ι) :
    A * relDF NP p q B ∈ MRfullCar NP := by
  have hB : B ∈ Submodule.span ℂ (Set.range (wbasis ι)) := by
    rw [(wbasis ι).span_eq]; trivial
  induction hB using Submodule.span_induction with
  | mem z hz => obtain ⟨w, rfl⟩ := hz; exact mem_MRfullCar NP A p q w
  | zero => rw [map_zero, mul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add, mul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
      rw [map_smul, mul_smul_comm]; exact Submodule.smul_mem _ c ha

theorem relDF_mem_MRfullCar (p q : GenIdx ι) (B : TR ι) :
    relDF NP p q B ∈ MRfullCar NP := by
  have h := mul_relDF_mem_MRfullCar NP 1 p q B
  rwa [one_mul] at h

/-- `MRfullCar` is closed under multiplication on the left. -/
theorem MRfullCar_left (A x : TR ι) (hx : x ∈ MRfullCar NP) : A * x ∈ MRfullCar NP := by
  rw [MRfullCar] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨B, p, q, w⟩, rfl⟩ := hz
      change A * (B * relDF NP p q (wbasis ι w)) ∈ MRfullCar NP
      rw [← mul_assoc]
      exact mem_MRfullCar NP (A * B) p q w
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy

/-- **`MRfullCar` is `T`-stable** — `Ttr_relDF` consumed, with the `relDF p q (Ttr B)`
term handled by linearity of the second slot (`mul_relDF_mem_MRfullCar`). -/
theorem Ttr_mem_MRfullCar : ∀ x ∈ MRfullCar NP, Ttr x ∈ MRfullCar NP := by
  intro x hx
  rw [MRfullCar] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨B, p, q, w⟩, rfl⟩ := hz
      change Ttr (B * relDF NP p q (wbasis ι w)) ∈ MRfullCar NP
      rw [Ttr_mul, Ttr_relDF]
      refine Submodule.add_mem _ ?_ (mem_MRfullCar NP (Ttr B) p q w)
      rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm]
      refine Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ (mem_MRfullCar NP B _ q w))
        (Submodule.smul_mem _ _ (mem_MRfullCar NP B p _ w))) ?_
      exact mul_relDF_mem_MRfullCar NP B p q (Ttr (wbasis ι w))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

end MRfull

/-! ## §3  Admissible ideals for the full relations: `NMIdeal` -/

section NMIdealSection

variable {D : OPEData ι}

/-- An **admissible relation ideal for the full De Sole–Kac generators**: the
generalization of `MIdeal` in which `rel_mem` is upgraded to membership of every
`D`-slice generator `relDF p q (wbasis w)`.  Left-closure and `T`-stability are
unchanged — the ideal is still only a *left* ideal. -/
structure NMIdeal (D : OPEData ι) (NP : NPExtension D) where
  /-- the underlying `ℂ`-subspace -/
  car : Submodule ℂ (TR ι)
  /-- closed under multiplication on the left — and only on the left -/
  left : ∀ (A x : TR ι), x ∈ car → A * x ∈ car
  /-- stable under the translation operator -/
  Tstable : ∀ x ∈ car, Ttr x ∈ car
  /-- contains every full Definition 3.4 generator -/
  relD_mem : ∀ (p q : GenIdx ι) (w : FreeMonoid (GenIdx ι)),
    relDF NP p q (wbasis ι w) ∈ car

variable {NP : NPExtension D}

/-- **The key reuse point**: every `NMIdeal` is an `MIdeal` (via `relDF_one`), so the
entire quotient machinery of `Core.NonlinearConformal` §§7–11 — `UR`, `vacU`, `TrU`,
`creHalf`, `wstU_span`, `aug`, `vacU_ne_zero_of_aug`, and the `GenFields` contract —
applies to these quotients with no change at all. -/
def NMIdeal.toMIdeal (M : NMIdeal D NP) : MIdeal D where
  car := M.car
  left := M.left
  Tstable := M.Tstable
  rel_mem := fun p q => by
    have h := M.relD_mem p q 1
    rwa [wbasis_one, relDF_one] at h

/-- **The smallest admissible full-relation ideal** — De Sole–Kac's `M(R)` itself,
over the interface. -/
noncomputable def MRfull (NP : NPExtension D) : NMIdeal D NP where
  car := MRfullCar NP
  left := MRfullCar_left NP
  Tstable := Ttr_mem_MRfullCar NP
  relD_mem := fun p q w => relDF_mem_MRfullCar NP p q (wbasis ι w)

/-- `MRfull` is contained in every admissible full-relation ideal. -/
theorem MRfull_le (M : NMIdeal D NP) : (MRfull NP).car ≤ M.car := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨⟨A, p, q, w⟩, rfl⟩
  exact M.left A _ (M.relD_mem p q w)

/-- The `D = 1` slice sits inside the full ideal: `MRbot ⊆ M(R)`, with the full
`M(R)` constructed over the interface. -/
theorem MRbot_le_MRfull (NP : NPExtension D) : (MRbot D).car ≤ MRfullCar NP :=
  MRbot_le (MRfull NP).toMIdeal

end NMIdealSection

/-! ## §4  The [DK] Corollary 4.5 closure — STATED, not proved

[DK] Corollary 4.5 (its ten inclusions, source labels `b1`–`b10`): `M(R)` is closed
under the extended
`N` and `P_λ` actions **on both sides** (with graded-slice bounds), which is what the
vertex algebra structure on the quotient actually needs in place of two-sidedness.
⚠ **The [DK] proof is an induction that uses the Jacobi axiom** — it is a theorem about
non-linear *Lie* conformal algebras, not a formal consequence of the `NPExtension`
interface.  Here it is therefore a `Prop` bundle to be consumed as a named
hypothesis; any "proof" from the bare interface would be the naive-two-sidedness trap.
It is expected to be discharged for Lie data (skewsymmetry + Jacobi) by a separate argument,
never before. -/

/-- ⚠ **Stated only** — see the section docstring.  Closure of an admissible ideal
under the extended `N`/`P` actions on both sides ([DK] Corollary 4.5). -/
structure NPClosure {D : OPEData ι} (NP : NPExtension D) (M : NMIdeal D NP) : Prop where
  /-- closure under `N` in the right slot -/
  nRightClosed : ∀ (A : TR ι) {x : TR ι}, x ∈ M.car → NP.N A x ∈ M.car
  /-- closure under `N` in the left slot -/
  nLeftClosed : ∀ (A : TR ι) {x : TR ι}, x ∈ M.car → NP.N x A ∈ M.car
  /-- closure under every slice of `P` in the right slot -/
  pRightClosed : ∀ (A : TR ι) (n : ℕ) {x : TR ι}, x ∈ M.car → NP.P A x n ∈ M.car
  /-- closure under every slice of `P` in the left slot -/
  pLeftClosed : ∀ (A : TR ι) (n : ℕ) {x : TR ι}, x ∈ M.car → NP.P x A n ∈ M.car

/-! ## §5  The graded guard: `aug` kills `MRfullCar`

Under `IsConformal` (so `∫₋ᵀ⁰[p_λ q]dλ` is exactly homogeneous of the positive weight
`Δp + Δq`, `opeInt_mem_gr`) and the `NPGraded` mixin (a named hypothesis, pending the [DK] recursion),
every generator of `MRfullCar` lies in the span `grPos` of the positive-weight words, so
the augmentation kills the whole ideal and the vacuum survives — `aug_MRbot`, upgraded
to the full `M(R)`. -/

section Graded

variable {D : OPEData ι} (NP : NPExtension D)

/-- Left multiplication by a generator lands in the positive-weight span, whatever the
other factor: every resulting word contains the letter `p`, of positive weight. -/
theorem gv_mul_mem_grPos {wt : ι → ℕ} (hpos : ∀ i, 0 < wt i) (p : GenIdx ι) (y : TR ι) :
    gv p * y ∈ grPos wt := by
  have hy : y ∈ Submodule.span ℂ (Set.range (wbasis ι)) := by
    rw [(wbasis ι).span_eq]; trivial
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      rw [gv, ← wbasis_mul]
      refine Submodule.subset_span ⟨FreeMonoid.of p * w, ?_, rfl⟩
      simp only [Set.mem_setOf_eq, wtWord_mul, wtWord_of, wtIdx]
      have := hpos p.1
      omega
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha

/-- Left multiplication preserves the positive-weight span: a word times a
positive-weight word has positive weight. -/
theorem mul_mem_grPos {wt : ι → ℕ} (A : TR ι) {x : TR ι} (hx : x ∈ grPos wt) :
    A * x ∈ grPos wt := by
  rw [grPos] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      have hA : A ∈ Submodule.span ℂ (Set.range (wbasis ι)) := by
        rw [(wbasis ι).span_eq]; trivial
      induction hA using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨v, rfl⟩ := hy
          rw [← wbasis_mul]
          refine Submodule.subset_span ⟨v * w, ?_, rfl⟩
          simp only [Set.mem_setOf_eq, wtWord_mul]
          omega
      | zero => rw [zero_mul]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha

/-- Under `IsConformal` and `NPGraded`, every full generator is a sum of words of
positive weight.  The `N` term is where the two hypotheses are consumed: the integral is
exactly homogeneous of weight `Δp + Δq > 0`, and `N` preserves gradedness. -/
theorem relDF_mem_grPos (hC : D.IsConformal) (hg : NPGraded NP) (p q : GenIdx ι)
    (B : TR ι) : relDF NP p q B ∈ grPos D.wt := by
  rw [relDF_apply]
  refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
  · rw [mul_assoc]
    exact gv_mul_mem_grPos D.wt_pos p (gv q * B)
  · exact Submodule.smul_mem _ _ (by rw [mul_assoc]; exact gv_mul_mem_grPos D.wt_pos q _)
  · refine N_mem_grPos_left hg B ?_
    exact gr_le_grPos (by have h1 := D.wt_pos p.1; simp only [wtIdx]; omega)
      (opeInt_mem_gr hC p q)

/-- **The full ideal lies in the positive-weight span** (conformal datum, graded
interface). -/
theorem MRfull_le_grPos (hC : D.IsConformal) (hg : NPGraded NP) :
    MRfullCar NP ≤ grPos D.wt := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨⟨A, p, q, w⟩, rfl⟩
  exact mul_mem_grPos A (relDF_mem_grPos NP hC hg p q (wbasis ι w))

/-- **The augmentation kills the full `M(R)`** — the graded upgrade of `aug_MRbot`,
conditional on the `NPGraded` named hypothesis. -/
theorem aug_MRfull (hC : D.IsConformal) (hg : NPGraded NP) :
    ∀ x ∈ MRfullCar NP, aug x = 0 :=
  fun x hx => aug_grPos x (MRfull_le_grPos NP hC hg hx)

/-- **The vacuum survives the quotient by the full `M(R)`** — no PBW, no model. -/
theorem vacU_ne_zero_MRfull (hC : D.IsConformal) (hg : NPGraded NP) :
    vacU (MRfull NP).toMIdeal ≠ 0 :=
  vacU_ne_zero_of_aug (MRfull NP).toMIdeal (aug_MRfull NP hC hg)

end Graded

/-! ## §6  The linear-compatibility theorem: `MRfullCar = MRtwoCar`

`Core.NonlinearVirasoro` §4 argued in prose that for a linear datum the two-sided ideal
`MRtwo` *is* De Sole–Kac's `M(R)`.  With the interface in hand that argument becomes a
theorem.  The hypothesis `OPEData.IsLinear` is exactly the §4 docstring's condition:
every OPE value lies in `ℂ·1 ⊕ span (gv)`. -/

section Linear

/-- The subspace `ℂ·1 ⊕ span (gv)` of `T(R)`: scalars plus single letters.  A datum
whose OPE values all lie here is *linear* — no genuine normally ordered products. -/
noncomputable def linSub (ι : Type u) : Submodule ℂ (TR ι) :=
  Submodule.span ℂ (insert (1 : TR ι) (Set.range gv))

theorem one_mem_linSub : (1 : TR ι) ∈ linSub ι :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem gv_mem_linSub (p : GenIdx ι) : gv p ∈ linSub ι :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨p, rfl⟩)

/-- `T` preserves `ℂ·1 ⊕ span (gv)`: it kills the unit and shifts letters to letters. -/
theorem Ttr_mem_linSub {x : TR ι} (hx : x ∈ linSub ι) : Ttr x ∈ linSub ι := by
  rw [linSub] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      rcases Set.mem_insert_iff.mp hz with rfl | ⟨p, rfl⟩
      · rw [Ttr_one]; exact Submodule.zero_mem _
      · rw [Ttr_gv]; exact Submodule.smul_mem _ _ (gv_mem_linSub _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem Ttr_pow_mem_linSub (m : ℕ) {x : TR ι} (hx : x ∈ linSub ι) :
    ((Ttr : End ℂ (TR ι)) ^ m) x ∈ linSub ι := by
  induction m with
  | zero => exact hx
  | succ m ih => rw [Ttr_pow_succ_left]; exact Ttr_mem_linSub ih

/-- **A linear OPE datum**: every singular-OPE value is a scalar plus a combination of
single letters — the exact hypothesis of the `Core.NonlinearVirasoro` §4 docstring. -/
def OPEData.IsLinear (D : OPEData ι) : Prop := ∀ i j (n : ℕ), D.ope i j n ∈ linSub ι

theorem Lstep_mem_linSub {f : ℕ → TR ι} (hf : ∀ n, f n ∈ linSub ι) (n : ℕ) :
    Lstep f n ∈ linSub ι := by
  change -((n : ℂ)) • f (n - 1) ∈ linSub ι
  exact Submodule.smul_mem _ _ (hf (n - 1))

theorem Rstep_mem_linSub {f : ℕ → TR ι} (hf : ∀ n, f n ∈ linSub ι) (n : ℕ) :
    Rstep f n ∈ linSub ι := by
  change Ttr (f n) + ((n : ℂ)) • f (n - 1) ∈ linSub ι
  exact Submodule.add_mem _ (Ttr_mem_linSub (hf n)) (Submodule.smul_mem _ _ (hf (n - 1)))

theorem Lstep_iterate_mem_linSub :
    ∀ (k : ℕ) {f : ℕ → TR ι}, (∀ n, f n ∈ linSub ι) → ∀ n, Lstep^[k] f n ∈ linSub ι := by
  intro k
  induction k with
  | zero => intro f hf n; exact hf n
  | succ k ih =>
      intro f hf n
      rw [Function.iterate_succ_apply]
      exact ih (fun m => Lstep_mem_linSub hf m) n

theorem Rstep_iterate_mem_linSub :
    ∀ (l : ℕ) {f : ℕ → TR ι}, (∀ n, f n ∈ linSub ι) → ∀ n, Rstep^[l] f n ∈ linSub ι := by
  intro l
  induction l with
  | zero => intro f hf n; exact hf n
  | succ l ih =>
      intro f hf n
      rw [Function.iterate_succ_apply]
      exact ih (fun m => Rstep_mem_linSub hf m) n

variable {D : OPEData ι}

/-- Linearity propagates from the OPE table to the whole extended bracket. -/
theorem brk_mem_linSub (hD : D.IsLinear) (p q : GenIdx ι) (n : ℕ) :
    brk D p q n ∈ linSub ι := by
  rw [brk]
  exact Submodule.smul_mem _ _
    (Lstep_iterate_mem_linSub p.2 (Rstep_iterate_mem_linSub q.2 (hD p.1 q.1)) n)

/-- Linearity propagates to the `∫₋ᵀ⁰` of the singular OPE. -/
theorem opeInt_mem_linSub (hD : D.IsLinear) (p q : GenIdx ι) :
    opeInt D p q ∈ linSub ι := by
  rw [opeInt]
  refine Submodule.sum_mem _ (fun n _ => ?_)
  exact Submodule.smul_mem _ _ (Ttr_pow_mem_linSub (n + 1) (brk_mem_linSub hD p q n))

/-- **The collapse of `N` on linear arguments**: for `X ∈ ℂ·1 ⊕ span (gv)`,
`N(X, B) = X · B` — plain concatenation.  This is an immediate consequence of [DK]
(3.1)–(3.2) — for `a ∈ R ⊕ ℂ1` the only instances of `N` are `a ⊗ B` — and it is the
regression check that
the interface laws `N_one_left`/`N_gv` degenerate correctly on the linear layer. -/
theorem N_linSub (NP : NPExtension D) {X : TR ι} (hX : X ∈ linSub ι) (B : TR ι) :
    NP.N X B = X * B := by
  rw [linSub] at hX
  induction hX using Submodule.span_induction with
  | mem z hz =>
      rcases Set.mem_insert_iff.mp hz with rfl | ⟨p, rfl⟩
      · rw [NP.N_one_left, one_mul]
      · rw [NP.N_gv]
  | zero =>
      rw [map_zero, zero_mul]
      rfl
  | add a b _ _ ha hb =>
      rw [map_add, LinearMap.add_apply, ha, hb, add_mul]
  | smul c a _ ha =>
      rw [map_smul, LinearMap.smul_apply, ha, smul_mul_assoc]

/-- **For a linear datum the full generator collapses to `rel · B`.**  The left
argument of `N` inside `relDF` is always `∫₋ᵀ⁰[p_λ q]dλ`, which linearity places in
`ℂ·1 ⊕ span (gv)` — so the quasi-associativity corrections for composite left arguments
never arise (W8(vi) never bites in this theorem). -/
theorem relDF_linear (hD : D.IsLinear) (NP : NPExtension D) (p q : GenIdx ι) (B : TR ι) :
    relDF NP p q B = rel D p q * B := by
  rw [relDF_apply, N_linSub NP (opeInt_mem_linSub hD p q), rel, sub_mul, sub_mul,
    smul_mul_assoc, mul_assoc, mul_assoc]

/-- **The compatibility theorem**: for a linear OPE datum the full De Sole–Kac ideal
over *any* interface term is the two-sided ideal `MRtwoCar` of
`Core.NonlinearVirasoro` §4.  This is what would reconcile the `NPExtension` layer with the
linear Virasoro presentation: `Examples.NonlinearVirasoroGenuine` (which proves
`MRtwoCar = ker PhiVir` and the genuine presentation equivalence) is then the linear
instance of the new layer, untouched — though that composition is not performed in Lean
anywhere (module header).

⚠ **Parametric in `NP`, and that is the whole caveat.**  No `NPExtension` is inhabited,
so this is a conditional whose antecedent the [DK] recursion must supply; as a Lean proposition
it is vacuously true, and it becomes evidence that the nonlinear layer *generalizes*
the linear one only once an instance is constructed.  What is checkable is that neither side is
rigged (`MRtwoCar` is defined independently in `Core.NonlinearVirasoro`; `MRfullCar` is a left-multiple span
built from `NP.N`), that the hypothesis `D.IsLinear` is real and discharged for the real
datum (`virasoroOPE_isLinear`), and that the proof consumes only the interface fields
`N_one_left`/`N_gv` through `N_linSub`. -/
theorem MRfullCar_eq_MRtwoCar (hD : D.IsLinear) (NP : NPExtension D) :
    MRfullCar NP = MRtwoCar D := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨⟨A, p, q, w⟩, rfl⟩
    change A * relDF NP p q (wbasis ι w) ∈ MRtwoCar D
    rw [relDF_linear hD NP, ← mul_assoc]
    exact mem_MRtwoCar D A p q (wbasis ι w)
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨⟨A, p, q, B⟩, rfl⟩
    change A * rel D p q * B ∈ MRfullCar NP
    have hB : B ∈ Submodule.span ℂ (Set.range (wbasis ι)) := by
      rw [(wbasis ι).span_eq]; trivial
    induction hB using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨w, rfl⟩ := hz
        rw [mul_assoc, ← relDF_linear hD NP]
        exact mem_MRfullCar NP A p q w
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha

/-- For a linear datum, `MRfullCar` does not depend on the choice of interface term —
the interface-level shadow of the [DK] uniqueness. -/
theorem MRfullCar_indep (hD : D.IsLinear) (NP NP' : NPExtension D) :
    MRfullCar NP = MRfullCar NP' := by
  rw [MRfullCar_eq_MRtwoCar hD NP, MRfullCar_eq_MRtwoCar hD NP']

/-- **`virasoroOPE` is linear**: read off the table — `TL`, `2L`, `(c/2)·1`, `0`. -/
theorem virasoroOPE_isLinear (c : ℂ) : (virasoroOPE c).IsLinear := by
  intro i j n
  rw [virasoro_ope_eq]
  split_ifs with h0 h1 h3
  · exact gv_mem_linSub _
  · exact Submodule.smul_mem _ _ (gv_mem_linSub _)
  · exact Submodule.smul_mem _ _ one_mem_linSub
  · exact Submodule.zero_mem _

/-- **The Virasoro instance of the compatibility theorem.**  Composing this with
`Examples.NonlinearVirasoroGenuine.MRtwo_eq_ker_PhiVir` *would* exhibit `MRfullCar NP` as
`ker PhiVir`, and `virasoro_presentation_equivalence_genuine` as the linear instance of
the presentation layer.  ⚠ That composition is **not** performed anywhere in the
repository (see the module header): `Core` cannot import `Examples`, so it needs a new
`Examples/` module.  ⚠ Also conditional on an interface term `NP` — no `NPExtension`
instance is constructed anywhere in the library. -/
theorem MRfull_virasoro (c : ℂ) (NP : NPExtension (virasoroOPE c)) :
    MRfullCar NP = MRtwoCar (virasoroOPE c) :=
  MRfullCar_eq_MRtwoCar (virasoroOPE_isLinear c) NP

end Linear

end VOA.NonlinearConformal
