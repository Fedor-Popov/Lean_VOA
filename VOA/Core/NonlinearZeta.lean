/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.NonlinearVirasoro

/-!
# The De Sole–Kac ζ-filtration on `T(R)`, with `deg T = 0`

De Sole–Kac, *Freely generated vertex algebras and non-linear Lie conformal algebras*,
Comm. Math. Phys. **254** (2005) 659–694 [DK], run their entire Lemma 3.2 recursion on a
filtration of `T(R)` in which **the translation operator has degree zero**: `R` is
`Γ'₊`-graded by `ℂ[T]`-*submodules* (their Definition 3.1), so the degree of `Tᵏaⁱ/k!` is
the degree of `aⁱ`, independent of `k`.  The library's conformal-weight filtration `filt`
(`Core.NonlinearConformal` §2) gives `T` degree `+1` (`Ttr_mem_filt`) — a recursion on
`filt` degree therefore cannot terminate, because the recursion terms
`N(∫₀ᵀdλ a, P_λ(B,C))` raise conformal weight without bound while preserving ζ.
Both [DK] (in Example 6.2) and the review De Sole–Kac, Japan. J. Math. **1** (2006),
§3 [DSK-rev] stress that the two devices must be kept separate.  This file adds the
missing device.

## Main definitions and results

* `zwtIdx`, `zwtWord`, `zfilt` — the ζ-weight of a basis letter (`ζ(Tᵏaⁱ/k!) = ζ(aⁱ)`,
  the `T`-power is **ignored**), of a word, and the induced `ℤ`-indexed filtration of
  `T(R)`, mirroring `wtIdx`/`wtWord`/`filt` verbatim.
* `Ttr_mem_zfilt` — **`T` has ζ-degree zero**: `Ttr` preserves every `zfilt d`.  This is
  the property that makes the [DK] induction terminate, and it is exactly where `zfilt`
  and `filt` part ways.
* `filt_le_zfilt` — pointwise on words `ζ ≤ Δ`, so the weight filtration refines the
  ζ-filtration degree by degree.
* `ope_mem_zfilt`, `brk_mem_zfilt`, `opeInt_mem_zfilt` — **the L1 axiom implies the DSK
  grading condition** (DK Example 6.2): the existing `OPEData.ope_wt` inequality already
  places `aⁱ₍ₙ₎aʲ` in `zfilt (ζᵢ + ζⱼ - 1)`, which for the grading monoid `ℕ` *is* De
  Sole–Kac's `T_{(ζ₁+ζ₂)₋}(R)`, i.e. the strict decrease `Δ([a_λ b]) < Δa + Δb` of their
  Definition 3.1(2).  **No new axiom on `OPEData` is needed**; L1 data feeds the L2
  machinery automatically.  The divided-power cases (`brk`, `opeInt`) are precisely where
  `Ttr_mem_zfilt` is consumed.
* `Ttr_pow_mem_gr`, `brk_mem_gr`, `opeInt_mem_gr`, `rel_mem_gr` — the exact-weight
  (`gr`) upgrades of the `filt` toolkit of `Core.NonlinearConformal` §5–§7, available
  under `OPEData.IsConformal`.  `rel_mem_gr` generalizes `virasoro_rel_mem_gr` to every
  conformal datum: the relation is homogeneous of weight `Δp + Δq`.
* `aug_gr_pos`, `grPos`, `aug_grPos`, `Ttr_mem_grPos` — the augmentation kills every
  homogeneous element of positive weight; `grPos` is the span of the positive-weight
  words, and `T` maps *all* of `T(R)` into it.  This is the engine of the graded
  vacuum-survival guard of `Core.VAPresentation`.
* `grProj`, `grProj_wbasis`, `grProj_mem_gr`, `grProj_eq_self_of_mem`,
  `grProj_eq_zero_of_mem_of_ne`, `sum_grProj_of_mem_filt`, `exists_sum_grProj`,
  `mem_grPos_iff` — the graded projections, from the coordinates of the Mathlib basis
  `wbasis`: every element of `T(R)` is a *finite* sum of its homogeneous components, and
  membership in `grPos` is exactly the vanishing of the weight-`0` component.  Scoped to
  what the vacuum-survival guard consumes.

## Where the strictness comes from, and what it is not

The strict decrease is **not** bought by positivity of the weights: the conclusion of
`ope_mem_zfilt` carries a literal `- 1` and the filtration index is `ℤ`, so
`ζᵢ + ζⱼ - 1 < ζᵢ + ζⱼ` holds outright.  What `OPEData.wt_pos` buys is *well-foundedness*
of the eventual [DK] recursive descent — every nonempty word has `ζ ≥ 1`, and `zfilt_neg` makes
negative degrees `⊥`, so the recursion bottoms out.  Both premises hold; neither is doing
the other's job.

⚠ **Scope of "no new axiom".**  What is derived here is the [DK] Definition 3.1(2)
condition **on `R`**, for the L1 bracket.  The corresponding strict decrease for the
*extended* bracket on all of `T(R)` ([DK] (3.8)) is an **assumed** field of the `NPExtension`
interface (`NPExtension.P_zfilt`), as it must be: in [DK] it is a conclusion of Lemma 3.2,
not a hypothesis.  "No new axiom on `OPEData`" is a statement about `R`, not about `T(R)`.

## What this file does *not* do

Nothing here touches `OPEData`, `MIdeal`, or any quotient; no Lemma 3.2 recursion is
performed (that is the [DK] existence theorem, not formalised in this library).  The file is pure bookkeeping over
`Core.NonlinearConformal` and `Core.NonlinearVirasoro`.

⚠ **Nothing in the interface layer depends on this file's ζ-results.**  Outside this module, `zfilt`
occurs *only* inside the two interface fields `NPExtension.N_zfilt` and
`NPExtension.P_zfilt`, and neither of those fields is consumed by any proof in the library.
Everything proved here is unconditional, correct, and the right list of obligations for the
[DK] existence recursion — but it is not load-bearing for the `NPExtension`, `M(R)` and
presentation layers, and must not be read as having done work for them.  (The `gr`/`grPos`/`grProj` half of the file *is* consumed
downstream, by the vacuum-survival guards; the `zfilt` half is not.)

No `sorry`, no `admit`, no `native_decide`, no new axiom; `VOA.pbw` is not used.
-/

namespace VOA.NonlinearConformal

open Module (End)

set_option maxRecDepth 4000

universe u

variable {ι : Type u}

/-! ## §1  The ζ-weight and the ζ-filtration

The mirror of `Core.NonlinearConformal` §2, with the single change that a letter `(i,k)`
— the divided power `Tᵏaⁱ/k!` — contributes `ζ(aⁱ) = wt i`, not `wt i + k`. -/

section Zeta
variable (wt : ι → ℕ)

/-- The ζ-weight of a basis letter of `R`: `ζ(Tᵏaⁱ/k!) = ζ(aⁱ)`.  The `T`-power is
**ignored** — this is De Sole–Kac's grading of `R` by `ℂ[T]`-submodules. -/
def zwtIdx : GenIdx ι → ℕ := fun p => wt p.1

/-- The ζ-weight of a word of `T(R)` — the sum of the ζ-weights of its letters. -/
def zwtWord : FreeMonoid (GenIdx ι) → ℕ := fun w => (w.toList.map (zwtIdx wt)).sum

/-- The ζ-weight of a one-letter word. -/
theorem zwtWord_of (p : GenIdx ι) : zwtWord wt (FreeMonoid.of p) = zwtIdx wt p := by
  change ((FreeMonoid.of p).toList.map (zwtIdx wt)).sum = zwtIdx wt p
  rw [show (FreeMonoid.of p).toList = [p] from rfl, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

/-- The ζ-weight of the empty word. -/
theorem zwtWord_one : zwtWord wt (1 : FreeMonoid (GenIdx ι)) = 0 := rfl

/-- ζ-weights add along the product of words. -/
theorem zwtWord_mul (v w : FreeMonoid (GenIdx ι)) :
    zwtWord wt (v * w) = zwtWord wt v + zwtWord wt w := by
  change (((v * w).toList).map (zwtIdx wt)).sum = _
  rw [show (v * w).toList = v.toList ++ w.toList from rfl, List.map_append, List.sum_append]
  rfl

/-- Pointwise on words, `ζ ≤ Δ`: the ζ-weight is bounded by the conformal weight,
because each letter drops its `T`-power. -/
theorem zwtWord_le_wtWord (w : FreeMonoid (GenIdx ι)) : zwtWord wt w ≤ wtWord wt w := by
  change ((w.toList).map (zwtIdx wt)).sum ≤ ((w.toList).map (wtIdx wt)).sum
  induction w.toList with
  | nil => simp
  | cons p l ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      have hp : zwtIdx wt p ≤ wtIdx wt p := by
        simp only [zwtIdx, wtIdx]; omega
      omega

/-- The **ζ-filtration** of `T(R)`, indexed by `ℤ` like `filt`, so that negative bounds
give `⊥` and `omega` arguments transfer. -/
noncomputable def zfilt (d : ℤ) : Submodule ℂ (TR ι) :=
  Submodule.span ℂ (wbasis ι '' {w | ((zwtWord wt w : ℤ)) ≤ d})

/-- Below `0` the ζ-filtration is trivial. -/
theorem zfilt_neg {d : ℤ} (hd : d < 0) : zfilt wt d = (⊥ : Submodule ℂ (TR ι)) := by
  rw [zfilt, Submodule.span_eq_bot]
  rintro x ⟨w, hw, rfl⟩
  simp only [Set.mem_setOf_eq] at hw
  exact absurd (hw.trans_lt hd) (by omega)

/-- The ζ-filtration is monotone. -/
theorem zfilt_mono {d e : ℤ} (h : d ≤ e) : zfilt wt d ≤ zfilt wt e := by
  rw [zfilt, zfilt]
  refine Submodule.span_mono ?_
  rintro x ⟨w, hw, rfl⟩
  exact ⟨w, le_trans hw h, rfl⟩

/-- A word of ζ-weight at most `d` lies in `zfilt d`. -/
theorem wbasis_mem_zfilt {w : FreeMonoid (GenIdx ι)} {d : ℤ} (h : (zwtWord wt w : ℤ) ≤ d) :
    wbasis ι w ∈ zfilt wt d :=
  Submodule.subset_span ⟨w, h, rfl⟩

/-- A generator of ζ-weight at most `d` lies in `zfilt d` — for **any** `T`-power. -/
theorem gv_mem_zfilt {p : GenIdx ι} {d : ℤ} (h : (zwtIdx wt p : ℤ) ≤ d) :
    gv p ∈ zfilt wt d := by
  refine wbasis_mem_zfilt wt ?_
  rw [zwtWord_of]
  exact h

/-- The unit word has ζ-weight `0`. -/
theorem one_mem_zfilt {d : ℤ} (h : 0 ≤ d) : (1 : TR ι) ∈ zfilt wt d := by
  rw [← wbasis_one]
  refine wbasis_mem_zfilt wt ?_
  rw [zwtWord_one]
  exact_mod_cast h

/-- Multiplying by a generator shifts the ζ-filtration by that generator's ζ-weight. -/
theorem gv_mul_mem_zfilt (p : GenIdx ι) {e : ℤ} {y : TR ι} (hy : y ∈ zfilt wt e) :
    gv p * y ∈ zfilt wt ((zwtIdx wt p : ℤ) + e) := by
  rw [zfilt] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      refine Submodule.subset_span ⟨FreeMonoid.of p * w, ?_, ?_⟩
      · simp only [Set.mem_setOf_eq, zwtWord_mul, zwtWord_of]
        push_cast
        omega
      · rw [wbasis_mul, ← gv]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha

/-- **The weight filtration refines the ζ-filtration degree by degree**: every word of
conformal weight `≤ d` has ζ-weight `≤ d`. -/
theorem filt_le_zfilt (d : ℤ) : filt wt d ≤ zfilt wt d := by
  rw [filt]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨w, hw, rfl⟩
  simp only [Set.mem_setOf_eq] at hw
  refine wbasis_mem_zfilt wt ?_
  have := zwtWord_le_wtWord wt w
  omega

end Zeta

/-! ## §2  `T` has ζ-degree zero

`Ttr_gv` sends the letter `(i,k)` to a multiple of `(i,k+1)` — same ζ-weight.  Mirroring
the `Ttr_wbasis_mem_filt` induction letter by letter therefore gives *preservation* of
`zfilt`, in contrast with the shift by one of `Ttr_mem_filt`.  This is the property the
De Sole–Kac recursion terminates on. -/

theorem Ttr_wbasis_mem_zfilt (wt : ι → ℕ) (l : List (GenIdx ι)) :
    Ttr (wbasis ι (FreeMonoid.ofList l))
      ∈ zfilt wt ((zwtWord wt (FreeMonoid.ofList l) : ℤ)) := by
  induction l with
  | nil =>
      rw [show (FreeMonoid.ofList ([] : List (GenIdx ι))) = 1 from rfl, wbasis_one, Ttr_one]
      exact Submodule.zero_mem _
  | cons p l ih =>
      have hsplit : (FreeMonoid.ofList (p :: l))
          = FreeMonoid.of p * FreeMonoid.ofList l := rfl
      have hw : wbasis ι (FreeMonoid.ofList (p :: l))
          = gv p * wbasis ι (FreeMonoid.ofList l) := by rw [hsplit, wbasis_mul, gv]
      have hwt : zwtWord wt (FreeMonoid.ofList (p :: l))
          = zwtIdx wt p + zwtWord wt (FreeMonoid.ofList l) := by
        rw [hsplit, zwtWord_mul, zwtWord_of]
      rw [hw, Ttr_mul, hwt]
      refine Submodule.add_mem _ ?_ ?_
      · push_cast
        exact gv_mul_mem_zfilt wt p ih
      · rw [Ttr_gv, smul_mul_assoc]
        refine Submodule.smul_mem _ _ ?_
        have h := gv_mul_mem_zfilt wt (p.1, p.2 + 1)
          (wbasis_mem_zfilt wt (le_refl ((zwtWord wt (FreeMonoid.ofList l) : ℤ))))
        have he : (zwtIdx wt (p.1, p.2 + 1) : ℤ) = (zwtIdx wt p : ℤ) := rfl
        rw [he] at h
        push_cast
        exact h

/-- **`T` preserves the ζ-filtration** — `deg T = 0`, the De Sole–Kac bookkeeping.
Contrast `Ttr_mem_filt`, which shifts `filt` by one. -/
theorem Ttr_mem_zfilt (wt : ι → ℕ) {d : ℤ} {x : TR ι} (hx : x ∈ zfilt wt d) :
    Ttr x ∈ zfilt wt d := by
  rw [zfilt] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      have hT := Ttr_wbasis_mem_zfilt wt (FreeMonoid.toList w)
      rw [show FreeMonoid.ofList (FreeMonoid.toList w) = w from rfl] at hT
      exact zfilt_mono wt hw hT
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- Powers of `T` preserve the ζ-filtration. -/
theorem Ttr_pow_mem_zfilt (wt : ι → ℕ) (m : ℕ) {d : ℤ} {x : TR ι} (hx : x ∈ zfilt wt d) :
    ((Ttr : End ℂ (TR ι)) ^ m) x ∈ zfilt wt d := by
  induction m with
  | zero => exact hx
  | succ m ih => rw [Ttr_pow_succ_left]; exact Ttr_mem_zfilt wt ih

/-! ## §3  The L1 axiom implies the De Sole–Kac grading condition  (DK Example 6.2)

De Sole–Kac's single structural axiom (Definition 3.1(2)) is the strict decrease
`Δ([a_λ b]) < Δ(a) + Δ(b)` in the ζ-filtration.  The library's `OPEData.ope_wt` places
`aⁱ₍ₙ₎aʲ` in `filt (Δᵢ + Δⱼ - n - 1)`, which sits inside `zfilt (ζᵢ + ζⱼ - 1)` — and with
the grading monoid `ℕ` (positive weights) the bound `ζᵢ + ζⱼ - 1` is exactly De Sole–Kac's
`(ζ₁+ζ₂)₋`.  So exact-weight L1 data already satisfies the L2 axiom, exactly as [DK]
record in their Example 6.2 for graded vertex algebras. -/

/-- **The DSK grading condition on the bottom letters, from `ope_wt` alone.** -/
theorem ope_mem_zfilt (D : OPEData ι) (i j : ι) (n : ℕ) :
    D.ope i j n ∈ zfilt D.wt ((D.wt i : ℤ) + (D.wt j : ℤ) - 1) :=
  filt_le_zfilt D.wt _ (filt_mono D.wt (by omega) (D.ope_wt i j n))

/-- The right sesquilinearity step preserves a uniform ζ-bound: both `Ttr` (ζ-degree
zero) and the index shift stay inside `zfilt c`. -/
theorem Rstep_mem_zfilt {wt : ι → ℕ} {f : ℕ → TR ι} {c : ℤ}
    (hf : ∀ n : ℕ, f n ∈ zfilt wt c) (n : ℕ) : Rstep f n ∈ zfilt wt c := by
  change Ttr (f n) + ((n : ℂ)) • f (n - 1) ∈ zfilt wt c
  exact Submodule.add_mem _ (Ttr_mem_zfilt wt (hf n)) (Submodule.smul_mem _ _ (hf (n - 1)))

/-- The left sesquilinearity step preserves a uniform ζ-bound. -/
theorem Lstep_mem_zfilt {wt : ι → ℕ} {f : ℕ → TR ι} {c : ℤ}
    (hf : ∀ n : ℕ, f n ∈ zfilt wt c) (n : ℕ) : Lstep f n ∈ zfilt wt c := by
  change -((n : ℂ)) • f (n - 1) ∈ zfilt wt c
  exact Submodule.smul_mem _ _ (hf (n - 1))

/-- Iterating the right step. -/
theorem Rstep_iterate_mem_zfilt {wt : ι → ℕ} :
    ∀ (l : ℕ) {f : ℕ → TR ι} {c : ℤ}, (∀ n : ℕ, f n ∈ zfilt wt c) →
      ∀ n : ℕ, Rstep^[l] f n ∈ zfilt wt c := by
  intro l
  induction l with
  | zero => intro f c hf n; rw [Function.iterate_zero_apply]; exact hf n
  | succ l ih =>
      intro f c hf n
      rw [Function.iterate_succ_apply]
      exact ih (fun m => Rstep_mem_zfilt hf m) n

/-- Iterating the left step. -/
theorem Lstep_iterate_mem_zfilt {wt : ι → ℕ} :
    ∀ (k : ℕ) {f : ℕ → TR ι} {c : ℤ}, (∀ n : ℕ, f n ∈ zfilt wt c) →
      ∀ n : ℕ, Lstep^[k] f n ∈ zfilt wt c := by
  intro k
  induction k with
  | zero => intro f c hf n; rw [Function.iterate_zero_apply]; exact hf n
  | succ k ih =>
      intro f c hf n
      rw [Function.iterate_succ_apply]
      exact ih (fun m => Lstep_mem_zfilt hf m) n

/-- **The extended bracket satisfies the DSK grading condition on all divided powers**:
`ζ(p₍ₙ₎q) ≤ ζp + ζq - 1 = (ζp + ζq)₋`, uniformly in `n`.  This is where
`Ttr_mem_zfilt` (through `Rstep_mem_zfilt`) is consumed — the divided-power case the
bottom-letter statement `ope_mem_zfilt` does not cover. -/
theorem brk_mem_zfilt (D : OPEData ι) (p q : GenIdx ι) (n : ℕ) :
    brk D p q n ∈ zfilt D.wt ((D.wt p.1 : ℤ) + (D.wt q.1 : ℤ) - 1) := by
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  have hbase : ∀ m : ℕ, D.ope i j m ∈ zfilt D.wt ((D.wt i : ℤ) + (D.wt j : ℤ) - 1) :=
    fun m => ope_mem_zfilt D i j m
  have hL := Lstep_iterate_mem_zfilt k (Rstep_iterate_mem_zfilt l hbase) n
  rw [brk]
  exact Submodule.smul_mem _ _ hL

/-- The `∫₋ᵀ⁰` of the singular OPE also satisfies the strict ζ-decrease: the integral
is a sum of `T`-powers of bracket values, and `T` has ζ-degree zero. -/
theorem opeInt_mem_zfilt (D : OPEData ι) (p q : GenIdx ι) :
    opeInt D p q ∈ zfilt D.wt ((D.wt p.1 : ℤ) + (D.wt q.1 : ℤ) - 1) := by
  rw [opeInt]
  refine Submodule.sum_mem _ (fun n _ => ?_)
  exact Submodule.smul_mem _ _ (Ttr_pow_mem_zfilt D.wt (n + 1) (brk_mem_zfilt D p q n))

/-! ## §4  The exact-weight (`gr`) toolkit, under `IsConformal`

The `gr` upgrades of `brk_mem_filt` and `opeInt`/`rel` membership.  The `ℕ`-truncated
subtraction in the graded indices is handled by the `IsConformal` precedent
(`Core.NonlinearVirasoro` §10): wherever the index truncates, `brk_vanish` has already
forced the element to `0`, so the statement is exact where it matters and vacuous
beyond. -/

/-- Powers of `T` shift the exact grading by their exponent. -/
theorem Ttr_pow_mem_gr (wt : ι → ℕ) (m : ℕ) {d : ℕ} {x : TR ι} (hx : x ∈ gr wt d) :
    ((Ttr : End ℂ (TR ι)) ^ m) x ∈ gr wt (d + m) := by
  induction m with
  | zero => exact hx
  | succ m ih =>
      rw [Ttr_pow_succ_left]
      have h := Ttr_mem_gr wt ih
      rwa [show d + m + 1 = d + (m + 1) from by omega] at h

/-- The right sesquilinearity step propagates exact-weight membership, given the
vanishing threshold `N ≤ c` of the slice function (supplied by `brk_vanish`-type
statements).  The threshold is what keeps the `ℕ`-truncated indices honest. -/
theorem Rstep_mem_gr {wt : ι → ℕ} {f : ℕ → TR ι} {c N : ℕ} (hN : N ≤ c)
    (h0 : ∀ n : ℕ, N ≤ n → f n = 0) (hg : ∀ n : ℕ, f n ∈ gr wt (c - n - 1)) (n : ℕ) :
    Rstep f n ∈ gr wt (c + 1 - n - 1) := by
  change Ttr (f n) + ((n : ℂ)) • f (n - 1) ∈ gr wt (c + 1 - n - 1)
  rcases lt_or_ge n N with hn | hn
  · -- `n < N ≤ c`: both indices are untruncated.
    refine Submodule.add_mem _ ?_ ?_
    · have h := Ttr_mem_gr wt (hg n)
      rwa [show c - n - 1 + 1 = c + 1 - n - 1 from by omega] at h
    · rcases Nat.eq_zero_or_pos n with rfl | hpos
      · rw [Nat.cast_zero, zero_smul]; exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ ?_
        have h := hg (n - 1)
        rwa [show c - (n - 1) - 1 = c + 1 - n - 1 from by omega] at h
  · -- `N ≤ n`: the `Ttr` term vanishes.
    rw [h0 n hn, map_zero, zero_add]
    rcases lt_or_ge n (N + 1) with hn1 | hn1
    · -- `n = N`.
      have hEq : n = N := by omega
      subst hEq
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · rw [Nat.cast_zero, zero_smul]; exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ ?_
        have h := hg (n - 1)
        rwa [show c - (n - 1) - 1 = c + 1 - n - 1 from by omega] at h
    · -- `N + 1 ≤ n`: the second term vanishes too.
      rw [h0 (n - 1) (by omega), smul_zero]
      exact Submodule.zero_mem _

/-- The left sesquilinearity step propagates exact-weight membership. -/
theorem Lstep_mem_gr {wt : ι → ℕ} {f : ℕ → TR ι} {c N : ℕ} (hN : N ≤ c)
    (h0 : ∀ n : ℕ, N ≤ n → f n = 0) (hg : ∀ n : ℕ, f n ∈ gr wt (c - n - 1)) (n : ℕ) :
    Lstep f n ∈ gr wt (c + 1 - n - 1) := by
  change -((n : ℂ)) • f (n - 1) ∈ gr wt (c + 1 - n - 1)
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [Nat.cast_zero, neg_zero, zero_smul]; exact Submodule.zero_mem _
  rcases lt_or_ge (n - 1) N with hn | hn
  · refine Submodule.smul_mem _ _ ?_
    have h := hg (n - 1)
    rwa [show c - (n - 1) - 1 = c + 1 - n - 1 from by omega] at h
  · rw [h0 (n - 1) hn, smul_zero]
    exact Submodule.zero_mem _

/-- Iterating the right step under the exact grading. -/
theorem Rstep_iterate_mem_gr {wt : ι → ℕ} :
    ∀ (l : ℕ) {f : ℕ → TR ι} {c N : ℕ}, N ≤ c → (∀ n : ℕ, N ≤ n → f n = 0) →
      (∀ n : ℕ, f n ∈ gr wt (c - n - 1)) →
      ∀ n : ℕ, Rstep^[l] f n ∈ gr wt (c + l - n - 1) := by
  intro l
  induction l with
  | zero =>
      intro f c N _ _ hg n
      rw [Function.iterate_zero_apply]
      have h := hg n
      rwa [show c - n - 1 = c + 0 - n - 1 from by omega] at h
  | succ l ih =>
      intro f c N hN h0 hg n
      rw [Function.iterate_succ_apply]
      have h0' : ∀ m : ℕ, N + 1 ≤ m → Rstep f m = 0 := by
        intro m hm
        change Ttr (f m) + ((m : ℂ)) • f (m - 1) = 0
        rw [h0 m (by omega), h0 (m - 1) (by omega), map_zero, smul_zero, add_zero]
      have hg' : ∀ m : ℕ, Rstep f m ∈ gr wt (c + 1 - m - 1) :=
        fun m => Rstep_mem_gr hN h0 hg m
      have h := ih (f := Rstep f) (c := c + 1) (N := N + 1) (by omega) h0' hg' n
      rwa [show c + 1 + l - n - 1 = c + (l + 1) - n - 1 from by omega] at h

/-- Iterating the left step under the exact grading. -/
theorem Lstep_iterate_mem_gr {wt : ι → ℕ} :
    ∀ (k : ℕ) {f : ℕ → TR ι} {c N : ℕ}, N ≤ c → (∀ n : ℕ, N ≤ n → f n = 0) →
      (∀ n : ℕ, f n ∈ gr wt (c - n - 1)) →
      ∀ n : ℕ, Lstep^[k] f n ∈ gr wt (c + k - n - 1) := by
  intro k
  induction k with
  | zero =>
      intro f c N _ _ hg n
      rw [Function.iterate_zero_apply]
      have h := hg n
      rwa [show c - n - 1 = c + 0 - n - 1 from by omega] at h
  | succ k ih =>
      intro f c N hN h0 hg n
      rw [Function.iterate_succ_apply]
      have h0' : ∀ m : ℕ, N + 1 ≤ m → Lstep f m = 0 := by
        intro m hm
        change -((m : ℂ)) • f (m - 1) = 0
        rw [h0 (m - 1) (by omega), smul_zero]
      have hg' : ∀ m : ℕ, Lstep f m ∈ gr wt (c + 1 - m - 1) :=
        fun m => Lstep_mem_gr hN h0 hg m
      have h := ih (f := Lstep f) (c := c + 1) (N := N + 1) (by omega) h0' hg' n
      rwa [show c + 1 + k - n - 1 = c + (k + 1) - n - 1 from by omega] at h

/-- **The extended bracket of a conformal datum is exactly homogeneous**:
`p₍ₙ₎q ∈ gr (Δp + Δq - n - 1)`.  (For `n + 1 > Δp + Δq` the element is already `0` by
`brk_vanish`, so the truncated index imposes nothing — the `IsConformal` precedent.) -/
theorem brk_mem_gr {D : OPEData ι} (hC : D.IsConformal) (p q : GenIdx ι) (n : ℕ) :
    brk D p q n ∈ gr D.wt (wtIdx D.wt p + wtIdx D.wt q - n - 1) := by
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  have h0 : ∀ m : ℕ, D.wt i + D.wt j ≤ m → D.ope i j m = 0 :=
    fun m hm => D.ope_eq_zero i j hm
  have hg : ∀ m : ℕ, D.ope i j m ∈ gr D.wt (D.wt i + D.wt j - m - 1) := fun m => hC i j m
  have hR := Rstep_iterate_mem_gr l (N := D.wt i + D.wt j) (le_refl _) h0 hg
  have h0R : ∀ m : ℕ, D.wt i + D.wt j + l ≤ m → Rstep^[l] (D.ope i j) m = 0 :=
    fun m hm => Rstep_iterate_eq_zero h0 l m hm
  have hL := Lstep_iterate_mem_gr k (N := D.wt i + D.wt j + l) (le_refl _) h0R hR n
  rw [brk]
  refine Submodule.smul_mem _ _ ?_
  rwa [show D.wt i + D.wt j + l + k - n - 1
      = wtIdx D.wt (i, k) + wtIdx D.wt (j, l) - n - 1 from by simp only [wtIdx]; omega] at hL

/-- The `∫₋ᵀ⁰` of the singular OPE of a conformal datum is exactly homogeneous of
weight `Δp + Δq` — the graded upgrade of the `filt` bound, consumed by the vacuum
survival guard. -/
theorem opeInt_mem_gr {D : OPEData ι} (hC : D.IsConformal) (p q : GenIdx ι) :
    opeInt D p q ∈ gr D.wt (wtIdx D.wt p + wtIdx D.wt q) := by
  rw [opeInt]
  refine Submodule.sum_mem _ (fun n hn => ?_)
  refine Submodule.smul_mem _ _ ?_
  have hbrk := brk_mem_gr hC p q n
  have hpow := Ttr_pow_mem_gr D.wt (n + 1) hbrk
  rwa [show wtIdx D.wt p + wtIdx D.wt q - n - 1 + (n + 1)
      = wtIdx D.wt p + wtIdx D.wt q from by
    have := Finset.mem_range.mp hn; omega] at hpow

/-- **The relation of a conformal datum is exactly homogeneous** of weight `Δp + Δq` —
`virasoro_rel_mem_gr`, generalized to every conformal `OPEData`.  This is what makes the
relation ideal graded. -/
theorem rel_mem_gr {D : OPEData ι} (hC : D.IsConformal) (p q : GenIdx ι) :
    rel D p q ∈ gr D.wt (wtIdx D.wt p + wtIdx D.wt q) := by
  have hgv : ∀ a b : GenIdx ι, gv a * gv b ∈ gr D.wt (wtIdx D.wt a + wtIdx D.wt b) :=
    fun a b => gv_mul_mem_gr a (gv_mem_gr D.wt b)
  rw [rel]
  refine Submodule.sub_mem _ (Submodule.sub_mem _ (hgv p q) ?_) (opeInt_mem_gr hC p q)
  refine Submodule.smul_mem _ _ ?_
  have h := hgv q p
  rwa [show wtIdx D.wt q + wtIdx D.wt p = wtIdx D.wt p + wtIdx D.wt q from by omega] at h

/-! ## §5  The augmentation kills positive weight

The augmentation `aug` (Core.NonlinearConformal §8) sends every generator to `0`; a word
of positive weight is nonempty, hence killed.  `grPos` packages the positive-weight
words, and `T` maps all of `T(R)` into it. -/

/-- A word of positive weight is nonempty, and the augmentation kills it. -/
theorem aug_wbasis_of_pos {wt : ι → ℕ} {w : FreeMonoid (GenIdx ι)}
    (hw : 0 < wtWord wt w) : aug (wbasis ι w) = 0 := by
  have hlist : w = FreeMonoid.ofList (FreeMonoid.toList w) := rfl
  rcases hl : FreeMonoid.toList w with _ | ⟨p, l⟩
  · exfalso
    have : wtWord wt w = 0 := by
      rw [hlist, hl]
      rfl
    omega
  · rw [hlist, hl, show (FreeMonoid.ofList (p :: l))
      = FreeMonoid.of p * FreeMonoid.ofList l from rfl, wbasis_mul, map_mul, ← gv, aug_gv,
      zero_mul]

/-- **The augmentation kills every homogeneous element of positive weight.** -/
theorem aug_gr_pos {wt : ι → ℕ} {d : ℕ} (hd : 0 < d) :
    ∀ x ∈ gr wt d, aug x = 0 := by
  intro x hx
  rw [gr] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      exact aug_wbasis_of_pos (wt := wt) (by omega)
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

/-- The span of the words of **positive** conformal weight. -/
noncomputable def grPos (wt : ι → ℕ) : Submodule ℂ (TR ι) :=
  Submodule.span ℂ (wbasis ι '' {w | 0 < wtWord wt w})

/-- A homogeneous piece of positive weight sits inside `grPos`. -/
theorem gr_le_grPos {wt : ι → ℕ} {d : ℕ} (hd : 0 < d) : gr wt d ≤ grPos wt := by
  rw [gr]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨w, hw, rfl⟩
  simp only [Set.mem_setOf_eq] at hw
  exact Submodule.subset_span ⟨w, by simp only [Set.mem_setOf_eq]; omega, rfl⟩

/-- The augmentation kills `grPos`. -/
theorem aug_grPos {wt : ι → ℕ} : ∀ x ∈ grPos wt, aug x = 0 := by
  intro x hx
  rw [grPos] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      exact aug_wbasis_of_pos hw
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

/-- **`T` maps all of `T(R)` into the positive-weight span**: `T` kills the unit word
and raises the weight of every other word by one. -/
theorem Ttr_mem_grPos (wt : ι → ℕ) (x : TR ι) : Ttr x ∈ grPos wt := by
  have hx : x ∈ Submodule.span ℂ (Set.range (wbasis ι)) := by
    rw [(wbasis ι).span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      have hT := Ttr_wbasis_mem_gr wt (FreeMonoid.toList w)
      rw [show FreeMonoid.ofList (FreeMonoid.toList w) = w from rfl] at hT
      exact gr_le_grPos (by omega) hT
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-! ## §6  Graded projections

The word basis is a genuine Mathlib `Module.Basis`, so filtering its coordinates by
weight yields the projection onto each homogeneous piece, and every element of `T(R)` is
a **finite** sum of its homogeneous components.  Scoped to what the vacuum-survival
guard of `Core.VAPresentation` consumes. -/

/-- The **graded projection** onto the weight-`d` piece: keep exactly the basis
coordinates at words of weight `d`. -/
noncomputable def grProj (wt : ι → ℕ) (d : ℕ) : TR ι →ₗ[ℂ] TR ι :=
  (Finsupp.lsum ℂ (fun w : FreeMonoid (GenIdx ι) =>
      if wtWord wt w = d then LinearMap.toSpanSingleton ℂ (TR ι) (wbasis ι w) else 0)) ∘ₗ
    ((wbasis ι).repr : TR ι ≃ₗ[ℂ] (FreeMonoid (GenIdx ι) →₀ ℂ)).toLinearMap

/-- `grProj` on a basis word: the word survives iff its weight is `d`. -/
theorem grProj_wbasis (wt : ι → ℕ) (d : ℕ) (w : FreeMonoid (GenIdx ι)) :
    grProj wt d (wbasis ι w) = if wtWord wt w = d then wbasis ι w else 0 := by
  rw [grProj, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
    Finsupp.lsum_single]
  split_ifs with h
  · rw [LinearMap.toSpanSingleton_apply, one_smul]
  · rw [LinearMap.zero_apply]

/-- The graded projection lands in the graded piece. -/
theorem grProj_mem_gr (wt : ι → ℕ) (d : ℕ) (x : TR ι) : grProj wt d x ∈ gr wt d := by
  have hx : x ∈ Submodule.span ℂ (Set.range (wbasis ι)) := by
    rw [(wbasis ι).span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      rw [grProj_wbasis]
      split_ifs with h
      · exact wbasis_mem_gr h
      · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- On the weight-`d` piece the projection is the identity. -/
theorem grProj_eq_self_of_mem {wt : ι → ℕ} {d : ℕ} {x : TR ι} (hx : x ∈ gr wt d) :
    grProj wt d x = x := by
  rw [gr] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      rw [grProj_wbasis, if_pos hw]
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, ha]

/-- On a homogeneous piece of a *different* weight the projection vanishes. -/
theorem grProj_eq_zero_of_mem_of_ne {wt : ι → ℕ} {d e : ℕ} {x : TR ι} (hx : x ∈ gr wt e)
    (hne : e ≠ d) : grProj wt d x = 0 := by
  rw [gr] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      rw [grProj_wbasis, if_neg (by omega)]
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

/-- **Finite graded decomposition**: an element of `filt D` is the sum of its
homogeneous components in weights `0, …, D`. -/
theorem sum_grProj_of_mem_filt {wt : ι → ℕ} {D : ℕ} {x : TR ι}
    (hx : x ∈ filt wt (D : ℤ)) :
    ∑ d ∈ Finset.range (D + 1), grProj wt d x = x := by
  rw [filt] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      have hmem : wtWord wt w ∈ Finset.range (D + 1) := Finset.mem_range.mpr (by omega)
      calc ∑ d ∈ Finset.range (D + 1), grProj wt d (wbasis ι w)
          = ∑ d ∈ Finset.range (D + 1), if wtWord wt w = d then wbasis ι w else 0 :=
            Finset.sum_congr rfl (fun d _ => grProj_wbasis wt d w)
        _ = if wtWord wt w ∈ Finset.range (D + 1) then wbasis ι w else 0 :=
            Finset.sum_ite_eq (Finset.range (D + 1)) (wtWord wt w) (fun _ => wbasis ι w)
        _ = wbasis ι w := if_pos hmem
  | zero => simp
  | add a b _ _ ha hb =>
      have hsplit : ∀ d ∈ Finset.range (D + 1),
          grProj wt d (a + b) = grProj wt d a + grProj wt d b :=
        fun d _ => map_add (grProj wt d) a b
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ha, hb]
  | smul c a _ ha =>
      have hsplit : ∀ d ∈ Finset.range (D + 1),
          grProj wt d (c • a) = c • grProj wt d a :=
        fun d _ => map_smul (grProj wt d) c a
      rw [Finset.sum_congr rfl hsplit, ← Finset.smul_sum, ha]

/-- Every element of `T(R)` is a finite sum of its homogeneous components. -/
theorem exists_sum_grProj (wt : ι → ℕ) (x : TR ι) :
    ∃ D : ℕ, ∑ d ∈ Finset.range (D + 1), grProj wt d x = x := by
  obtain ⟨d, hd⟩ := filt_exhaustive wt x
  rcases lt_or_ge d 0 with h0 | h0
  · rw [filt_neg wt h0, Submodule.mem_bot] at hd
    subst hd
    exact ⟨0, by simp⟩
  · refine ⟨d.toNat, sum_grProj_of_mem_filt ?_⟩
    rwa [Int.toNat_of_nonneg h0]

/-- Subtracting the weight-`0` component lands in the positive-weight span. -/
theorem sub_grProj_zero_mem_grPos (wt : ι → ℕ) (x : TR ι) :
    x - grProj wt 0 x ∈ grPos wt := by
  have hx : x ∈ Submodule.span ℂ (Set.range (wbasis ι)) := by
    rw [(wbasis ι).span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      rw [grProj_wbasis]
      split_ifs with h
      · rw [sub_self]; exact Submodule.zero_mem _
      · rw [sub_zero]
        exact Submodule.subset_span ⟨w, by simp only [Set.mem_setOf_eq]; omega, rfl⟩
  | zero => rw [map_zero, sub_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
      rw [map_add]
      have : a + b - (grProj wt 0 a + grProj wt 0 b)
          = (a - grProj wt 0 a) + (b - grProj wt 0 b) := by abel
      rw [this]
      exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ c ha

/-- The weight-`0` component of a positive-weight element vanishes. -/
theorem grProj_zero_eq_zero_of_mem_grPos {wt : ι → ℕ} {x : TR ι} (hx : x ∈ grPos wt) :
    grProj wt 0 x = 0 := by
  rw [grPos] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      rw [grProj_wbasis, if_neg (by omega)]
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

/-- **Membership in the positive-weight span is exactly the vanishing of the
weight-`0` component.**  This is the precise interface between the graded projections
and the vacuum-survival guard. -/
theorem mem_grPos_iff (wt : ι → ℕ) (x : TR ι) :
    x ∈ grPos wt ↔ grProj wt 0 x = 0 := by
  constructor
  · exact grProj_zero_eq_zero_of_mem_grPos
  · intro h
    have := sub_grProj_zero_mem_grPos wt x
    rwa [h, sub_zero] at this

end VOA.NonlinearConformal
