/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3Propagate
import VOA.Modules.ZhuVermaAnArchVhatJac3

/-!
# `DefectModeShift` — DLM2 Proposition 6.1 at the canonical pole, **proved**

`ZhuVermaAnArchDLM3Propagate` reduced the `(0,0)` gate to exactly two named inputs: the
independent `PBWFreeness` assumption, and the pure `V̂`-representation identity
`VHatRep.DefectModeShift`.
This file **proves** the second one, for every `ActModeTruncated` representation:

    δ(a, b, c₍ₖ₎x, −1, N)
      = c₍ₖ₎·δ(a, b, x, −1, N)
        − Σ_{p ≥ 0} C(k,p)·δ(a, c₍ₚ₎b, x, −1, k+N−p)
        − Σ_{q ≥ 0} C(k,q)·δ(c₍q₎a, b, x, −1, N+k−q)

(`defectModeShift_of_truncated_dms`). Hence the parameterized gate is conditional on
`PBWFreeness` **alone** (`gate_of_pbw_only`). Level independence is unconditional. The companion
`voaPBWFreeness` supplies the required `regularAMod` instance from the generic relative-induction
field of the theorem `VOA.pbw : PBWPrinciple`; no implication
from its affine-vacuum field alone is claimed.

## The proof, in two halves

Write `δ(a,b,x,−1,N) = (a₍₋₁₎b)₍N₎x − G(0,N)` (`defectVec_neg_one_eq`) with
`G(s,N) = Σ_{i ≥ 0} a₍ₛ₋₁₋ᵢ₎b₍N₊ᵢ₎x + Σ_{i ≥ 0} b₍N₋₁₋ᵢ₎a₍ₛ₊ᵢ₎x`.

* **Step B — the `G`-half** (`gsum_modeShift`).  Purely mechanical: push `c₍ₖ₎` leftwards through
  each of the two composites with the loop commutator (`actMode_push`, twice per half).  Both
  halves obey the *same* per-index law (`pterm_modeShift`, `qterm_modeShift`), so they are handled
  once through the combined summand `gterm`.  The result is

      G_{a,b,c₍ₖ₎x}(s,N) = c₍ₖ₎G_{a,b,x}(s,N) − Σ_q C(k,q)·G_{c₍q₎a,b,x}(s+k−q, N)
                                              − Σ_p C(k,p)·G_{a,c₍ₚ₎b,x}(s, k+N−p);

  note the `a`-slot correction sits at the **shifted** left index `s + k − q`.

* **Step A — the product half** (`stepA_dms`).  Push `c₍ₖ₎` through `(a₍₋₁₎b)₍N₎`, then split the
  resulting `𝒱`-level product with the Borcherds commutator `mode_commutator_vec`,
  `c₍ₜ₎(a₍₋₁₎b) = a₍₋₁₎(c₍ₜ₎b) + Σ_j C(t,j)(c₍ⱼ₎a)₍ₜ₋₁₋ⱼ₎b`.  The resulting double sum collapses by
  the subset-of-subset identity `C(k,t)·C(t,j) = C(k,j)·C(k−j,t−j)` (`cbz_subsetOfSubset`) under the
  reindexing `t = j + r` — this is `vandermonde_column`, and it produces exactly a full `a`-slot sum
  `R_{k−q}` at the *same* shifted index `k − q`.

* **Assembly** (`defectModeShift_of_truncated_dms`).  The `G`-halves cancel term for term against
  Step B at `s = 0`; the `q`-columns are `R_{k−q}(c₍q₎a,b,x,N+k−q) − G_{c₍q₎a,b,x}(k−q, N)`, which
  proved `sumR_sub_gsum_shift` (valid for **every** `s ∈ ℤ`) turns into
  `δ(c₍q₎a,b,x,−1,N+k−q)`.  That the two shifts agree — `(N+k−q) − (k−q) = N` — is the whole point
  of the `a`-slot shift law.

## Engine verification (before formalizing)

The identity had never been engine-checked.  It was verified in two **non-module**
`V̂`-representations
— defects vanish identically on any honest VOA module, so a module test is vacuous — namely the
DLM3 induced modules `U(V̂) ⊗_{U(P≤0)} ℂ_φ` over a rank-1 free boson (symbolic highest weight `λ`)
and over Virasoro `V(c,0)` (symbolic `c`, `h`), with the `V̂` derivative relation
`(L₋₁a)₍ₘ₎ = −m·a₍ₘ₋₁₎` imposed and exact (derived, not guessed) termination bounds.  Result:
**0 mismatches in 25 920 + 3 969 instances at `ℓ = −1`**, with all five sharpness controls failing
loudly and every defect correctly
dying under the projection onto the genuine module.

⚠ The same identity is **FALSE at a general pole `ℓ ≠ −1`** (refuted by the same engine); only the
canonical pole is claimed here, which is exactly what `DefectModeShift` states and all that DLM3 §4
needs.

## References
DLM2 (`q-alg/9509005`) Proposition 6.1 (`refs/dlm2.txt:784-911`); DLM3 (`q-alg/9612010`) §4;
`ZhuVermaAnArchDLM3Propagate` (`DefectModeShift`, `gsum`, `pterm`, `qterm`, `gsum_sub_gsum_zero`,
`sumR_sub_gsum_shift`, `gate_of_pbw_modeShift`); `ZhuVermaAnArchVhatJac3` (`mode_commutator_vec`,
`cbz_subsetOfSubset`).
-/

namespace VOA

open VertexOperatorAlgebra

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## Generic finiteness of an OPE-mode family -/

/-- **Generic finiteness**: any family indexed by the OPE index `t` whose vector part is
`(c₍ₜ₎d)₍f t₎ y` has finite support (VOA regularity `smul_eventually_zero`).  This generalizes
`opeMode_support_finite`, whose mode function is the special case `f t = T − 1 − t`. -/
theorem opeFam_support_finite (ρ : VHatRep W M) (c d : 𝒱) (y : M) (g : ℕ → ℂ) (f : ℕ → ℤ) :
    (Function.support fun t : ℕ => g t • ρ.actMode (W.smul c (t : ℤ) d) (f t) y).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero c d
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  refine hi ?_
  rw [hNz (i : ℤ) (by omega), actMode_zero_left, LinearMap.zero_apply, smul_zero]

/-- The commutator law rewritten as a **left-push**: moving `c₍ₖ₎` from the right of `d₍ₙ₎` to
its left costs exactly the OPE family. -/
theorem actMode_push (ρ : VHatRep W M) (c d : 𝒱) (y : M) (k n : ℤ) :
    ρ.actMode d n (ρ.actMode c k y)
      = ρ.actMode c k (ρ.actMode d n y)
        - ∑ᶠ t : ℕ, cbz k (t : ℤ) • ρ.actMode (W.smul c (t : ℤ) d) (k + n - (t : ℤ)) y := by
  rw [← actMode_comm_vec ρ c d y k n]
  abel

/-! ## The per-index shift law for the two halves of `G` -/

/-- **The `p`-half (`pterm`) shift law**, one summation index `i` at a time: pushing `c₍ₖ₎` out to
the left through `a₍ₛ₋₁₋ᵢ₎b₍N₊ᵢ₎` costs one OPE family in each slot. -/
theorem pterm_modeShift (ρ : VHatRep W M) (a b c : 𝒱) (x : M) (s k N : ℤ) (i : ℕ) :
    pterm ρ a b (ρ.actMode c k x) s N i
      = ρ.actMode c k (pterm ρ a b x s N i)
        - (∑ᶠ q : ℕ, cbz k (q : ℤ) • pterm ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N i)
        - ∑ᶠ p : ℕ, cbz k (p : ℤ) • pterm ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) i := by
  have hfin : (Function.support fun p : ℕ =>
      cbz k (p : ℤ) • ρ.actMode (W.smul c (p : ℤ) b) (k + (N + (i : ℤ)) - (p : ℤ)) x).Finite :=
    opeFam_support_finite ρ c b x _ _
  have hb := actMode_push ρ c b x k (N + (i : ℤ))
  have ha := actMode_push ρ c a (ρ.actMode b (N + (i : ℤ)) x) k (s - 1 - (i : ℤ))
  simp only [pterm]
  rw [hb, map_sub, map_finsum (ρ.actMode a (s - 1 - (i : ℤ))) hfin, ha]
  have e1 : (∑ᶠ p : ℕ, (ρ.actMode a (s - 1 - (i : ℤ)))
        (cbz k (p : ℤ) • ρ.actMode (W.smul c (p : ℤ) b) (k + (N + (i : ℤ)) - (p : ℤ)) x))
      = ∑ᶠ p : ℕ, cbz k (p : ℤ) • ρ.actMode a (s - 1 - (i : ℤ))
          (ρ.actMode (W.smul c (p : ℤ) b) (k + N - (p : ℤ) + (i : ℤ)) x) := by
    refine finsum_congr fun p => ?_
    rw [show k + (N + (i : ℤ)) - (p : ℤ) = k + N - (p : ℤ) + (i : ℤ) from by ring, map_smul]
  have e2 : (∑ᶠ q : ℕ, cbz k (q : ℤ) • ρ.actMode (W.smul c (q : ℤ) a)
        (k + (s - 1 - (i : ℤ)) - (q : ℤ)) (ρ.actMode b (N + (i : ℤ)) x))
      = ∑ᶠ q : ℕ, cbz k (q : ℤ) • ρ.actMode (W.smul c (q : ℤ) a)
          (s + k - (q : ℤ) - 1 - (i : ℤ)) (ρ.actMode b (N + (i : ℤ)) x) := by
    refine finsum_congr fun q => ?_
    rw [show k + (s - 1 - (i : ℤ)) - (q : ℤ) = s + k - (q : ℤ) - 1 - (i : ℤ) from by ring]
  rw [e1, e2]

/-- **The `q`-half (`qterm`) shift law**, one summation index `i` at a time.  Same shape as
`pterm_modeShift` — the two OPE corrections just arrive in the opposite order. -/
theorem qterm_modeShift (ρ : VHatRep W M) (a b c : 𝒱) (x : M) (s k N : ℤ) (i : ℕ) :
    qterm ρ a b (ρ.actMode c k x) s N i
      = ρ.actMode c k (qterm ρ a b x s N i)
        - (∑ᶠ q : ℕ, cbz k (q : ℤ) • qterm ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N i)
        - ∑ᶠ p : ℕ, cbz k (p : ℤ) • qterm ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) i := by
  have hfin : (Function.support fun q : ℕ =>
      cbz k (q : ℤ) • ρ.actMode (W.smul c (q : ℤ) a) (k + (s + (i : ℤ)) - (q : ℤ)) x).Finite :=
    opeFam_support_finite ρ c a x _ _
  have ha := actMode_push ρ c a x k (s + (i : ℤ))
  have hb := actMode_push ρ c b (ρ.actMode a (s + (i : ℤ)) x) k (N - 1 - (i : ℤ))
  simp only [qterm]
  rw [ha, map_sub, map_finsum (ρ.actMode b (N - 1 - (i : ℤ))) hfin, hb]
  have e1 : (∑ᶠ q : ℕ, (ρ.actMode b (N - 1 - (i : ℤ)))
        (cbz k (q : ℤ) • ρ.actMode (W.smul c (q : ℤ) a) (k + (s + (i : ℤ)) - (q : ℤ)) x))
      = ∑ᶠ q : ℕ, cbz k (q : ℤ) • ρ.actMode b (N - 1 - (i : ℤ))
          (ρ.actMode (W.smul c (q : ℤ) a) (s + k - (q : ℤ) + (i : ℤ)) x) := by
    refine finsum_congr fun q => ?_
    rw [show k + (s + (i : ℤ)) - (q : ℤ) = s + k - (q : ℤ) + (i : ℤ) from by ring, map_smul]
  have e2 : (∑ᶠ p : ℕ, cbz k (p : ℤ) • ρ.actMode (W.smul c (p : ℤ) b)
        (k + (N - 1 - (i : ℤ)) - (p : ℤ)) (ρ.actMode a (s + (i : ℤ)) x))
      = ∑ᶠ p : ℕ, cbz k (p : ℤ) • ρ.actMode (W.smul c (p : ℤ) b)
          (k + N - (p : ℤ) - 1 - (i : ℤ)) (ρ.actMode a (s + (i : ℤ)) x) := by
    refine finsum_congr fun p => ?_
    rw [show k + (N - 1 - (i : ℤ)) - (p : ℤ) = k + N - (p : ℤ) - 1 - (i : ℤ) from by ring]
  rw [e1, e2]
  abel

/-! ## Vanishing of the two halves in a zero slot -/

@[simp] theorem pterm_zero_left_dms (ρ : VHatRep W M) (b : 𝒱) (x : M) (s N : ℤ) (i : ℕ) :
    pterm ρ 0 b x s N i = 0 := by
  rw [pterm, actMode_zero_left, LinearMap.zero_apply]

@[simp] theorem pterm_zero_right_dms (ρ : VHatRep W M) (a : 𝒱) (x : M) (s N : ℤ) (i : ℕ) :
    pterm ρ a 0 x s N i = 0 := by
  rw [pterm, actMode_zero_left, LinearMap.zero_apply, map_zero]

@[simp] theorem qterm_zero_left_dms (ρ : VHatRep W M) (b : 𝒱) (x : M) (s N : ℤ) (i : ℕ) :
    qterm ρ 0 b x s N i = 0 := by
  rw [qterm, actMode_zero_left, LinearMap.zero_apply, map_zero]

@[simp] theorem qterm_zero_right_dms (ρ : VHatRep W M) (a : 𝒱) (x : M) (s N : ℤ) (i : ℕ) :
    qterm ρ a 0 x s N i = 0 := by
  rw [qterm, actMode_zero_left, LinearMap.zero_apply]

/-! ## The combined summand `gterm` -/

/-- The combined summand of the shifted normal-ordered sum: `gsum = ∑ᶠ i, gterm i`. -/
noncomputable def gterm (ρ : VHatRep W M) (a b : 𝒱) (x : M) (s N : ℤ) (i : ℕ) : M :=
  pterm ρ a b x s N i + qterm ρ a b x s N i

@[simp] theorem gterm_zero_left (ρ : VHatRep W M) (b : 𝒱) (x : M) (s N : ℤ) (i : ℕ) :
    gterm ρ 0 b x s N i = 0 := by
  rw [gterm, pterm_zero_left_dms, qterm_zero_left_dms, add_zero]

@[simp] theorem gterm_zero_right (ρ : VHatRep W M) (a : 𝒱) (x : M) (s N : ℤ) (i : ℕ) :
    gterm ρ a 0 x s N i = 0 := by
  rw [gterm, pterm_zero_right_dms, qterm_zero_right_dms, add_zero]

theorem gterm_support_finite (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M)
    (s N : ℤ) : (Function.support (gterm ρ a b x s N)).Finite := by
  refine Set.Finite.subset ((pterm_support_finite ρ htr a b x s N).union
    (qterm_support_finite ρ htr a b x s N)) ?_
  intro i hi
  rw [Function.mem_support] at hi
  by_contra hc
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
  exact hi (by rw [gterm, hc.1, hc.2, add_zero])

/-- `gsum` is the `finsum` of `gterm`. -/
theorem gsum_eq_finsum_gterm (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M)
    (s N : ℤ) : gsum ρ a b x s N = ∑ᶠ i : ℕ, gterm ρ a b x s N i := by
  simp only [gterm]
  rw [gsum, finsum_add_distrib (pterm_support_finite ρ htr a b x s N)
    (qterm_support_finite ρ htr a b x s N)]

@[simp] theorem gsum_zero_left_dms (ρ : VHatRep W M) (b : 𝒱) (x : M) (s N : ℤ) :
    gsum ρ 0 b x s N = 0 := by
  rw [gsum, finsum_eq_zero_of_forall_eq_zero fun i => pterm_zero_left_dms ρ b x s N i,
    finsum_eq_zero_of_forall_eq_zero fun i => qterm_zero_left_dms ρ b x s N i, add_zero]

@[simp] theorem gsum_zero_right_dms (ρ : VHatRep W M) (a : 𝒱) (x : M) (s N : ℤ) :
    gsum ρ a 0 x s N = 0 := by
  rw [gsum, finsum_eq_zero_of_forall_eq_zero fun i => pterm_zero_right_dms ρ a x s N i,
    finsum_eq_zero_of_forall_eq_zero fun i => qterm_zero_right_dms ρ a x s N i, add_zero]

/-! ## Two bookkeeping tools -/

/-- A family indexed by the OPE index has finite support as soon as it vanishes whenever the OPE
product does (VOA regularity `smul_eventually_zero`). -/
theorem opeIndexed_support_finite (W : VertexOperatorAlgebra 𝒱) (c d : 𝒱) {N' : Type*}
    [AddCommGroup N'] (F : ℕ → N') (hF : ∀ t : ℕ, W.smul c (t : ℤ) d = 0 → F t = 0) :
    (Function.support F).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero c d
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  exact hi (hF i (hNz (i : ℤ) (by omega)))

/-- An `ℕ`-indexed `finsum` that vanishes from `Q` on is the corresponding `Finset.range` sum. -/
theorem finsumN_eq_range_sum {N' : Type*} [AddCommMonoid N'] (f : ℕ → N') (Q : ℕ)
    (hf : ∀ q : ℕ, Q ≤ q → f q = 0) : (∑ᶠ q : ℕ, f q) = ∑ q ∈ Finset.range Q, f q := by
  refine finsum_eq_sum_of_support_subset f ?_
  intro q hq
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hq (hf q (by omega))

/-- A `Finset`-indexed sum of families with finite support has finite support. -/
theorem finset_sum_support_finite {ι : Type*} {N' : Type*} [AddCommMonoid N'] (s : Finset ι)
    (F : ℕ → ι → N') (h : ∀ j ∈ s, (Function.support fun i : ℕ => F i j).Finite) :
    (Function.support fun i : ℕ => ∑ j ∈ s, F i j).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion s.finite_toSet
    (fun j hj => h j (Finset.mem_coe.mp hj))) ?_
  intro i hi
  rw [Function.mem_support] at hi
  by_contra hc
  simp only [Set.mem_iUnion, Function.mem_support, exists_prop, not_exists, not_and,
    not_not] at hc
  exact hi (Finset.sum_eq_zero fun j hj => hc j (Finset.mem_coe.mpr hj))

/-! ## The `gterm` and `gsum` shift laws -/

/-- **The combined per-index shift law** — `pterm_modeShift` plus `qterm_modeShift`. -/
theorem gterm_modeShift (ρ : VHatRep W M) (a b c : 𝒱) (x : M) (s k N : ℤ) (i : ℕ) :
    gterm ρ a b (ρ.actMode c k x) s N i
      = ρ.actMode c k (gterm ρ a b x s N i)
        - (∑ᶠ q : ℕ, cbz k (q : ℤ) • gterm ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N i)
        - ∑ᶠ p : ℕ, cbz k (p : ℤ) • gterm ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) i := by
  have hqp : (Function.support fun q : ℕ =>
      cbz k (q : ℤ) • pterm ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N i).Finite :=
    opeIndexed_support_finite W c a _ fun q hq => by rw [hq, pterm_zero_left_dms, smul_zero]
  have hqq : (Function.support fun q : ℕ =>
      cbz k (q : ℤ) • qterm ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N i).Finite :=
    opeIndexed_support_finite W c a _ fun q hq => by rw [hq, qterm_zero_left_dms, smul_zero]
  have hpp : (Function.support fun p : ℕ =>
      cbz k (p : ℤ) • pterm ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) i).Finite :=
    opeIndexed_support_finite W c b _ fun p hp => by rw [hp, pterm_zero_right_dms, smul_zero]
  have hpq : (Function.support fun p : ℕ =>
      cbz k (p : ℤ) • qterm ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) i).Finite :=
    opeIndexed_support_finite W c b _ fun p hp => by rw [hp, qterm_zero_right_dms, smul_zero]
  have hq : (∑ᶠ q : ℕ, cbz k (q : ℤ) • gterm ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N i)
      = (∑ᶠ q : ℕ, cbz k (q : ℤ) • pterm ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N i)
        + ∑ᶠ q : ℕ, cbz k (q : ℤ) • qterm ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N i := by
    rw [← finsum_add_distrib hqp hqq]
    exact finsum_congr fun q => by rw [gterm, smul_add]
  have hp : (∑ᶠ p : ℕ, cbz k (p : ℤ) • gterm ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) i)
      = (∑ᶠ p : ℕ, cbz k (p : ℤ) • pterm ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) i)
        + ∑ᶠ p : ℕ, cbz k (p : ℤ) • qterm ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) i := by
    rw [← finsum_add_distrib hpp hpq]
    exact finsum_congr fun p => by rw [gterm, smul_add]
  rw [gterm, gterm, hq, hp, pterm_modeShift ρ a b c x s k N i, qterm_modeShift ρ a b c x s k N i,
    map_add]
  abel

/-- **The `G`-shift law (DLM2 Proposition 6.1's normal-ordered side).**  Pushing `c₍ₖ₎` out of
the shifted normal-ordered sum costs exactly one OPE family in each of the two `𝒱`-slots — and the
`a`-slot correction arrives at the *shifted* left index `s + k − q`. -/
theorem gsum_modeShift (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b c : 𝒱) (x : M)
    (s k N : ℤ) :
    gsum ρ a b (ρ.actMode c k x) s N
      = ρ.actMode c k (gsum ρ a b x s N)
        - (∑ᶠ q : ℕ, cbz k (q : ℤ) • gsum ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N)
        - ∑ᶠ p : ℕ, cbz k (p : ℤ) • gsum ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) := by
  obtain ⟨Nq, hNq⟩ := W.smul_eventually_zero c a
  obtain ⟨Np, hNp⟩ := W.smul_eventually_zero c b
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → W.smul c (q : ℤ) a = 0 :=
    ⟨Nq.toNat, fun q hq => hNq (q : ℤ) (by omega)⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ, ∀ p : ℕ, P ≤ p → W.smul c (p : ℤ) b = 0 :=
    ⟨Np.toNat, fun p hp => hNp (p : ℤ) (by omega)⟩
  -- the two `Finset.range` truncations, for `gterm` (each `i`) and for `gsum`
  have hQt : ∀ i q : ℕ, Q ≤ q →
      cbz k (q : ℤ) • gterm ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N i = 0 :=
    fun i q hq => by rw [hQ q hq, gterm_zero_left, smul_zero]
  have hPt : ∀ i p : ℕ, P ≤ p →
      cbz k (p : ℤ) • gterm ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) i = 0 :=
    fun i p hp => by rw [hP p hp, gterm_zero_right, smul_zero]
  have hQs : ∀ q : ℕ, Q ≤ q →
      cbz k (q : ℤ) • gsum ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N = 0 :=
    fun q hq => by rw [hQ q hq, gsum_zero_left_dms, smul_zero]
  have hPs : ∀ p : ℕ, P ≤ p →
      cbz k (p : ℤ) • gsum ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) = 0 :=
    fun p hp => by rw [hP p hp, gsum_zero_right_dms, smul_zero]
  -- the per-index law, with both corrections as `Finset.range` sums
  have hstep : ∀ i : ℕ, gterm ρ a b (ρ.actMode c k x) s N i
      = ρ.actMode c k (gterm ρ a b x s N i)
        - (∑ q ∈ Finset.range Q,
            cbz k (q : ℤ) • gterm ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N i)
        - ∑ p ∈ Finset.range P,
            cbz k (p : ℤ) • gterm ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) i := by
    intro i
    rw [gterm_modeShift ρ a b c x s k N i, finsumN_eq_range_sum _ Q (hQt i),
      finsumN_eq_range_sum _ P (hPt i)]
  -- finiteness of the three `i`-families
  have hA : (Function.support fun i : ℕ => ρ.actMode c k (gterm ρ a b x s N i)).Finite := by
    refine Set.Finite.subset (gterm_support_finite ρ htr a b x s N) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Function.mem_support]
    intro h
    exact hi (by rw [h, map_zero])
  have hB : (Function.support fun i : ℕ => ∑ q ∈ Finset.range Q,
      cbz k (q : ℤ) • gterm ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N i).Finite := by
    refine finset_sum_support_finite _ _ fun q _ => ?_
    refine Set.Finite.subset (gterm_support_finite ρ htr (W.smul c (q : ℤ) a) b x
      (s + k - (q : ℤ)) N) ?_
    intro i hi
    rw [Function.mem_support] at hi ⊢
    intro h
    exact hi (by rw [h, smul_zero])
  have hC : (Function.support fun i : ℕ => ∑ p ∈ Finset.range P,
      cbz k (p : ℤ) • gterm ρ a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ)) i).Finite := by
    refine finset_sum_support_finite _ _ fun p _ => ?_
    refine Set.Finite.subset (gterm_support_finite ρ htr a (W.smul c (p : ℤ) b) x s
      (k + N - (p : ℤ))) ?_
    intro i hi
    rw [Function.mem_support] at hi ⊢
    intro h
    exact hi (by rw [h, smul_zero])
  have hAB : (Function.support fun i : ℕ => ρ.actMode c k (gterm ρ a b x s N i)
      - ∑ q ∈ Finset.range Q,
          cbz k (q : ℤ) • gterm ρ (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N i).Finite := by
    refine Set.Finite.subset (hA.union hB) ?_
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
    exact hi (by rw [hc.1, hc.2, sub_zero])
  -- assemble
  rw [gsum_eq_finsum_gterm ρ htr a b (ρ.actMode c k x) s N, finsum_congr hstep,
    finsum_sub_distrib hAB hC, finsum_sub_distrib hA hB,
    finsumN_eq_range_sum _ Q hQs, finsumN_eq_range_sum _ P hPs]
  congr 1
  · congr 1
    · rw [← map_finsum (ρ.actMode c k) (gterm_support_finite ρ htr a b x s N),
        ← gsum_eq_finsum_gterm ρ htr a b x s N]
    · rw [finsum_sum_comm (Finset.range Q) _ (fun q _ =>
        Set.Finite.subset (gterm_support_finite ρ htr (W.smul c (q : ℤ) a) b x
          (s + k - (q : ℤ)) N) (fun i hi => by
            rw [Function.mem_support] at hi ⊢
            intro h
            exact hi (by rw [h, smul_zero])))]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← smul_finsum' (cbz k (q : ℤ)) (gterm_support_finite ρ htr (W.smul c (q : ℤ) a) b x
          (s + k - (q : ℤ)) N),
        ← gsum_eq_finsum_gterm ρ htr (W.smul c (q : ℤ) a) b x (s + k - (q : ℤ)) N]
  · rw [finsum_sum_comm (Finset.range P) _ (fun p _ =>
      Set.Finite.subset (gterm_support_finite ρ htr a (W.smul c (p : ℤ) b) x s
        (k + N - (p : ℤ))) (fun i hi => by
          rw [Function.mem_support] at hi ⊢
          intro h
          exact hi (by rw [h, smul_zero])))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← smul_finsum' (cbz k (p : ℤ)) (gterm_support_finite ρ htr a (W.smul c (p : ℤ) b) x s
        (k + N - (p : ℤ))),
      ← gsum_eq_finsum_gterm ρ htr a (W.smul c (p : ℤ) b) x s (k + N - (p : ℤ))]

/-! ## The `a`-slot sum `R` and the Vandermonde column collapse -/

/-- The **`a`-slot shifted sum** `R_s(a,b,x,T) = Σ_{r ≥ 0} C(s,r)·(a₍ᵣ₋₁₎b)₍T₋ᵣ₎x`, the left-hand
side of the proved shift law `sumR_sub_gsum_shift`. -/
noncomputable def sumR (ρ : VHatRep W M) (a b : 𝒱) (x : M) (s T : ℤ) : M :=
  ∑ᶠ r : ℕ, cbz s (r : ℤ) • ρ.actMode (W.smul a ((r : ℤ) - 1) b) (T - (r : ℤ)) x

/-- The proved `a`-slot shift law, restated for `sumR`: `R_s − G(s, T−s) = δ(a,b,x,−1,T)`, for
**every** `s ∈ ℤ`. -/
theorem sumR_sub_gsum (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M) (s T : ℤ) :
    sumR ρ a b x s T - gsum ρ a b x s (T - s) = defectVec ρ a b x (-1) T :=
  sumR_sub_gsum_shift ρ htr a b x s T

@[simp] theorem sumR_zero_left (ρ : VHatRep W M) (b : 𝒱) (x : M) (s T : ℤ) :
    sumR ρ 0 b x s T = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun r => ?_
  rw [PreVertexAlgebra.smul_zero_left, actMode_zero_left, LinearMap.zero_apply, smul_zero]

/-- A family indexed by `ℕ` has finite support as soon as it vanishes whenever a **shifted** OPE
product does. -/
theorem opeShift_support_finite (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) {N' : Type*}
    [AddCommGroup N'] (F : ℕ → N') (e : ℤ) (hF : ∀ t : ℕ, W.smul u ((t : ℤ) - e) v = 0 → F t = 0) :
    (Function.support F).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero u v
  refine Set.Finite.subset (Set.finite_Iio (Nz + e).toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  exact hi (hF i (hNz ((i : ℤ) - e) (by omega)))

/-- A `ℤ`-indexed family vanishing outside `[lo, hi)` has finite support. -/
theorem finiteZ_of_bounds {N' : Type*} [AddCommGroup N'] (F : ℤ → N') (lo hi : ℤ)
    (hlo : ∀ i : ℤ, i < lo → F i = 0) (hhi : ∀ i : ℤ, hi ≤ i → F i = 0) :
    (Function.support F).Finite := by
  refine Set.Finite.subset (Set.finite_Ico lo hi) ?_
  intro i hmem
  rw [Function.mem_support] at hmem
  rw [Set.mem_Ico]
  exact ⟨not_lt.mp fun h => hmem (hlo i h), not_le.mp fun h => hmem (hhi i h)⟩

/-- **The Vandermonde column collapse.**  Summing the inner OPE column of the `𝒱`-level
commutator against `C(k,t)` turns the *subset-of-subset* identity
`C(k,t)·C(t,j) = C(k,j)·C(k−j,t−j)`
(`cbz_subsetOfSubset`) into a single `a`-slot sum at the shifted index `k − j`.  The reindexing is
`t = j + r`; the terms with `r < 0` vanish on **both** sides (for `0 ≤ j + r < j` the middle
binomial
`C(j+r, j)` is zero, for `j + r < 0` the outer `C(k, j+r)` is). -/
theorem vandermonde_column (ρ : VHatRep W M) (A b : 𝒱) (x : M) (k N : ℤ) (j : ℕ) :
    (∑ᶠ t : ℕ, (cbz k (t : ℤ) * cbz (t : ℤ) (j : ℤ)) •
        ρ.actMode (W.smul A ((t : ℤ) - 1 - (j : ℤ)) b) (k + N - (t : ℤ)) x)
      = cbz k (j : ℤ) • sumR ρ A b x (k - (j : ℤ)) (N + k - (j : ℤ)) := by
  obtain ⟨Z, hZ⟩ := W.smul_eventually_zero A b
  -- the `t`-family, extended to `ℤ`
  have hlo : ∀ t : ℤ, t < 0 → (cbz k t * cbz t (j : ℤ)) •
      ρ.actMode (W.smul A (t - 1 - (j : ℤ)) b) (k + N - t) x = 0 := by
    intro t ht
    rw [cbz_apply_neg k ht, zero_mul, zero_smul]
  have hhi : ∀ t : ℤ, Z + 1 + (j : ℤ) ≤ t → (cbz k t * cbz t (j : ℤ)) •
      ρ.actMode (W.smul A (t - 1 - (j : ℤ)) b) (k + N - t) x = 0 := by
    intro t ht
    rw [hZ (t - 1 - (j : ℤ)) (by omega), actMode_zero_left, LinearMap.zero_apply, smul_zero]
  have hZN : (∑ᶠ t : ℕ, (cbz k (t : ℤ) * cbz (t : ℤ) (j : ℤ)) •
        ρ.actMode (W.smul A ((t : ℤ) - 1 - (j : ℤ)) b) (k + N - (t : ℤ)) x)
      = ∑ᶠ t : ℤ, (cbz k t * cbz t (j : ℤ)) •
          ρ.actMode (W.smul A (t - 1 - (j : ℤ)) b) (k + N - t) x :=
    (finsumZ_eq_finsumN _ (Z + 1 + (j : ℤ)).toNat hlo
      (fun t ht => hhi t (by omega))).symm
  -- the `r`-family, extended to `ℤ`
  have hrlo : ∀ r : ℤ, r < 0 → (cbz k (j : ℤ) * cbz (k - (j : ℤ)) r) •
      ρ.actMode (W.smul A (r - 1) b) (N + k - (j : ℤ) - r) x = 0 := by
    intro r hr
    rw [cbz_apply_neg (k - (j : ℤ)) hr, mul_zero, zero_smul]
  have hrhi : ∀ r : ℤ, Z + 1 ≤ r → (cbz k (j : ℤ) * cbz (k - (j : ℤ)) r) •
      ρ.actMode (W.smul A (r - 1) b) (N + k - (j : ℤ) - r) x = 0 := by
    intro r hr
    rw [hZ (r - 1) (by omega), actMode_zero_left, LinearMap.zero_apply, smul_zero]
  -- the termwise reindexing `t = j + r`
  have key : ∀ r : ℤ, (cbz k ((j : ℤ) + r) * cbz ((j : ℤ) + r) (j : ℤ)) •
      ρ.actMode (W.smul A (((j : ℤ) + r) - 1 - (j : ℤ)) b) (k + N - ((j : ℤ) + r)) x
      = (cbz k (j : ℤ) * cbz (k - (j : ℤ)) r) •
        ρ.actMode (W.smul A (r - 1) b) (N + k - (j : ℤ) - r) x := by
    intro r
    have hmode : ((j : ℤ) + r) - 1 - (j : ℤ) = r - 1 := by ring
    have hmode2 : k + N - ((j : ℤ) + r) = N + k - (j : ℤ) - r := by ring
    rw [hmode, hmode2]
    congr 1
    rcases lt_or_ge r 0 with hr | hr
    · rw [cbz_apply_neg (k - (j : ℤ)) hr, mul_zero]
      rcases lt_or_ge ((j : ℤ) + r) 0 with hj | hj
      · rw [cbz_apply_neg k hj, zero_mul]
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, (j : ℤ) + r = (n : ℤ) := ⟨((j : ℤ) + r).toNat,
          (Int.toNat_of_nonneg hj).symm⟩
        rw [hn, cbz_apply_nonneg (n : ℤ) (Int.natCast_nonneg j), Int.toNat_natCast,
          gBinom_natCast_eq_zero (by omega : n < j), mul_zero]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, r = (n : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr).symm⟩
      subst hn
      have hcast : (j : ℤ) + (n : ℤ) = ((j + n : ℕ) : ℤ) := by push_cast; ring
      rw [hcast, cbz_apply_nonneg k (by positivity), cbz_apply_nonneg ((j + n : ℕ) : ℤ)
          (Int.natCast_nonneg j), cbz_apply_nonneg k (Int.natCast_nonneg j),
        cbz_apply_nonneg (k - (j : ℤ)) (Int.natCast_nonneg n)]
      simp only [Int.toNat_natCast]
      rw [cbz_subsetOfSubset k (i := j + n) (t := j) (by omega),
        show j + n - j = n from by omega]
  rw [hZN, ← finsum_comp_equiv (Equiv.addLeft (j : ℤ))
      (f := fun t : ℤ => (cbz k t * cbz t (j : ℤ)) •
        ρ.actMode (W.smul A (t - 1 - (j : ℤ)) b) (k + N - t) x)]
  simp only [Equiv.coe_addLeft]
  rw [finsum_congr key, sumR]
  rw [← finsumZ_eq_finsumN (fun r : ℤ => cbz (k - (j : ℤ)) r •
      ρ.actMode (W.smul A (r - 1) b) (N + k - (j : ℤ) - r) x) (Z + 1).toNat
    (fun r hr => by dsimp only; rw [cbz_apply_neg (k - (j : ℤ)) hr, zero_smul])
    (fun r hr => by
      dsimp only
      rw [hZ (r - 1) (by omega), actMode_zero_left, LinearMap.zero_apply, smul_zero])]
  have hfinr : (Function.support fun r : ℤ => cbz (k - (j : ℤ)) r •
      ρ.actMode (W.smul A (r - 1) b) (N + k - (j : ℤ) - r) x).Finite :=
    finiteZ_of_bounds _ 0 (Z + 1)
      (fun r hr => by rw [cbz_apply_neg (k - (j : ℤ)) hr, zero_smul])
      (fun r hr => by
        rw [hZ (r - 1) (by omega), actMode_zero_left, LinearMap.zero_apply, smul_zero])
  rw [show (∑ᶠ r : ℤ, (cbz k (j : ℤ) * cbz (k - (j : ℤ)) r) •
        ρ.actMode (W.smul A (r - 1) b) (N + k - (j : ℤ) - r) x)
      = ∑ᶠ r : ℤ, cbz k (j : ℤ) • (cbz (k - (j : ℤ)) r •
          ρ.actMode (W.smul A (r - 1) b) (N + k - (j : ℤ) - r) x) from
    finsum_congr fun r => by rw [mul_smul]]
  exact (smul_finsum' (cbz k (j : ℤ)) hfinr).symm

/-! ## Step A: the product term -/

/-- The `𝒱`-slot of `actMode` as a bundled linear map, so `finsum`s can be pushed through it. -/
noncomputable def actModeAt (ρ : VHatRep W M) (m : ℤ) (x : M) : 𝒱 →ₗ[ℂ] M where
  toFun v := ρ.actMode v m x
  map_add' u v := by rw [actMode_add_left]; rfl
  map_smul' c v := by rw [actMode_smul_left]; rfl

@[simp] theorem actModeAt_apply (ρ : VHatRep W M) (m : ℤ) (x : M) (v : 𝒱) :
    actModeAt ρ m x v = ρ.actMode v m x := rfl

/-- **Step A** — the `Y(Y(a,z₀)b,z₂)` side of DLM2 Proposition 6.1 at `ℓ = −1`.  Pushing `c₍ₖ₎`
out of `(a₍₋₁₎b)₍N₎` costs the `b`-slot OPE family plus, in the `a`-slot, a **full `R`-sum at the
shifted index `k − q`** — this is exactly the shift that `sumR_sub_gsum_shift` absorbs. -/
theorem stepA_dms (ρ : VHatRep W M) (a b c : 𝒱) (x : M) (k N : ℤ) :
    ρ.actMode (W.smul a (-1) b) N (ρ.actMode c k x)
      = ρ.actMode c k (ρ.actMode (W.smul a (-1) b) N x)
        - (∑ᶠ q : ℕ, cbz k (q : ℤ) •
            sumR ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) (N + k - (q : ℤ)))
        - ∑ᶠ p : ℕ, cbz k (p : ℤ) •
            ρ.actMode (W.smul a (-1) (W.smul c (p : ℤ) b)) (k + N - (p : ℤ)) x := by
  obtain ⟨Nq, hNq⟩ := W.smul_eventually_zero c a
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → W.smul c (q : ℤ) a = 0 :=
    ⟨Nq.toNat, fun q hq => hNq (q : ℤ) (by omega)⟩
  -- the inner `𝒱`-level commutator, pushed through `actMode` and truncated to `Finset.range Q`
  have hdec : ∀ t : ℕ,
      cbz k (t : ℤ) • ρ.actMode (W.smul c (t : ℤ) (W.smul a (-1) b)) (k + N - (t : ℤ)) x
      = cbz k (t : ℤ) • ρ.actMode (W.smul a (-1) (W.smul c (t : ℤ) b)) (k + N - (t : ℤ)) x
        + ∑ j ∈ Finset.range Q, (cbz k (t : ℤ) * cbz (t : ℤ) (j : ℤ)) •
            ρ.actMode (W.smul (W.smul c (j : ℤ) a) ((t : ℤ) - 1 - (j : ℤ)) b)
              (k + N - (t : ℤ)) x := by
    intro t
    have hcomm := mode_commutator_vec W c a b (t : ℤ) (-1)
    have hfinj : (Function.support fun j : ℤ =>
        cbz (t : ℤ) j • W.smul (W.smul c j a) ((t : ℤ) + (-1) - j) b).Finite := by
      obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero c a
      refine finiteZ_of_bounds _ 0 Nz (fun j hj => by rw [cbz_apply_neg (t : ℤ) hj, zero_smul])
        (fun j hj => by
          rw [hNz j hj, PreVertexAlgebra.smul_zero_left, smul_zero])
    have hsplit : W.smul c (t : ℤ) (W.smul a (-1) b)
        = W.smul a (-1) (W.smul c (t : ℤ) b)
          + ∑ᶠ j : ℤ, cbz (t : ℤ) j • W.smul (W.smul c j a) ((t : ℤ) + (-1) - j) b := by
      rw [← hcomm]; abel
    rw [hsplit, ← actModeAt_apply ρ (k + N - (t : ℤ)) x, map_add,
      map_finsum (actModeAt ρ (k + N - (t : ℤ)) x) hfinj]
    have e : (∑ᶠ j : ℤ, (actModeAt ρ (k + N - (t : ℤ)) x)
          (cbz (t : ℤ) j • W.smul (W.smul c j a) ((t : ℤ) + (-1) - j) b))
        = ∑ᶠ j : ℤ, cbz (t : ℤ) j •
            ρ.actMode (W.smul (W.smul c j a) ((t : ℤ) - 1 - j) b) (k + N - (t : ℤ)) x := by
      refine finsum_congr fun j => ?_
      rw [map_smul, actModeAt_apply, show (t : ℤ) + (-1) - j = (t : ℤ) - 1 - j from by ring]
    rw [e]
    have eN : (∑ᶠ j : ℤ, cbz (t : ℤ) j •
          ρ.actMode (W.smul (W.smul c j a) ((t : ℤ) - 1 - j) b) (k + N - (t : ℤ)) x)
        = ∑ j ∈ Finset.range Q, cbz (t : ℤ) (j : ℤ) •
            ρ.actMode (W.smul (W.smul c (j : ℤ) a) ((t : ℤ) - 1 - (j : ℤ)) b)
              (k + N - (t : ℤ)) x := by
      rw [finsumZ_eq_finsumN _ Q (fun j hj => by rw [cbz_apply_neg (t : ℤ) hj, zero_smul])
        (fun j hj => by
          obtain ⟨n, hn⟩ : ∃ n : ℕ, j = (n : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
          subst hn
          rw [hQ n (by exact_mod_cast hj), PreVertexAlgebra.smul_zero_left, actMode_zero_left,
            LinearMap.zero_apply, smul_zero])]
      exact finsumN_eq_range_sum _ Q fun j hj => by
        rw [hQ j hj, PreVertexAlgebra.smul_zero_left, actMode_zero_left, LinearMap.zero_apply,
          smul_zero]
    rw [eN, smul_add, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  -- sum the decomposition over `t` and swap the two sums
  have hfinP : (Function.support fun t : ℕ => cbz k (t : ℤ) •
      ρ.actMode (W.smul a (-1) (W.smul c (t : ℤ) b)) (k + N - (t : ℤ)) x).Finite :=
    opeIndexed_support_finite W c b _ fun t ht => by
      rw [ht, PreVertexAlgebra.smul_zero_right, actMode_zero_left, LinearMap.zero_apply, smul_zero]
  have hcolFin : ∀ j : ℕ, (Function.support fun t : ℕ =>
      (cbz k (t : ℤ) * cbz (t : ℤ) (j : ℤ)) •
        ρ.actMode (W.smul (W.smul c (j : ℤ) a) ((t : ℤ) - 1 - (j : ℤ)) b)
          (k + N - (t : ℤ)) x).Finite := by
    intro j
    refine opeShift_support_finite W (W.smul c (j : ℤ) a) b _ (1 + (j : ℤ)) fun t ht => ?_
    rw [show (t : ℤ) - 1 - (j : ℤ) = (t : ℤ) - (1 + (j : ℤ)) from by ring, ht, actMode_zero_left,
      LinearMap.zero_apply, smul_zero]
  have hfinD : (Function.support fun t : ℕ => ∑ j ∈ Finset.range Q,
      (cbz k (t : ℤ) * cbz (t : ℤ) (j : ℤ)) •
        ρ.actMode (W.smul (W.smul c (j : ℤ) a) ((t : ℤ) - 1 - (j : ℤ)) b)
          (k + N - (t : ℤ)) x).Finite :=
    finset_sum_support_finite _ _ fun j _ => hcolFin j
  have hmain : (∑ᶠ t : ℕ, cbz k (t : ℤ) •
        ρ.actMode (W.smul c (t : ℤ) (W.smul a (-1) b)) (k + N - (t : ℤ)) x)
      = (∑ᶠ q : ℕ, cbz k (q : ℤ) •
          sumR ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) (N + k - (q : ℤ)))
        + ∑ᶠ p : ℕ, cbz k (p : ℤ) •
            ρ.actMode (W.smul a (-1) (W.smul c (p : ℤ) b)) (k + N - (p : ℤ)) x := by
    rw [finsum_congr hdec, finsum_add_distrib hfinP hfinD,
      finsum_sum_comm (Finset.range Q) _ fun j _ => hcolFin j]
    have ecol : (∑ j ∈ Finset.range Q, ∑ᶠ t : ℕ, (cbz k (t : ℤ) * cbz (t : ℤ) (j : ℤ)) •
          ρ.actMode (W.smul (W.smul c (j : ℤ) a) ((t : ℤ) - 1 - (j : ℤ)) b)
            (k + N - (t : ℤ)) x)
        = ∑ j ∈ Finset.range Q, cbz k (j : ℤ) •
            sumR ρ (W.smul c (j : ℤ) a) b x (k - (j : ℤ)) (N + k - (j : ℤ)) :=
      Finset.sum_congr rfl fun j _ => vandermonde_column ρ (W.smul c (j : ℤ) a) b x k N j
    rw [ecol, ← finsumN_eq_range_sum _ Q fun q hq => by
      rw [hQ q hq, sumR_zero_left, smul_zero]]
    abel
  rw [actMode_push ρ c (W.smul a (-1) b) x k N, hmain]
  abel

/-! ## The assembly -/

/-- **`DefectModeShift` holds in every truncated `V̂`-representation** (DLM2 Proposition 6.1 at
the canonical pole `ℓ = −1`).

    δ(a, b, c₍ₖ₎x, −1, N)
      = c₍ₖ₎·δ(a, b, x, −1, N)
        − Σ_{p ≥ 0} C(k,p)·δ(a, c₍ₚ₎b, x, −1, k+N−p)
        − Σ_{q ≥ 0} C(k,q)·δ(c₍q₎a, b, x, −1, N+k−q).

The `G`-halves match term for term through `gsum_modeShift` (Step B); the product halves match
through `stepA_dms`, whose `a`-slot correction is an `R`-sum at the shifted index `k − q` — and
`sumR_sub_gsum_shift` turns exactly that shifted `R` minus `G(k−q, N)` into `δ(c₍q₎a,b,x,−1,N+k−q)`.
No grading, no bottom, no `U`, no `π₀`, no PBW. -/
theorem defectModeShift_of_truncated_dms (ρ : VHatRep W M) (htr : ActModeTruncated ρ) :
    DefectModeShift ρ := by
  intro a b c x k N
  obtain ⟨Nq, hNq⟩ := W.smul_eventually_zero c a
  obtain ⟨Np, hNp⟩ := W.smul_eventually_zero c b
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → W.smul c (q : ℤ) a = 0 :=
    ⟨Nq.toNat, fun q hq => hNq (q : ℤ) (by omega)⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ, ∀ p : ℕ, P ≤ p → W.smul c (p : ℤ) b = 0 :=
    ⟨Np.toNat, fun p hp => hNp (p : ℤ) (by omega)⟩
  -- the `q`-column: `R` at the shifted index minus `G` at the shifted index **is** the defect
  have hqcol : ∀ q : ℕ,
      cbz k (q : ℤ) • sumR ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) (N + k - (q : ℤ))
        - cbz k (q : ℤ) • gsum ρ (W.smul c (q : ℤ) a) b x (0 + k - (q : ℤ)) N
      = cbz k (q : ℤ) • defectVec ρ (W.smul c (q : ℤ) a) b x (-1) (N + k - (q : ℤ)) := by
    intro q
    have h := sumR_sub_gsum ρ htr (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) (N + k - (q : ℤ))
    rw [show N + k - (q : ℤ) - (k - (q : ℤ)) = N from by ring] at h
    rw [show (0 : ℤ) + k - (q : ℤ) = k - (q : ℤ) from by ring, ← smul_sub, h]
  -- the `p`-column: the product term minus the `G` term **is** the defect
  have hpcol : ∀ p : ℕ,
      cbz k (p : ℤ) • ρ.actMode (W.smul a (-1) (W.smul c (p : ℤ) b)) (k + N - (p : ℤ)) x
        - cbz k (p : ℤ) • gsum ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ))
      = cbz k (p : ℤ) • defectVec ρ a (W.smul c (p : ℤ) b) x (-1) (k + N - (p : ℤ)) := by
    intro p
    rw [← smul_sub, defectVec_neg_one_eq ρ htr a (W.smul c (p : ℤ) b) x (k + N - (p : ℤ))]
  -- combine the two columns into the two `finsum`s of the statement
  have hqsum : (∑ᶠ q : ℕ, cbz k (q : ℤ) •
        sumR ρ (W.smul c (q : ℤ) a) b x (k - (q : ℤ)) (N + k - (q : ℤ)))
      - (∑ᶠ q : ℕ, cbz k (q : ℤ) • gsum ρ (W.smul c (q : ℤ) a) b x (0 + k - (q : ℤ)) N)
      = ∑ᶠ q : ℕ, cbz k (q : ℤ) • defectVec ρ (W.smul c (q : ℤ) a) b x (-1) (N + k - (q : ℤ)) := by
    rw [← finsum_sub_distrib
      (opeIndexed_support_finite W c a _ fun q hq => by rw [hq, sumR_zero_left, smul_zero])
      (opeIndexed_support_finite W c a _ fun q hq => by rw [hq, gsum_zero_left_dms, smul_zero])]
    exact finsum_congr hqcol
  have hpsum : (∑ᶠ p : ℕ, cbz k (p : ℤ) •
        ρ.actMode (W.smul a (-1) (W.smul c (p : ℤ) b)) (k + N - (p : ℤ)) x)
      - (∑ᶠ p : ℕ, cbz k (p : ℤ) • gsum ρ a (W.smul c (p : ℤ) b) x 0 (k + N - (p : ℤ)))
      = ∑ᶠ p : ℕ, cbz k (p : ℤ) • defectVec ρ a (W.smul c (p : ℤ) b) x (-1) (k + N - (p : ℤ)) := by
    rw [← finsum_sub_distrib
      (opeIndexed_support_finite W c b _ fun p hp => by
        rw [hp, PreVertexAlgebra.smul_zero_right, actMode_zero_left, LinearMap.zero_apply, smul_zero])
      (opeIndexed_support_finite W c b _ fun p hp => by rw [hp, gsum_zero_right_dms, smul_zero])]
    exact finsum_congr hpcol
  rw [defectVec_neg_one_eq ρ htr a b (ρ.actMode c k x) N, stepA_dms ρ a b c x k N,
    gsum_modeShift ρ htr a b c x 0 k N, defectVec_neg_one_eq ρ htr a b x N, map_sub,
    ← hqsum, ← hpsum]
  abel

end VHatRep

/-! ## The induced modules, and the gate conditional on bottom injectivity -/

namespace DLM3

variable {W : VertexOperatorAlgebra 𝒱} {n : ℕ} {U : Type u} [AddCommGroup U] [Module ℂ U]

/-- **`DefectModeShift` on the induced module `Mₙ(U)`** — `indRho P` is truncated
(`ind_actModeTruncated`), so the general theorem applies. -/
theorem defectModeShift_indRho (P : ParabolicRep W n U) :
    VHatRep.DefectModeShift (indRho P) :=
  VHatRep.defectModeShift_of_truncated_dms (indRho P) (ind_actModeTruncated P)

end DLM3

end VHat

/-! ## The `(0,0)` gate, conditional on `PBWFreeness` alone -/

section GateOnPBW

open VHat VHat.DLM3

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The `(0,0)` gate, conditional on the independent `PBWFreeness` assumption.**

    (GATE)   OnmFull W 0 0 = O W

`gate_of_pbw_modeShift` carried two named inputs; `DefectModeShift` is a **theorem**
(`defectModeShift_indRho`), so the only remaining explicit input is
`PBWFreeness (parabolicRepOfAMod W (regularAMod W))`. Level independence is unconditional. The
companion `voaPBWFreeness` supplies this instance from the generic relative-induction field of the
theorem `VOA.pbw : PBWPrinciple`. -/
theorem gate_of_pbw_only (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W))) :
    OnmFull W 0 0 = O W :=
  gate_of_pbw_modeShift hP (defectModeShift_indRho (parabolicRepOfAMod W (regularAMod W)))

/-- The downstream package, conditional on `PBWFreeness` alone. -/
theorem downstream_of_pbw_only (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W))) :
    OnmFull W 0 0 = O W ∧ DJAnnEqAn W 0 ∧ OnmFull W 0 0 = OnFull W 0 ∧ OnmCollapses W 0 :=
  downstream_of_pbw_modeShift hP
    (defectModeShift_indRho (parabolicRepOfAMod W (regularAMod W)))

/-- `U` survives in `M̄₀(U)`, conditional on `Pr` alone (DLM3's `U ∩ J = 0` at `n = 0`). -/
theorem indBarBottom_injective_of_pbw_only (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U)) :
    Function.Injective (indBarBottom (parabolicRepOfAMod W U)) :=
  indBarBottom_injective_of_modeShift W U Pr
    (defectModeShift_indRho (parabolicRepOfAMod W U))

end GateOnPBW

end VOA

-- Axiom check. Explicit `PBWFreeness`/`BottomProjection` parameters are not printed.
