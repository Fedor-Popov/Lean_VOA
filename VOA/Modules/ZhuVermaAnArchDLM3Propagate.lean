/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3Pairing

/-!
# DLM3 §4 at `n = 0` — the two propagations (Propositions 4.6 and 4.7)

This is the **S3 + S4** slice of the B2 attack plan (`PHASE4_PLAN` C-11).  S0/S1/S2 are proved
(`ZhuVermaAnArchDLM3Prop43`, `ZhuVermaAnArchDLM3Pairing`); what was left were the two carried
`Prop`s `BottomPropagates` (DLM3 Prop 4.6) and `OrbitPropagates` (DLM3 Prop 4.7).  Both are
**proved here**, from a single *representation-level*, PBW-free, `U`-free input:

* `VHatRep.DefectModeShift ρ` — the mode-shift law for the canonical-pole (`ℓ = −1`) iterate
  defect.  This is exactly the commutator computation that DLM2 Proposition 6.1
  (`refs/dlm2.txt:784-911`) performs in generating-function form, specialized to the residue
  `ℓ = −1` (the only pole DLM3 §4 needs, everything else being either identically zero or an
  `L₋₁`-derivative of it).

Nothing about `U`, `π₀`, `A(𝒱)`, grading or PBW enters `DefectModeShift`: it is a statement about
an arbitrary `V̂`-representation.

## What is proved here

1. **The `ℓ`-reduction** (`defectVec_mem_dOneSpanAt`).  On a representation whose non-negative-pole
   defects vanish (`DefectNonnegZero`, true for `indRho P` by the proved `indDefectVec_nonneg`),
   *every* iterate defect at `x` lies in the span of the `ℓ = −1` defects **at the same `x`**: the
   `ℓ ≥ 0` ones are zero, and the `ℓ ≤ −2` ones are `L₋₁`-derivatives (`defectVec_Lneg1_left`).
2. **DLM3 Proposition 4.7 is free from 4.6** (`defectSubmodule_eq_dOneSpan`).  `DefectModeShift`
   says the *plain span* of the canonical defects is already `V̂`-invariant, so it **equals** the
   defect submodule.  Hence "the projection kills every defect" upgrades by itself to "the
   projection kills every `U(V̂)`-translate of every defect" — which is DLM3's `U(V̂)W ⊆ J`.
3. **DLM3 Proposition 4.6 by a level argument** (`proj_defect_neg_one_top`).  This is the new
   ingredient and it is *cheap*, because at `n = 0` the induced module is non-negatively graded and
   its level-`0` piece is exactly the bottom (both **PBW-free**, `levCover_eq_bot_of_neg` and
   `levCover_zero_eq_range`).  Straightening (`levCover_eq_posLevel`) lets the generation run over
   **non-negative** modes only, and for a non-negative mode `x ∈ V̂(e)`, `e ≥ 0`:

   * if the defect sits strictly above level `0`, `x·δ` sits strictly above level `0` and `π₀`
     kills it outright;
   * if it sits strictly below level `0`, it is already `0`;
   * if it sits *at* level `0`, then it lies in `1 ⊗ U`, where `π₀` is **injective** — so the
     induction hypothesis `π₀ δ = 0` forces `δ = 0`.

   So the troublesome term `π₀(x · δ)` of the DLM2 induction never has any content at `n = 0`.
4. **Assembly**: `defectPairsToZero_of_modeShift`, `bottomPropagates_of_modeShift`,
   `orbitPropagates_of_modeShift`, and the gate `gate_of_pbw_modeShift`.

## The toolkit for `DefectModeShift`, and exactly what is left of it

The normal-ordered rewriting of the canonical defect is proved here in full:

    δ(a,b,x,−1,N) = (a₍₋₁₎b)₍N₎x − G(0,N),
    G(s,N) = Σ_{i ≥ 0} a₍ₛ₋₁₋ᵢ₎b₍N₊ᵢ₎x + Σ_{i ≥ 0} b₍N₋₁₋ᵢ₎a₍ₛ₊ᵢ₎x

(`defectVec_neg_one_eq`), together with

* `gsum_succ` — the telescoping `G(s,N) − G(s−1,N+1) = [a₍ₛ₋₁₎, b₍N₎]x`;
* `actMode_comm_vec` — the free loop commutator in vector form;
* `gsum_sub_gsum_zero` — **the hockey stick**, `G(s,T−s) − G(0,T) = Σ_t C(s,t+1)(a₍ₜ₎b)₍T₋₁₋ₜ₎x`,
  for **every** `s ∈ ℤ` (Pascal, iterated in both directions);
* `sumR_sub_gsum_shift` — the resulting **`a`-slot shift law**
  `Σ_r C(s,r)(a₍ᵣ₋₁₎b)₍T₋ᵣ₎x − G(s,T−s) = δ(a,b,x,−1,T)`.

`sumR_sub_gsum_shift` is precisely the step that makes DLM2's `a`-slot bookkeeping collapse, and it
is the only non-mechanical ingredient of `DefectModeShift`.  What is *not* formalized here is the
remaining mechanical bookkeeping: pushing `c₍ₖ₎` leftwards term by term through `G(0,N)` (three
`actMode_comm_vec` applications and one `finsum_sum_comm` swap per half), and the single
double-sum reindexing `Σ_p Σ_t C(k,p)C(p,t)· = Σ_t Σ_r C(k,t)C(k−t,r)·` (`cbz_subsetOfSubset` with
`r = p − t`) that turns the `𝒱`-level commutator
`c₍ₚ₎(a₍₋₁₎b) = a₍₋₁₎(c₍ₚ₎b) + Σ_t C(p,t)(c₍ₜ₎a)₍ₚ₋₁₋ₜ₎b`
(`mode_commutator_vec`) into the `a`-slot shift law's left-hand side.

## Status, stated without over-claim

* `DefectModeShift (indRho P)` — **carried, named hypothesis**; a pure `V̂`-representation identity
  (DLM2 Prop 6.1).  It is *not* assumed anywhere silently and *no* axiom is declared.  Its
  non-mechanical core (the hockey stick) **is** proved here.
* `BottomProjection` / `PBWFreeness` — bottom injectivity is an explicit assumption, untouched
  here; level independence is unconditional. Concrete adjoint and Heisenberg instances exist
  axiom-free. The companion project wrapper supplies the `regularAMod` witness from the generic
  relative-induction field of the theorem `VOA.pbw : PBWPrinciple`.
* Everything else in the S3/S4 chain is proved here.

## References
DLM3 (`q-alg/9612010v2`) §4: Prop 4.3 (`refs/dlm3.txt:751`), Prop 4.6 (`:1086-1096`),
Prop 4.7 (`:1098-1122`); DLM2 (`q-alg/9509005`) Prop 6.1 (`refs/dlm2.txt:784-911`);
`ZhuVermaAnArchDLM3Survival` (`levCover_eq_bot_of_neg`, `levCover_zero_eq_range`, `posOrbit`),
`ZhuVermaAnArchDLM3Prop43` (`proj_indDefectVec_bottom`), `ZhuVermaAnArchDLM3Pairing`
(`ProjKillsDefectSubmodule`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## A `finsum` bookkeeping lemma -/

/-- A `finsum` of a family taking values in a submodule lies in that submodule (if the support is
infinite the `finsum` is `0`, which is also in the submodule). -/
theorem finsum_mem_of_forall_mem {ι : Type*} {N : Type*} [AddCommGroup N] [Module ℂ N]
    (S : Submodule ℂ N) (f : ι → N) (hf : ∀ i, f i ∈ S) : (∑ᶠ i, f i) ∈ S := by
  classical
  by_cases h : (Function.support f).Finite
  · have hsub : Function.support f ⊆ (h.toFinset : Set ι) := by
      rw [Set.Finite.coe_toFinset]
    rw [finsum_eq_sum_of_support_subset f hsub]
    exact Submodule.sum_mem _ fun i _ => hf i
  · rw [finsum_of_infinite_support h]
    exact S.zero_mem

namespace VHat

namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The canonical-pole defects and their spans -/

/-- The **canonical-pole defect set at a fixed vector** `x`: all `δ(a, b, x, −1, N)`. -/
def dOneSetAt (ρ : VHatRep W M) (x : M) : Set M :=
  {y | ∃ (a b : 𝒱) (N : ℤ), y = defectVec ρ a b x (-1) N}

/-- The span of the canonical-pole defects at a fixed vector `x`. -/
noncomputable def dOneSpanAt (ρ : VHatRep W M) (x : M) : Submodule ℂ M :=
  Submodule.span ℂ (dOneSetAt ρ x)

/-- A canonical-pole defect at `x` lies in `dOneSpanAt ρ x`. -/
theorem defectVec_neg_one_mem_dOneSpanAt (ρ : VHatRep W M) (a b : 𝒱) (x : M) (N : ℤ) :
    defectVec ρ a b x (-1) N ∈ dOneSpanAt ρ x :=
  Submodule.subset_span ⟨a, b, N, rfl⟩

/-- The **canonical-pole defect set**: all `δ(a, b, x, −1, N)`, `x` ranging over `M`. -/
def dOneSet (ρ : VHatRep W M) : Set M :=
  {y | ∃ (a b : 𝒱) (x : M) (N : ℤ), y = defectVec ρ a b x (-1) N}

/-- The span of all canonical-pole defects. -/
noncomputable def dOneSpan (ρ : VHatRep W M) : Submodule ℂ M := Submodule.span ℂ (dOneSet ρ)

/-- Defects at a fixed vector are defects. -/
theorem dOneSpanAt_le_dOneSpan (ρ : VHatRep W M) (x : M) : dOneSpanAt ρ x ≤ dOneSpan ρ := by
  refine Submodule.span_le.mpr ?_
  rintro y ⟨a, b, N, rfl⟩
  exact Submodule.subset_span ⟨a, b, x, N, rfl⟩

/-! ### Toolkit for the mode-shift law

The canonical-pole defect is `δ(a,b,x,−1,N) = (a₍₋₁₎b)₍N₎x − G(0,N)` where

    G(s, N) = Σ_{i ≥ 0} a₍ₛ₋₁₋ᵢ₎ b₍N₊ᵢ₎ x + Σ_{i ≥ 0} b₍N₋₁₋ᵢ₎ a₍ₛ₊ᵢ₎ x

is the *shifted* normal-ordered sum.  Two facts drive everything:

* **telescoping** `gsum_succ`: `G(s,N) − G(s−1,N+1) = [a₍ₛ₋₁₎, b₍N₎]` — a one-line index shift on
  each half plus the free loop commutator `actMode_bracket`;
* **the hockey stick** `gsum_sub_gsum_zero`: iterating the telescoping in *both* directions along
  `s` sums the binomials by Pascal, `Σ_{m<s} C(m,t) = C(s,t+1)`, valid for every `s ∈ ℤ`.
-/

/-- `(−1)ⁱ·C(−1,i) = 1` for `i ≥ 0`. -/
theorem negOnePow_mul_cbz_neg_one (i : ℕ) : negOnePow (i : ℤ) * cbz (-1 : ℤ) (i : ℤ) = 1 := by
  rw [ZhuRes.cbz_neg_one i, negOnePow_natCast, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- Splitting off the `i = 0` term of an `ℕ`-indexed `finsum`. -/
theorem finsumN_split_zero {N : Type*} [AddCommGroup N] (f : ℕ → N)
    (hf : (Function.support f).Finite) : (∑ᶠ i : ℕ, f i) = f 0 + ∑ᶠ i : ℕ, f (i + 1) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ i : ℕ, K ≤ i → f i = 0 := by
    refine ⟨hf.toFinset.sup id + 1, fun i hi => ?_⟩
    by_contra hne
    have hmem : i ∈ hf.toFinset := by rw [Set.Finite.mem_toFinset]; exact hne
    have hle : i ≤ hf.toFinset.sup id := Finset.le_sup (f := id) hmem
    omega
  have h1 : (∑ᶠ i : ℕ, f i) = ∑ i ∈ Finset.range K, f i := by
    refine finsum_eq_sum_of_support_subset f ?_
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hi (hK i (by omega))
  have h2 : (∑ᶠ i : ℕ, f (i + 1)) = ∑ i ∈ Finset.range K, f (i + 1) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hi (hK (i + 1) (by omega))
  have h3 : ∑ i ∈ Finset.range (K + 1), f i = (∑ i ∈ Finset.range K, f (i + 1)) + f 0 :=
    Finset.sum_range_succ' f K
  have h4 : ∑ i ∈ Finset.range (K + 1), f i = (∑ i ∈ Finset.range K, f i) + f K :=
    Finset.sum_range_succ f K
  rw [hK K le_rfl, add_zero] at h4
  rw [h1, h2, ← h4, h3]
  abel

/-- Bridge from an `ℤ`-indexed `finsum` supported in `[0, K)` to the `ℕ`-indexed one. -/
theorem finsumZ_eq_finsumN {N : Type*} [AddCommMonoid N] (F : ℤ → N) (K : ℕ)
    (hlo : ∀ i : ℤ, i < 0 → F i = 0) (hhi : ∀ i : ℤ, (K : ℤ) ≤ i → F i = 0) :
    (∑ᶠ i : ℤ, F i) = ∑ᶠ i : ℕ, F (i : ℤ) := by
  rw [← range_sum_eq_finsumZ K F (fun x hx => hx.elim (hlo x) (hhi x))]
  refine (finsum_eq_sum_of_support_subset (fun i : ℕ => F (i : ℤ)) ?_).symm
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hi (hhi (i : ℤ) (by omega))

/-- The "product" half of the canonical-pole defect sum, at left shift `s`. -/
noncomputable def pterm (ρ : VHatRep W M) (a b : 𝒱) (x : M) (s N : ℤ) (i : ℕ) : M :=
  ρ.actMode a (s - 1 - (i : ℤ)) (ρ.actMode b (N + (i : ℤ)) x)

/-- The "opposite" half of the canonical-pole defect sum, at left shift `s`. -/
noncomputable def qterm (ρ : VHatRep W M) (a b : 𝒱) (x : M) (s N : ℤ) (i : ℕ) : M :=
  ρ.actMode b (N - 1 - (i : ℤ)) (ρ.actMode a (s + (i : ℤ)) x)

/-- The shifted normal-ordered sum `G(s, N)`. -/
noncomputable def gsum (ρ : VHatRep W M) (a b : 𝒱) (x : M) (s N : ℤ) : M :=
  (∑ᶠ i : ℕ, pterm ρ a b x s N i) + ∑ᶠ i : ℕ, qterm ρ a b x s N i

theorem pterm_eq_zero_of_le (ρ : VHatRep W M) {b : 𝒱} {x : M} {Nv : ℤ}
    (hNv : ∀ m : ℤ, Nv ≤ m → ρ.actMode b m x = 0) (a : 𝒱) (s N : ℤ) {i : ℕ}
    (hi : Nv - N ≤ (i : ℤ)) : pterm ρ a b x s N i = 0 := by
  rw [pterm, hNv (N + (i : ℤ)) (by omega), map_zero]

theorem qterm_eq_zero_of_le (ρ : VHatRep W M) {a : 𝒱} {x : M} {Nu : ℤ}
    (hNu : ∀ m : ℤ, Nu ≤ m → ρ.actMode a m x = 0) (b : 𝒱) (s N : ℤ) {i : ℕ}
    (hi : Nu - s ≤ (i : ℤ)) : qterm ρ a b x s N i = 0 := by
  rw [qterm, hNu (s + (i : ℤ)) (by omega), map_zero]

theorem pterm_support_finite (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M)
    (s N : ℤ) : (Function.support (pterm ρ a b x s N)).Finite := by
  obtain ⟨Nv, hNv⟩ := htr b x
  refine Set.Finite.subset (Set.finite_Iio (Nv - N).toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra h
  exact hi (pterm_eq_zero_of_le ρ hNv a s N (by omega))

theorem qterm_support_finite (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M)
    (s N : ℤ) : (Function.support (qterm ρ a b x s N)).Finite := by
  obtain ⟨Nu, hNu⟩ := htr a x
  refine Set.Finite.subset (Set.finite_Iio (Nu - s).toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra h
  exact hi (qterm_eq_zero_of_le ρ hNu b s N (by omega))

/-- **The canonical-pole defect in normal-ordered form**:
`δ(a,b,x,−1,N) = (a₍₋₁₎b)₍N₎x − G(0,N)`. -/
theorem defectVec_neg_one_eq (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M)
    (N : ℤ) : defectVec ρ a b x (-1) N
      = ρ.actMode (W.smul a (-1) b) N x - gsum ρ a b x 0 N := by
  obtain ⟨Nv, hNv⟩ := htr b x
  obtain ⟨Nu, hNu⟩ := htr a x
  have ha : (∑ᶠ i : ℤ, aterm ρ a b x (-1) N i) = ∑ᶠ i : ℕ, pterm ρ a b x 0 N i := by
    rw [finsumZ_eq_finsumN (aterm ρ a b x (-1) N) (Nv - N).toNat
      (fun i hi => by rw [aterm, cbz_apply_neg (-1) hi, mul_zero, zero_smul])
      (fun i hi => by
        rw [aterm, hNv (N + i) (by omega), map_zero, smul_zero])]
    refine finsum_congr fun i => ?_
    rw [aterm, negOnePow_mul_cbz_neg_one i, one_smul, pterm,
      show (0 : ℤ) - 1 - (i : ℤ) = -1 - (i : ℤ) from by ring]
  have hb : (∑ᶠ i : ℤ, bterm ρ a b x (-1) N i) = -∑ᶠ i : ℕ, qterm ρ a b x 0 N i := by
    rw [finsumZ_eq_finsumN (bterm ρ a b x (-1) N) (Nu).toNat
      (fun i hi => by rw [bterm, cbz_apply_neg (-1) hi, mul_zero, zero_smul])
      (fun i hi => by
        rw [bterm, hNu i (by omega), map_zero, smul_zero, smul_zero])]
    rw [show (-∑ᶠ i : ℕ, qterm ρ a b x 0 N i)
        = ∑ᶠ i : ℕ, (-1 : ℂ) • qterm ρ a b x 0 N i from by
      rw [← smul_finsum' (-1 : ℂ) (qterm_support_finite ρ htr a b x 0 N)]
      simp]
    refine finsum_congr fun i => ?_
    rw [bterm, negOnePow_mul_cbz_neg_one i, one_smul, show negOnePow (-1 : ℤ) = (-1 : ℂ) from by
      simp [negOnePow], qterm, show (0 : ℤ) + (i : ℤ) = (i : ℤ) from by ring,
      show (-1 : ℤ) + N - (i : ℤ) = N - 1 - (i : ℤ) from by ring]
  rw [defectVec_eq_split ρ htr a b x (-1) N, ha, hb, gsum]
  abel

/-- **The telescoping step** `G(s,N) − G(s−1,N+1) = [a₍ₛ₋₁₎, b₍N₎]x`.  Each half shifts its
summation index by one; the leftover is exactly the commutator. -/
theorem gsum_succ (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M) (s N : ℤ) :
    gsum ρ a b x s N - gsum ρ a b x (s - 1) (N + 1)
      = ρ.actMode a (s - 1) (ρ.actMode b N x) - ρ.actMode b N (ρ.actMode a (s - 1) x) := by
  have hcast : ∀ i : ℕ, (((i + 1 : ℕ)) : ℤ) = (i : ℤ) + 1 := by intro i; push_cast; ring
  have hp : ∀ i : ℕ, pterm ρ a b x (s - 1) (N + 1) i = pterm ρ a b x s N (i + 1) := by
    intro i
    simp only [pterm, hcast]
    rw [show s - 1 - 1 - (i : ℤ) = s - 1 - ((i : ℤ) + 1) from by ring,
      show N + 1 + (i : ℤ) = N + ((i : ℤ) + 1) from by ring]
  have hq : ∀ i : ℕ, qterm ρ a b x s N i = qterm ρ a b x (s - 1) (N + 1) (i + 1) := by
    intro i
    simp only [qterm, hcast]
    rw [show N + 1 - 1 - ((i : ℤ) + 1) = N - 1 - (i : ℤ) from by ring,
      show s - 1 + ((i : ℤ) + 1) = s + (i : ℤ) from by ring]
  have hp0 := finsumN_split_zero (pterm ρ a b x s N) (pterm_support_finite ρ htr a b x s N)
  have hq0 := finsumN_split_zero (qterm ρ a b x (s - 1) (N + 1))
    (qterm_support_finite ρ htr a b x (s - 1) (N + 1))
  have hpsum : (∑ᶠ i : ℕ, pterm ρ a b x (s - 1) (N + 1) i)
      = ∑ᶠ i : ℕ, pterm ρ a b x s N (i + 1) := finsum_congr hp
  have hqsum : (∑ᶠ i : ℕ, qterm ρ a b x s N i)
      = ∑ᶠ i : ℕ, qterm ρ a b x (s - 1) (N + 1) (i + 1) := finsum_congr hq
  have hpval : pterm ρ a b x s N 0 = ρ.actMode a (s - 1) (ρ.actMode b N x) := by
    simp only [pterm, Nat.cast_zero, sub_zero, add_zero]
  have hqval : qterm ρ a b x (s - 1) (N + 1) 0 = ρ.actMode b N (ρ.actMode a (s - 1) x) := by
    simp only [qterm, Nat.cast_zero, sub_zero, add_zero]
    rw [show N + 1 - 1 = N from by ring]
  rw [gsum, gsum, hpsum, hqsum, ← hpval, ← hqval, hp0, hq0]
  abel

/-- The loop commutator in vector form, `ℕ`-indexed:
`[a₍ₘ₎, b₍ₙ₎]x = Σ_t C(m,t)·(a₍ₜ₎b)₍ₘ₊ₙ₋ₜ₎x`. -/
theorem actMode_comm_vec (ρ : VHatRep W M) (a b : 𝒱) (x : M) (m n : ℤ) :
    ρ.actMode a m (ρ.actMode b n x) - ρ.actMode b n (ρ.actMode a m x)
      = ∑ᶠ t : ℕ, cbz m (t : ℤ) • ρ.actMode (W.smul a (t : ℤ) b) (m + n - (t : ℤ)) x := by
  classical
  have hfin : (Function.support fun t : ℕ =>
      (gBinom m t) • ρ.actMode (W.smul a (t : ℤ) b) (m + n - (t : ℤ))).Finite := by
    obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
    refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Iio]
    by_contra hcon
    refine hi ?_
    rw [hNz (i : ℤ) (by omega), actMode_zero_left, smul_zero]
  let ev : Module.End ℂ M →ₗ[ℂ] M :=
    { toFun := fun T => T x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := congrArg (fun T : Module.End ℂ M => ev T) (actMode_bracket ρ a b m n)
  simp only [ev, LinearMap.coe_mk, AddHom.coe_mk] at h
  rw [Ring.lie_def] at h
  rw [show (ρ.actMode a m * ρ.actMode b n - ρ.actMode b n * ρ.actMode a m) x
      = ρ.actMode a m (ρ.actMode b n x) - ρ.actMode b n (ρ.actMode a m x) from rfl] at h
  rw [h]
  rw [show (∑ᶠ t : ℕ, (gBinom m t) • ρ.actMode (W.smul a (t : ℤ) b) (m + n - (t : ℤ))) x
      = ∑ᶠ t : ℕ, ((gBinom m t) • ρ.actMode (W.smul a (t : ℤ) b) (m + n - (t : ℤ))) x from by
    exact map_finsum
      ({ toFun := fun T : Module.End ℂ M => T x
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } : Module.End ℂ M →ₗ[ℂ] M) hfin]
  refine finsum_congr fun t => ?_
  rw [cbz_apply_nonneg m (Int.natCast_nonneg t), Int.toNat_natCast]
  rfl

/-- The hockey-stick sum `Σ_{t ≥ 0} C(s, t+1)·(a₍ₜ₎b)₍T₋₁₋ₜ₎x`. -/
noncomputable def hockSum (ρ : VHatRep W M) (a b : 𝒱) (x : M) (s T : ℤ) : M :=
  ∑ᶠ t : ℕ, cbz s ((t : ℤ) + 1) • ρ.actMode (W.smul a (t : ℤ) b) (T - 1 - (t : ℤ)) x

theorem opeMode_support_finite (ρ : VHatRep W M) (a b : 𝒱) (x : M) (T : ℤ) (g : ℕ → ℂ) :
    (Function.support fun t : ℕ =>
      g t • ρ.actMode (W.smul a (t : ℤ) b) (T - 1 - (t : ℤ)) x).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  refine hi ?_
  rw [hNz (i : ℤ) (by omega), actMode_zero_left, LinearMap.zero_apply, smul_zero]

/-- Pascal, applied to the hockey-stick sum: `hock(s+1) − hock(s)` is the commutator family. -/
theorem hockSum_succ (ρ : VHatRep W M) (a b : 𝒱) (x : M) (s T : ℤ) :
    hockSum ρ a b x (s + 1) T - hockSum ρ a b x s T
      = ∑ᶠ t : ℕ, cbz s (t : ℤ) • ρ.actMode (W.smul a (t : ℤ) b) (T - 1 - (t : ℤ)) x := by
  rw [hockSum, hockSum,
    ← finsum_sub_distrib (opeMode_support_finite ρ a b x T (fun t => cbz (s + 1) ((t : ℤ) + 1)))
      (opeMode_support_finite ρ a b x T (fun t => cbz s ((t : ℤ) + 1)))]
  refine finsum_congr fun t => ?_
  rw [← sub_smul]
  congr 1
  rw [cbz_pascal_up s ((t : ℤ) + 1), show ((t : ℤ) + 1 - 1) = (t : ℤ) from by ring]
  ring

/-- The telescoping step along the *anti-diagonal* `s + N = T`, in commutator form. -/
theorem gsum_shift_succ (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M) (s T : ℤ) :
    gsum ρ a b x (s + 1) (T - (s + 1)) - gsum ρ a b x s (T - s)
      = ∑ᶠ t : ℕ, cbz s (t : ℤ) • ρ.actMode (W.smul a (t : ℤ) b) (T - 1 - (t : ℤ)) x := by
  have h := gsum_succ ρ htr a b x (s + 1) (T - (s + 1))
  rw [show (s + 1 - 1 : ℤ) = s from by ring, show (T - (s + 1) + 1 : ℤ) = T - s from by ring] at h
  rw [h, actMode_comm_vec ρ a b x s (T - (s + 1))]
  refine finsum_congr fun t => ?_
  rw [show s + (T - (s + 1)) - (t : ℤ) = T - 1 - (t : ℤ) from by ring]

/-- **The hockey stick.**  Iterating the telescoping step in both directions along `s`:

    G(s, T−s) − G(0, T) = Σ_{t ≥ 0} C(s, t+1)·(a₍ₜ₎b)₍T₋₁₋ₜ₎x     for every `s ∈ ℤ`.

The binomial bookkeeping is exactly Pascal's rule `C(s,j) − C(s−1,j) = C(s−1,j−1)`, i.e. the
identity `Σ_{m<s} C(m,t) = C(s,t+1)` extended to all integers `s`. -/
theorem gsum_sub_gsum_zero (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M)
    (s T : ℤ) : gsum ρ a b x s (T - s) - gsum ρ a b x 0 T = hockSum ρ a b x s T := by
  induction s using Int.induction_on with
  | zero =>
    rw [sub_zero, sub_self, hockSum]
    refine (finsum_eq_zero_of_forall_eq_zero fun t => ?_).symm
    rw [cbz_zero_left ((t : ℤ) + 1), if_neg (by omega), zero_smul]
  | succ i ih =>
    have h1 := gsum_shift_succ ρ htr a b x (i : ℤ) T
    have h2 := hockSum_succ ρ a b x (i : ℤ) T
    have : gsum ρ a b x ((i : ℤ) + 1) (T - ((i : ℤ) + 1)) - gsum ρ a b x 0 T
        = (gsum ρ a b x ((i : ℤ) + 1) (T - ((i : ℤ) + 1)) - gsum ρ a b x (i : ℤ) (T - (i : ℤ)))
          + (gsum ρ a b x (i : ℤ) (T - (i : ℤ)) - gsum ρ a b x 0 T) := by abel
    rw [this, h1, ih, ← h2]
    abel
  | pred i ih =>
    have h1 := gsum_shift_succ ρ htr a b x (-(i : ℤ) - 1) T
    have h2 := hockSum_succ ρ a b x (-(i : ℤ) - 1) T
    rw [show (-(i : ℤ) - 1 + 1) = -(i : ℤ) from by ring] at h1 h2
    have : gsum ρ a b x (-(i : ℤ) - 1) (T - (-(i : ℤ) - 1)) - gsum ρ a b x 0 T
        = (gsum ρ a b x (-(i : ℤ)) (T - (-(i : ℤ))) - gsum ρ a b x 0 T)
          - (gsum ρ a b x (-(i : ℤ)) (T - (-(i : ℤ)))
              - gsum ρ a b x (-(i : ℤ) - 1) (T - (-(i : ℤ) - 1))) := by abel
    rw [this, ih, h1]
    have h3 : hockSum ρ a b x (-(i : ℤ)) T - hockSum ρ a b x (-(i : ℤ) - 1) T
        = ∑ᶠ t : ℕ, cbz (-(i : ℤ) - 1) (t : ℤ) •
            ρ.actMode (W.smul a (t : ℤ) b) (T - 1 - (t : ℤ)) x := h2
    rw [← h3]
    abel

/-- **The `a`-slot shift law.**  The full `Σ_{r ≥ 0} C(s,r)·(a₍ᵣ₋₁₎b)₍T₋ᵣ₎x` sum, minus the
shifted normal-ordered sum, is exactly the *unshifted* canonical-pole defect. -/
theorem sumR_sub_gsum_shift (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (a b : 𝒱) (x : M)
    (s T : ℤ) :
    (∑ᶠ r : ℕ, cbz s (r : ℤ) • ρ.actMode (W.smul a ((r : ℤ) - 1) b) (T - (r : ℤ)) x)
      - gsum ρ a b x s (T - s) = defectVec ρ a b x (-1) T := by
  have hfin : (Function.support
      fun r : ℕ =>
        cbz s (r : ℤ) • ρ.actMode (W.smul a ((r : ℤ) - 1) b) (T - (r : ℤ)) x).Finite := by
    obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
    refine Set.Finite.subset (Set.finite_Iio (Nz + 1).toNat) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Iio]
    by_contra hcon
    refine hi ?_
    rw [hNz ((i : ℤ) - 1) (by omega), actMode_zero_left, LinearMap.zero_apply, smul_zero]
  have hsplit : (∑ᶠ r : ℕ, cbz s (r : ℤ) •
        ρ.actMode (W.smul a ((r : ℤ) - 1) b) (T - (r : ℤ)) x)
      = (cbz s ((0 : ℕ) : ℤ) • ρ.actMode (W.smul a (((0 : ℕ) : ℤ) - 1) b) (T - ((0 : ℕ) : ℤ)) x)
        + ∑ᶠ r : ℕ, cbz s ((r + 1 : ℕ) : ℤ) •
            ρ.actMode (W.smul a (((r + 1 : ℕ) : ℤ) - 1) b) (T - ((r + 1 : ℕ) : ℤ)) x :=
    finsumN_split_zero _ hfin
  have hcast : ∀ r : ℕ, (((r + 1 : ℕ)) : ℤ) = (r : ℤ) + 1 := by intro r; push_cast; ring
  have hzero : cbz s ((0 : ℕ) : ℤ) • ρ.actMode (W.smul a (((0 : ℕ) : ℤ) - 1) b)
      (T - ((0 : ℕ) : ℤ)) x = ρ.actMode (W.smul a (-1) b) T x := by
    simp only [Nat.cast_zero, zero_sub, sub_zero, cbz_zero, one_smul]
  have htail : (∑ᶠ r : ℕ, cbz s ((r + 1 : ℕ) : ℤ) •
      ρ.actMode (W.smul a (((r + 1 : ℕ) : ℤ) - 1) b) (T - ((r + 1 : ℕ) : ℤ)) x)
      = hockSum ρ a b x s T := by
    rw [hockSum]
    refine finsum_congr fun r => ?_
    rw [hcast r, show ((r : ℤ) + 1 - 1) = (r : ℤ) from by ring,
      show T - ((r : ℤ) + 1) = T - 1 - (r : ℤ) from by ring]
  rw [hsplit, hzero, htail, defectVec_neg_one_eq ρ htr a b x T,
    ← gsum_sub_gsum_zero ρ htr a b x s T]
  abel

/-! ## The mode-shift law (DLM2 Proposition 6.1 at `ℓ = −1`) -/

/-- **DLM2 Proposition 6.1's commutator core, at the canonical pole `ℓ = −1`.**

    δ(a, b, c₍ₖ₎x, −1, N)
      = c₍ₖ₎·δ(a, b, x, −1, N)
        − Σ_{p ≥ 0} C(k,p)·δ(a, c₍ₚ₎b, x, −1, k+N−p)
        − Σ_{q ≥ 0} C(k,q)·δ(c₍q₎a, b, x, −1, N+k−q).

This is exactly the displayed computation of DLM2 Proposition 6.1 (`refs/dlm2.txt:784-911`) —
push `c(m)` leftwards through `Y(a,z₀+z₂)Y(b,z₂)` and through `Y(Y(a,z₀)b,z₂)` with the commutator
formula `[c(m), Y(b,z)] = Σᵢ C(m,i) z^{m−i} Y(c₍ᵢ₎b, z)` — written at the single residue `ℓ = −1`.

It is a statement about an **arbitrary** `V̂`-representation: no grading, no bottom, no `U`, no
`π₀`, no PBW.  **Carried as a named hypothesis; never assumed silently, and no axiom is
declared.** -/
def DefectModeShift (ρ : VHatRep W M) : Prop :=
  ∀ (a b c : 𝒱) (x : M) (k N : ℤ),
    defectVec ρ a b (ρ.actMode c k x) (-1) N
      = ρ.actMode c k (defectVec ρ a b x (-1) N)
        - (∑ᶠ p : ℕ, cbz k (p : ℤ) • defectVec ρ a (W.smul c (p : ℤ) b) x (-1) (k + N - (p : ℤ)))
        - ∑ᶠ q : ℕ, cbz k (q : ℤ) • defectVec ρ (W.smul c (q : ℤ) a) b x (-1) (N + k - (q : ℤ))

/-- The mode-shift law, in membership form: applying a mode to a canonical defect changes it only
by canonical defects **at the same vector**. -/
theorem defectVec_actMode_sub_mem_dOneSpanAt (ρ : VHatRep W M) (h : DefectModeShift ρ)
    (a b c : 𝒱) (x : M) (k N : ℤ) :
    defectVec ρ a b (ρ.actMode c k x) (-1) N - ρ.actMode c k (defectVec ρ a b x (-1) N)
      ∈ dOneSpanAt ρ x := by
  have h1 : (∑ᶠ p : ℕ, cbz k (p : ℤ) •
      defectVec ρ a (W.smul c (p : ℤ) b) x (-1) (k + N - (p : ℤ))) ∈ dOneSpanAt ρ x :=
    finsum_mem_of_forall_mem _ _ fun p =>
      Submodule.smul_mem _ _ (defectVec_neg_one_mem_dOneSpanAt ρ _ _ _ _)
  have h2 : (∑ᶠ q : ℕ, cbz k (q : ℤ) •
      defectVec ρ (W.smul c (q : ℤ) a) b x (-1) (N + k - (q : ℤ))) ∈ dOneSpanAt ρ x :=
    finsum_mem_of_forall_mem _ _ fun q =>
      Submodule.smul_mem _ _ (defectVec_neg_one_mem_dOneSpanAt ρ _ _ _ _)
  have hsum := Submodule.sub_mem _ (Submodule.neg_mem _ h1) h2
  rw [h a b c x k N]
  convert hsum using 1
  abel

/-- The mode-shift law for a general element of `V̂` (both sides are linear in it). -/
theorem defectVec_rho_sub_mem_dOneSpanAt (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (h : DefectModeShift ρ) (a b : 𝒱) (g : VHatCarrier W) (x : M) (N : ℤ) :
    defectVec ρ a b (ρ g x) (-1) N - ρ g (defectVec ρ a b x (-1) N) ∈ dOneSpanAt ρ x := by
  have hspan : g ∈ Submodule.span ℂ (Set.range (fun p : 𝒱 × ℤ => gen W p.1 p.2)) := by
    rw [gen_span_top]; exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun g _ => defectVec ρ a b (ρ g x) (-1) N - ρ g (defectVec ρ a b x (-1) N)
      ∈ dOneSpanAt ρ x) ?_ ?_ ?_ ?_ hspan
  · rintro g ⟨⟨c, k⟩, rfl⟩
    exact defectVec_actMode_sub_mem_dOneSpanAt ρ h a b c x k N
  · change defectVec ρ a b (ρ 0 x) (-1) N - ρ 0 (defectVec ρ a b x (-1) N) ∈ dOneSpanAt ρ x
    rw [map_zero, LinearMap.zero_apply, LinearMap.zero_apply, defectVec_zero_right ρ htr,
      sub_zero]
    exact Submodule.zero_mem _
  · intro g₁ g₂ _ _ h₁ h₂
    change defectVec ρ a b (ρ (g₁ + g₂) x) (-1) N - ρ (g₁ + g₂) (defectVec ρ a b x (-1) N)
      ∈ dOneSpanAt ρ x
    rw [map_add, LinearMap.add_apply, LinearMap.add_apply, defectVec_add_right ρ htr]
    have : defectVec ρ a b (ρ g₁ x) (-1) N + defectVec ρ a b (ρ g₂ x) (-1) N
        - (ρ g₁ (defectVec ρ a b x (-1) N) + ρ g₂ (defectVec ρ a b x (-1) N))
        = (defectVec ρ a b (ρ g₁ x) (-1) N - ρ g₁ (defectVec ρ a b x (-1) N))
          + (defectVec ρ a b (ρ g₂ x) (-1) N - ρ g₂ (defectVec ρ a b x (-1) N)) := by abel
    rw [this]
    exact Submodule.add_mem _ h₁ h₂
  · intro c g₁ _ h₁
    change defectVec ρ a b (ρ (c • g₁) x) (-1) N - ρ (c • g₁) (defectVec ρ a b x (-1) N)
      ∈ dOneSpanAt ρ x
    rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, defectVec_smul_right ρ htr,
      ← smul_sub]
    exact Submodule.smul_mem _ _ h₁

/-- **DLM3 Proposition 4.7, at the level of the representation.**  Under the mode-shift law the
*plain span* of the canonical defects is already a `V̂`-subrepresentation — no `U(V̂)`-orbit is
needed. -/
theorem dOneSpan_invariant (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (h : DefectModeShift ρ) :
    IsInvariant ρ (dOneSpan ρ) := by
  intro g d hd
  refine Submodule.span_induction (p := fun d _ => ρ g d ∈ dOneSpan ρ) ?_ ?_ ?_ ?_ hd
  · rintro y ⟨a, b, x, N, rfl⟩
    have hmem := defectVec_rho_sub_mem_dOneSpanAt ρ htr h a b g x N
    have hrw : ρ g (defectVec ρ a b x (-1) N)
        = defectVec ρ a b (ρ g x) (-1) N
          - (defectVec ρ a b (ρ g x) (-1) N - ρ g (defectVec ρ a b x (-1) N)) := by abel
    rw [hrw]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨a, b, ρ g x, N, rfl⟩)
      (dOneSpanAt_le_dOneSpan ρ x hmem)
  · change ρ g (0 : M) ∈ dOneSpan ρ
    rw [map_zero]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    change ρ g (y + z) ∈ dOneSpan ρ
    rw [map_add]; exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    change ρ g (c • y) ∈ dOneSpan ρ
    rw [map_smul]; exact Submodule.smul_mem _ _ hy

/-! ## The `ℓ`-reduction: only the canonical pole matters -/

/-- The non-negative-pole defects of `ρ` vanish identically.  True for `indRho P` by the proved
`indDefectVec_nonneg` (the `ℓ ≥ 0` half of the iterate identity is free on `M_n(U)`). -/
def DefectNonnegZero (ρ : VHatRep W M) : Prop :=
  ∀ (a b : 𝒱) (x : M) (j : ℕ) (N : ℤ), defectVec ρ a b x (j : ℤ) N = 0

/-- **Every iterate defect at `x` is a combination of canonical (`ℓ = −1`) defects at `x`.**
`ℓ ≥ 0` is zero by `DefectNonnegZero`; `ℓ ≤ −2` is an `L₋₁`-derivative of the next pole up
(`defectVec_Lneg1_left`), and the scalar `−ℓ` is invertible there. -/
theorem defectVec_mem_dOneSpanAt (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (hnn : DefectNonnegZero ρ) (a b : 𝒱) (x : M) (ℓ N : ℤ) :
    defectVec ρ a b x ℓ N ∈ dOneSpanAt ρ x := by
  rcases lt_or_ge ℓ 0 with hl | hl
  · obtain ⟨s, rfl⟩ : ∃ s : ℕ, ℓ = -1 - (s : ℤ) := ⟨(-1 - ℓ).toNat, by omega⟩
    clear hl
    induction s generalizing a with
    | zero =>
      have : ((-1 : ℤ) - ((0 : ℕ) : ℤ)) = -1 := by norm_num
      rw [this]
      exact defectVec_neg_one_mem_dOneSpanAt ρ a b x N
    | succ s ih =>
      have hrec := defectVec_Lneg1_left ρ htr a b x (-1 - (s : ℤ)) N
      have hne : (-((-1 - (s : ℤ) : ℤ) : ℂ)) ≠ 0 := by
        have heq : (-((-1 - (s : ℤ) : ℤ) : ℂ)) = ((s + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [heq]
        exact_mod_cast Nat.succ_ne_zero s
      have hstep : defectVec ρ a b x (-1 - ((s + 1 : ℕ) : ℤ)) N
          = (-((-1 - (s : ℤ) : ℤ) : ℂ))⁻¹ • defectVec ρ (W.L (-1) a) b x (-1 - (s : ℤ)) N := by
        rw [hrec, smul_smul, inv_mul_cancel₀ hne, one_smul]
        congr 1
        push_cast; ring
      rw [hstep]
      exact Submodule.smul_mem _ _ (ih (W.L (-1) a))
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hl
    rw [hnn a b x j N]
    exact Submodule.zero_mem _

/-- Every defect lies in the span of the canonical defects. -/
theorem defectSet_subset_dOneSpan (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (hnn : DefectNonnegZero ρ) : defectSet ρ ⊆ (dOneSpan ρ : Set M) := by
  rintro y ⟨a, b, x, ℓ, N, rfl⟩
  exact dOneSpanAt_le_dOneSpan ρ x (defectVec_mem_dOneSpanAt ρ htr hnn a b x ℓ N)

/-- **The defect submodule is the plain span of the canonical defects.**  This is the exact
content of DLM3 Proposition 4.7 for the repo's `radical`-style formulation: the `U(V̂)`-quantifier
adds nothing once `DefectModeShift` holds. -/
theorem defectSubmodule_eq_dOneSpan (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (hnn : DefectNonnegZero ρ) (h : DefectModeShift ρ) : defectSubmodule ρ = dOneSpan ρ := by
  refine le_antisymm (sInf_le ⟨defectSet_subset_dOneSpan ρ htr hnn, dOneSpan_invariant ρ htr h⟩) ?_
  refine Submodule.span_le.mpr ?_
  rintro y ⟨a, b, x, N, rfl⟩
  exact defectVec_mem_defectSubmodule ρ a b x (-1) N

end VHatRep

/-! ## The level argument at `n = 0` -/

namespace DLM3

variable {W : VertexOperatorAlgebra 𝒱} {U : Type u} [AddCommGroup U] [Module ℂ U]

section LevelZero

variable {Q : ParabolicRep W 0 U}

/-- **The level argument, homogeneous slots.**  For a **non-negative** mode `g ∈ V̂(e)`, the
projection kills `g·δ` whenever it kills `δ`.  Three cases, all cheap at `n = 0`:
below level `0` the defect is already zero (`levCover_eq_bot_of_neg`); at level `0` it lies in the
bottom `1 ⊗ U` where `π₀` is injective (`levCover_zero_eq_range` + `proj_bottom`), so `π₀ δ = 0`
forces `δ = 0`; above level `0` the translate still sits above level `0`, where `π₀` vanishes. -/
theorem proj_deg_defect_neg_one_homog (Pr : BottomProjection Q) {wa wb : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading wa) (hb : b ∈ W.grading wb) {d : ℤ} {z : IndMod Q}
    (hz : z ∈ levCover Q d) (N : ℤ)
    (hG : Pr.proj (VHatRep.defectVec (indRho Q) a b z (-1) N) = 0)
    {e : ℤ} (he : 0 ≤ e) {g : VHatCarrier W} (hg : g ∈ deg W e) :
    Pr.proj (indRho Q g (VHatRep.defectVec (indRho Q) a b z (-1) N)) = 0 := by
  have hlev := indDefectVec_mem_levCover Q ha hb hz (-1) N
  rcases lt_trichotomy (d + (wa + wb - (-1) - N - 2)) 0 with hc | hc | hc
  · rw [levCover_eq_bot_of_neg Q hc, Submodule.mem_bot] at hlev
    rw [hlev, map_zero, map_zero]
  · rw [hc, levCover_zero_eq_range] at hlev
    obtain ⟨v, hv⟩ := hlev
    have hpv := Pr.proj_bottom v
    rw [hv] at hpv
    have hv0 : v = 0 := by rw [← hpv]; exact hG
    rw [← hv, hv0, map_zero, map_zero, map_zero]
  · refine Pr.proj_levCover ?_ (indRho_deg_levCover Q hg hlev)
    push_cast
    omega

/-- The level argument for arbitrary (not necessarily homogeneous) `a, b`: both sides are bilinear
in the two `𝒱`-slots. -/
theorem proj_deg_defect_neg_one (Pr : BottomProjection Q) (a b : 𝒱) {d : ℤ} {z : IndMod Q}
    (hz : z ∈ levCover Q d)
    (hG : ∀ (a' b' : 𝒱) (N' : ℤ), Pr.proj (VHatRep.defectVec (indRho Q) a' b' z (-1) N') = 0)
    (N : ℤ) {e : ℤ} (he : 0 ≤ e) {g : VHatCarrier W} (hg : g ∈ deg W e) :
    Pr.proj (indRho Q g (VHatRep.defectVec (indRho Q) a b z (-1) N)) = 0 := by
  have htr := ind_actModeTruncated Q
  have hkey : ∀ (w : ℤ) (a' : 𝒱), a' ∈ W.grading w → ∀ b' : 𝒱,
      Pr.proj (indRho Q g (VHatRep.defectVec (indRho Q) a' b' z (-1) N)) = 0 := by
    intro w a' ha' b'
    have hbtop : b' ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading
      (motive := fun b' => Pr.proj (indRho Q g
        (VHatRep.defectVec (indRho Q) a' b' z (-1) N)) = 0) hbtop ?_ ?_ ?_
    · intro i y hy
      exact proj_deg_defect_neg_one_homog Pr ha' hy hz N (hG a' y N) he hg
    · change Pr.proj (indRho Q g (VHatRep.defectVec (indRho Q) a' 0 z (-1) N)) = 0
      rw [VHatRep.defectVec_zero_left₂ _ htr, map_zero, map_zero]
    · intro y y' hy hy'
      change Pr.proj (indRho Q g (VHatRep.defectVec (indRho Q) a' (y + y') z (-1) N)) = 0
      rw [VHatRep.defectVec_add_left₂ _ htr, map_add, map_add, hy, hy', add_zero]
  have hatop : a ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun a => Pr.proj (indRho Q g
      (VHatRep.defectVec (indRho Q) a b z (-1) N)) = 0) hatop ?_ ?_ ?_
  · intro i y hy
    exact hkey i y hy b
  · change Pr.proj (indRho Q g (VHatRep.defectVec (indRho Q) 0 b z (-1) N)) = 0
    rw [VHatRep.defectVec_zero_left₁ _ htr, map_zero, map_zero]
  · intro y y' hy hy'
    change Pr.proj (indRho Q g (VHatRep.defectVec (indRho Q) (y + y') b z (-1) N)) = 0
    rw [VHatRep.defectVec_add_left₁ _ htr, map_add, map_add, hy, hy', add_zero]

/-- The submodule of vectors whose canonical defects are killed by `π₀` — DLM3 Proposition 4.6's
set `X`, at the canonical pole. -/
noncomputable def projKernelSet (Pr : BottomProjection Q) : Submodule ℂ (IndMod Q) where
  carrier := {z | ∀ (a b : 𝒱) (N : ℤ),
    Pr.proj (VHatRep.defectVec (indRho Q) a b z (-1) N) = 0}
  add_mem' := by
    intro x y hx hy a b N
    rw [VHatRep.defectVec_add_right (indRho Q) (ind_actModeTruncated Q), map_add, hx a b N,
      hy a b N, add_zero]
  zero_mem' := by
    intro a b N
    rw [VHatRep.defectVec_zero_right (indRho Q) (ind_actModeTruncated Q), map_zero]
  smul_mem' := by
    intro c x hx a b N
    rw [VHatRep.defectVec_smul_right (indRho Q) (ind_actModeTruncated Q), map_smul, hx a b N,
      smul_zero]

@[simp] theorem mem_projKernelSet (Pr : BottomProjection Q) (z : IndMod Q) :
    z ∈ projKernelSet Pr ↔ ∀ (a b : 𝒱) (N : ℤ),
      Pr.proj (VHatRep.defectVec (indRho Q) a b z (-1) N) = 0 := Iff.rfl

/-- **The propagation step.**  `projKernelSet` is stable under every **non-negative** mode.  The
correction terms of `DefectModeShift` are canonical defects at the *same* `z`, hence killed by the
induction hypothesis; the remaining term `g·δ` is killed by the level argument. -/
theorem projKernelSet_step (Pr : BottomProjection Q)
    (hshift : VHatRep.DefectModeShift (indRho Q)) {d : ℤ} {z : IndMod Q}
    (hz : z ∈ levCover Q d) (hG : z ∈ projKernelSet Pr) {e : ℤ} (he : 0 ≤ e)
    {g : VHatCarrier W} (hg : g ∈ deg W e) : indRho Q g z ∈ projKernelSet Pr := by
  have htr := ind_actModeTruncated Q
  -- the statement is linear in `g`; reduce to the generators of `deg W e`
  refine Submodule.span_induction
    (p := fun g _ => indRho Q g z ∈ projKernelSet Pr) ?_ ?_ ?_ ?_ hg
  · rintro g ⟨w, m, c, hc, hd, rfl⟩
    intro a b N
    have hgmem : gen W c m ∈ deg W e := by
      have := gen_mem_deg W hc m
      rwa [hd] at this
    have hact : indRho Q (gen W c m) z = (indRho Q).actMode c m z := rfl
    rw [hact, hshift a b c z m N, map_sub, map_sub]
    have h0 : Pr.proj ((indRho Q).actMode c m
        (VHatRep.defectVec (indRho Q) a b z (-1) N)) = 0 := by
      have := proj_deg_defect_neg_one Pr a b hz (fun a' b' N' => hG a' b' N') N he hgmem
      rwa [show indRho Q (gen W c m) = (indRho Q).actMode c m from rfl] at this
    have h1 : Pr.proj (∑ᶠ p : ℕ, cbz m (p : ℤ) •
        VHatRep.defectVec (indRho Q) a (W.smul c (p : ℤ) b) z (-1) (m + N - (p : ℤ))) = 0 := by
      have : (∑ᶠ p : ℕ, cbz m (p : ℤ) •
          VHatRep.defectVec (indRho Q) a (W.smul c (p : ℤ) b) z (-1) (m + N - (p : ℤ)))
          ∈ LinearMap.ker Pr.proj :=
        finsum_mem_of_forall_mem _ _ fun p => Submodule.smul_mem _ _
          (LinearMap.mem_ker.mpr (hG a (W.smul c (p : ℤ) b) (m + N - (p : ℤ))))
      exact LinearMap.mem_ker.mp this
    have h2 : Pr.proj (∑ᶠ q : ℕ, cbz m (q : ℤ) •
        VHatRep.defectVec (indRho Q) (W.smul c (q : ℤ) a) b z (-1) (N + m - (q : ℤ))) = 0 := by
      have : (∑ᶠ q : ℕ, cbz m (q : ℤ) •
          VHatRep.defectVec (indRho Q) (W.smul c (q : ℤ) a) b z (-1) (N + m - (q : ℤ)))
          ∈ LinearMap.ker Pr.proj :=
        finsum_mem_of_forall_mem _ _ fun q => Submodule.smul_mem _ _
          (LinearMap.mem_ker.mpr (hG (W.smul c (q : ℤ) a) b (N + m - (q : ℤ))))
      exact LinearMap.mem_ker.mp this
    rw [h0, h1, h2, sub_zero, sub_zero]
  · intro a b N
    rw [map_zero, LinearMap.zero_apply, VHatRep.defectVec_zero_right (indRho Q) htr, map_zero]
  · intro g₁ g₂ _ _ h₁ h₂ a b N
    rw [map_add, LinearMap.add_apply, VHatRep.defectVec_add_right (indRho Q) htr, map_add,
      h₁ a b N, h₂ a b N, add_zero]
  · intro c g₁ _ h₁ a b N
    rw [map_smul, LinearMap.smul_apply, VHatRep.defectVec_smul_right (indRho Q) htr, map_smul,
      h₁ a b N, smul_zero]

/-- **DLM3 Proposition 4.6 at `n = 0`.**  Generation along **non-negative** words
(`levCover_eq_posLevel`, PBW-free) from the bottom base case. -/
theorem proj_defect_neg_one_top (Pr : BottomProjection Q)
    (hshift : VHatRep.DefectModeShift (indRho Q))
    (hbot : ∀ (u : U) (a b : 𝒱) (N : ℤ),
      Pr.proj (VHatRep.defectVec (indRho Q) a b (indBottom Q u) (-1) N) = 0)
    (a b : 𝒱) (z : IndMod Q) (N : ℤ) :
    Pr.proj (VHatRep.defectVec (indRho Q) a b z (-1) N) = 0 := by
  have horbit : ∀ (r : ℕ) (d : ℤ), posOrbit Q r d ≤ projKernelSet Pr := by
    intro r
    induction r with
    | zero =>
      intro d
      rw [posOrbit_zero]
      by_cases hd : d = 0
      · subst hd
        rw [if_pos rfl]
        rintro t ⟨u, rfl⟩
        exact fun a' b' N' => hbot u a' b' N'
      · rw [if_neg hd]; exact bot_le
    | succ r ih =>
      intro d
      rw [posOrbit_succ]
      refine iSup_le fun e => Submodule.span_le.mpr ?_
      rintro t ⟨g, hg, y, hy, rfl⟩
      exact projKernelSet_step Pr hshift (posOrbit_le_levCover Q r (d - (e : ℤ)) hy)
        (ih (d - (e : ℤ)) hy) (by positivity) hg
  have hlev : ∀ d : ℤ, levCover Q d ≤ projKernelSet Pr := by
    intro d
    rw [levCover_eq_posLevel]
    exact iSup_le fun r => horbit r d
  have htop : (⊤ : Submodule ℂ (IndMod Q)) ≤ projKernelSet Pr := by
    rw [← levCover_spanning Q]
    exact iSup_le fun k => hlev k
  exact htop (Submodule.mem_top) a b N

/-- **DLM3 Proposition 4.6 at `n = 0`, all poles.**  Combining the canonical-pole statement with
the `ℓ`-reduction. -/
theorem proj_defect_top (Pr : BottomProjection Q) (hshift : VHatRep.DefectModeShift (indRho Q))
    (hbot : ∀ (u : U) (a b : 𝒱) (N : ℤ),
      Pr.proj (VHatRep.defectVec (indRho Q) a b (indBottom Q u) (-1) N) = 0)
    (a b : 𝒱) (z : IndMod Q) (ℓ N : ℤ) :
    Pr.proj (VHatRep.defectVec (indRho Q) a b z ℓ N) = 0 := by
  have hnn : VHatRep.DefectNonnegZero (indRho Q) := fun a' b' x j N' =>
    indDefectVec_nonneg Q a' b' x j N'
  have hmem := VHatRep.defectVec_mem_dOneSpanAt (indRho Q) (ind_actModeTruncated Q) hnn a b z ℓ N
  have hle : VHatRep.dOneSpanAt (indRho Q) z ≤ LinearMap.ker Pr.proj := by
    refine Submodule.span_le.mpr ?_
    rintro t ⟨a', b', N', rfl⟩
    exact LinearMap.mem_ker.mpr (proj_defect_neg_one_top Pr hshift hbot a' b' z N')
  exact LinearMap.mem_ker.mp (hle hmem)

/-- **DLM3 Propositions 4.6 + 4.7 at `n = 0`, assembled**: the projection kills the whole defect
submodule.  This is `ProjKillsDefectSubmodule`, hence (via `ZhuVermaAnArchDLM3Pairing`)
`DefectPairsToZero` — DLM3's `U(V̂)W ⊆ J`. -/
theorem projKills_of_modeShift (Pr : BottomProjection Q)
    (hshift : VHatRep.DefectModeShift (indRho Q))
    (hbot : ∀ (u : U) (a b : 𝒱) (N : ℤ),
      Pr.proj (VHatRep.defectVec (indRho Q) a b (indBottom Q u) (-1) N) = 0) :
    ProjKillsDefectSubmodule Pr := by
  have hnn : VHatRep.DefectNonnegZero (indRho Q) := fun a' b' x j N' =>
    indDefectVec_nonneg Q a' b' x j N'
  rw [ProjKillsDefectSubmodule,
    VHatRep.defectSubmodule_eq_dOneSpan (indRho Q) (ind_actModeTruncated Q) hnn hshift]
  refine Submodule.span_le.mpr ?_
  rintro t ⟨a, b, x, N, rfl⟩
  exact LinearMap.mem_ker.mpr (proj_defect_neg_one_top Pr hshift hbot a b x N)

/-- The same, as `DefectPairsToZero`. -/
theorem defectPairsToZero_of_modeShift (Pr : BottomProjection Q)
    (hshift : VHatRep.DefectModeShift (indRho Q))
    (hbot : ∀ (u : U) (a b : 𝒱) (N : ℤ),
      Pr.proj (VHatRep.defectVec (indRho Q) a b (indBottom Q u) (-1) N) = 0) :
    DefectPairsToZero Pr :=
  defectPairsToZero_of_projKills Pr (projKills_of_modeShift Pr hshift hbot)

end LevelZero

/-! ## The `A(𝒱)`-module case: the bottom base is proved -/

section AMod

/-- **`DefectPairsToZero` from the mode-shift law.** The bottom base case is the proved DLM3
Proposition 4.3 (`proj_indDefectVec_bottom`), so for a bundled `A(𝒱)`-module `U` the only input
beyond the independent `BottomProjection`/bottom-injectivity hypothesis `Pr` is `DefectModeShift`.
-/
theorem defectPairsToZero_of_modeShift_aMod (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W U))) :
    DefectPairsToZero Pr :=
  defectPairsToZero_of_modeShift Pr hshift
    (fun u a b N => proj_indDefectVec_bottom W U Pr a b u (-1) N)

/-- DLM3 Proposition 4.6 as the repo states it (`BottomPropagates`), **proved** from the
mode-shift law. -/
theorem bottomPropagates_of_modeShift (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W U))) :
    BottomPropagates Pr := by
  intro _ a b z ℓ N
  exact proj_defect_top Pr hshift
    (fun u a' b' N' => proj_indDefectVec_bottom W U Pr a' b' u (-1) N') a b z ℓ N

/-- DLM3 Proposition 4.7 as the repo states it (`OrbitPropagates`), **proved** from the mode-shift
law. -/
theorem orbitPropagates_of_modeShift (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W U))) :
    OrbitPropagates Pr := by
  intro _ a b z ℓ N y
  exact defectPairsToZero_of_modeShift_aMod W U Pr hshift a b z ℓ N y

/-- **`U` survives**, conditional on the mode-shift law and the independent
`BottomProjection`/bottom-injectivity hypothesis `Pr`. -/
theorem indBarBottom_injective_of_modeShift (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W U))) :
    Function.Injective (indBarBottom (parabolicRepOfAMod W U)) :=
  indBarBottom_injective_of_defectPairsToZero Pr
    (defectPairsToZero_of_modeShift_aMod W U Pr hshift)

end AMod

end DLM3
end VHat

/-! ## The gate, on the independent `BottomProjection` boundary plus the mode-shift law -/

section GateConsumers

open VHat VHat.DLM3

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The `(0,0)` gate on the independent bottom-injectivity hypothesis and the mode-shift law.**

    (GATE)   OnmFull W 0 0 = O W

* `hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W))` — an explicit bottom-injectivity
  assumption; the companion `voaPBWFreeness` supplies this instance from the generic
  relative-induction field of the theorem `VOA.pbw : PBWPrinciple`;
* `hshift : DefectModeShift (indRho …)` — DLM2 Proposition 6.1 at `ℓ = −1`, a pure
  `V̂`-representation identity.

Both DLM3 propagations (Props 4.6 and 4.7) are **proved**, not carried.  Not a proof of the gate:
the exact reduction, with both inputs named. -/
theorem gate_of_pbw_modeShift (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W)))) :
    OnmFull W 0 0 = O W :=
  gate_of_pbw hP (defectPairsToZero_of_modeShift_aMod W (regularAMod W) hP.bottomProjection hshift)

/-- The downstream package, on the same two inputs. -/
theorem downstream_of_pbw_modeShift (hP : PBWFreeness (parabolicRepOfAMod W (regularAMod W)))
    (hshift : VHatRep.DefectModeShift (indRho (parabolicRepOfAMod W (regularAMod W)))) :
    OnmFull W 0 0 = O W ∧ DJAnnEqAn W 0 ∧ OnmFull W 0 0 = OnFull W 0 ∧ OnmCollapses W 0 :=
  downstream_of_pbw hP
    (defectPairsToZero_of_modeShift_aMod W (regularAMod W) hP.bottomProjection hshift)

end GateConsumers

end VOA

-- Axiom check. Explicit `PBWFreeness`/`BottomProjection` parameters are not printed.
