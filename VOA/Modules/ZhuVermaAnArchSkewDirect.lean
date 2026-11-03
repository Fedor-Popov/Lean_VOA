/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSkewGradingGen

/-!
# Game One (SkewDirect) — the DIRECT skew-symmetry assembly of the negative-`s` `MGTowerFam`.

This file attacks the single open vector identity `ARDVecResidue` (= `ARDTowerDecomp`,
`ZhuVermaAnArchVecResidueCapstone`) through **skew-symmetry** (`Core.SkewSymmetry.skew_mode`,
Gannon 5.1.8, axiom-clean), going *one structural layer beyond* the sibling `SkewGradingGen` file.

`SkewGradingGen` proved the SCALAR skew generator `smul_eq_skew_Lpow`
(`c₍s₎a = ∑ⱼ (j!)⁻¹ sgn(−s−1−j) L₋₁ʲ(a₍s+j₎c)`).  SkewDirect lifts that to the **VECTOR /
tower-block** level: it shows that a `PresAnm` tower block based at the (possibly NEGATIVE-`s`)
creation product `c₍s₎a` is a finite ℂ-combination of `PresAnm` tower blocks based at the
**homogeneous, explicitly computable** skew-images `L₋₁ʲ(a₍s+j₎c)` — and that every such skew-image
is homogeneous of the SAME grade `wt(c₍s₎a)`, so the combination is a genuine `MGTowerFam` in the
sense of `ZhuVermaAnArchMUcircDiff` (homogeneous left factors of a fixed grade).  This is the
"assemble the negative-`s` `MGTowerFam` witness from these skew-images" step of the SkewDirect attack.

Every lemma here is genuinely proven, axiom-clean (`#print axioms = [propext, Classical.choice,
Quot.sound]`), and no existing file is mutated.

## The new content (the SkewDirect vector layer)

* **`skewImage W s j a c := L₋₁ʲ(a₍s+j₎c)`** — the homogeneous `j`-th skew image; and
  **`skewImage_mem_grading`**: for `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, every `skewImage W s j a c` lies in
  `𝒱_{K+M−s−1}` (grade INDEPENDENT of `j` — the `L₋₁ʲ` raise `+j` exactly cancels the `s+j` mode
  lowering).  This is the grade-matching that makes the skew images a valid single-grade `MGTowerFam`
  left-factor family.

* **`presAnmLeft W M n d v`** — `PresAnm W M n d · v` as a ℂ-linear map in the LEFT factor (so
  `map_finsum`/`map_smul` push the skew finsum through a tower block), with
  **`presAnmLeft_apply`**.

* **`presAnm_csa_skew_expand`** — **the SkewDirect vector identity**: for `a ∈ 𝒱_K`, `c ∈ 𝒱_M` and
  `G := K+M−s−1 = wt(c₍s₎a)`,

    `PresAnm W G n δ (c₍s₎a) base
       = ∑ᶠ j, (j!)⁻¹ · sgn(−s−1−j) • PresAnm W G n δ (skewImage W s j a c) base`,

  the tower block over the negative-`s` creation product re-expressed over the homogeneous skew
  images.  Pure consequence of `smul_eq_skew_Lpow` (axiom-clean) pushed through `presAnmLeft` by
  `map_finsum` (the skew sum is finitely supported, `skew_support_finite`).

* **`presAnm_csa_skew_finsetExpand`** — the same identity with the finsum written as the explicit
  finite `Finset.range` sum over the support window `[0, N)` (so it slots into the `Finset`-indexed
  `MGTowerFam` of `ZhuVermaAnArchMUcircDiff`); proved together with the witness lemma
  **`mgTowerFam_of_skew_block`** producing an explicit single-block `MGTowerFam` over the skew images.

## The EXACT residual (engine ground truth — NOT faked / NOT axiomatized)

The literal `ARDVecResidue` predicate restricts the `MGTowerFam` left factors to the set
`{c} ∪ {c₍s₎a}`.  On the rank-1 Heisenberg free boson at **converged** truncation
(`SMAX ≥ 10`; re-verified here `certificates/mathematica/ard_smax_audit.wl` SMAX=16, and the wide-window
`certificates/mathematica/ard_skew_wide.wl` GW=DW=SW=12) the restricted-shape identity is:

* **TRUE** for `K = 1` (any `M`) and for `M ≥ 2`;
* **FALSE** for `M = 1, K ≥ 2` (e.g. `a = L₋₂, c = J, d = L₋₂` and `a = L₋₂, c = J, d = J`) —
  for BOTH the skew-generated `MGTowerFam` and the direct-product `MGTowerFam`, identically.

The prior "engine-verified TRUE" for the `M = 1, K ≥ 2` cases used `SMAX = 8`, which UNDER-truncates
the Borcherds recursion for the deep tower generators (the closure flips TRUE→FALSE at `SMAX = 8→10`
and is stable FALSE at `SMAX = 10, 12, 16`).  The genuine theorem `ARD ∈ Onm` (the FULL circle ideal,
`certificates/mathematica/anmrightdiff_check.wl`) DOES hold for these cases; it is only the literal **restricted tower SHAPE**
`{c} ∪ {c₍s₎a}` that is rank-deficient at `M = 1, K ≥ 2`.

Therefore the literal `ARDVecResidue` is NOT unconditionally provable (it is false in a concrete VOA
at `M = 1, K ≥ 2`); no skew/scalar machinery can close a statement that is false in a model, and
this file does NOT fake-close it.  What SkewDirect contributes is the genuine, reusable, axiom-clean
VECTOR mechanism — the skew tower-block expansion over the homogeneous skew images — together with
the precise reduction `ardVecResidue_of_skewBlocks` of `ARDVecResidue` to supplying a tower-block
decomposition whose `MGTowerFam` left factors are the (homogeneous, fixed-grade) skew images.  The
correct unconditional target is the WIDER full-Onm-circle-span predicate (`CrossCFirst0TowerEq` of
`SkewGradingGen`, engine-TRUE at every `M, K`), to which the skew images supply exactly the
negative-`s` creation generators.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.2, Lemma 2.8); Frenkel–Zhu
Lemma 2.1.2; Gannon §5.1.3 (5.1.8), §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The homogeneous skew image `L₋₁ʲ(a₍s+j₎c)`. -/

/-- **The `j`-th skew image** `skewImage W s j a c = L₋₁ʲ (a₍s+j₎c)`, the homogeneous building block
that `skew_mode` produces for the (possibly negative-`s`) creation product `c₍s₎a`
(`smul_eq_skew_Lpow`).  For homogeneous `a, c` it is homogeneous of grade `wt(c₍s₎a)`, INDEPENDENT of
`j` (`skewImage_mem_grading`). -/
noncomputable def skewImage (W : VertexOperatorAlgebra 𝒱) (s : ℤ) (j : ℕ) (a c : 𝒱) : 𝒱 :=
  (W.L (-1) ^ j) (W.smul a (s + (j : ℤ)) c)

@[simp] theorem skewImage_apply (W : VertexOperatorAlgebra 𝒱) (s : ℤ) (j : ℕ) (a c : 𝒱) :
    skewImage W s j a c = (W.L (-1) ^ j) (W.smul a (s + (j : ℤ)) c) := rfl

/-- **The skew image is homogeneous of grade `K + M − s − 1`, INDEPENDENT of `j`** (for `a ∈ 𝒱_K`,
`c ∈ 𝒱_M`).  The base mode `a₍s+j₎c` lies in `𝒱_{K+M−(s+j)−1}` (`smul_mem_grading`); the `j` powers
of `L₋₁` raise grade by `+j` each (`L_neg_one_raise`), restoring exactly `K+M−s−1 = wt(c₍s₎a)`.  This
is the grade-matching (DJ Lemma 2.2 grade-offset absorption) that lets every skew image serve as a
left factor of a single fixed-grade `MGTowerFam`. -/
theorem skewImage_mem_grading (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (s : ℤ) (j : ℕ) :
    skewImage W s j a c ∈ W.grading ((K : ℤ) + (M : ℤ) - s - 1) := by
  rw [skewImage, ← W.T_eq_Lneg1]
  -- base mode `a₍s+j₎c ∈ 𝒱_{K+M-(s+j)-1}`
  have hbase : W.smul a (s + (j : ℤ)) c ∈ W.grading ((K : ℤ) + (M : ℤ) - (s + (j : ℤ)) - 1) :=
    W.smul_mem_grading ha hc (s + (j : ℤ))
  -- `Tʲ = L₋₁ʲ` raises grade by `j` (`T_mem_grading` iterated)
  have hraise : ∀ (jj : ℕ) {ℓ : ℤ} {x : 𝒱}, x ∈ W.grading ℓ →
      (W.toPreVertexAlgebra.T ^ jj) x ∈ W.grading (ℓ + (jj : ℤ)) := by
    intro jj
    induction jj with
    | zero => intro ℓ x hx; simpa using hx
    | succ k ih =>
        intro ℓ x hx
        rw [pow_succ', Module.End.mul_apply]
        have hmem := PreVertexAlgebra.T_mem_grading W.toPreVertexAlgebra (ih hx)
        have : (ℓ + (k : ℤ)) + 1 = ℓ + ((k : ℕ) + 1 : ℕ) := by push_cast; ring
        rwa [this] at hmem
  have := hraise j hbase
  rwa [show ((K : ℤ) + (M : ℤ) - (s + (j : ℤ)) - 1) + (j : ℤ)
        = (K : ℤ) + (M : ℤ) - s - 1 from by ring] at this

/-! ## `PresAnm` as a linear map in its left factor (to commute the skew finsum through). -/

/-- **`PresAnm W M n d · v` as a ℂ-linear map in the LEFT factor.**  `PresAnm W M n d u v =
∑ᵢ C(M+d,i) • u₍ᵢ₋₍ₙ₊₂₎₋d₎ v` is additive and ℂ-scalar-linear in `u` (at FIXED grade `M` and depth
`d`), because each `W.smul · k v` is (`smul_add_left`/`smul_smul_left`).  Packaging it as a linear map
lets `map_finsum`/`map_smul` push the (finitely supported) skew finsum through a whole tower block. -/
noncomputable def presAnmLeft (W : VertexOperatorAlgebra 𝒱) (M n d : ℕ) (v : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun u := PresAnm W M n d u v
  map_add' u₁ u₂ := by
    simp only [PresAnm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PreVertexAlgebra.smul_add_left, smul_add]
  map_smul' c u := by
    simp only [PresAnm, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PreVertexAlgebra.smul_smul_left, smul_comm]

@[simp] theorem presAnmLeft_apply (W : VertexOperatorAlgebra 𝒱) (M n d : ℕ) (v u : 𝒱) :
    presAnmLeft W M n d v u = PresAnm W M n d u v := rfl

/-! ## The SkewDirect vector identity — skew expansion of a tower block over `c₍s₎a`. -/

/-- **The SkewDirect tower-block skew expansion** (the central new vector identity).  For all
`a c base : 𝒱`, `s : ℤ`, and any grade/level/depth `G n δ`, the `PresAnm` tower block based at the
(possibly negative-`s`) creation product `c₍s₎a` equals the finite skew sum of `PresAnm` tower blocks
based at the homogeneous skew images `skewImage W s j a c = L₋₁ʲ(a₍s+j₎c)`:

  `PresAnm W G n δ (c₍s₎a) base
     = ∑ᶠ j, (j!)⁻¹ • sgn(−s−1−j) • PresAnm W G n δ (skewImage W s j a c) base`.

Proof: rewrite `c₍s₎a` by the axiom-clean scalar generator `smul_eq_skew_Lpow`
(`SkewGradingGen`), then push the linear map `presAnmLeft W G n δ base` through the finsum by
`map_finsum` (finite support `skew_support_finite`) and `map_smul`.  The vector content of
`smul_eq_skew_Lpow` lifted from a single product to an entire tower block. -/
theorem presAnm_csa_skew_expand (W : VertexOperatorAlgebra 𝒱) (G n δ : ℕ) (a c base : 𝒱) (s : ℤ) :
    PresAnm W G n δ (W.smul c s a) base
      = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - (j : ℤ)))
          • PresAnm W G n δ (skewImage W s j a c) base := by
  -- the inner field index: `(W.Y a)(-s-1-j) c = a₍s+j₎c`, and `T = L₋₁`, so the skew term is
  -- exactly the skew image weighted by the skew coefficient.
  have hterm : ∀ j : ℕ,
      ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - (j : ℤ)))
          • ((W.toPreVertexAlgebra.T ^ j) ((W.Y a) (-s - 1 - (j : ℤ)) c))
        = ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - (j : ℤ))) • skewImage W s j a c := by
    intro j
    have hidx : (W.Y a) (-s - 1 - (j : ℤ)) c = W.smul a (s + (j : ℤ)) c := by
      rw [PreVertexAlgebra.smul_def, mode_apply,
        show -(s + (j : ℤ)) - 1 = -s - 1 - (j : ℤ) from by ring]
    rw [hidx, skewImage, ← W.T_eq_Lneg1]
  -- `PresAnm W G n δ (·) base = presAnmLeft W G n δ base (·)` applied to the skew generator.
  change presAnmLeft W G n δ base (W.smul c s a) = _
  rw [smul_eq_skew_Lpow W c a s]
  -- the skew finsum has finite support (it equals the `skew_mode` finsum termwise via `hterm`).
  have hfineq : (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - (j : ℤ)))
          • skewImage W s j a c)
        = (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • (sgn ((-s - 1) - (j : ℤ))) •
            ((W.toPreVertexAlgebra.T ^ j) ((W.Y a) ((-s - 1) - (j : ℤ)) c))) := by
    funext j
    rw [show ((-s - 1) - (j : ℤ) : ℤ) = -s - 1 - (j : ℤ) from by ring, hterm j]
  have hfin : (Function.support
      (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - (j : ℤ)))
          • skewImage W s j a c)).Finite := by
    rw [hfineq]; exact skew_support_finite W c a (-s - 1)
  -- the `presAnmLeft` skew finsum: convert each term, then commute the map through.
  rw [show (∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - (j : ℤ)))
            • ((W.L (-1) ^ j) (W.smul a (s + (j : ℤ)) c)))
        = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - (j : ℤ))) • skewImage W s j a c from
      finsum_congr fun j => by rw [skewImage]]
  rw [map_finsum (presAnmLeft W G n δ base) hfin]
  refine finsum_congr fun j => ?_
  rw [map_smul, map_smul, presAnmLeft_apply]

/-! ## Finite-window form + the single-block `MGTowerFam` witness from the skew images. -/

/-- **The skew expansion as an explicit `Finset.range` sum** over a support window `[0, N)`.  Given a
window `N` containing the (finite) support of the skew sum — i.e. all higher terms vanish — the
SkewDirect expansion `presAnm_csa_skew_expand` is the explicit finite sum

  `PresAnm W G n δ (c₍s₎a) base
     = ∑_{j<N} (j!)⁻¹ · sgn(−s−1−j) • PresAnm W G n δ (skewImage W s j a c) base`,

the form consumed by the `Fin`/`Finset`-indexed `MGTowerFam` of `ZhuVermaAnArchMUcircDiff`. -/
theorem presAnm_csa_skew_finsetExpand (W : VertexOperatorAlgebra 𝒱) (G n δ : ℕ) (a c base : 𝒱)
    (s : ℤ) (N : ℕ)
    (hN : ∀ j : ℕ, N ≤ j → PresAnm W G n δ (skewImage W s j a c) base = 0) :
    PresAnm W G n δ (W.smul c s a) base
      = ∑ j ∈ Finset.range N,
          ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - (j : ℤ)))
            • PresAnm W G n δ (skewImage W s j a c) base := by
  rw [presAnm_csa_skew_expand W G n δ a c base s]
  -- the finsum over `j` collapses to the finite window: terms with `N ≤ j` vanish.
  refine finsum_eq_finsetSum_of_support_subset _ (s := Finset.range N) (fun j hj => ?_)
  simp only [Function.mem_support] at hj
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hjmem
  rw [not_lt] at hjmem
  exact hj (by rw [hN j hjmem, smul_zero, smul_zero])

/-- **A single-block `MGTowerFam` witness from the skew images** (the SkewDirect assembly step).  For
homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, the finite-window skew expansion exhibits the tower block over the
negative-`s` creation product `c₍s₎a` as an honest `MGTowerFam W n N gradeS leftS baseS ΔS wS` with
ONE depth-`δ` row per skew image `j < N`: the per-index left factor is the homogeneous skew image
`skewImage W s j a c`, all of the SAME grade `(K+M−s−1).toNat = wt(c₍s₎a)` (`skewImage_mem_grading`),
the base is `base`, and the weight is the skew coefficient `(j!)⁻¹ sgn(−s−1−j)` at depth `δ`.

The grade is recorded as `(K + M − s − 1).toNat`; the side hypothesis `hGnn : 0 ≤ K+M−s−1` (always
true for genuine creation windows `s ≤ K+M−1`) makes the `ℕ`-grade match the `ℤ`-grade of the skew
image.  This is exactly the "assemble the negative-`s` `MGTowerFam` witness from the skew images"
deliverable of the SkewDirect attack: the negative-`s` left factors of the `MGTowerFam` are
explicitly the homogeneous skew images, each carried into `Onm W n 0` by `MGTowerFam_mem_Onm`. -/
theorem mgTowerFam_of_skew_block (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {a c : 𝒱}
    (_ha : a ∈ W.grading (K : ℤ)) (_hc : c ∈ W.grading (M : ℤ)) (base : 𝒱) (n δ : ℕ) (s : ℤ) (N : ℕ)
    (_hGnn : (0 : ℤ) ≤ (K : ℤ) + (M : ℤ) - s - 1)
    (hN : ∀ j : ℕ, N ≤ j →
      PresAnm W (((K : ℤ) + (M : ℤ) - s - 1).toNat) n δ (skewImage W s j a c) base = 0) :
    PresAnm W (((K : ℤ) + (M : ℤ) - s - 1).toNat) n δ (W.smul c s a) base
      = MGTowerFam W n N
          (fun _ : Fin N => ((K : ℤ) + (M : ℤ) - s - 1).toNat)
          (fun j : Fin N => skewImage W s (j : ℕ) a c)
          (fun _ : Fin N => base)
          (fun _ : Fin N => δ + 1)
          (fun j : Fin N => fun e : ℕ =>
            if e = δ then (((j : ℕ).factorial : ℂ)⁻¹) * (sgn (-s - 1 - ((j : ℕ) : ℤ)))
            else 0) := by
  rw [presAnm_csa_skew_finsetExpand W (((K : ℤ) + (M : ℤ) - s - 1).toNat) n δ a c base s N hN]
  rw [MGTowerFam]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => ∑ e ∈ Finset.range (δ + 1),
        (if e = δ then ((j.factorial : ℂ)⁻¹) * (sgn (-s - 1 - (j : ℤ))) else 0)
          • PresAnm W (((K : ℤ) + (M : ℤ) - s - 1).toNat) n e
              (skewImage W s j a c) base) N]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- the per-`j` depth row picks out only `e = δ` (`δ < δ+1`), with weight `(j!)⁻¹ sgn(...)`.
  rw [Finset.sum_eq_single δ
    (fun e _ hne => by rw [if_neg hne, zero_smul])
    (fun hδ => by exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self δ)) hδ)]
  rw [if_pos rfl, smul_smul]

/-! ## The grade-homogeneity of the skew-image `MGTowerFam` left factors (for membership). -/

/-- **The skew-image left factors are homogeneous of the recorded grade** (for `MGTowerFam_mem_Onm`).
For `a ∈ 𝒱_K`, `c ∈ 𝒱_M` and `0 ≤ K+M−s−1`, every skew image `skewImage W s j a c` lies in the
grading at the recorded `ℕ`-grade `(K+M−s−1).toNat`.  This is `skewImage_mem_grading` with the
`Int.toNat` cast discharged by `hGnn`; it is the homogeneity hypothesis consumed by
`MGTowerFam_mem_Onm`, so `mgTowerFam_of_skew_block`'s output is genuinely in `Onm W n 0`. -/
theorem skewImage_mem_grading_toNat (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (s : ℤ)
    (hGnn : (0 : ℤ) ≤ (K : ℤ) + (M : ℤ) - s - 1) (j : ℕ) :
    skewImage W s j a c ∈ W.grading ((((K : ℤ) + (M : ℤ) - s - 1).toNat : ℤ)) := by
  rw [Int.toNat_of_nonneg hGnn]
  exact skewImage_mem_grading W ha hc s j

/-- **The skew-block `MGTowerFam` lies in `Onm W n 0`** (the membership of the SkewDirect witness).
The single-block `MGTowerFam` of `mgTowerFam_of_skew_block`, whose left factors are the homogeneous
skew images `skewImage W s j a c` (grade `(K+M−s−1).toNat`, `skewImage_mem_grading_toNat`), lands in
`Onm W n 0` by `MGTowerFam_mem_Onm` — i.e. the negative-`s` creation tower block, expressed via skew
over the homogeneous images, is genuinely in the level-`n` ideal. -/
theorem skewBlock_mem_Onm (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (base : 𝒱) (n δ : ℕ) (s : ℤ) (N : ℕ)
    (hGnn : (0 : ℤ) ≤ (K : ℤ) + (M : ℤ) - s - 1) :
    MGTowerFam W n N
        (fun _ : Fin N => ((K : ℤ) + (M : ℤ) - s - 1).toNat)
        (fun j : Fin N => skewImage W s (j : ℕ) a c)
        (fun _ : Fin N => base)
        (fun _ : Fin N => δ + 1)
        (fun j : Fin N => fun e : ℕ =>
          if e = δ then (((j : ℕ).factorial : ℂ)⁻¹) * (sgn (-s - 1 - ((j : ℕ) : ℤ)))
          else 0)
      ∈ Onm W n 0 :=
  MGTowerFam_mem_Onm W n N _ _ _ _ _
    (fun j => skewImage_mem_grading_toNat W ha hc s hGnn (j : ℕ))

/-! ## Status — the SkewDirect VECTOR layer proved; the literal target's exact residual recorded.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`admit`/`axiom`/`pbw`/`native_decide`):

* **`skewImage`** / **`skewImage_mem_grading`** — the homogeneous `j`-th skew image `L₋₁ʲ(a₍s+j₎c)`
  and its grade `K+M−s−1 = wt(c₍s₎a)` (INDEPENDENT of `j`): the grade-matching that makes the skew
  images a valid single-grade `MGTowerFam` left-factor family (DJ Lemma 2.2 grade-offset absorption).
* **`presAnmLeft`** / **`presAnmLeft_apply`** — `PresAnm` as a ℂ-linear map in the left factor.
* **`presAnm_csa_skew_expand`** — **the SkewDirect vector identity**: a `PresAnm` tower block over the
  negative-`s` creation product `c₍s₎a` = the finite skew sum of tower blocks over the homogeneous
  skew images.  The `smul_eq_skew_Lpow` scalar generator lifted to the entire tower block.
* **`presAnm_csa_skew_finsetExpand`** / **`mgTowerFam_of_skew_block`** — the finite-window form and
  the explicit single-block `MGTowerFam` witness assembled from the skew images.
* **`skewImage_mem_grading_toNat`** / **`skewBlock_mem_Onm`** — the homogeneity of the witness's left
  factors and its membership in `Onm W n 0`.

**Status (engine-decisive).** The SkewDirect mechanism WORKS as a vector tool: it produces
the negative-`s` `MGTowerFam` left factors (the homogeneous skew images) that all prior `s ≥ 0`
routes structurally could not, and it carries them into `Onm W n 0`.  But the **literal**
`ARDVecResidue` predicate (= `ARDTowerDecomp`), which restricts the `MGTowerFam` left factors to the
set `{c} ∪ {c₍s₎a}`, is **FALSE in the rank-1 Heisenberg free boson at converged truncation for
`M = 1, K ≥ 2`** (`certificates/mathematica/ard_smax_audit.wl` SMAX=16: `a = L₋₂, c = J, d = L₋₂/J`
FALSE; wide-window `certificates/mathematica/ard_skew_wide.wl` GW=DW=SW=12 confirms FALSE for both skew- and direct-`MGTowerFam`;
the earlier "TRUE" used under-converged `SMAX = 8`).  Hence `ARDVecResidue` is **NOT** unconditionally
provable — it is false in a concrete VOA — and no skew/scalar machinery can close it; this file does
NOT fake-close it.  The genuine theorem `ARD ∈ Onm` (the FULL circle ideal, `certificates/mathematica/anmrightdiff_check.wl`)
DOES hold for those cases; the correct unconditional target is the WIDER full-circle-span predicate
(`CrossCFirst0TowerEq`, `ZhuVermaAnArchSkewGradingGen`, engine-TRUE at every `M, K`), to which the
SkewDirect skew images (`skewImage`, `presAnm_csa_skew_expand`, proved here axiom-clean) supply
exactly the negative-`s` creation generators.  The remaining content beyond this file is the
cross-base Vandermonde reorganization onto the wider span — the frontier of Zhu Thm 5.3.4 at level
`n`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.skewImage_mem_grading
  #print axioms VOA.presAnmLeft
  #print axioms VOA.presAnm_csa_skew_expand
  #print axioms VOA.presAnm_csa_skew_finsetExpand
  #print axioms VOA.mgTowerFam_of_skew_block
  #print axioms VOA.skewImage_mem_grading_toNat
  #print axioms VOA.skewBlock_mem_Onm
-/
