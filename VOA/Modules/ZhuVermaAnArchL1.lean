/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArch
import VOA.Modules.ZhuVermaAnDescent23

/-!
# (L1∘) — the level-matched LEFT circle tower `leftProd W n (circ W n c d) b ∈ OnFull W n`.

This is the LEFT mirror of the proven right chain `RightCircTowerEq` (`ZhuVermaAnDescent19/20/21`)
and its master split `rightProd_circ_eq_USideR_sub_VSideR` (`ZhuVermaAnDescent10`).  Both sides shift
`2n+2`: the circle here is the **depth-`n`** circle `circ W n c d` (mode `i-2n-2`, weight
`cbz(M+n) i`), so the U-side and V-side both carry the `PresOn` shift `2n+2` — the clean mirror, NOT
the dead depth-`0`-circle cross-assembly of `ZhuVermaAnDescent23` (whose `circ W 0` mode `i-2`,
weight `cbz M i` gives the shift-`2` "pole-2 overshoot" obstruction for `n ≥ 1`).

The structural skeleton is IDENTICAL to the RIGHT chain `ZhuVermaAnDescent7→10`, with only the FZ
scalars changed: `leftProd` uses `cbz(j+n,n)` (and inner residue `cbz(G+n,p)`) where `rightProd`
uses `cbz(j+n,j)` (inner `cbz(G+j,r)`).  The mode/word structure (`iterate_term_rewrite`) and the
depth-`n` circle distribution (`leftProd_circ_homogeneous_left`, `ZhuVermaAnDescent5`) are shared,
and the generic finsum helpers (`USideL_s_fin`/`VSideL_s_fin`/`UwordL_reindex`/`VwordL_reindex`/
`UgammaL_fin`/`VgammaL_fin`/`hasFinSupp_finsetSumL`/`usingleL_eq_muFinsum`/…) are reused verbatim
from `ZhuVermaAnDescent23` (they are generic in the per-`(i,j,p)` scalar and base-mode, independent
of the circle depth).

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `leftProd_circ_inner_UVterm` / `leftProd_circ_UV_assembly` — the depth-`n` LEFT U/V split of
  `leftProd W n (circ W n c d) b`, the LEFT lift of `rightProd_circ_UV_assembly`.
* `USideLn` / `VSideLn` — the depth-`n` LEFT U/V sides (mode `i-2n-2`, weight `cbz(M+n) i`).
* `leftProd_circ_eq_USideLn_sub_VSideLn` — the **LEFT master split** `leftProd W n (circ W n c d) b =
  USideLn − VSideLn`, the LEFT lift of `rightProd_circ_eq_USideR_sub_VSideR`.
* `USideLn_eq_gammaModeFinsum` / `VSideLn_eq_gammaModeFinsum` — each side reindexed to the base-mode
  `γ` ⊗ mode `μ` double finsum `∑ᶠ γ ∑ᶠ μ, UgammaModeCollLn/VgammaModeCollLn • word`.
* `LeftCircTowerEqn` + `LeftCircTowerEqn_of_sides` — the LEFT tower-decomposition predicate and the
  criterion reducing it to the two side-collapses (LEFT lift of `RightCircTowerEq_of_sides`).
* `leftProd_circ_mem_OnFull_of_tower_eq` + `hLcirc_of_towerEq` — the membership criterion (via the
  proved `UfamOn_mem_On`/`VfamOn_mem_On` + `On_le_OnFull`) and the `AnIdeal_of_gens`-shaped `hLcirc`
  from the universally-quantified predicate.

## The PRECISE remaining content (NOT `sorry`'d / NOT axiomatized) — the two scalar cores

`LeftCircTowerEqn` reduces, via `LeftCircTowerEqn_of_sides`, to the two per-`(γ,μ)` scalar
tower-collapse cores `UgammaModeCollLn = towerCoeff M n (wU γ) Δ` and `VgammaModeCollLn = -towerCoeff
P n (wV γ) Δ` (the LEFT lift of `UgammaModeColl_eq_towerCoeff`/`VgammaModeColl_eq_towerCoeff`,
`ZhuVermaAnDescent19/20`, with `leftProd`'s `cbz(j+n,n)` FZ scalar replacing `rightProd`'s
`cbz(j+n,j)`, via `ZhuRes.gen_vandermonde`/`gen_jsum`).  These are the genuine combinatorial content,
stated as the predicate input — exactly mirroring how the RIGHT chain's `RightCircTowerEq_holds`
consumes its two cores.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.2; Dong–Li–Mason.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Step 1 — the per-`i` inner LEFT product collapse (depth-`n` circle, mode `i-2n-2`). -/

/-- The depth-`n` circle inner factor `c₍ᵢ₋₂ₙ₋₂₎d` lands in `𝒱_{M+P-(i-2n-2)-1}`. -/
theorem circ_inner_mem_grading_n (W : VertexOperatorAlgebra 𝒱) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (i : ℕ) :
    W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d
      ∈ W.grading ((M : ℤ) + (P : ℤ) - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) :=
  W.smul_mem_grading hc hd ((i : ℤ) - 2 * (n : ℤ) - 2)

/-- The per-`i` inner LEFT product `leftProd W n (c₍ᵢ₋₂ₙ₋₂₎d) b`, when the inner grade
`G := M+P-(i-2n-2)-1 ≥ 0`, expanded by `leftProd_homog_expand` (`ZhuVermaAnDescent23`) and split (per
`(j,p)`) into the U/V finsum families via `iterate_term_rewrite`/`iterate_UV_split`.  The LEFT lift
of `rightProd_circ_inner_UVterm` (`ZhuVermaAnDescent7`), depth-`n` circle. -/
theorem leftProd_circ_inner_UVterm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P G : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (i : ℕ)
    (hG : (G : ℤ) = (M : ℤ) + (P : ℤ) - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) (b : 𝒱) :
    leftProd W n (W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d) b
      = ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
            ∑ p ∈ Finset.range (G + n + 1),
              cbz ((G : ℤ) + n) (p : ℤ) •
                (∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s) •
                  (W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) - s)
                      (W.smul d ((p - ((n : ℤ) + (j : ℤ) + 1)) + s) b)
                    - ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2))
                      • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + (p - ((n : ℤ) + (j : ℤ) + 1)) - s)
                          (W.smul c (s : ℤ) b))) := by
  have hmem : W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d ∈ W.grading (G : ℤ) := by
    rw [hG]; exact circ_inner_mem_grading_n W (n := n) hc hd i
  rw [leftProd_homog_expand W n hmem b]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  exact iterate_term_rewrite W c d b ((i : ℤ) - 2 * (n : ℤ) - 2) (p : ℤ) n j

/-! ## Step 1d — the assembled depth-`n` LEFT U/V split of `leftProd W n (circ W n c d) b`. -/

/-- The full assembled U/V split of `leftProd W n (circ W n c d) b` over the circle index `i`, FZ
index `j`, residue index `p`, and `mode_iterate` index `s`, with the negative-inner-grade indices `i`
(where `c₍ᵢ₋₂ₙ₋₂₎d` vanishes) carried by an explicit `if`-guard.  The LEFT lift of
`rightProd_circ_UV_assembly`. -/
theorem leftProd_circ_UV_assembly (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (b : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + n + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) :
    leftProd W n (circ W n c d) b
      = ∑ i ∈ Finset.range (M + n + 1),
          cbz ((M : ℤ) + n) (i : ℤ) •
            (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 then
              ∑ j ∈ Finset.range (n + 1),
                ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
                  ∑ p ∈ Finset.range (G i + n + 1),
                    cbz ((G i : ℤ) + n) (p : ℤ) •
                      (∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s) •
                        (W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) - s)
                            (W.smul d ((p - ((n : ℤ) + (j : ℤ) + 1)) + s) b)
                          - ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2))
                            • W.smul d
                                (((i : ℤ) - 2 * (n : ℤ) - 2) + (p - ((n : ℤ) + (j : ℤ) + 1)) - s)
                                (W.smul c (s : ℤ) b)))
            else 0) := by
  rw [leftProd_circ_homogeneous_left W n hc d b]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  rcases lt_or_ge ((M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) 0 with hlt | hge
  · rw [if_neg (not_le.mpr hlt)]
    have hmem : W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d
        ∈ W.grading ((M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) :=
      circ_inner_mem_grading_n W (n := n) hc hd i
    rw [W.positivity _ hlt, Submodule.mem_bot] at hmem
    rw [hmem, leftProd_zero_left]
  · rw [if_pos hge]
    exact leftProd_circ_inner_UVterm W n hc hd i (G := G i) (hG i hi hge) b

/-! ## Step 2 — the LEFT master split `leftProd W n (circ W n c d) b = USideLn − VSideLn`. -/

/-- The per-`(i,j,p)` leading scalar of the LEFT depth-`n` assembly body (shared U/V), guarded by the
`if` that kills the negative-inner-grade circle indices `i` (`G_i = M+P-(i-2n-2)-1`).  Depth-`n`
circle weight `cbz(M+n) i`, mode `i-2n-2`; LEFT FZ shift `cbz(j+n,n)`, inner residue `cbz(G_i+n,p)`. -/
noncomputable def assemblyLeadLn (M P n : ℕ) (G : ℕ → ℕ) (i j p : ℕ) : ℂ :=
  if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 then
    cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ))
      * cbz ((G i : ℤ) + n) (p : ℤ)
  else 0

/-- The depth-`n` LEFT **U-side**: all `c₍(i-2n-2)-s₎(d₍(p-n-j-1)+s₎b)` terms.  Base-mode
`γ = (p-n-j-1)+s`, mode `μ = (i-2n-2)-s`; `mode_iterate` coefficient `(-1)^s · gBinom (i-2n-2) s`. -/
noncomputable def USideLn (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱) (G : ℕ → ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ p ∈ Finset.range (G i + n + 1),
      ∑ᶠ s : ℕ,
        (assemblyLeadLn M P n G i j p * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s))
          • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) - s)
              (W.smul d ((p - ((n : ℤ) + (j : ℤ) + 1)) + s) b)

/-- The depth-`n` LEFT **V-side**: all `d₍(i-2n-2)+(p-n-j-1)-s₎(c₍s₎b)` terms (sign `(-1)^(i-2n-2)`).
Base-mode `γ = s` (`s : ℕ`, so `≥ 0`), mode `μ = (i-2n-2)+(p-n-j-1)-s`. -/
noncomputable def VSideLn (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱) (G : ℕ → ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ p ∈ Finset.range (G i + n + 1),
      ∑ᶠ s : ℕ,
        (assemblyLeadLn M P n G i j p * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s)
            * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2)))
          • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + (p - ((n : ℤ) + (j : ℤ) + 1)) - s)
              (W.smul c (s : ℤ) b)

/-- **The LEFT master split** `leftProd W n (circ W n c d) b = USideLn − VSideLn`.  Depth-`n` LEFT
lift of `rightProd_circ_eq_USideR_sub_VSideR`.  From `leftProd_circ_UV_assembly`, pull the leading
per-`(i,j,p)` scalars into the `∑ᶠ s`-finsum, then split each finsum body `coef_s • (Uword − sv•Vword)`
into the U-part and the V-part (`smul_finsum'` + `finsum_sub_distrib`, valid by the generic
`USideL_s_fin`/`VSideL_s_fin`, `ZhuVermaAnDescent23`).  Negative-inner-grade `i` contribute `0`. -/
theorem leftProd_circ_eq_USideLn_sub_VSideLn (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ}
    {c d : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (b : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + n + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) :
    leftProd W n (circ W n c d) b = USideLn W M P n c d b G - VSideLn W M P n c d b G := by
  rw [leftProd_circ_UV_assembly W n hc hd b G hG, USideLn, VSideLn, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases lt_or_ge ((M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) 0 with hlt | hge
  · rw [if_neg (not_le.mpr hlt), smul_zero]
    simp only [assemblyLeadLn, if_neg (not_le.mpr hlt), zero_mul, zero_smul,
      finsum_zero, Finset.sum_const_zero]
    rw [sub_zero]
  · rw [if_pos hge, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    set ℓ : ℤ := (i : ℤ) - 2 * (n : ℤ) - 2 with hℓ
    set N : ℤ := (p : ℤ) - ((n : ℤ) + (j : ℤ) + 1) with hN
    set lead : ℂ := assemblyLeadLn M P n G i j p with hlead
    have hlead_val : assemblyLeadLn M P n G i j p
        = cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ))
            * cbz ((G i : ℤ) + n) (p : ℤ) := by
      rw [assemblyLeadLn, if_pos hge]
    rw [show (cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)))
            • (cbz ((G i : ℤ) + n) (p : ℤ)
                • ∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ℓ s) •
                    (W.smul c (ℓ - s) (W.smul d (N + s) b)
                      - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) b)))
          = lead • ∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ℓ s) •
                (W.smul c (ℓ - s) (W.smul d (N + s) b)
                  - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) b)) from by
        rw [smul_smul, hlead, hlead_val, mul_assoc]]
    have hfin_body : Function.HasFiniteSupport (fun s : ℕ =>
        ((-1 : ℂ) ^ s * gBinom ℓ s) •
          (W.smul c (ℓ - s) (W.smul d (N + s) b)
            - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) b))) := by
      obtain ⟨Nd, hNd⟩ := W.regularity d b
      obtain ⟨Nc, hNc⟩ := W.regularity c b
      apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) ((Nd - N).toNat + Nc.toNat))
      intro s hs
      rw [Function.mem_support] at hs
      simp only [Set.mem_Icc]
      refine ⟨Nat.zero_le _, ?_⟩
      by_contra hbig
      apply hs
      have hNdle : (Nd - N) ≤ ((Nd - N).toNat : ℤ) := Int.self_le_toNat _
      have hNcle : Nc ≤ (Nc.toNat : ℤ) := Int.self_le_toNat _
      have hs' : ((Nd - N).toNat : ℤ) + (Nc.toNat : ℤ) + 1 ≤ (s : ℤ) := by
        exact_mod_cast (by omega : (Nd - N).toNat + Nc.toNat + 1 ≤ s)
      rw [show W.smul d (N + (s : ℤ)) b = (0 : 𝒱) from hNd _ (by omega),
        show W.smul c (s : ℤ) b = (0 : 𝒱) from hNc _ (by omega)]
      simp only [PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero]
    rw [smul_finsum' lead hfin_body]
    rw [show (∑ᶠ s : ℕ, lead • ((-1 : ℂ) ^ s * gBinom ℓ s) •
              (W.smul c (ℓ - s) (W.smul d (N + s) b)
                - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) b)))
          = ∑ᶠ s : ℕ, ((lead * ((-1 : ℂ) ^ s * gBinom ℓ s)) • W.smul c (ℓ - s) (W.smul d (N + s) b)
              - (lead * ((-1 : ℂ) ^ s * gBinom ℓ s) * ((-1 : ℂ) ^ ℓ))
                  • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) b)) from
        finsum_congr fun s => by
          rw [smul_smul, smul_sub, smul_smul, mul_assoc]]
    rw [finsum_sub_distrib
        (USideL_s_fin W c d b (fun s => lead * ((-1 : ℂ) ^ s * gBinom ℓ s)) ℓ N)
        (VSideL_s_fin W c d b
          (fun s => lead * ((-1 : ℂ) ^ s * gBinom ℓ s) * ((-1 : ℂ) ^ ℓ)) (ℓ + N))]

/-! ## Step 3 — the LEFT γ-outer mode-value forms (base-mode `γ` ⊗ mode `μ`). -/

/-- The per-`(i,j,p)` LEFT U-side coefficient of `c₍ℓ+N-γ₎(d₍γ₎b)` after the `UwordL_reindex`
base-mode reindex (`ℓ = i-2n-2`, `N = p-n-j-1`): `assemblyLeadLn` times the `mode_iterate`
coefficient at the peeling index `s = γ-N`, guarded by `N ≤ γ`.  LEFT lift of `UgammaCoeff`. -/
noncomputable def UgammaCoeffLn (M P n : ℕ) (G : ℕ → ℕ) (i j p : ℕ) (γ : ℤ) : ℂ :=
  if (p : ℤ) - ((n : ℤ) + (j : ℤ) + 1) ≤ γ then
    assemblyLeadLn M P n G i j p
      * ((-1 : ℂ) ^ ((γ - ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1))).toNat)
          * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2)
              (γ - ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1))).toNat)
  else 0

/-- The per-`(i,j,p)` U-word γ-body has finite support (`UgammaL_fin` specialised). -/
theorem UgammaCoeffLn_body_fin (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱) (G : ℕ → ℕ)
    (i j p : ℕ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      UgammaCoeffLn M P n G i j p γ
        • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
            (W.smul d γ b)) :=
  UgammaL_fin W c d b
    (fun s => assemblyLeadLn M P n G i j p
      * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s))
    ((i : ℤ) - 2 * (n : ℤ) - 2) ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1))

/-- The per-`(i,j,p)` LEFT V-side coefficient of `d₍ℓ+N-γ₎(c₍γ₎b)` after the `VwordL_reindex`
base-mode reindex (`M₀ = ℓ+N = (i-2n-2)+(p-n-j-1)`): `assemblyLeadLn` times the `mode_iterate`
coefficient at `s = γ` and the V-sign `(-1)^ℓ`, guarded by `0 ≤ γ`.  LEFT lift of `VgammaCoeff`. -/
noncomputable def VgammaCoeffLn (M P n : ℕ) (G : ℕ → ℕ) (i j p : ℕ) (γ : ℤ) : ℂ :=
  if 0 ≤ γ then
    assemblyLeadLn M P n G i j p
      * ((-1 : ℂ) ^ γ.toNat * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) γ.toNat)
      * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2))
  else 0

/-- The per-`(i,j,p)` V-word γ-body has finite support (`VgammaL_fin` specialised). -/
theorem VgammaCoeffLn_body_fin (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱) (G : ℕ → ℕ)
    (i j p : ℕ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      VgammaCoeffLn M P n G i j p γ
        • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
            (W.smul c γ b)) :=
  VgammaL_fin W c d b
    (fun s => assemblyLeadLn M P n G i j p
      * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s)
      * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2)))
    (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)))

/-- **The depth-`n` LEFT U-side γ-outer mode-value form.**  LEFT lift of `USideR_eq_gammaSum`. -/
theorem USideLn_eq_gammaSum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱) (G : ℕ → ℕ) :
    USideLn W M P n c d b G
      = ∑ᶠ γ : ℤ, ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ p ∈ Finset.range (G i + n + 1),
            UgammaCoeffLn M P n G i j p γ
              • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                  (W.smul d γ b) := by
  rw [USideLn]
  rw [show (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ p ∈ Finset.range (G i + n + 1),
              ∑ᶠ s : ℕ,
                (assemblyLeadLn M P n G i j p
                    * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s))
                  • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) - s)
                      (W.smul d ((p - ((n : ℤ) + (j : ℤ) + 1)) + s) b))
        = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ p ∈ Finset.range (G i + n + 1),
              ∑ᶠ γ : ℤ, UgammaCoeffLn M P n G i j p γ
                • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                    (W.smul d γ b) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun p _ => by
          rw [UwordL_reindex W c d b
            (fun s => assemblyLeadLn M P n G i j p
              * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s))
            ((i : ℤ) - 2 * (n : ℤ) - 2) ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1))]
          exact finsum_congr fun γ => by rw [UgammaCoeffLn]]
  rw [finsum_sum_comm (Finset.range (M + n + 1))
      (fun γ i => ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (G i + n + 1),
        UgammaCoeffLn M P n G i j p γ
          • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul d γ b))
      (fun i _ => hasFinSupp_finsetSumL (Finset.range (n + 1)) _ (fun j _ =>
        hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
          UgammaCoeffLn_body_fin W M P n c d b G i j p)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_sum_comm (Finset.range (n + 1))
      (fun γ j => ∑ p ∈ Finset.range (G i + n + 1),
        UgammaCoeffLn M P n G i j p γ
          • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul d γ b))
      (fun j _ => hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
        UgammaCoeffLn_body_fin W M P n c d b G i j p))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finsum_sum_comm (Finset.range (G i + n + 1))
      (fun γ p => UgammaCoeffLn M P n G i j p γ
          • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul d γ b))
      (fun p _ => UgammaCoeffLn_body_fin W M P n c d b G i j p)]

/-- **The depth-`n` LEFT V-side γ-outer mode-value form.**  LEFT lift of `VSideR_eq_gammaSum`. -/
theorem VSideLn_eq_gammaSum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱) (G : ℕ → ℕ) :
    VSideLn W M P n c d b G
      = ∑ᶠ γ : ℤ, ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ p ∈ Finset.range (G i + n + 1),
            VgammaCoeffLn M P n G i j p γ
              • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                  (W.smul c γ b) := by
  rw [VSideLn]
  rw [show (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ p ∈ Finset.range (G i + n + 1),
              ∑ᶠ s : ℕ,
                (assemblyLeadLn M P n G i j p
                    * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s)
                    * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2)))
                  • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + (p - ((n : ℤ) + (j : ℤ) + 1)) - s)
                      (W.smul c (s : ℤ) b))
        = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ p ∈ Finset.range (G i + n + 1),
              ∑ᶠ γ : ℤ, VgammaCoeffLn M P n G i j p γ
                • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                    (W.smul c γ b) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun p _ => by
          rw [VwordL_reindex W c d b
            (fun s => assemblyLeadLn M P n G i j p
              * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s)
              * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2)))
            (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)))]
          exact finsum_congr fun γ => by rw [VgammaCoeffLn]]
  rw [finsum_sum_comm (Finset.range (M + n + 1))
      (fun γ i => ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (G i + n + 1),
        VgammaCoeffLn M P n G i j p γ
          • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul c γ b))
      (fun i _ => hasFinSupp_finsetSumL (Finset.range (n + 1)) _ (fun j _ =>
        hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
          VgammaCoeffLn_body_fin W M P n c d b G i j p)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_sum_comm (Finset.range (n + 1))
      (fun γ j => ∑ p ∈ Finset.range (G i + n + 1),
        VgammaCoeffLn M P n G i j p γ
          • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul c γ b))
      (fun j _ => hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
        VgammaCoeffLn_body_fin W M P n c d b G i j p))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finsum_sum_comm (Finset.range (G i + n + 1))
      (fun γ p => VgammaCoeffLn M P n G i j p γ
          • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul c γ b))
      (fun p _ => VgammaCoeffLn_body_fin W M P n c d b G i j p)]

/-! ## Step 4 — the per-`γ` mode collection and the double-finsum forms. -/

/-- The net per-`(γ,μ)` LEFT U-side scalar: the finite `(i,j,p)`-sum of `UgammaCoeffLn` whose
`mode_iterate` mode value `(i-2n-2)+(p-n-j-1)-γ` equals `μ`.  LEFT lift of `UgammaModeColl`. -/
noncomputable def UgammaModeCollLn (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ p ∈ Finset.range (G i + n + 1),
      (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
        then UgammaCoeffLn M P n G i j p γ else 0)

/-- The net per-`(γ,μ)` LEFT V-side scalar.  LEFT lift of `VgammaModeColl`. -/
noncomputable def VgammaModeCollLn (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ p ∈ Finset.range (G i + n + 1),
      (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
        then VgammaCoeffLn M P n G i j p γ else 0)

/-- **Per-`γ` LEFT U-side mode collection.**  LEFT lift of `gammaBody_eq_muSum_U`. -/
theorem gammaBodyLn_eq_muSum_U (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱) (G : ℕ → ℕ)
    (γ : ℤ) :
    (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
        ∑ p ∈ Finset.range (G i + n + 1),
          UgammaCoeffLn M P n G i j p γ
            • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                (W.smul d γ b))
      = ∑ᶠ μ : ℤ, UgammaModeCollLn M P n G γ μ • W.smul c μ (W.smul d γ b) := by
  rw [show (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ p ∈ Finset.range (G i + n + 1),
              UgammaCoeffLn M P n G i j p γ
                • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                    (W.smul d γ b))
        = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ μ : ℤ, ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then UgammaCoeffLn M P n G i j p γ else 0)
                  • W.smul c μ (W.smul d γ b) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [show (∑ p ∈ Finset.range (G i + n + 1),
                  UgammaCoeffLn M P n G i j p γ
                    • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                        (W.smul d γ b))
              = ∑ p ∈ Finset.range (G i + n + 1),
                  ∑ᶠ μ : ℤ, (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2)
                        + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                      then UgammaCoeffLn M P n G i j p γ else 0) • W.smul c μ (W.smul d γ b) from
            Finset.sum_congr rfl fun p _ =>
              usingleL_eq_muFinsum W c d b (UgammaCoeffLn M P n G i j p γ)
                (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ) γ]
        rw [← finsum_sum_comm (Finset.range (G i + n + 1))
            (fun μ p => (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2)
                  + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                then UgammaCoeffLn M P n G i j p γ else 0) • W.smul c μ (W.smul d γ b))
            (fun p _ => umuL_indicator_fin W c d b (UgammaCoeffLn M P n G i j p γ) _ γ)]]
  rw [show (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ μ : ℤ, ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then UgammaCoeffLn M P n G i j p γ else 0) • W.smul c μ (W.smul d γ b))
        = ∑ i ∈ Finset.range (M + n + 1),
            ∑ᶠ μ : ℤ, ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then UgammaCoeffLn M P n G i j p γ else 0) • W.smul c μ (W.smul d γ b) from
      Finset.sum_congr rfl fun i _ => by
        rw [← finsum_sum_comm (Finset.range (n + 1))
            (fun μ j => ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then UgammaCoeffLn M P n G i j p γ else 0) • W.smul c μ (W.smul d γ b))
            (fun j _ => hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
              umuL_indicator_fin W c d b (UgammaCoeffLn M P n G i j p γ) _ γ))]]
  rw [← finsum_sum_comm (Finset.range (M + n + 1))
      (fun μ i => ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (G i + n + 1),
          (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
            then UgammaCoeffLn M P n G i j p γ else 0) • W.smul c μ (W.smul d γ b))
      (fun i _ => hasFinSupp_finsetSumL (Finset.range (n + 1)) _ (fun j _ =>
        hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
          umuL_indicator_fin W c d b (UgammaCoeffLn M P n G i j p γ) _ γ)))]
  refine finsum_congr fun μ => ?_
  rw [UgammaModeCollLn, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul]

/-- **Per-`γ` LEFT V-side mode collection** (the V mirror). -/
theorem gammaBodyLn_eq_muSum_V (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱) (G : ℕ → ℕ)
    (γ : ℤ) :
    (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
        ∑ p ∈ Finset.range (G i + n + 1),
          VgammaCoeffLn M P n G i j p γ
            • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                (W.smul c γ b))
      = ∑ᶠ μ : ℤ, VgammaModeCollLn M P n G γ μ • W.smul d μ (W.smul c γ b) := by
  rw [show (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ p ∈ Finset.range (G i + n + 1),
              VgammaCoeffLn M P n G i j p γ
                • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                    (W.smul c γ b))
        = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ μ : ℤ, ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then VgammaCoeffLn M P n G i j p γ else 0)
                  • W.smul d μ (W.smul c γ b) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [show (∑ p ∈ Finset.range (G i + n + 1),
                  VgammaCoeffLn M P n G i j p γ
                    • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                        (W.smul c γ b))
              = ∑ p ∈ Finset.range (G i + n + 1),
                  ∑ᶠ μ : ℤ, (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2)
                        + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                      then VgammaCoeffLn M P n G i j p γ else 0) • W.smul d μ (W.smul c γ b) from
            Finset.sum_congr rfl fun p _ =>
              vsingleL_eq_muFinsum W c d b (VgammaCoeffLn M P n G i j p γ)
                (((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ) γ]
        rw [← finsum_sum_comm (Finset.range (G i + n + 1))
            (fun μ p => (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2)
                  + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                then VgammaCoeffLn M P n G i j p γ else 0) • W.smul d μ (W.smul c γ b))
            (fun p _ => vmuL_indicator_fin W c d b (VgammaCoeffLn M P n G i j p γ) _ γ)]]
  rw [show (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ μ : ℤ, ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then VgammaCoeffLn M P n G i j p γ else 0) • W.smul d μ (W.smul c γ b))
        = ∑ i ∈ Finset.range (M + n + 1),
            ∑ᶠ μ : ℤ, ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then VgammaCoeffLn M P n G i j p γ else 0) • W.smul d μ (W.smul c γ b) from
      Finset.sum_congr rfl fun i _ => by
        rw [← finsum_sum_comm (Finset.range (n + 1))
            (fun μ j => ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then VgammaCoeffLn M P n G i j p γ else 0) • W.smul d μ (W.smul c γ b))
            (fun j _ => hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
              vmuL_indicator_fin W c d b (VgammaCoeffLn M P n G i j p γ) _ γ))]]
  rw [← finsum_sum_comm (Finset.range (M + n + 1))
      (fun μ i => ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (G i + n + 1),
          (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
            then VgammaCoeffLn M P n G i j p γ else 0) • W.smul d μ (W.smul c γ b))
      (fun i _ => hasFinSupp_finsetSumL (Finset.range (n + 1)) _ (fun j _ =>
        hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
          vmuL_indicator_fin W c d b (VgammaCoeffLn M P n G i j p γ) _ γ)))]
  refine finsum_congr fun μ => ?_
  rw [VgammaModeCollLn, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul]

/-- **`USideLn` as a base-mode ⊗ mode double finsum.** -/
theorem USideLn_eq_gammaModeFinsum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱)
    (G : ℕ → ℕ) :
    USideLn W M P n c d b G
      = ∑ᶠ γ : ℤ, ∑ᶠ μ : ℤ, UgammaModeCollLn M P n G γ μ • W.smul c μ (W.smul d γ b) := by
  rw [USideLn_eq_gammaSum]
  exact finsum_congr fun γ => gammaBodyLn_eq_muSum_U W M P n c d b G γ

/-- **`VSideLn` as a base-mode ⊗ mode double finsum.** -/
theorem VSideLn_eq_gammaModeFinsum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱)
    (G : ℕ → ℕ) :
    VSideLn W M P n c d b G
      = ∑ᶠ γ : ℤ, ∑ᶠ μ : ℤ, VgammaModeCollLn M P n G γ μ • W.smul d μ (W.smul c γ b) := by
  rw [VSideLn_eq_gammaSum]
  exact finsum_congr fun γ => gammaBodyLn_eq_muSum_V W M P n c d b G γ

/-! ## Step 5 — the LEFT depth-`n` tower-decomposition predicate and the membership criterion.

The U-words of `USideLn` are `c₍μ₎(d₍γ₎b)` — exactly the body of `UfamOn W M n c d b` — and the
V-words of `VSideLn` are `d₍μ₎(c₍γ₎b)` — exactly `VfamOn W P n c d b`.  So the existing membership
engine `UfamOn_mem_On`/`VfamOn_mem_On` (`ZhuVermaAnDescent8`, via the keystone `Pres_mem_On`) carries
the tower decomposition into `On W n`, hence into `OnFull W n` (via `On_le_OnFull`, `ZhuVermaAnArch`).
This is the level-matched LEFT mirror of `RightCircTowerEq` / `rightProd_circ_mem_On_of_tower_eq`. -/

/-- **The LEFT depth-`n` circle tower-decomposition predicate**: `leftProd W n (circ W n c d) b`
equals a `UfamOn` (towers in `c` based at `d₍γ₎b`) plus a `VfamOn` (towers in `d` based at `c₍γ₎b`).
LEFT lift of `RightCircTowerEq`, depth-`n` circle (shift `2n+2` BOTH sides). -/
def LeftCircTowerEqn (W : VertexOperatorAlgebra 𝒱) (n M P : ℕ) (c d b : 𝒱) : Prop :=
  ∃ (wU wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ),
    leftProd W n (circ W n c d) b
      = UfamOn W M n c d b wU γ₀ Γ Δ + VfamOn W P n c d b wV γ₀ Γ Δ

/-- **The LEFT tower-collapse membership criterion (into `On W n`).**  For homogeneous `c ∈ 𝒱_M`,
`d ∈ 𝒱_P`, if `leftProd W n (circ W n c d) b` collapses onto the U/V `PresOn`-tower families
(`LeftCircTowerEqn`), then it lies in `On W n`.  Membership closed by `UfamOn_mem_On`/`VfamOn_mem_On`
(via `Pres_mem_On`).  LEFT lift of `rightProd_circ_mem_On_of_tower_eq`. -/
theorem leftProd_circ_mem_On_of_tower_eq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (b : 𝒱)
    (htow : LeftCircTowerEqn W n M P c d b) :
    leftProd W n (circ W n c d) b ∈ On W n := by
  obtain ⟨wU, wV, γ₀, Γ, Δ, heq⟩ := htow
  rw [heq]
  exact Submodule.add_mem _ (UfamOn_mem_On W n hc d b wU γ₀ Γ Δ)
    (VfamOn_mem_On W n hd c b wV γ₀ Γ Δ)

/-- **The LEFT tower-collapse membership criterion (into `OnFull W n`).**  Wraps
`leftProd_circ_mem_On_of_tower_eq` with `On_le_OnFull` — the exact `hLcirc` shape consumed by
`AnIdeal_of_gens` (`ZhuVermaAnArch`). -/
theorem leftProd_circ_mem_OnFull_of_tower_eq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ}
    {c d : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (b : 𝒱)
    (htow : LeftCircTowerEqn W n M P c d b) :
    leftProd W n (circ W n c d) b ∈ OnFull W n :=
  On_le_OnFull W n (leftProd_circ_mem_On_of_tower_eq W n hc hd b htow)

/-- **`LeftCircTowerEqn` from the U-side / V-side tower-collapse.**  If, for some grade witness `G`
matching the inner circle grades, the U-side `USideLn` equals the U-family `UfamOn W M n c d b wU …`
and the V-side `VSideLn` equals the *negated* V-family `−VfamOn W P n c d b wV …`, then
`LeftCircTowerEqn W n M P c d b` holds (via the master split `leftProd_circ_eq_USideLn_sub_VSideLn`).
LEFT lift of `RightCircTowerEq_of_sides`. -/
theorem LeftCircTowerEqn_of_sides (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (b : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + n + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (wU wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ)
    (hU : USideLn W M P n c d b G = UfamOn W M n c d b wU γ₀ Γ Δ)
    (hV : VSideLn W M P n c d b G = -VfamOn W P n c d b wV γ₀ Γ Δ) :
    LeftCircTowerEqn W n M P c d b := by
  refine ⟨wU, wV, γ₀, Γ, Δ, ?_⟩
  rw [leftProd_circ_eq_USideLn_sub_VSideLn W n hc hd b G hG, hU, hV, sub_neg_eq_add]

/-! ## Step 6 — the assembled `hLcirc` from the universally-quantified predicate.

Supplying `LeftCircTowerEqn` for ALL grades `M, P` and homogeneous `c, d` discharges (L1∘) on
homogeneous data; the `reduce_homogeneous` triple (mirroring `rightProd_On_mem_On_of_homog`,
`ZhuVermaAnDescent5`) extends it to ALL `c, d`, giving the `AnIdeal_of_gens` field `hLcirc`. -/

/-- **(L1∘) on homogeneous data from the universally-quantified `LeftCircTowerEqn`.** -/
theorem leftProd_circ_mem_OnFull_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P : ℕ), ∀ c ∈ W.grading (M : ℤ), ∀ d ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      LeftCircTowerEqn W n M P c d b) :
    ∀ M P : ℕ, ∀ c ∈ W.grading (M : ℤ), ∀ d ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      leftProd W n (circ W n c d) b ∈ OnFull W n := by
  intro M P c hc d hd b
  exact leftProd_circ_mem_OnFull_of_tower_eq W n hc hd b (Htow M P c hc d hd b)

/-- **`hLcirc` (the `AnIdeal_of_gens` left-circle field) from the universally-quantified
`LeftCircTowerEqn`.**  Reduces the general `c, d` to homogeneous via the `reduce_homogeneous` triple
(the circle product is bilinear in both factors and vanishes on negative gradings), then applies the
homogeneous criterion.  This is the precise input `AnIdeal_of_gens` consumes for `hLcirc`. -/
theorem hLcirc_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P : ℕ), ∀ c ∈ W.grading (M : ℤ), ∀ d ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      LeftCircTowerEqn W n M P c d b) :
    ∀ c d b : 𝒱, leftProd W n (circ W n c d) b ∈ OnFull W n := by
  have key := leftProd_circ_mem_OnFull_of_towerEq W n Htow
  intro c d b
  -- reduce `c` to homogeneous.
  refine reduce_homogeneous W
    (P := fun c => leftProd W n (circ W n c d) b ∈ OnFull W n) ?_ ?_ ?_ c
  · intro M c hc
    -- reduce `d` to homogeneous.
    refine reduce_homogeneous W
      (P := fun d => leftProd W n (circ W n c d) b ∈ OnFull W n) ?_ ?_ ?_ d
    · intro P d hd
      rcases lt_or_ge M 0 with hM | hM
      · rw [W.positivity M hM, Submodule.mem_bot] at hc
        subst hc; rw [circ_zero_left W n d, leftProd_zero_left]; exact (OnFull W n).zero_mem
      rcases lt_or_ge P 0 with hP | hP
      · rw [W.positivity P hP, Submodule.mem_bot] at hd
        subst hd; rw [circ_zero_right, leftProd_zero_left]; exact (OnFull W n).zero_mem
      · obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = (M' : ℤ) := ⟨M.toNat, by omega⟩
        obtain ⟨P', rfl⟩ : ∃ P' : ℕ, P = (P' : ℤ) := ⟨P.toNat, by omega⟩
        exact key M' P' c hc d hd b
    · show leftProd W n (circ W n c (0 : 𝒱)) b ∈ OnFull W n
      rw [circ_zero_right, leftProd_zero_left]; exact (OnFull W n).zero_mem
    · intro x y hx hy
      show leftProd W n (circ W n c (x + y)) b ∈ OnFull W n
      rw [circ_add_right, leftProd_add_left]
      exact (OnFull W n).add_mem hx hy
  · show leftProd W n (circ W n (0 : 𝒱) d) b ∈ OnFull W n
    rw [circ_zero_left W n d, leftProd_zero_left]; exact (OnFull W n).zero_mem
  · intro x y hx hy
    show leftProd W n (circ W n (x + y) d) b ∈ OnFull W n
    rw [circ_add_left, leftProd_add_left]
    exact (OnFull W n).add_mem hx hy

/-!
## Status of (L1∘): the PRECISE remaining target (NOT `sorry`, NOT axiomatized).

Everything above is axiom-clean (`[propext, Classical.choice, Quot.sound]`).  (L1∘)
— the `hLcirc` field of `AnIdeal_of_gens` (`ZhuVermaAnArch`) — is reduced to the single
tower-decomposition predicate

  **`LeftCircTowerEqn W n M P c d b`** : `leftProd W n (circ W n c d) b = UfamOn W M n c d b wU … +
  VfamOn W P n c d b wV …`  (`∃ wU wV γ₀ Γ Δ`),

via `hLcirc_of_towerEq` (general `c,d` from the homogeneous criterion + `reduce_homogeneous`).  The
proved **LEFT master split** (`leftProd_circ_eq_USideLn_sub_VSideLn`) + the γ-outer mode-value forms
(`USideLn_eq_gammaModeFinsum`/`VSideLn_eq_gammaModeFinsum`) put both sides in the exact
`∑ᶠ γ, ∑ᶠ μ, (scalar) • word` shape that `UfamOn_eq_finsum`/`VfamOn_eq_finsum`
(`ZhuVermaAnDescent9`) consume, and `LeftCircTowerEqn_of_sides` reduces the predicate to the two
side-collapses `USideLn = UfamOn` / `VSideLn = −VfamOn`.

Because the circle here is the **depth-`n`** circle `circ W n` (mode `i-2n-2`, weight `cbz(M+n) i`),
BOTH `UgammaModeCollLn` and `VgammaModeCollLn` carry the `PresOn` shift `2n+2` — exactly matching the
tower-family weights `towerCoeff M n (wU γ) Δ` / `towerCoeff P n (wV γ) Δ` (`ZhuVermaAnDescent9`).
This is the clean level-matched mirror; there is NO shift-`2` "pole-2 overshoot" (the dead
`circ W 0` obstruction of `ZhuVermaAnDescent23`).

### The single remaining combinatorial content (the two scalar cores)

  (U-core)  `UgammaModeCollLn M P n G γ μ = towerCoeff M n (wU γ) Δ μ`     for some `wU, Δ`,
  (V-core)  `VgammaModeCollLn M P n G γ μ = -towerCoeff P n (wV γ) Δ μ`    for some `wV, Δ`,

(plus the finite-base-mode-window bridge `∑ᶠ γ → ∑ g ∈ range Γ`, exactly the `finsum_window` /
`towerCoeff_pad` bookkeeping of `ZhuVermaAnDescent21`).  These are the LEFT lift of the proven RIGHT
cores `UgammaModeColl_eq_towerCoeff`/`VgammaModeColl_eq_towerCoeff` (`ZhuVermaAnDescent19/20`), with
`leftProd`'s `cbz(j+n,n)` FZ scalar replacing `rightProd`'s `cbz(j+n,j)` — the same
`ZhuRes.gen_vandermonde`/`gen_jsum` engine.  Formalising the two cores (and assembling them through
`LeftCircTowerEqn_of_sides` exactly as `RightCircTowerEq_holds`, `ZhuVermaAnDescent21`, assembles its
two cores) discharges `LeftCircTowerEqn`, hence (L1∘), for all `n`.  Nothing is `sorry`'d or
axiomatized.
-/

end VOA
