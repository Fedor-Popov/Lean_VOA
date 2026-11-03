/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent22
import VOA.Modules.ZhuVermaAnDescent21
import VOA.Modules.ZhuVermaAnDescent6

/-!
# The LEFT depth-`0`-circle cross-assembly infrastructure (toward (L-circ0)).

The depth-`n` LEFT lift of the right-circle `ZhuVermaAnDescent7→10` pipeline, specialized to the
depth-`0` circle `circ W 0 u v` in the FIRST slot of `leftProd`.  This is the structural reduction
of the left circle-0 membership (L-circ0) `leftProd W n (circ W 0 u v) b ∈ Oₙ` (which discharges the
left `gen_mem` via `leftProd_genL_mem_On_of_circ0`, `ZhuVermaAnDescent22`).

Proved here (all `[propext, Classical.choice, Quot.sound]`):
* `leftProd_circ0_eq_USideL_sub_VSideL` — the **LEFT master split** `leftProd W n (circ W 0 u v) b
  = USideL − VSideL` (lift of `ZhuAssociator.lhs_split`).
* `USideL_eq_gammaModeFinsum` / `VSideL_eq_gammaModeFinsum` — each side reindexed to the base-mode
  `γ` ⊗ mode `μ` double finsum `∑ᶠ γ ∑ᶠ μ, UgammaModeCollL/VgammaModeCollL • word`.
* `LeftCircTowerEq` + `LeftCircTowerEq_of_sides` + the conditional discharge chain
  `leftProd_circ0_mem_On_of_towerEq` → `leftProd_genL_mem_On_of_towerEq` →
  `LeftGenTowerEq_holds_of_towerEq` (membership criterion + routing to the left `gen_mem`).

## The PRECISE remaining content (NOT `sorry`'d / NOT axiomatized) — the genuine cross-assembly

Mathematica-verified (exact `Solve`, `n ≤ 2`, `M,P ≤ 5`): the per-side LEFT scalars are towers but
with the **depth-`0` circle shift `2`** (`UgammaModeCollL = ∑_δ wU(n,P,γ,δ)·cbz(M+n+δ, μ+2+δ)`),
whereas the `PresOn` towers (`UfamOn`/`VfamOn`, `∈ On` by `Pres_mem_On`) carry shift `2n+2`.  For
`n = 0` (`2 = 2n+2`) the per-side decomposition closes directly; for `n ≥ 1` (`2 ≠ 2n+2`) NEITHER
side is a `PresOn` tower individually — this is the genuine "pole-`2` overshoot".
The remaining step is the **combined U+V cross-assembly**: the Borcherds commutator
`v₍μ₎(u₍γ₎b) = u₍γ₎(v₍μ₎b) + ∑ₖ cbz(μ,k)·(v₍k₎u)₍μ+γ−k₎b` (`mode_split_gen`, `ZhuVermaAnDescent6`)
recombines `USideL − VSideL` into shift-`2n+2` `PresOn` towers plus a `(v₍k₎u)`-circle commutator
family (the analog of the right-side commutator-family membership) — the depth-`n` LEFT lift of
`ZhuMu.mu_identity` / `ZhuAssociator.assoc_eq`.  This combined collapse (and its `R`-mirror for
(R-circ0)) is the last gate of the `A_n(𝒱)` bimodule's `gen_mem` fields.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.2; Dong–Li–Mason.
-/
/-!
# (L-circ0) — the depth-`n` LEFT U+V cross-assembly for `leftProd W n (circ W 0 u v) b ∈ Oₙ`.

The keystone of the left `gen_mem` for the `A_n(𝒱)` bimodule.  This is the depth-`n` LEFT lift of
`ZhuAssociator` (the `n=0` associator) and the LEFT analog of the depth-`n` RIGHT machinery
(`ZhuVermaAnDescent5`→`21`), but with the depth-`0` circle `circ W 0 u v` in the FIRST slot of
`leftProd`.

## Strategy (step by step)
* **Step 1.** `leftProd W n (circ W 0 u v) b` for homogeneous `u ∈ 𝒱_M` distributes over the
  depth-`0` circle weight `cbz M i`, mode `i-2`: `∑ᵢ cbz M i • leftProd W n (u₍ᵢ₋₂₎v) b`.  Each inner
  factor `u₍ᵢ₋₂₎v` is homogeneous of grade `G_i = M+P-i+1`, so the inner LEFT product collapses by
  `leftProd_homogeneous` into the FZ residue double sum over `(j,p)` of the iterated mode
  `(u₍ᵢ₋₂₎v)₍N₎b` (`N = p-n-j-1`); `iterate_term_rewrite` splits each into the U-family
  `u₍(i-2)-s₎(v₍N+s₎b)` minus the sign-weighted V-family `v₍(i-2)+N-s₎(u₍s₎b)`.  This is the LEFT lift
  of `ZhuAssociator.lhs_split` / `rightProd_circ_UV_assembly`.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Step 1a — the LEFT homogeneous collapse of `leftProd W n w b`, `ℕ`-range form. -/

/-- For homogeneous `w ∈ 𝒱_G`, `leftProd W n w b = ∑_{j≤n} (-1)^j C(j+n,n) ∑_p C(G+n,p) w₍p-n-j-1₎b`,
normalising the inner `toNat` range to `range (G+n+1)`.  The LEFT analog of `rightProd_homog_expand`
(`ZhuVermaAnDescent6`); both extra-range terms vanish via `cbz`. -/
theorem leftProd_homog_expand (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {G : ℕ} {w : 𝒱}
    (hw : w ∈ W.grading (G : ℤ)) (b : 𝒱) :
    leftProd W n w b
      = ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
            ∑ p ∈ Finset.range (G + n + 1),
              cbz ((G : ℤ) + n) (p : ℤ)
                • W.smul w ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) b := by
  rw [leftProd_homogeneous W n hw b]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (((G : ℤ) + (n : ℤ)).toNat + 1) = G + n + 1 from by
        rw [show ((G : ℤ) + (n : ℤ)) = ((G + n : ℕ) : ℤ) from by push_cast; ring, Int.toNat_natCast]]

/-! ## Step 1b — the depth-`0` circle distribution over `leftProd`, mode `i-2`, weight `cbz M i`. -/

/-- `leftProd W n (circ W 0 u v) b` for homogeneous `u ∈ 𝒱_M` distributes over the depth-`0` circle
expansion: `∑ᵢ cbz M i • leftProd W n (u₍ᵢ₋₂₎v) b` (the LEFT lift of `leftProd_circ_homogeneous_left`
specialised to the depth-`0` circle). -/
theorem leftProd_circ0_homogeneous_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v b : 𝒱) :
    leftProd W n (circ W 0 u v) b
      = ∑ i ∈ Finset.range (M + 1),
          cbz (M : ℤ) (i : ℤ) • leftProd W n (W.smul u ((i : ℤ) - 2) v) b := by
  rw [circ0_homog W hu v]
  induction (Finset.range (M + 1)) using Finset.induction with
  | empty => simp [leftProd_zero_left]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, leftProd_add_left, leftProd_smul_left, ih]

/-! ## Step 1c — the inner factor grade, and the per-`i` inner LEFT product collapse. -/

/-- The depth-`0` circle inner factor `u₍ᵢ₋₂₎v` lands in `𝒱_{M+P-(i-2)-1} = 𝒱_{M+P-i+1}`. -/
theorem circ0_inner_mem_grading (W : VertexOperatorAlgebra 𝒱) {M P : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (i : ℕ) :
    W.smul u ((i : ℤ) - 2) v ∈ W.grading ((M : ℤ) + (P : ℤ) - ((i : ℤ) - 2) - 1) :=
  W.smul_mem_grading hu hv ((i : ℤ) - 2)

/-- The per-`i` inner LEFT product `leftProd W n (u₍ᵢ₋₂₎v) b`, when the inner grade `G := M+P-(i-2)-1
≥ 0`, expanded by `leftProd_homog_expand` and split (per `(j,p)`) into the U/V finsum families via
`iterate_term_rewrite`/`iterate_UV_split`.  The LEFT lift of `rightProd_circ_inner_UVterm`. -/
theorem leftProd_circ0_inner_UVterm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P G : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (i : ℕ)
    (hG : (G : ℤ) = (M : ℤ) + (P : ℤ) - ((i : ℤ) - 2) - 1) (b : 𝒱) :
    leftProd W n (W.smul u ((i : ℤ) - 2) v) b
      = ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
            ∑ p ∈ Finset.range (G + n + 1),
              cbz ((G : ℤ) + n) (p : ℤ) •
                (∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2) s) •
                  (W.smul u (((i : ℤ) - 2) - s)
                      (W.smul v ((p - ((n : ℤ) + (j : ℤ) + 1)) + s) b)
                    - ((-1 : ℂ) ^ ((i : ℤ) - 2))
                      • W.smul v (((i : ℤ) - 2) + (p - ((n : ℤ) + (j : ℤ) + 1)) - s)
                          (W.smul u (s : ℤ) b))) := by
  have hmem : W.smul u ((i : ℤ) - 2) v ∈ W.grading (G : ℤ) := by
    rw [hG]; exact circ0_inner_mem_grading W hu hv i
  rw [leftProd_homog_expand W n hmem b]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  exact iterate_term_rewrite W u v b ((i : ℤ) - 2) (p : ℤ) n j

/-! ## Step 1d — the assembled depth-`n` LEFT U/V split of `leftProd W n (circ W 0 u v) b`. -/

/-- The full assembled U/V split of `leftProd W n (circ W 0 u v) b` over the circle index `i`, FZ
index `j`, residue index `p`, and `mode_iterate` index `s`, with the negative-inner-grade indices `i`
(where `u₍ᵢ₋₂₎v` vanishes) carried by an explicit `if`-guard.  The LEFT lift of
`rightProd_circ_UV_assembly` / `ZhuAssociator.lhs_split`. -/
theorem leftProd_circ0_UV_assembly (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (b : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2) - 1) :
    leftProd W n (circ W 0 u v) b
      = ∑ i ∈ Finset.range (M + 1),
          cbz (M : ℤ) (i : ℤ) •
            (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2) - 1 then
              ∑ j ∈ Finset.range (n + 1),
                ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
                  ∑ p ∈ Finset.range (G i + n + 1),
                    cbz ((G i : ℤ) + n) (p : ℤ) •
                      (∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2) s) •
                        (W.smul u (((i : ℤ) - 2) - s)
                            (W.smul v ((p - ((n : ℤ) + (j : ℤ) + 1)) + s) b)
                          - ((-1 : ℂ) ^ ((i : ℤ) - 2))
                            • W.smul v (((i : ℤ) - 2) + (p - ((n : ℤ) + (j : ℤ) + 1)) - s)
                                (W.smul u (s : ℤ) b)))
            else 0) := by
  rw [leftProd_circ0_homogeneous_left W n hu v b]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  rcases lt_or_ge ((M : ℤ) + P - ((i : ℤ) - 2) - 1) 0 with hlt | hge
  · rw [if_neg (not_le.mpr hlt)]
    have hmem : W.smul u ((i : ℤ) - 2) v
        ∈ W.grading ((M : ℤ) + P - ((i : ℤ) - 2) - 1) :=
      circ0_inner_mem_grading W hu hv i
    rw [W.positivity _ hlt, Submodule.mem_bot] at hmem
    rw [hmem, leftProd_zero_left]
  · rw [if_pos hge]
    exact leftProd_circ0_inner_UVterm W n hu hv i (G := G i) (hG i hi hge) b

/-! ## Step 2 — the LEFT master split `leftProd W n (circ W 0 u v) b = USideL − VSideL`.

The LEFT depth-`0` analog of `ZhuAssociator.lhs_split` / `rightProd_circ_eq_USideR_sub_VSideR`
(`ZhuVermaAnDescent10`).  We package the U-words `u₍μ₎(v₍γ₎b)` and V-words `v₍μ₎(u₍γ₎b)` of the
proved assembly `leftProd_circ0_UV_assembly` as separate finite `(i,j,p)`-sums with an inner `∑ᶠ s`
(`mode_iterate` peeling index, finite by `W.regularity`).  The leading per-`(i,j,p)` scalar
`assemblyLeadL := cbz M i · (-1)^j cbz(j+n,n) · cbz(G_i+n, p)` (depth-`0` circle weight `cbz M i`,
mode `i-2`; LEFT shift `cbz(j+n,n)`) is shared. -/

/-- The per-`(i,j,p)` leading scalar of the LEFT depth-`0` assembly body (shared U/V), guarded by the
`if` that kills the negative-inner-grade circle indices `i` (`G_i = M+P-(i-2)-1 = M+P-i+1`). -/
noncomputable def assemblyLeadL (M P n : ℕ) (G : ℕ → ℕ) (i j p : ℕ) : ℂ :=
  if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2) - 1 then
    cbz (M : ℤ) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ))
      * cbz ((G i : ℤ) + n) (p : ℤ)
  else 0

/-- The LEFT **U-side**: all `u₍(i-2)-s₎(v₍(p-n-j-1)+s₎b)` terms.  Base-mode `γ = (p-n-j-1)+s`, mode
`μ = (i-2)-s`; the `mode_iterate` coefficient is `(-1)^s · gBinom (i-2) s`. -/
noncomputable def USideL (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ p ∈ Finset.range (G i + n + 1),
      ∑ᶠ s : ℕ,
        (assemblyLeadL M P n G i j p * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2) s))
          • W.smul u (((i : ℤ) - 2) - s)
              (W.smul v ((p - ((n : ℤ) + (j : ℤ) + 1)) + s) b)

/-- The LEFT **V-side**: all `v₍(i-2)+(p-n-j-1)-s₎(u₍s₎b)` terms (carrying the sign `(-1)^(i-2)`).
Base-mode `γ = s` (`s : ℕ`, so `≥ 0`), mode `μ = (i-2)+(p-n-j-1)-s`. -/
noncomputable def VSideL (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ p ∈ Finset.range (G i + n + 1),
      ∑ᶠ s : ℕ,
        (assemblyLeadL M P n G i j p * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2) s)
            * ((-1 : ℂ) ^ ((i : ℤ) - 2)))
          • W.smul v (((i : ℤ) - 2) + (p - ((n : ℤ) + (j : ℤ) + 1)) - s)
              (W.smul u (s : ℤ) b)

/-! ## Finite support of the per-`(i,j,p)` U/V `mode_iterate` `s`-finsums. -/

/-- The U-word `s`-finsum (per `(i,j,p)`, arbitrary `s`-coefficient `co`) has finite support: the
U-word `u₍ℓ-s₎(v₍N+s₎b)` vanishes once `N+s ≥ N_v` (`W.regularity v b`). -/
theorem USideL_s_fin (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (co : ℕ → ℂ) (ℓ N : ℤ) :
    Function.HasFiniteSupport (fun s : ℕ =>
      co s • W.smul u (ℓ - s) (W.smul v (N + s) b)) := by
  obtain ⟨Nv, hNv⟩ := W.regularity v b
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) (Nv - N).toNat)
  intro s hs
  rw [Function.mem_support] at hs
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hs
  have hNle : (Nv - N) ≤ ((Nv - N).toNat : ℤ) := Int.self_le_toNat _
  have hs' : ((Nv - N).toNat : ℤ) + 1 ≤ (s : ℤ) := by
    exact_mod_cast (by omega : (Nv - N).toNat + 1 ≤ s)
  rw [show W.smul v (N + (s : ℤ)) b = (0 : 𝒱) from hNv _ (by omega)]
  rw [PreVertexAlgebra.smul_zero_right, smul_zero]

/-- The V-word `s`-finsum (per `(i,j,p)`, arbitrary `s`-coefficient `co`) has finite support: the
V-word `v₍μ-s₎(u₍s₎b)` vanishes once `s ≥ N_u` (`W.regularity u b`). -/
theorem VSideL_s_fin (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (co : ℕ → ℂ) (μ : ℤ) :
    Function.HasFiniteSupport (fun s : ℕ =>
      co s • W.smul v (μ - s) (W.smul u (s : ℤ) b)) := by
  obtain ⟨Nu, hNu⟩ := W.regularity u b
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) Nu.toNat)
  intro s hs
  rw [Function.mem_support] at hs
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hs
  have hNle : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat _
  have hs' : (Nu.toNat : ℤ) + 1 ≤ (s : ℤ) := by exact_mod_cast (by omega : Nu.toNat + 1 ≤ s)
  rw [show W.smul u (s : ℤ) b = (0 : 𝒱) from hNu _ (by omega)]
  rw [PreVertexAlgebra.smul_zero_right, smul_zero]

/-- **The LEFT master split** `leftProd W n (circ W 0 u v) b = USideL − VSideL`.  Depth-`0` LEFT lift
of `ZhuAssociator.lhs_split`.  From the proved assembly `leftProd_circ0_UV_assembly`, pull the leading
per-`(i,j,p)` scalars into the `∑ᶠ s`-finsum, then split each finsum body `coef_s • (Uword − sv·Vword)`
into the U-part and the V-part (`smul_finsum'` + `finsum_sub_distrib`, valid by
`USideL_s_fin`/`VSideL_s_fin`).  The negative-inner-grade circle indices `i` contribute `0` on both
sides through the `assemblyLeadL` `if`. -/
theorem leftProd_circ0_eq_USideL_sub_VSideL (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ}
    {u v : 𝒱} (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (b : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2) - 1) :
    leftProd W n (circ W 0 u v) b = USideL W M P n u v b G - VSideL W M P n u v b G := by
  rw [leftProd_circ0_UV_assembly W n hu hv b G hG, USideL, VSideL, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases lt_or_ge ((M : ℤ) + P - ((i : ℤ) - 2) - 1) 0 with hlt | hge
  · rw [if_neg (not_le.mpr hlt), smul_zero]
    simp only [assemblyLeadL, if_neg (not_le.mpr hlt), zero_mul, zero_smul,
      finsum_zero, Finset.sum_const_zero]
    rw [sub_zero]
  · rw [if_pos hge, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    set ℓ : ℤ := (i : ℤ) - 2 with hℓ
    set N : ℤ := (p : ℤ) - ((n : ℤ) + (j : ℤ) + 1) with hN
    set lead : ℂ := assemblyLeadL M P n G i j p with hlead
    have hlead_val : assemblyLeadL M P n G i j p
        = cbz (M : ℤ) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ))
            * cbz ((G i : ℤ) + n) (p : ℤ) := by
      rw [assemblyLeadL, if_pos hge]
    rw [show (cbz (M : ℤ) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)))
            • (cbz ((G i : ℤ) + n) (p : ℤ)
                • ∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ℓ s) •
                    (W.smul u (ℓ - s) (W.smul v (N + s) b)
                      - ((-1 : ℂ) ^ ℓ) • W.smul v (ℓ + N - s) (W.smul u (s : ℤ) b)))
          = lead • ∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ℓ s) •
                (W.smul u (ℓ - s) (W.smul v (N + s) b)
                  - ((-1 : ℂ) ^ ℓ) • W.smul v (ℓ + N - s) (W.smul u (s : ℤ) b)) from by
        rw [smul_smul, hlead, hlead_val, mul_assoc]]
    have hfin_body : Function.HasFiniteSupport (fun s : ℕ =>
        ((-1 : ℂ) ^ s * gBinom ℓ s) •
          (W.smul u (ℓ - s) (W.smul v (N + s) b)
            - ((-1 : ℂ) ^ ℓ) • W.smul v (ℓ + N - s) (W.smul u (s : ℤ) b))) := by
      obtain ⟨Nv, hNv⟩ := W.regularity v b
      obtain ⟨Nu, hNu⟩ := W.regularity u b
      apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) ((Nv - N).toNat + Nu.toNat))
      intro s hs
      rw [Function.mem_support] at hs
      simp only [Set.mem_Icc]
      refine ⟨Nat.zero_le _, ?_⟩
      by_contra hbig
      apply hs
      have hNvle : (Nv - N) ≤ ((Nv - N).toNat : ℤ) := Int.self_le_toNat _
      have hNule : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat _
      have hs' : ((Nv - N).toNat : ℤ) + (Nu.toNat : ℤ) + 1 ≤ (s : ℤ) := by
        exact_mod_cast (by omega : (Nv - N).toNat + Nu.toNat + 1 ≤ s)
      rw [show W.smul v (N + (s : ℤ)) b = (0 : 𝒱) from hNv _ (by omega),
        show W.smul u (s : ℤ) b = (0 : 𝒱) from hNu _ (by omega)]
      simp only [PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero]
    rw [smul_finsum' lead hfin_body]
    rw [show (∑ᶠ s : ℕ, lead • ((-1 : ℂ) ^ s * gBinom ℓ s) •
              (W.smul u (ℓ - s) (W.smul v (N + s) b)
                - ((-1 : ℂ) ^ ℓ) • W.smul v (ℓ + N - s) (W.smul u (s : ℤ) b)))
          = ∑ᶠ s : ℕ, ((lead * ((-1 : ℂ) ^ s * gBinom ℓ s)) • W.smul u (ℓ - s) (W.smul v (N + s) b)
              - (lead * ((-1 : ℂ) ^ s * gBinom ℓ s) * ((-1 : ℂ) ^ ℓ))
                  • W.smul v (ℓ + N - s) (W.smul u (s : ℤ) b)) from
        finsum_congr fun s => by
          rw [smul_smul, smul_sub, smul_smul, mul_assoc]]
    rw [finsum_sub_distrib
        (USideL_s_fin W u v b (fun s => lead * ((-1 : ℂ) ^ s * gBinom ℓ s)) ℓ N)
        (VSideL_s_fin W u v b
          (fun s => lead * ((-1 : ℂ) ^ s * gBinom ℓ s) * ((-1 : ℂ) ^ ℓ)) (ℓ + N))]

/-! ## Step 3 — the LEFT γ-outer mode-value forms (base-mode `γ` ⊗ mode `μ`).

The LEFT depth-`0` lift of `ZhuVermaAnDescent10`'s reindexing chain
(`USideR_eq_gammaModeFinsum`/`VSideR_eq_gammaModeFinsum`).  We reindex each per-`(i,j,p)` `∑ᶠ s` by
its base-mode `γ`, pull `∑ᶠ γ` outermost, then collect each fixed-`γ` body by the mode value `μ` into
a net per-`(γ,μ)` scalar.  The U-words are `u₍μ₎(v₍γ₎b)`, the V-words `v₍μ₎(u₍γ₎b)`. -/

/-- **U-word base-mode reindex.**  The per-`(i,j,p)` U-word `∑ᶠ s, co(s) • u₍ℓ-s₎(v₍N+s₎b)` reindexes
by the U-base-mode `γ = N+s` to a `∑ᶠ γ`.  (LEFT lift of `Uword_reindex`.) -/
theorem UwordL_reindex (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (co : ℕ → ℂ) (ℓ N : ℤ) :
    (∑ᶠ s : ℕ, co s • W.smul u (ℓ - s) (W.smul v (N + s) b))
      = ∑ᶠ γ : ℤ, (if N ≤ γ then co (γ - N).toNat else 0)
          • W.smul u (ℓ + N - γ) (W.smul v γ b) := by
  rw [finsum_nat_to_int
      (fun s : ℕ => co s • W.smul u (ℓ - s) (W.smul v (N + s) b))
      (fun s' : ℤ => (if 0 ≤ s' then co s'.toNat else 0)
          • W.smul u (ℓ - s') (W.smul v (N + s') b))
      (fun p hp => by simp only []; rw [if_neg (by omega), zero_smul])
      (fun j => by simp only [Int.toNat_natCast]; rw [if_pos (by omega)])]
  rw [← finsum_comp_equiv (Equiv.addRight N)
      (f := fun γ : ℤ => (if N ≤ γ then co (γ - N).toNat else 0)
          • W.smul u (ℓ + N - γ) (W.smul v γ b))]
  refine finsum_congr fun s' => ?_
  simp only [Equiv.coe_addRight]
  rw [show ℓ + N - (s' + N) = ℓ - s' from by ring, show (s' + N) - N = s' from by ring]
  by_cases h : 0 ≤ s'
  · rw [if_pos h, if_pos (by omega), show N + s' = s' + N from by ring]
  · rw [if_neg h, if_neg (by omega), show N + s' = s' + N from by ring]

/-- **V-word base-mode reindex.**  The per-`(i,j,p)` V-word `∑ᶠ s, co(s) • v₍M₀-s₎(u₍s₎b)` reindexes
by the V-base-mode `γ = s`, `M₀ = ℓ+N`.  (LEFT lift of `Vword_reindex`.) -/
theorem VwordL_reindex (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (co : ℕ → ℂ) (M0 : ℤ) :
    (∑ᶠ s : ℕ, co s • W.smul v (M0 - s) (W.smul u (s : ℤ) b))
      = ∑ᶠ γ : ℤ, (if 0 ≤ γ then co γ.toNat else 0)
          • W.smul v (M0 - γ) (W.smul u γ b) := by
  rw [finsum_nat_to_int
      (fun s : ℕ => co s • W.smul v (M0 - s) (W.smul u (s : ℤ) b))
      (fun γ : ℤ => (if 0 ≤ γ then co γ.toNat else 0)
          • W.smul v (M0 - γ) (W.smul u γ b))
      (fun p hp => by simp only []; rw [if_neg (by omega), zero_smul])
      (fun j => by simp only [Int.toNat_natCast]; rw [if_pos (by omega)])]

/-- Finite support (in U-base-mode `γ`) of a per-`(i,j,p)` U-word γ-body. -/
theorem UgammaL_fin (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (co : ℕ → ℂ) (ℓ N : ℤ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      (if N ≤ γ then co (γ - N).toNat else 0) • W.smul u (ℓ + N - γ) (W.smul v γ b)) := by
  obtain ⟨Nv, hNv⟩ := W.regularity v b
  apply Set.Finite.subset (Set.finite_Icc N Nv)
  intro γ hγ
  rw [Function.mem_support] at hγ
  simp only [Set.mem_Icc]
  refine ⟨by by_contra h; exact hγ (by rw [if_neg (by omega), zero_smul]),
    by by_contra h; exact hγ (by rw [show W.smul v γ b = (0 : 𝒱) from hNv γ (by omega),
      PreVertexAlgebra.smul_zero_right, smul_zero])⟩

/-- Finite support (in V-base-mode `γ`) of a per-`(i,j,p)` V-word γ-body. -/
theorem VgammaL_fin (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (co : ℕ → ℂ) (M0 : ℤ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      (if 0 ≤ γ then co γ.toNat else 0) • W.smul v (M0 - γ) (W.smul u γ b)) := by
  obtain ⟨Nu, hNu⟩ := W.regularity u b
  apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) Nu)
  intro γ hγ
  rw [Function.mem_support] at hγ
  simp only [Set.mem_Icc]
  refine ⟨by by_contra h; exact hγ (by rw [if_neg (by omega), zero_smul]),
    by by_contra h; exact hγ (by rw [show W.smul u γ b = (0 : 𝒱) from hNu γ (by omega),
      PreVertexAlgebra.smul_zero_right, smul_zero])⟩

omit [Module ℂ 𝒱] in
/-- Finite support of a `Finset`-sum of finitely-supported `ℤ`-indexed families. -/
theorem hasFinSupp_finsetSumL {ι : Type} (s : Finset ι) (F : ι → ℤ → 𝒱)
    (hF : ∀ i ∈ s, Function.HasFiniteSupport (fun γ : ℤ => F i γ)) :
    Function.HasFiniteSupport (fun γ : ℤ => ∑ i ∈ s, F i γ) := by
  apply Set.Finite.subset (s.finite_toSet.biUnion (fun i hi => hF i (Finset.mem_coe.mp hi)))
  intro γ hγ
  rw [Function.mem_support] at hγ
  simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  apply hγ
  refine Finset.sum_eq_zero fun i hi => ?_
  have := hcon i hi
  rw [Function.mem_support, not_not] at this
  exact this

/-- The per-`(i,j,p)` LEFT U-side coefficient of `u₍ℓ+N-γ₎(v₍γ₎b)` (`ℓ = i-2`, `N = p-n-j-1`). -/
noncomputable def UgammaCoeffL (M P n : ℕ) (G : ℕ → ℕ) (i j p : ℕ) (γ : ℤ) : ℂ :=
  if (p : ℤ) - ((n : ℤ) + (j : ℤ) + 1) ≤ γ then
    assemblyLeadL M P n G i j p
      * ((-1 : ℂ) ^ ((γ - ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1))).toNat)
          * gBinom ((i : ℤ) - 2)
              (γ - ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1))).toNat)
  else 0

/-- The per-`(i,j,p)` U-word γ-body has finite support (`UgammaL_fin` specialised). -/
theorem UgammaCoeffL_body_fin (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ)
    (i j p : ℕ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      UgammaCoeffL M P n G i j p γ
        • W.smul u (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
            (W.smul v γ b)) :=
  UgammaL_fin W u v b
    (fun s => assemblyLeadL M P n G i j p
      * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2) s))
    ((i : ℤ) - 2) ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1))

/-- The per-`(i,j,p)` LEFT V-side coefficient of `v₍ℓ+N-γ₎(u₍γ₎b)` (`M₀ = ℓ+N = (i-2)+(p-n-j-1)`),
carrying the V-sign `(-1)^ℓ`. -/
noncomputable def VgammaCoeffL (M P n : ℕ) (G : ℕ → ℕ) (i j p : ℕ) (γ : ℤ) : ℂ :=
  if 0 ≤ γ then
    assemblyLeadL M P n G i j p
      * ((-1 : ℂ) ^ γ.toNat * gBinom ((i : ℤ) - 2) γ.toNat)
      * ((-1 : ℂ) ^ ((i : ℤ) - 2))
  else 0

/-- The per-`(i,j,p)` V-word γ-body has finite support (`VgammaL_fin` specialised). -/
theorem VgammaCoeffL_body_fin (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ)
    (i j p : ℕ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      VgammaCoeffL M P n G i j p γ
        • W.smul v (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
            (W.smul u γ b)) :=
  VgammaL_fin W u v b
    (fun s => assemblyLeadL M P n G i j p
      * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2) s)
      * ((-1 : ℂ) ^ ((i : ℤ) - 2)))
    (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)))

/-- **The LEFT U-side γ-outer mode-value form.** -/
theorem USideL_eq_gammaSum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ) :
    USideL W M P n u v b G
      = ∑ᶠ γ : ℤ, ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ p ∈ Finset.range (G i + n + 1),
            UgammaCoeffL M P n G i j p γ
              • W.smul u (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                  (W.smul v γ b) := by
  rw [USideL]
  rw [show (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ p ∈ Finset.range (G i + n + 1),
              ∑ᶠ s : ℕ,
                (assemblyLeadL M P n G i j p
                    * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2) s))
                  • W.smul u (((i : ℤ) - 2) - s)
                      (W.smul v ((p - ((n : ℤ) + (j : ℤ) + 1)) + s) b))
        = ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ p ∈ Finset.range (G i + n + 1),
              ∑ᶠ γ : ℤ, UgammaCoeffL M P n G i j p γ
                • W.smul u (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                    (W.smul v γ b) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun p _ => by
          rw [UwordL_reindex W u v b
            (fun s => assemblyLeadL M P n G i j p
              * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2) s))
            ((i : ℤ) - 2) ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1))]
          exact finsum_congr fun γ => by rw [UgammaCoeffL]]
  rw [finsum_sum_comm (Finset.range (M + 1))
      (fun γ i => ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (G i + n + 1),
        UgammaCoeffL M P n G i j p γ
          • W.smul u (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul v γ b))
      (fun i _ => hasFinSupp_finsetSumL (Finset.range (n + 1)) _ (fun j _ =>
        hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
          UgammaCoeffL_body_fin W M P n u v b G i j p)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_sum_comm (Finset.range (n + 1))
      (fun γ j => ∑ p ∈ Finset.range (G i + n + 1),
        UgammaCoeffL M P n G i j p γ
          • W.smul u (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul v γ b))
      (fun j _ => hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
        UgammaCoeffL_body_fin W M P n u v b G i j p))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finsum_sum_comm (Finset.range (G i + n + 1))
      (fun γ p => UgammaCoeffL M P n G i j p γ
          • W.smul u (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul v γ b))
      (fun p _ => UgammaCoeffL_body_fin W M P n u v b G i j p)]

/-- **The LEFT V-side γ-outer mode-value form.** -/
theorem VSideL_eq_gammaSum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ) :
    VSideL W M P n u v b G
      = ∑ᶠ γ : ℤ, ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ p ∈ Finset.range (G i + n + 1),
            VgammaCoeffL M P n G i j p γ
              • W.smul v (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                  (W.smul u γ b) := by
  rw [VSideL]
  rw [show (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ p ∈ Finset.range (G i + n + 1),
              ∑ᶠ s : ℕ,
                (assemblyLeadL M P n G i j p
                    * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2) s)
                    * ((-1 : ℂ) ^ ((i : ℤ) - 2)))
                  • W.smul v (((i : ℤ) - 2) + (p - ((n : ℤ) + (j : ℤ) + 1)) - s)
                      (W.smul u (s : ℤ) b))
        = ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ p ∈ Finset.range (G i + n + 1),
              ∑ᶠ γ : ℤ, VgammaCoeffL M P n G i j p γ
                • W.smul v (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                    (W.smul u γ b) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun p _ => by
          rw [VwordL_reindex W u v b
            (fun s => assemblyLeadL M P n G i j p
              * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2) s)
              * ((-1 : ℂ) ^ ((i : ℤ) - 2)))
            (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)))]
          exact finsum_congr fun γ => by rw [VgammaCoeffL]]
  rw [finsum_sum_comm (Finset.range (M + 1))
      (fun γ i => ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (G i + n + 1),
        VgammaCoeffL M P n G i j p γ
          • W.smul v (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul u γ b))
      (fun i _ => hasFinSupp_finsetSumL (Finset.range (n + 1)) _ (fun j _ =>
        hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
          VgammaCoeffL_body_fin W M P n u v b G i j p)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_sum_comm (Finset.range (n + 1))
      (fun γ j => ∑ p ∈ Finset.range (G i + n + 1),
        VgammaCoeffL M P n G i j p γ
          • W.smul v (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul u γ b))
      (fun j _ => hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
        VgammaCoeffL_body_fin W M P n u v b G i j p))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finsum_sum_comm (Finset.range (G i + n + 1))
      (fun γ p => VgammaCoeffL M P n G i j p γ
          • W.smul v (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul u γ b))
      (fun p _ => VgammaCoeffL_body_fin W M P n u v b G i j p)]

/-! ## Step 4 — the per-`γ` mode collection and the double-finsum forms. -/

/-- The net per-`(γ,μ)` LEFT U-side scalar (LEFT lift of `UgammaModeColl`): the finite `(i,j,p)`-sum
of `UgammaCoeffL` whose mode value `(i-2)+(p-n-j-1)-γ` equals `μ`. -/
noncomputable def UgammaModeCollL (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ p ∈ Finset.range (G i + n + 1),
      (if μ = ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
        then UgammaCoeffL M P n G i j p γ else 0)

/-- The net per-`(γ,μ)` LEFT V-side scalar (LEFT lift of `VgammaModeColl`). -/
noncomputable def VgammaModeCollL (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ p ∈ Finset.range (G i + n + 1),
      (if μ = ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
        then VgammaCoeffL M P n G i j p γ else 0)

/-- A single U-word `x • u₍μ₀₎(v₍γ₎b)` is the one-point mode-finsum. -/
theorem usingleL_eq_muFinsum (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (x : ℂ) (μ0 γ : ℤ) :
    x • W.smul u μ0 (W.smul v γ b)
      = ∑ᶠ μ : ℤ, (if μ = μ0 then x else 0) • W.smul u μ (W.smul v γ b) := by
  rw [finsum_eq_single (fun μ : ℤ => (if μ = μ0 then x else 0) • W.smul u μ (W.smul v γ b)) μ0
    (fun μ hμ => by simp only []; rw [if_neg hμ, zero_smul])]
  simp only [if_pos]

/-- A single V-word `x • v₍μ₀₎(u₍γ₎b)` is the one-point mode-finsum. -/
theorem vsingleL_eq_muFinsum (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (x : ℂ) (μ0 γ : ℤ) :
    x • W.smul v μ0 (W.smul u γ b)
      = ∑ᶠ μ : ℤ, (if μ = μ0 then x else 0) • W.smul v μ (W.smul u γ b) := by
  rw [finsum_eq_single (fun μ : ℤ => (if μ = μ0 then x else 0) • W.smul v μ (W.smul u γ b)) μ0
    (fun μ hμ => by simp only []; rw [if_neg hμ, zero_smul])]
  simp only [if_pos]

/-- The one-point U-mode indicator family has finite (singleton) support. -/
theorem umuL_indicator_fin (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (x : ℂ) (μ0 γ : ℤ) :
    Function.HasFiniteSupport
      (fun μ : ℤ => (if μ = μ0 then x else 0) • W.smul u μ (W.smul v γ b)) := by
  apply Set.Finite.subset (Set.finite_singleton μ0)
  intro μ hμ
  rw [Function.mem_support] at hμ
  simp only [Set.mem_singleton_iff]
  by_contra h; exact hμ (by rw [if_neg h, zero_smul])

/-- The one-point V-mode indicator family has finite (singleton) support. -/
theorem vmuL_indicator_fin (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (x : ℂ) (μ0 γ : ℤ) :
    Function.HasFiniteSupport
      (fun μ : ℤ => (if μ = μ0 then x else 0) • W.smul v μ (W.smul u γ b)) := by
  apply Set.Finite.subset (Set.finite_singleton μ0)
  intro μ hμ
  rw [Function.mem_support] at hμ
  simp only [Set.mem_singleton_iff]
  by_contra h; exact hμ (by rw [if_neg h, zero_smul])

/-- **Per-`γ` LEFT U-side mode collection** (LEFT lift of `gammaBody_eq_muSum_U`). -/
theorem gammaBodyL_eq_muSum_U (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ)
    (γ : ℤ) :
    (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
        ∑ p ∈ Finset.range (G i + n + 1),
          UgammaCoeffL M P n G i j p γ
            • W.smul u (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                (W.smul v γ b))
      = ∑ᶠ μ : ℤ, UgammaModeCollL M P n G γ μ • W.smul u μ (W.smul v γ b) := by
  rw [show (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ p ∈ Finset.range (G i + n + 1),
              UgammaCoeffL M P n G i j p γ
                • W.smul u (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                    (W.smul v γ b))
        = ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ μ : ℤ, ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then UgammaCoeffL M P n G i j p γ else 0)
                  • W.smul u μ (W.smul v γ b) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [show (∑ p ∈ Finset.range (G i + n + 1),
                  UgammaCoeffL M P n G i j p γ
                    • W.smul u (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                        (W.smul v γ b))
              = ∑ p ∈ Finset.range (G i + n + 1),
                  ∑ᶠ μ : ℤ, (if μ = ((i : ℤ) - 2)
                        + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                      then UgammaCoeffL M P n G i j p γ else 0) • W.smul u μ (W.smul v γ b) from
            Finset.sum_congr rfl fun p _ =>
              usingleL_eq_muFinsum W u v b (UgammaCoeffL M P n G i j p γ)
                (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ) γ]
        rw [← finsum_sum_comm (Finset.range (G i + n + 1))
            (fun μ p => (if μ = ((i : ℤ) - 2)
                  + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                then UgammaCoeffL M P n G i j p γ else 0) • W.smul u μ (W.smul v γ b))
            (fun p _ => umuL_indicator_fin W u v b (UgammaCoeffL M P n G i j p γ) _ γ)]]
  rw [show (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ μ : ℤ, ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then UgammaCoeffL M P n G i j p γ else 0) • W.smul u μ (W.smul v γ b))
        = ∑ i ∈ Finset.range (M + 1),
            ∑ᶠ μ : ℤ, ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then UgammaCoeffL M P n G i j p γ else 0) • W.smul u μ (W.smul v γ b) from
      Finset.sum_congr rfl fun i _ => by
        rw [← finsum_sum_comm (Finset.range (n + 1))
            (fun μ j => ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then UgammaCoeffL M P n G i j p γ else 0) • W.smul u μ (W.smul v γ b))
            (fun j _ => hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
              umuL_indicator_fin W u v b (UgammaCoeffL M P n G i j p γ) _ γ))]]
  rw [← finsum_sum_comm (Finset.range (M + 1))
      (fun μ i => ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (G i + n + 1),
          (if μ = ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
            then UgammaCoeffL M P n G i j p γ else 0) • W.smul u μ (W.smul v γ b))
      (fun i _ => hasFinSupp_finsetSumL (Finset.range (n + 1)) _ (fun j _ =>
        hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
          umuL_indicator_fin W u v b (UgammaCoeffL M P n G i j p γ) _ γ)))]
  refine finsum_congr fun μ => ?_
  rw [UgammaModeCollL, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul]

/-- **Per-`γ` LEFT V-side mode collection** (the V mirror). -/
theorem gammaBodyL_eq_muSum_V (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ)
    (γ : ℤ) :
    (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
        ∑ p ∈ Finset.range (G i + n + 1),
          VgammaCoeffL M P n G i j p γ
            • W.smul v (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                (W.smul u γ b))
      = ∑ᶠ μ : ℤ, VgammaModeCollL M P n G γ μ • W.smul v μ (W.smul u γ b) := by
  rw [show (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ p ∈ Finset.range (G i + n + 1),
              VgammaCoeffL M P n G i j p γ
                • W.smul v (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                    (W.smul u γ b))
        = ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ μ : ℤ, ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then VgammaCoeffL M P n G i j p γ else 0)
                  • W.smul v μ (W.smul u γ b) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [show (∑ p ∈ Finset.range (G i + n + 1),
                  VgammaCoeffL M P n G i j p γ
                    • W.smul v (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                        (W.smul u γ b))
              = ∑ p ∈ Finset.range (G i + n + 1),
                  ∑ᶠ μ : ℤ, (if μ = ((i : ℤ) - 2)
                        + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                      then VgammaCoeffL M P n G i j p γ else 0) • W.smul v μ (W.smul u γ b) from
            Finset.sum_congr rfl fun p _ =>
              vsingleL_eq_muFinsum W u v b (VgammaCoeffL M P n G i j p γ)
                (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ) γ]
        rw [← finsum_sum_comm (Finset.range (G i + n + 1))
            (fun μ p => (if μ = ((i : ℤ) - 2)
                  + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                then VgammaCoeffL M P n G i j p γ else 0) • W.smul v μ (W.smul u γ b))
            (fun p _ => vmuL_indicator_fin W u v b (VgammaCoeffL M P n G i j p γ) _ γ)]]
  rw [show (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ μ : ℤ, ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then VgammaCoeffL M P n G i j p γ else 0) • W.smul v μ (W.smul u γ b))
        = ∑ i ∈ Finset.range (M + 1),
            ∑ᶠ μ : ℤ, ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then VgammaCoeffL M P n G i j p γ else 0) • W.smul v μ (W.smul u γ b) from
      Finset.sum_congr rfl fun i _ => by
        rw [← finsum_sum_comm (Finset.range (n + 1))
            (fun μ j => ∑ p ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then VgammaCoeffL M P n G i j p γ else 0) • W.smul v μ (W.smul u γ b))
            (fun j _ => hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
              vmuL_indicator_fin W u v b (VgammaCoeffL M P n G i j p γ) _ γ))]]
  rw [← finsum_sum_comm (Finset.range (M + 1))
      (fun μ i => ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (G i + n + 1),
          (if μ = ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
            then VgammaCoeffL M P n G i j p γ else 0) • W.smul v μ (W.smul u γ b))
      (fun i _ => hasFinSupp_finsetSumL (Finset.range (n + 1)) _ (fun j _ =>
        hasFinSupp_finsetSumL (Finset.range (G i + n + 1)) _ (fun p _ =>
          vmuL_indicator_fin W u v b (VgammaCoeffL M P n G i j p γ) _ γ)))]
  refine finsum_congr fun μ => ?_
  rw [VgammaModeCollL, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul]

/-- **`USideL` as a base-mode ⊗ mode double finsum.** -/
theorem USideL_eq_gammaModeFinsum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱)
    (G : ℕ → ℕ) :
    USideL W M P n u v b G
      = ∑ᶠ γ : ℤ, ∑ᶠ μ : ℤ, UgammaModeCollL M P n G γ μ • W.smul u μ (W.smul v γ b) := by
  rw [USideL_eq_gammaSum]
  exact finsum_congr fun γ => gammaBodyL_eq_muSum_U W M P n u v b G γ

/-- **`VSideL` as a base-mode ⊗ mode double finsum.** -/
theorem VSideL_eq_gammaModeFinsum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱)
    (G : ℕ → ℕ) :
    VSideL W M P n u v b G
      = ∑ᶠ γ : ℤ, ∑ᶠ μ : ℤ, VgammaModeCollL M P n G γ μ • W.smul v μ (W.smul u γ b) := by
  rw [VSideL_eq_gammaSum]
  exact finsum_congr fun γ => gammaBodyL_eq_muSum_V W M P n u v b G γ

/-! ## Step 5 — the LEFT tower-decomposition predicate and the membership criterion.

The LEFT depth-`0` analog of `RightCircTowerEq` (`ZhuVermaAnDescent8`) and `RightCircTowerEq_of_sides`
(`ZhuVermaAnDescent10`).  The U-words of `USideL` are `u₍μ₎(v₍γ₎b)` — exactly the body of
`UfamOn W M n u v b` (`PresOn W M n δ u (v₍γ₎b)`) — and the V-words of `VSideL` are `v₍μ₎(u₍γ₎b)` —
exactly `VfamOn W P n u v b` (`PresOn W P n δ v (u₍γ₎b)`).  So the existing membership engine
`UfamOn_mem_On`/`VfamOn_mem_On` (`ZhuVermaAnDescent8`, via the keystone `Pres_mem_On`) carries the
tower decomposition into `On W n` directly. -/

/-- **The LEFT circle-`0` tower-decomposition predicate**: `leftProd W n (circ W 0 u v) b` equals a
`UfamOn` (towers in `u` based at `v₍γ₎b`) plus a `VfamOn` (towers in `v` based at `u₍γ₎b`).  LEFT lift
of `RightCircTowerEq`. -/
def LeftCircTowerEq (W : VertexOperatorAlgebra 𝒱) (n M P : ℕ) (u v b : 𝒱) : Prop :=
  ∃ (wU wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ),
    leftProd W n (circ W 0 u v) b
      = UfamOn W M n u v b wU γ₀ Γ Δ + VfamOn W P n u v b wV γ₀ Γ Δ

/-- **The LEFT tower-collapse membership criterion.**  For homogeneous `u ∈ 𝒱_M`, `v ∈ 𝒱_P`, if
`leftProd W n (circ W 0 u v) b` collapses onto the U/V `PresOn`-tower families (`LeftCircTowerEq`),
then it lies in `On W n`.  LEFT lift of `rightProd_circ_mem_On_of_tower_eq`; the membership is closed
by the keystone `Pres_mem_On` (via `UfamOn_mem_On`/`VfamOn_mem_On`). -/
theorem leftProd_circ0_mem_On_of_tower_eq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (b : 𝒱)
    (htow : LeftCircTowerEq W n M P u v b) :
    leftProd W n (circ W 0 u v) b ∈ On W n := by
  obtain ⟨wU, wV, γ₀, Γ, Δ, heq⟩ := htow
  rw [heq]
  exact Submodule.add_mem _ (UfamOn_mem_On W n hu v b wU γ₀ Γ Δ)
    (VfamOn_mem_On W n hv u b wV γ₀ Γ Δ)

/-- **`LeftCircTowerEq` from the U-side / V-side tower-collapse.**  If, for some grade witness `G`
matching the inner circle grades, `USideL` equals the U-family `UfamOn W M n u v b wU …` and `VSideL`
equals the *negated* V-family `−VfamOn W P n u v b wV …`, then `LeftCircTowerEq W n M P u v b` holds
(via the master split `leftProd_circ0_eq_USideL_sub_VSideL`).  LEFT lift of
`RightCircTowerEq_of_sides`. -/
theorem LeftCircTowerEq_of_sides (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (b : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2) - 1)
    (wU wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ)
    (hU : USideL W M P n u v b G = UfamOn W M n u v b wU γ₀ Γ Δ)
    (hV : VSideL W M P n u v b G = -VfamOn W P n u v b wV γ₀ Γ Δ) :
    LeftCircTowerEq W n M P u v b := by
  refine ⟨wU, wV, γ₀, Γ, Δ, ?_⟩
  rw [leftProd_circ0_eq_USideL_sub_VSideL W n hu hv b G hG, hU, hV, sub_neg_eq_add]

/-! ## The full conditional discharge of (L-circ0) from `LeftCircTowerEq`.

Supplying `LeftCircTowerEq` for ALL grades `M, P` and homogeneous `u, v` discharges (L-circ0), hence
(via `leftProd_genL_mem_On_of_circ0` / `LeftGenTowerEq_holds_of_circ0`, `ZhuVermaAnDescent22`) the
full left `gen_mem` predicate `LeftGenTowerEq_holds`. -/

/-- **(L-circ0) from the universally-quantified `LeftCircTowerEq`.** -/
theorem leftProd_circ0_mem_On_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P : ℕ), ∀ u ∈ W.grading (M : ℤ), ∀ v ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      LeftCircTowerEq W n M P u v b) :
    ∀ M P : ℕ, ∀ u ∈ W.grading (M : ℤ), ∀ v ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      leftProd W n (circ W 0 u v) b ∈ On W n := by
  intro M P u hu v hv b
  exact leftProd_circ0_mem_On_of_tower_eq W n hu hv b (Htow M P u hu v hv b)

/-- **Left `gen_mem` from the universally-quantified `LeftCircTowerEq`.**  Chains
`leftProd_circ0_mem_On_of_towerEq` through the proved `leftProd_genL_mem_On_of_circ0`
(`ZhuVermaAnDescent22`). -/
theorem leftProd_genL_mem_On_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P : ℕ), ∀ u ∈ W.grading (M : ℤ), ∀ v ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      LeftCircTowerEq W n M P u v b) :
    ∀ u v b : 𝒱, leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ On W n :=
  leftProd_genL_mem_On_of_circ0 W n (leftProd_circ0_mem_On_of_towerEq W n Htow)

/-- **`LeftGenTowerEq_holds` from the universally-quantified `LeftCircTowerEq`.** -/
theorem LeftGenTowerEq_holds_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P : ℕ), ∀ u ∈ W.grading (M : ℤ), ∀ v ∈ W.grading (P : ℤ), ∀ b : 𝒱,
      LeftCircTowerEq W n M P u v b)
    (u v b : 𝒱) : LeftGenTowerEq W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b :=
  LeftGenTowerEq_holds_of_circ0 W n (leftProd_circ0_mem_On_of_towerEq W n Htow) u v b

/-!
## State of (L-circ0): the PRECISE remaining target (NOT `sorry`, NOT axiomatized).

Everything above is axiom-clean (`[propext, Classical.choice, Quot.sound]`).  (L-circ0) is
reduced to the single tower-decomposition predicate

  **`LeftCircTowerEq W n M P u v b`** : `leftProd W n (circ W 0 u v) b = UfamOn W M n u v b wU … +
  VfamOn W P n u v b wV …`  (`∃ wU wV γ₀ Γ Δ`),

via `leftProd_circ0_mem_On_of_towerEq` (and thence the full left `gen_mem` via
`leftProd_genL_mem_On_of_towerEq` / `LeftGenTowerEq_holds_of_towerEq`, routed through the proved
`ZhuVermaAnDescent22`).  The proved **LEFT master split** + γ-outer mode-value forms put both sides in
the exact `∑ᶠ γ, ∑ᶠ μ, (scalar) • word` shape that `UfamOn_eq_finsum`/`VfamOn_eq_finsum`
(`ZhuVermaAnDescent9`) consume:

  `USideL_eq_gammaModeFinsum` : `USideL = ∑ᶠ γ ∑ᶠ μ, UgammaModeCollL M P n G γ μ • u₍μ₎(v₍γ₎b)`,
  `VSideL_eq_gammaModeFinsum` : `VSideL = ∑ᶠ γ ∑ᶠ μ, VgammaModeCollL M P n G γ μ • v₍μ₎(u₍γ₎b)`,
  `leftProd_circ0_eq_USideL_sub_VSideL` : `leftProd W n (circ W 0 u v) b = USideL − VSideL`.

### The Mathematica-verified scalar structure (exact `Solve`; `n = 0,1,2`, `M,P ≤ 5`, all contributing `γ`)

* **U-side** `UgammaModeCollL M P n G γ μ` is, for each fixed `γ`, a **grade-`M` tower with the
  depth-`0`-circle shift `2`** (NOT the depth-`n` `PresOn` shift `2n+2`), with `M`-independent weights
  `wU(n,P,γ,δ)`:
      `UgammaModeCollL = ∑_δ wU(n,P,γ,δ) · cbz(M+n+δ, μ+2+δ)`.
  Verified weights e.g. `n=1,P=1`: `wU(γ=0)=(0,-9,17,-8)`, `wU(γ=1)=(0,9,-29,30,-10)`;
  `n=2,P=1`: `wU(γ=0)=(0,40,-155,226,-147,36)`.

* **V-side** `VgammaModeCollL M P n G γ μ` is, for each fixed `γ`, a **grade-`P` tower with shift `2`**
  with `P`-independent (but `M`-DEPENDENT, linear at `γ=1`, …) weights `wV(n,M,P,γ,δ)`:
      `VgammaModeCollL = ∑_δ wV(n,M,P,γ,δ) · cbz(P+n+δ, μ+2+δ)`.

### THE OBSTRUCTION and the precise remaining stage (the genuine `n ≥ 1` content)

A depth-`n` `PresOn W M n δ u (v₍γ₎b)` tower has `u₍μ₎(v₍γ₎b)`-coefficient `cbz(M+n+δ, μ+2n+2+δ)`
(shift `2n+2`) — `UfamOn_eq_finsum` / `towerCoeff M n (wU γ) Δ`.  But the U-side has shift `2`.
**For `n = 0`, `2 = 2n+2`**, so `UgammaModeCollL`/`VgammaModeCollL` ARE genuine `PresOn` towers
(`towerCoeff … `), `LeftCircTowerEq_of_sides` applies, and (L-circ0) closes via this chain (consistent
with `On W 0 = O W`).  **For `n ≥ 1`, `2 ≠ 2n+2`**, so neither side is a `PresOn` tower individually
(exact-`Solve` confirms `USideL = UfamOn` / `VSideL = −VfamOn` are FALSE per-side) — the shift-`2`
"pole-2 overshoot" is the obstruction.

The single remaining input is therefore the **depth-`n` cross-assembly identity** (the depth-`n` LEFT
lift of `ZhuMu.mu_identity`): the shift-`2` U-tower and shift-`2` V-tower recombine — via the
Borcherds commutator `v₍μ₎(u₍γ₎b) = u₍γ₎(v₍μ₎b) + ∑_{k≥0} cbz(μ,k)·(v₍k₎u)₍μ+γ-k₎b`
(`mode_split_gen`, `ZhuVermaAnDescent4`) — into genuine **shift-`2n+2`** `PresOn` towers
(`UfamOn`/`VfamOn`, both `∈ On W n` by `Pres_mem_On`) plus a `(v₍k₎u)`-circle commutator family (the
analog of `leftProd_circ_commutator_family_mem_On`, `ZhuVermaAnDescent4`, also `∈ On W n`).  The naive
mode-transpose alone does NOT suffice (exact-`Solve` checked); the `(v₍k₎u)`-residue terms carry the
genuine combinatorial content (the depth-`n` `cbz` identity converting pole-`2` → pole-`2n+2`, the
left analog of the right-side `UgammaModeColl_eq_towerCoeff`/`VgammaModeColl_eq_towerCoeff`,
`ZhuVermaAnDescent19`/`20`, via `ZhuRes.gen_vandermonde`/`gen_jsum`).  Formalising that one identity
discharges `LeftCircTowerEq` (hence (L-circ0)) for all `n`.
-/

end VOA
