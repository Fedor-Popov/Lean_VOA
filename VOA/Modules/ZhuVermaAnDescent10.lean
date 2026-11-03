/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent9

/-!
# The depth-`n` iterate-reindexing chain toward `RightCircTowerEq_holds`.

This file continues `Modules.ZhuVermaAnDescent9` (the `UfamOn`/`VfamOn` mode-value finsum forms
`UfamOn_eq_finsum`/`VfamOn_eq_finsum`, the per-base-mode tower collapse `presOnFamily_eq_finsum`,
and `towerCoeff`).  It builds the depth-`n` lift of the `n = 0` associator reindexing apparatus
`ZhuAssociator.USide_eq`/`VSide_eq` (the finsum-swap bookkeeping that turns the raw `(i,j,r,s)`
assembly into the U/V mode-value finsum forms), routed from the proved split
`rightProd_circ_UV_assembly` (`ZhuVermaAnDescent7`).

## The reduction state and the route

`rightProd_circ_UV_assembly` (proved, `ZhuVermaAnDescent7`) expresses
`rightProd W n (circ W n c d) a` as a finite `(i, j, r)`-sum whose body, for the contributing
indices `i` (those with `0 ≤ M+P-(i-2n-2)-1`), is `∑ᶠ s, coef_s • (Uterm − Vterm)` with

* **U-term** `c₍(i-2n-2)-s₎(d₍(r-n-j-1)+s₎a)` — a `c`-mode acting on a `d`-base-mode `d₍γ₎a`, where
  the U base-mode is `γ = (r-n-j-1)+s` and the U mode is `μ = (i-2n-2)-s`;
* **V-term** `d₍(i-2n-2)+(r-n-j-1)-s₎(c₍s₎a)` — a `d`-mode acting on a `c`-base-mode `c₍s₎a`, where
  the V base-mode is `γ = s` (`s : ℕ`, so `≥ 0`) and the V mode is
  `μ = (i-2n-2)+(r-n-j-1)-s`;

with the `mode_iterate` coefficient `coef_s = (-1)^s · gBinom (i-2n-2) s`, and the leading scalar
`cbz(M+n,i) · (-1)^j cbz(j+n,j) · cbz(G_i+j, r)`.

The depth-`n` lift of `ZhuAssociator.USide_eq`/`VSide_eq` is the **finsum-swap regrouping**: pull the
`∑ᶠ s`-finsum (the `mode_iterate` index, finite by `W.regularity`) past the finite `(i,j,r)`-sum and
collect, for each U base-mode `γ` and mode `μ`, the net scalar coefficient (the depth-`n`
`uSideScalar`/`vSideScalar`) of `c₍μ₎(d₍γ₎a)` resp. `d₍μ₎(c₍γ₎a)`.  This file proves that
regrouping infrastructure — the U-side and V-side as `∑ᶠ`-mode-value forms — exactly the input the
final `RightCircTowerEq_holds` consumes once the depth-`n` scalar tower-collapse cores
(`u_core`/`v_core` lifts, the dual-Hahn tower weights `wU`/`wV`) are supplied.

## Mathematica-verified (exact `Solve`, `n = 1,2`, `M,P ≤ 3`)

The U/V split is TRUE and both families collapse onto `PresOn`-towers (per the recorded findings of
`ZhuVermaAnDescent6/7/8/9`): for each fixed U base-mode `γ` the net `uSideScalar`-coefficient of
`c₍μ₎(d₍γ₎a)` is a finite ℂ-combination of `cbz(M+n+δ, μ+2n+2+δ)` (a `towerCoeff M n (wU γ) Δ`), and
for each fixed V base-mode `γ = s ≥ 0` the net `vSideScalar`-coefficient of `d₍μ₎(c₍γ₎a)` is a finite
ℂ-combination of `cbz(P+n+δ, μ+2n+2+δ)` (a `towerCoeff P n (wV γ) Δ`).  So `RightCircTowerEq` is TRUE
for all arguments; the existential weights need NOT be computed in closed form — only the reindexing
(this file) plus the per-base-mode tower-collapse cores are required.

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

/-! ## The depth-`n` U-side and V-side of `rightProd W n (circ W n c d) a`.

Mirroring `ZhuAssociator.USide`/`VSide`, we package the U-modes `c₍μ₎(d₍γ₎a)` and the V-modes
`d₍μ₎(c₍γ₎a)` of the proved split `rightProd_circ_UV_assembly` (`ZhuVermaAnDescent7`) as separate
finite `(i,j,r)`-sums with an inner `∑ᶠ s`-finsum (the `mode_iterate` peeling index, finite by
`W.regularity`).  The leading per-`(i,j,r)` scalar
`L i j r := cbz(M+n,i) · (-1)^j cbz(j+n,j) · cbz(G_i+j, r)` is shared; the U-side carries the
`mode_iterate` coefficient `(-1)^s gBinom (i-2n-2) s` on the U-word, and the V-side the same with the
extra `(-1)^(i-2n-2)` sign on the V-word. -/

/-- The per-`(i,j,r)` leading scalar of the assembly body (shared by U-side and V-side), guarded by
the `if` that kills the negative-inner-grade circle indices `i`. -/
noncomputable def assemblyLead (M P n : ℕ) (G : ℕ → ℕ) (i j r : ℕ) : ℂ :=
  if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 then
    cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ))
      * cbz ((G i : ℤ) + j) (r : ℤ)
  else 0

/-- The depth-`n` **U-side**: all `c₍(i-2n-2)-s₎(d₍(r-n-j-1)+s₎a)` terms.  The base-mode is
`γ = (r-n-j-1)+s`, the mode `μ = (i-2n-2)-s`; the `mode_iterate` coefficient is
`(-1)^s · gBinom (i-2n-2) s`. -/
noncomputable def USideR (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱) (G : ℕ → ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ r ∈ Finset.range (G i + n + 1),
      ∑ᶠ s : ℕ,
        (assemblyLead M P n G i j r * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s))
          • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) - s)
              (W.smul d ((r - ((n : ℤ) + (j : ℤ) + 1)) + s) a)

/-- The depth-`n` **V-side**: all `d₍(i-2n-2)+(r-n-j-1)-s₎(c₍s₎a)` terms (carrying the sign
`(-1)^(i-2n-2)`).  The base-mode is `γ = s` (`s : ℕ`, so `≥ 0`), the mode
`μ = (i-2n-2)+(r-n-j-1)-s`. -/
noncomputable def VSideR (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱) (G : ℕ → ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ r ∈ Finset.range (G i + n + 1),
      ∑ᶠ s : ℕ,
        (assemblyLead M P n G i j r * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s)
            * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2)))
          • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + (r - ((n : ℤ) + (j : ℤ) + 1)) - s)
              (W.smul c (s : ℤ) a)

/-! ## Finite support of the per-`(i,j,r)` U/V `mode_iterate` `s`-finsums.

The U-word `c₍(i-2n-2)-s₎(d₍(r-n-j-1)+s₎a)` vanishes for large `s` because `d₍(r-n-j-1)+s₎a = 0`
once `(r-n-j-1)+s ≥ N_d` (`W.regularity d a`); the V-word `d₍…₎(c₍s₎a)` vanishes once `c₍s₎a = 0`
(`W.regularity c a`).  These bound the supports, so the `∑ᶠ s` are honest finite sums and may be
swapped past the finite `(i,j,r)`-sum and split across the `Uword − Vword` subtraction. -/

/-- The U-word `s`-finsum (per `(i,j,r)`, arbitrary `s`-coefficient `co`) has finite support: the
U-word `c₍ℓ-s₎(d₍N+s₎a)` vanishes once `N+s ≥ N_d` (`W.regularity d a`). -/
theorem USideR_s_fin (W : VertexOperatorAlgebra 𝒱) (c d a : 𝒱) (co : ℕ → ℂ) (ℓ N : ℤ) :
    Function.HasFiniteSupport (fun s : ℕ =>
      co s • W.smul c (ℓ - s) (W.smul d (N + s) a)) := by
  obtain ⟨Nd, hNd⟩ := W.regularity d a
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) (Nd - N).toNat)
  intro s hs
  rw [Function.mem_support] at hs
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hs
  have hNle : (Nd - N) ≤ ((Nd - N).toNat : ℤ) := Int.self_le_toNat _
  have hs' : ((Nd - N).toNat : ℤ) + 1 ≤ (s : ℤ) := by
    exact_mod_cast (by omega : (Nd - N).toNat + 1 ≤ s)
  rw [show W.smul d (N + (s : ℤ)) a = (0 : 𝒱) from hNd _ (by omega)]
  rw [PreVertexAlgebra.smul_zero_right, smul_zero]

/-- The V-word `s`-finsum (per `(i,j,r)`, arbitrary `s`-coefficient `co`) has finite support: the
V-word `d₍μ-s₎(c₍s₎a)` vanishes once `s ≥ N_c` (`W.regularity c a`). -/
theorem VSideR_s_fin (W : VertexOperatorAlgebra 𝒱) (c d a : 𝒱) (co : ℕ → ℂ) (μ : ℤ) :
    Function.HasFiniteSupport (fun s : ℕ =>
      co s • W.smul d (μ - s) (W.smul c (s : ℤ) a)) := by
  obtain ⟨Nc, hNc⟩ := W.regularity c a
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) Nc.toNat)
  intro s hs
  rw [Function.mem_support] at hs
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hs
  have hNle : Nc ≤ (Nc.toNat : ℤ) := Int.self_le_toNat _
  have hs' : (Nc.toNat : ℤ) + 1 ≤ (s : ℤ) := by exact_mod_cast (by omega : Nc.toNat + 1 ≤ s)
  rw [show W.smul c (s : ℤ) a = (0 : 𝒱) from hNc _ (by omega)]
  rw [PreVertexAlgebra.smul_zero_right, smul_zero]

/-! ## The master split `rightProd W n (circ W n c d) a = USideR − VSideR`.

The depth-`n` lift of `ZhuAssociator.lhs_split` (`(u*v)*w = USide − VSide`).  Starting from the proved
assembly `rightProd_circ_UV_assembly` (`ZhuVermaAnDescent7`), pull the leading per-`(i,j,r)` scalars
into the `∑ᶠ s`-finsum, then split each finsum body `coef_s • (Uword − sv·Vword)` into the U-part and
the V-part (`smul_finsum'` + `finsum_sub_distrib`, valid by `USideR_s_fin`/`VSideR_s_fin`).  The
negative-inner-grade circle indices `i` (where the `if` guard is `false`) contribute `0` on both
sides through the `assemblyLead` `if`. -/
theorem rightProd_circ_eq_USideR_sub_VSideR (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ}
    {c d : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (a : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + n + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) :
    rightProd W n (circ W n c d) a = USideR W M P n c d a G - VSideR W M P n c d a G := by
  rw [rightProd_circ_UV_assembly W n hc hd a G hG, USideR, VSideR, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  -- Push `cbz (M+n) i` inside the `if`, then split the `if` into the contributing/zero cases.
  rcases lt_or_ge ((M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) 0 with hlt | hge
  · -- guard false: both sides are `0`.
    rw [if_neg (not_le.mpr hlt), smul_zero]
    simp only [assemblyLead, if_neg (not_le.mpr hlt), zero_mul, zero_smul,
      finsum_zero, Finset.sum_const_zero]
    rw [sub_zero]
  · -- guard true: distribute and split per `(j,r)`.
    rw [if_pos hge, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    -- the per-`(i,j,r)` finsum split.
    set ℓ : ℤ := (i : ℤ) - 2 * (n : ℤ) - 2 with hℓ
    set N : ℤ := (r : ℤ) - ((n : ℤ) + (j : ℤ) + 1) with hN
    set lead : ℂ := assemblyLead M P n G i j r with hlead
    have hlead_val : assemblyLead M P n G i j r
        = cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ))
            * cbz ((G i : ℤ) + j) (r : ℤ) := by
      rw [assemblyLead, if_pos hge]
    -- LHS body: `(cbz(M+n,i)·scalar_j) • cbz(G_i+j,r) • ∑ᶠ s, coef_s • (Uword - sv•Vword)`.
    -- collapse the two leading `•` into the single scalar `lead`, then push it into the finsum.
    rw [show (cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ)))
            • (cbz ((G i : ℤ) + j) (r : ℤ)
                • ∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ℓ s) •
                    (W.smul c (ℓ - s) (W.smul d (N + s) a)
                      - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) a)))
          = lead • ∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ℓ s) •
                (W.smul c (ℓ - s) (W.smul d (N + s) a)
                  - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) a)) from by
        rw [smul_smul, hlead, hlead_val, mul_assoc]]
    -- push `lead` inside; combined coefficient on each summand is `lead·coef_s`.
    have hfin_body : Function.HasFiniteSupport (fun s : ℕ =>
        ((-1 : ℂ) ^ s * gBinom ℓ s) •
          (W.smul c (ℓ - s) (W.smul d (N + s) a)
            - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) a))) := by
      obtain ⟨Nd, hNd⟩ := W.regularity d a
      obtain ⟨Nc, hNc⟩ := W.regularity c a
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
      rw [show W.smul d (N + (s : ℤ)) a = (0 : 𝒱) from hNd _ (by omega),
        show W.smul c (s : ℤ) a = (0 : 𝒱) from hNc _ (by omega)]
      simp only [PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero]
    rw [smul_finsum' lead hfin_body]
    -- each finsum body: `lead • coef_s • (Uword - sv•Vword) = (lead·coef_s)•Uword - (lead·coef_s·sv)•Vword`.
    rw [show (∑ᶠ s : ℕ, lead • ((-1 : ℂ) ^ s * gBinom ℓ s) •
              (W.smul c (ℓ - s) (W.smul d (N + s) a)
                - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) a)))
          = ∑ᶠ s : ℕ, ((lead * ((-1 : ℂ) ^ s * gBinom ℓ s)) • W.smul c (ℓ - s) (W.smul d (N + s) a)
              - (lead * ((-1 : ℂ) ^ s * gBinom ℓ s) * ((-1 : ℂ) ^ ℓ))
                  • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) a)) from
        finsum_congr fun s => by
          rw [smul_smul, smul_sub, smul_smul, mul_assoc]]
    rw [finsum_sub_distrib
        (USideR_s_fin W c d a (fun s => lead * ((-1 : ℂ) ^ s * gBinom ℓ s)) ℓ N)
        (VSideR_s_fin W c d a
          (fun s => lead * ((-1 : ℂ) ^ s * gBinom ℓ s) * ((-1 : ℂ) ^ ℓ)) (ℓ + N))]

/-! ## The `RightCircTowerEq` criterion via the U-side / V-side tower-collapse.

The master split `rightProd_circ_eq_USideR_sub_VSideR` reduces `RightCircTowerEq W n M P c d a` to
the **two tower-collapse equalities**: that the (Mathematica-verified) U-side `USideR` collapses onto
the U-family `UfamOn` and `−VSideR` onto the V-family `VfamOn` for some finite tower weights
`wU, wV : ℤ → ℕ → ℂ` and ranges `γ₀, Γ, Δ`.  We record that reduction as a clean criterion
(`RightCircTowerEq_of_sides`), isolating the remaining work to the two side-collapses (the depth-`n`
lifts of `ZhuAssociator.USide_eq_Ufam_add_RHS`/`VSide_eq`, which consume the per-base-mode scalar
tower-collapse cores `u_core`/`v_core`).  Membership is then carried by the proved
`UfamOn_mem_On`/`VfamOn_mem_On` (`ZhuVermaAnDescent8`), regardless of the weights' closed form. -/

/-- **`RightCircTowerEq` from the U-side / V-side tower-collapse.**  If, for some grade witness `G`
matching the inner circle grades, the U-side `USideR` equals the U-family `UfamOn W M n c d a wU …`
and the V-side `VSideR` equals the *negated* V-family `−VfamOn W P n c d a wV …`, then
`RightCircTowerEq W n M P c d a` holds (via the master split
`rightProd_circ_eq_USideR_sub_VSideR`).  This is the precise reduction of the predicate to the
two side-collapses. -/
theorem RightCircTowerEq_of_sides (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (a : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + n + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (wU wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ)
    (hU : USideR W M P n c d a G = UfamOn W M n c d a wU γ₀ Γ Δ)
    (hV : VSideR W M P n c d a G = -VfamOn W P n c d a wV γ₀ Γ Δ) :
    RightCircTowerEq W n M P c d a := by
  refine ⟨wU, wV, γ₀, Γ, Δ, ?_⟩
  rw [rightProd_circ_eq_USideR_sub_VSideR W n hc hd a G hG, hU, hV, sub_neg_eq_add]

/-! ## The depth-`n` iterate-reindexing chain: U/V base-mode reindex and the γ-outer mode-value forms.

These are the depth-`n` lift of `ZhuAssociator.vside_r_reindex`/`USide_eq`'s reindexing step.  In the
proved split `rightProd_circ_eq_USideR_sub_VSideR`, the per-`(i,j,r)` `mode_iterate` peeling index
`s : ℕ` carries the U-base-mode `γ = (r-n-j-1)+s` (U-word `c₍ℓ-s₎(d₍γ₎a)`, `ℓ = i-2n-2`) and the
V-base-mode `γ = s` (V-word `d₍ℓ+N-s₎(c₍γ₎a)`).  We reindex each `∑ᶠ s` finsum by its base-mode `γ`
(`Uword_reindex`/`Vword_reindex`, via `finsum_nat_to_int` + an integer shift), then swap the
`∑ᶠ γ` past the finite `(i,j,r)`-sum (`finsum_sum_comm`, finite by `hasFinSupp_finsetSum`), landing
on the γ-outer mode-value forms `USideR_eq_gammaSum`/`VSideR_eq_gammaSum` — the exact input the
per-`γ` scalar tower-collapse (the depth-`n` `u_core`/`v_core` via `gen_vandermonde`/`gen_jsum`)
consumes to produce the `UfamOn`/`VfamOn` mode-value forms `UfamOn_eq_finsum`/`VfamOn_eq_finsum`
(`ZhuVermaAnDescent9`). -/

/-- **U-word base-mode reindex** (depth-`n` `mode_iterate` reindexing).  The per-`(i,j,r)` U-word
`∑ᶠ s, co(s) • c₍ℓ-s₎(d₍N+s₎a)` reindexes by the U-base-mode `γ = N+s` to a `∑ᶠ γ` over `ℤ`
(extended by `0` for `γ < N`).  Two-step: lift `s : ℕ → s' : ℤ` (`finsum_nat_to_int`), then shift
`s' ↦ γ = s'+N` (`finsum_comp_equiv (Equiv.addRight N)`). -/
theorem Uword_reindex (W : VertexOperatorAlgebra 𝒱) (c d a : 𝒱) (co : ℕ → ℂ) (ℓ N : ℤ) :
    (∑ᶠ s : ℕ, co s • W.smul c (ℓ - s) (W.smul d (N + s) a))
      = ∑ᶠ γ : ℤ, (if N ≤ γ then co (γ - N).toNat else 0)
          • W.smul c (ℓ + N - γ) (W.smul d γ a) := by
  rw [finsum_nat_to_int
      (fun s : ℕ => co s • W.smul c (ℓ - s) (W.smul d (N + s) a))
      (fun s' : ℤ => (if 0 ≤ s' then co s'.toNat else 0)
          • W.smul c (ℓ - s') (W.smul d (N + s') a))
      (fun p hp => by simp only []; rw [if_neg (by omega), zero_smul])
      (fun j => by simp only [Int.toNat_natCast]; rw [if_pos (by omega)])]
  rw [← finsum_comp_equiv (Equiv.addRight N)
      (f := fun γ : ℤ => (if N ≤ γ then co (γ - N).toNat else 0)
          • W.smul c (ℓ + N - γ) (W.smul d γ a))]
  refine finsum_congr fun s' => ?_
  simp only [Equiv.coe_addRight]
  rw [show ℓ + N - (s' + N) = ℓ - s' from by ring, show (s' + N) - N = s' from by ring]
  by_cases h : 0 ≤ s'
  · rw [if_pos h, if_pos (by omega), show N + s' = s' + N from by ring]
  · rw [if_neg h, if_neg (by omega), show N + s' = s' + N from by ring]

/-- **V-word base-mode reindex** (depth-`n` `mode_iterate` reindexing).  The per-`(i,j,r)` V-word
`∑ᶠ s, co(s) • d₍M₀-s₎(c₍s₎a)` reindexes by the V-base-mode `γ = s` (`s : ℕ`, so `γ ≥ 0`) to a
`∑ᶠ γ` over `ℤ` (extended by `0` for `γ < 0`), `M₀ = ℓ+N`.  Single-step `finsum_nat_to_int`
(the V-base-mode IS the iterate index `s`). -/
theorem Vword_reindex (W : VertexOperatorAlgebra 𝒱) (c d a : 𝒱) (co : ℕ → ℂ) (M0 : ℤ) :
    (∑ᶠ s : ℕ, co s • W.smul d (M0 - s) (W.smul c (s : ℤ) a))
      = ∑ᶠ γ : ℤ, (if 0 ≤ γ then co γ.toNat else 0)
          • W.smul d (M0 - γ) (W.smul c γ a) := by
  rw [finsum_nat_to_int
      (fun s : ℕ => co s • W.smul d (M0 - s) (W.smul c (s : ℤ) a))
      (fun γ : ℤ => (if 0 ≤ γ then co γ.toNat else 0)
          • W.smul d (M0 - γ) (W.smul c γ a))
      (fun p hp => by simp only []; rw [if_neg (by omega), zero_smul])
      (fun j => by simp only [Int.toNat_natCast]; rw [if_pos (by omega)])]

/-- Finite support (in the U-base-mode `γ`) of a per-`(i,j,r)` U-word γ-body: `d₍γ₎a = 0` once
`γ ≥ N_d` (`W.regularity d a`), and the `if`-guard kills `γ < N`. -/
theorem Ugamma_fin (W : VertexOperatorAlgebra 𝒱) (c d a : 𝒱) (co : ℕ → ℂ) (ℓ N : ℤ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      (if N ≤ γ then co (γ - N).toNat else 0) • W.smul c (ℓ + N - γ) (W.smul d γ a)) := by
  obtain ⟨Nd, hNd⟩ := W.regularity d a
  apply Set.Finite.subset (Set.finite_Icc N Nd)
  intro γ hγ
  rw [Function.mem_support] at hγ
  simp only [Set.mem_Icc]
  refine ⟨by by_contra h; exact hγ (by rw [if_neg (by omega), zero_smul]),
    by by_contra h; exact hγ (by rw [show W.smul d γ a = (0 : 𝒱) from hNd γ (by omega),
      PreVertexAlgebra.smul_zero_right, smul_zero])⟩

/-- Finite support (in the V-base-mode `γ`) of a per-`(i,j,r)` V-word γ-body: `c₍γ₎a = 0` once
`γ ≥ N_c` (`W.regularity c a`), and the `if`-guard kills `γ < 0`. -/
theorem Vgamma_fin (W : VertexOperatorAlgebra 𝒱) (c d a : 𝒱) (co : ℕ → ℂ) (M0 : ℤ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      (if 0 ≤ γ then co γ.toNat else 0) • W.smul d (M0 - γ) (W.smul c γ a)) := by
  obtain ⟨Nc, hNc⟩ := W.regularity c a
  apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) Nc)
  intro γ hγ
  rw [Function.mem_support] at hγ
  simp only [Set.mem_Icc]
  refine ⟨by by_contra h; exact hγ (by rw [if_neg (by omega), zero_smul]),
    by by_contra h; exact hγ (by rw [show W.smul c γ a = (0 : 𝒱) from hNc γ (by omega),
      PreVertexAlgebra.smul_zero_right, smul_zero])⟩

/-- Finite support of a `Finset`-sum of finitely-supported `ℤ`-indexed families (so a `∑ᶠ γ` may be
swapped past the finite `(i,j,r)`-sum). -/
theorem hasFinSupp_finsetSum {ι : Type} (s : Finset ι) (F : ι → ℤ → 𝒱)
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

/-- The per-`(i,j,r)` U-side coefficient of `c₍ℓ+N-γ₎(d₍γ₎a)` after the `Uword_reindex`
base-mode reindex (`ℓ = i-2n-2`, `N = r-n-j-1`): the `assemblyLead` times the `mode_iterate`
coefficient at the peeling index `s = γ-N`, guarded by `N ≤ γ`. -/
noncomputable def UgammaCoeff (M P n : ℕ) (G : ℕ → ℕ) (i j r : ℕ) (γ : ℤ) : ℂ :=
  if (r : ℤ) - ((n : ℤ) + (j : ℤ) + 1) ≤ γ then
    assemblyLead M P n G i j r
      * ((-1 : ℂ) ^ ((γ - ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1))).toNat)
          * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2)
              (γ - ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1))).toNat)
  else 0

/-- The per-`(i,j,r)` U-word γ-body has finite support (`Ugamma_fin` specialised). -/
theorem UgammaCoeff_body_fin (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱) (G : ℕ → ℕ)
    (i j r : ℕ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      UgammaCoeff M P n G i j r γ
        • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
            (W.smul d γ a)) :=
  Ugamma_fin W c d a
    (fun s => assemblyLead M P n G i j r
      * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s))
    ((i : ℤ) - 2 * (n : ℤ) - 2) ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1))

/-- The per-`(i,j,r)` V-side coefficient of `d₍ℓ+N-γ₎(c₍γ₎a)` after the `Vword_reindex` base-mode
reindex (`M₀ = ℓ+N = (i-2n-2)+(r-n-j-1)`): the `assemblyLead` times the `mode_iterate` coefficient
at `s = γ` and the V-sign `(-1)^ℓ`, guarded by `0 ≤ γ`. -/
noncomputable def VgammaCoeff (M P n : ℕ) (G : ℕ → ℕ) (i j r : ℕ) (γ : ℤ) : ℂ :=
  if 0 ≤ γ then
    assemblyLead M P n G i j r
      * ((-1 : ℂ) ^ γ.toNat * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) γ.toNat)
      * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2))
  else 0

/-- The per-`(i,j,r)` V-word γ-body has finite support (`Vgamma_fin` specialised). -/
theorem VgammaCoeff_body_fin (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱) (G : ℕ → ℕ)
    (i j r : ℕ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      VgammaCoeff M P n G i j r γ
        • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
            (W.smul c γ a)) :=
  Vgamma_fin W c d a
    (fun s => assemblyLead M P n G i j r
      * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s)
      * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2)))
    (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)))

/-- **The depth-`n` U-side γ-outer mode-value form.**  `USideR` reindexes by the U-base-mode `γ`
(`Uword_reindex` per `(i,j,r)`) and the `∑ᶠ γ` is pulled outermost past the finite `(i,j,r)`-sum:
`USideR = ∑ᶠ γ, ∑_{i,j,r} UgammaCoeff … γ • c₍(ℓ+N)-γ₎(d₍γ₎a)`.  Depth-`n` lift of the reindexing
step of `ZhuAssociator.USide_eq`. -/
theorem USideR_eq_gammaSum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱) (G : ℕ → ℕ) :
    USideR W M P n c d a G
      = ∑ᶠ γ : ℤ, ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ r ∈ Finset.range (G i + n + 1),
            UgammaCoeff M P n G i j r γ
              • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                  (W.smul d γ a) := by
  rw [USideR]
  rw [show (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ r ∈ Finset.range (G i + n + 1),
              ∑ᶠ s : ℕ,
                (assemblyLead M P n G i j r
                    * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s))
                  • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) - s)
                      (W.smul d ((r - ((n : ℤ) + (j : ℤ) + 1)) + s) a))
        = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ r ∈ Finset.range (G i + n + 1),
              ∑ᶠ γ : ℤ, UgammaCoeff M P n G i j r γ
                • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                    (W.smul d γ a) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun r _ => by
          rw [Uword_reindex W c d a
            (fun s => assemblyLead M P n G i j r
              * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s))
            ((i : ℤ) - 2 * (n : ℤ) - 2) ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1))]
          exact finsum_congr fun γ => by rw [UgammaCoeff]]
  rw [finsum_sum_comm (Finset.range (M + n + 1))
      (fun γ i => ∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (G i + n + 1),
        UgammaCoeff M P n G i j r γ
          • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul d γ a))
      (fun i _ => hasFinSupp_finsetSum (Finset.range (n + 1)) _ (fun j _ =>
        hasFinSupp_finsetSum (Finset.range (G i + n + 1)) _ (fun r _ =>
          UgammaCoeff_body_fin W M P n c d a G i j r)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_sum_comm (Finset.range (n + 1))
      (fun γ j => ∑ r ∈ Finset.range (G i + n + 1),
        UgammaCoeff M P n G i j r γ
          • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul d γ a))
      (fun j _ => hasFinSupp_finsetSum (Finset.range (G i + n + 1)) _ (fun r _ =>
        UgammaCoeff_body_fin W M P n c d a G i j r))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finsum_sum_comm (Finset.range (G i + n + 1))
      (fun γ r => UgammaCoeff M P n G i j r γ
          • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul d γ a))
      (fun r _ => UgammaCoeff_body_fin W M P n c d a G i j r)]

/-- **The depth-`n` V-side γ-outer mode-value form.**  `VSideR` reindexes by the V-base-mode `γ`
(`Vword_reindex` per `(i,j,r)`, `M₀ = ℓ+N`) and the `∑ᶠ γ` is pulled outermost past the finite
`(i,j,r)`-sum: `VSideR = ∑ᶠ γ, ∑_{i,j,r} VgammaCoeff … γ • d₍(ℓ+N)-γ₎(c₍γ₎a)`.  Depth-`n` lift of
the reindexing step of `ZhuAssociator.VSide_eq`/`vside_per_i`. -/
theorem VSideR_eq_gammaSum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱) (G : ℕ → ℕ) :
    VSideR W M P n c d a G
      = ∑ᶠ γ : ℤ, ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ r ∈ Finset.range (G i + n + 1),
            VgammaCoeff M P n G i j r γ
              • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                  (W.smul c γ a) := by
  rw [VSideR]
  rw [show (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ r ∈ Finset.range (G i + n + 1),
              ∑ᶠ s : ℕ,
                (assemblyLead M P n G i j r
                    * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s)
                    * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2)))
                  • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + (r - ((n : ℤ) + (j : ℤ) + 1)) - s)
                      (W.smul c (s : ℤ) a))
        = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ r ∈ Finset.range (G i + n + 1),
              ∑ᶠ γ : ℤ, VgammaCoeff M P n G i j r γ
                • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                    (W.smul c γ a) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun r _ => by
          rw [Vword_reindex W c d a
            (fun s => assemblyLead M P n G i j r
              * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s)
              * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2)))
            (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)))]
          exact finsum_congr fun γ => by rw [VgammaCoeff]]
  rw [finsum_sum_comm (Finset.range (M + n + 1))
      (fun γ i => ∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (G i + n + 1),
        VgammaCoeff M P n G i j r γ
          • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul c γ a))
      (fun i _ => hasFinSupp_finsetSum (Finset.range (n + 1)) _ (fun j _ =>
        hasFinSupp_finsetSum (Finset.range (G i + n + 1)) _ (fun r _ =>
          VgammaCoeff_body_fin W M P n c d a G i j r)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_sum_comm (Finset.range (n + 1))
      (fun γ j => ∑ r ∈ Finset.range (G i + n + 1),
        VgammaCoeff M P n G i j r γ
          • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul c γ a))
      (fun j _ => hasFinSupp_finsetSum (Finset.range (G i + n + 1)) _ (fun r _ =>
        VgammaCoeff_body_fin W M P n c d a G i j r))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finsum_sum_comm (Finset.range (G i + n + 1))
      (fun γ r => VgammaCoeff M P n G i j r γ
          • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
              (W.smul c γ a))
      (fun r _ => VgammaCoeff_body_fin W M P n c d a G i j r)]

/-! ## The per-`γ` mode-value collection: the γ-outer forms as `∑ᶠ γ, ∑ᶠ μ` over base-mode AND mode.

The γ-outer forms `USideR_eq_gammaSum`/`VSideR_eq_gammaSum` (proved) carry, for each fixed base-mode
`γ`, a finite `(i,j,r)`-sum of single words `c₍μ₍i,j,r₎₎(d₍γ₎a)` (U) resp. `d₍μ₍i,j,r₎₎(c₍γ₎a)` (V),
the mode being determined by `(i,j,r,γ)` as `μ₍i,j,r₎ = (i-2n-2)+(r-n-j-1)-γ`.  We collect that
finite `(i,j,r)`-sum by the mode value `μ`: rewrite each single word as the one-point `∑ᶠ μ`
(`usingle_eq_muFinsum`/`vsingle_eq_muFinsum`), swap the finite `(i,j,r)`-sum out past the `∑ᶠ μ`
(`finsum_sum_comm` innermost-out, finite by `umu_indicator_fin`/`vmu_indicator_fin`), and assemble the
net per-`(γ,μ)` scalar `UgammaModeColl`/`VgammaModeColl` (the `(i,j,r)`-sum of the `mode_iterate`
coefficients hitting mode `μ`).  This is the depth-`n` lift of the inner `μ`-finsum form
`ZhuAssociator.USide_eq3` — putting both sides in the exact `∑ᶠ μ, (scalar) • c₍μ₎base` shape that
`UfamOn_eq_finsum`/`VfamOn_eq_finsum` (`ZhuVermaAnDescent9`) consume per base-mode.  The only
remaining content is then the **per-`(γ,μ)` scalar identity** `UgammaModeColl = towerCoeff` (the
depth-`n` `u_core`/`v_core` via `gen_vandermonde`/`gen_jsum`). -/

/-- The net per-`(γ, μ)` U-side scalar: the finite `(i,j,r)`-sum of the `UgammaCoeff`-coefficients
whose `mode_iterate` mode value `(i-2n-2)+(r-n-j-1)-γ` equals `μ`.  This is the depth-`n` lift of
`ZhuAssociator.uSideScalar` (collected by base-mode `γ` and mode `μ`); the per-`γ` scalar
tower-collapse is the identity `UgammaModeColl M P n G γ μ = towerCoeff M n (wU γ) Δ μ`. -/
noncomputable def UgammaModeColl (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ r ∈ Finset.range (G i + n + 1),
      (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
        then UgammaCoeff M P n G i j r γ else 0)

/-- The net per-`(γ, μ)` V-side scalar (the `VgammaCoeff`-coefficient counterpart of
`UgammaModeColl`); the per-`γ` collapse is `VgammaModeColl M P n G γ μ = towerCoeff P n (wV γ) Δ μ`. -/
noncomputable def VgammaModeColl (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ r ∈ Finset.range (G i + n + 1),
      (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
        then VgammaCoeff M P n G i j r γ else 0)

/-- A single U-word `x • c₍μ₀₎(d₍γ₎a)` is the one-point mode-finsum `∑ᶠ μ, (if μ = μ₀ then x else 0)
• c₍μ₎(d₍γ₎a)` (`finsum_eq_single`). -/
theorem usingle_eq_muFinsum (W : VertexOperatorAlgebra 𝒱) (c d a : 𝒱) (x : ℂ) (μ0 γ : ℤ) :
    x • W.smul c μ0 (W.smul d γ a)
      = ∑ᶠ μ : ℤ, (if μ = μ0 then x else 0) • W.smul c μ (W.smul d γ a) := by
  rw [finsum_eq_single (fun μ : ℤ => (if μ = μ0 then x else 0) • W.smul c μ (W.smul d γ a)) μ0
    (fun μ hμ => by simp only []; rw [if_neg hμ, zero_smul])]
  simp only [if_pos]

/-- A single V-word `x • d₍μ₀₎(c₍γ₎a)` is the one-point mode-finsum. -/
theorem vsingle_eq_muFinsum (W : VertexOperatorAlgebra 𝒱) (c d a : 𝒱) (x : ℂ) (μ0 γ : ℤ) :
    x • W.smul d μ0 (W.smul c γ a)
      = ∑ᶠ μ : ℤ, (if μ = μ0 then x else 0) • W.smul d μ (W.smul c γ a) := by
  rw [finsum_eq_single (fun μ : ℤ => (if μ = μ0 then x else 0) • W.smul d μ (W.smul c γ a)) μ0
    (fun μ hμ => by simp only []; rw [if_neg hμ, zero_smul])]
  simp only [if_pos]

/-- The one-point U-mode indicator family has finite (singleton) support. -/
theorem umu_indicator_fin (W : VertexOperatorAlgebra 𝒱) (c d a : 𝒱) (x : ℂ) (μ0 γ : ℤ) :
    Function.HasFiniteSupport
      (fun μ : ℤ => (if μ = μ0 then x else 0) • W.smul c μ (W.smul d γ a)) := by
  apply Set.Finite.subset (Set.finite_singleton μ0)
  intro μ hμ
  rw [Function.mem_support] at hμ
  simp only [Set.mem_singleton_iff]
  by_contra h; exact hμ (by rw [if_neg h, zero_smul])

/-- The one-point V-mode indicator family has finite (singleton) support. -/
theorem vmu_indicator_fin (W : VertexOperatorAlgebra 𝒱) (c d a : 𝒱) (x : ℂ) (μ0 γ : ℤ) :
    Function.HasFiniteSupport
      (fun μ : ℤ => (if μ = μ0 then x else 0) • W.smul d μ (W.smul c γ a)) := by
  apply Set.Finite.subset (Set.finite_singleton μ0)
  intro μ hμ
  rw [Function.mem_support] at hμ
  simp only [Set.mem_singleton_iff]
  by_contra h; exact hμ (by rw [if_neg h, zero_smul])

/-- **Per-`γ` U-side mode collection.**  For fixed base-mode `γ`, the finite `(i,j,r)`-sum of single
U-words collapses to the single mode-value finsum `∑ᶠ μ, UgammaModeColl … μ • c₍μ₎(d₍γ₎a)`.  Depth-`n`
lift of `ZhuAssociator.USide_eq3`'s inner `μ`-finsum form: rewrite each word as a one-point `∑ᶠ μ`
(`usingle_eq_muFinsum`), pull the `∑ᶠ μ` out past the finite `(i,j,r)`-sum (innermost-out), and
assemble `UgammaModeColl`. -/
theorem gammaBody_eq_muSum_U (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱) (G : ℕ → ℕ)
    (γ : ℤ) :
    (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
        ∑ r ∈ Finset.range (G i + n + 1),
          UgammaCoeff M P n G i j r γ
            • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                (W.smul d γ a))
      = ∑ᶠ μ : ℤ, UgammaModeColl M P n G γ μ • W.smul c μ (W.smul d γ a) := by
  rw [show (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ r ∈ Finset.range (G i + n + 1),
              UgammaCoeff M P n G i j r γ
                • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                    (W.smul d γ a))
        = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ μ : ℤ, ∑ r ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then UgammaCoeff M P n G i j r γ else 0)
                  • W.smul c μ (W.smul d γ a) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [show (∑ r ∈ Finset.range (G i + n + 1),
                  UgammaCoeff M P n G i j r γ
                    • W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                        (W.smul d γ a))
              = ∑ r ∈ Finset.range (G i + n + 1),
                  ∑ᶠ μ : ℤ, (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2)
                        + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                      then UgammaCoeff M P n G i j r γ else 0) • W.smul c μ (W.smul d γ a) from
            Finset.sum_congr rfl fun r _ =>
              usingle_eq_muFinsum W c d a (UgammaCoeff M P n G i j r γ)
                (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ) γ]
        rw [← finsum_sum_comm (Finset.range (G i + n + 1))
            (fun μ r => (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2)
                  + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                then UgammaCoeff M P n G i j r γ else 0) • W.smul c μ (W.smul d γ a))
            (fun r _ => umu_indicator_fin W c d a (UgammaCoeff M P n G i j r γ) _ γ)]]
  rw [show (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ μ : ℤ, ∑ r ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then UgammaCoeff M P n G i j r γ else 0) • W.smul c μ (W.smul d γ a))
        = ∑ i ∈ Finset.range (M + n + 1),
            ∑ᶠ μ : ℤ, ∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then UgammaCoeff M P n G i j r γ else 0) • W.smul c μ (W.smul d γ a) from
      Finset.sum_congr rfl fun i _ => by
        rw [← finsum_sum_comm (Finset.range (n + 1))
            (fun μ j => ∑ r ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then UgammaCoeff M P n G i j r γ else 0) • W.smul c μ (W.smul d γ a))
            (fun j _ => hasFinSupp_finsetSum (Finset.range (G i + n + 1)) _ (fun r _ =>
              umu_indicator_fin W c d a (UgammaCoeff M P n G i j r γ) _ γ))]]
  rw [← finsum_sum_comm (Finset.range (M + n + 1))
      (fun μ i => ∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (G i + n + 1),
          (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
            then UgammaCoeff M P n G i j r γ else 0) • W.smul c μ (W.smul d γ a))
      (fun i _ => hasFinSupp_finsetSum (Finset.range (n + 1)) _ (fun j _ =>
        hasFinSupp_finsetSum (Finset.range (G i + n + 1)) _ (fun r _ =>
          umu_indicator_fin W c d a (UgammaCoeff M P n G i j r γ) _ γ)))]
  refine finsum_congr fun μ => ?_
  rw [UgammaModeColl, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul]

/-- **Per-`γ` V-side mode collection** (the `VgammaCoeff` mirror of `gammaBody_eq_muSum_U`). -/
theorem gammaBody_eq_muSum_V (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱) (G : ℕ → ℕ)
    (γ : ℤ) :
    (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
        ∑ r ∈ Finset.range (G i + n + 1),
          VgammaCoeff M P n G i j r γ
            • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                (W.smul c γ a))
      = ∑ᶠ μ : ℤ, VgammaModeColl M P n G γ μ • W.smul d μ (W.smul c γ a) := by
  rw [show (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ r ∈ Finset.range (G i + n + 1),
              VgammaCoeff M P n G i j r γ
                • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                    (W.smul c γ a))
        = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ μ : ℤ, ∑ r ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then VgammaCoeff M P n G i j r γ else 0)
                  • W.smul d μ (W.smul c γ a) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [show (∑ r ∈ Finset.range (G i + n + 1),
                  VgammaCoeff M P n G i j r γ
                    • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
                        (W.smul c γ a))
              = ∑ r ∈ Finset.range (G i + n + 1),
                  ∑ᶠ μ : ℤ, (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2)
                        + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                      then VgammaCoeff M P n G i j r γ else 0) • W.smul d μ (W.smul c γ a) from
            Finset.sum_congr rfl fun r _ =>
              vsingle_eq_muFinsum W c d a (VgammaCoeff M P n G i j r γ)
                (((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ) γ]
        rw [← finsum_sum_comm (Finset.range (G i + n + 1))
            (fun μ r => (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2)
                  + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                then VgammaCoeff M P n G i j r γ else 0) • W.smul d μ (W.smul c γ a))
            (fun r _ => vmu_indicator_fin W c d a (VgammaCoeff M P n G i j r γ) _ γ)]]
  rw [show (∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ᶠ μ : ℤ, ∑ r ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then VgammaCoeff M P n G i j r γ else 0) • W.smul d μ (W.smul c γ a))
        = ∑ i ∈ Finset.range (M + n + 1),
            ∑ᶠ μ : ℤ, ∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then VgammaCoeff M P n G i j r γ else 0) • W.smul d μ (W.smul c γ a) from
      Finset.sum_congr rfl fun i _ => by
        rw [← finsum_sum_comm (Finset.range (n + 1))
            (fun μ j => ∑ r ∈ Finset.range (G i + n + 1),
                (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
                  then VgammaCoeff M P n G i j r γ else 0) • W.smul d μ (W.smul c γ a))
            (fun j _ => hasFinSupp_finsetSum (Finset.range (G i + n + 1)) _ (fun r _ =>
              vmu_indicator_fin W c d a (VgammaCoeff M P n G i j r γ) _ γ))]]
  rw [← finsum_sum_comm (Finset.range (M + n + 1))
      (fun μ i => ∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (G i + n + 1),
          (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
            then VgammaCoeff M P n G i j r γ else 0) • W.smul d μ (W.smul c γ a))
      (fun i _ => hasFinSupp_finsetSum (Finset.range (n + 1)) _ (fun j _ =>
        hasFinSupp_finsetSum (Finset.range (G i + n + 1)) _ (fun r _ =>
          vmu_indicator_fin W c d a (VgammaCoeff M P n G i j r γ) _ γ)))]
  refine finsum_congr fun μ => ?_
  rw [VgammaModeColl, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul]

/-! ## The double-finsum (base-mode `γ` ⊗ mode `μ`) forms of `USideR`/`VSideR`.

Feeding the per-`γ` collection `gammaBody_eq_muSum_U`/`gammaBody_eq_muSum_V` into the proved γ-outer
forms `USideR_eq_gammaSum`/`VSideR_eq_gammaSum` gives `USideR`/`VSideR` as a clean double finsum over
the base-mode `γ` AND the mode `μ` — exactly the shape `UfamOn_eq_finsum`/`VfamOn_eq_finsum`
(`ZhuVermaAnDescent9`) produce (a finite base-mode sum of mode-value finsums).  This is the depth-`n`
lift of `ZhuAssociator.USide_eq3`. -/

/-- **`USideR` as a base-mode ⊗ mode double finsum.** -/
theorem USideR_eq_gammaModeFinsum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱)
    (G : ℕ → ℕ) :
    USideR W M P n c d a G
      = ∑ᶠ γ : ℤ, ∑ᶠ μ : ℤ, UgammaModeColl M P n G γ μ • W.smul c μ (W.smul d γ a) := by
  rw [USideR_eq_gammaSum]
  exact finsum_congr fun γ => gammaBody_eq_muSum_U W M P n c d a G γ

/-- **`VSideR` as a base-mode ⊗ mode double finsum.** -/
theorem VSideR_eq_gammaModeFinsum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱)
    (G : ℕ → ℕ) :
    VSideR W M P n c d a G
      = ∑ᶠ γ : ℤ, ∑ᶠ μ : ℤ, VgammaModeColl M P n G γ μ • W.smul d μ (W.smul c γ a) := by
  rw [VSideR_eq_gammaSum]
  exact finsum_congr fun γ => gammaBody_eq_muSum_V W M P n c d a G γ

/-! ## The finite base-mode range reduction (the `∑ᶠ γ → ∑ g ∈ range Γ` bridge to `UfamOn`/`VfamOn`).

The double-finsum forms `USideR_eq_gammaModeFinsum`/`VSideR_eq_gammaModeFinsum` carry an OUTER
`∑ᶠ γ` over all of `ℤ`, whereas the tower-family mode-value forms `UfamOn_eq_finsum`/`VfamOn_eq_finsum`
(`ZhuVermaAnDescent9`) carry an outer FINITE `∑ g ∈ range Γ` (base-mode `γ = γ₀ + g`).  To match
`HU`/`HV` of `RightCircTowerEq_of_collapse` the two outer indexings must be identified.  They are: the
`γ`-support of each side's double-finsum body is finite, bounded

* **above** by `W.regularity` (`d₍γ₎a = 0` for `γ ≥ N_d` on the U-side; `c₍γ₎a = 0` for `γ ≥ N_c` on
  the V-side), and
* **below** by the `mode_iterate` guard — `UgammaCoeff` requires `N = r-(n+j+1) ≤ γ`, so vanishes for
  `γ < -(2n+1)` (`j ≤ n`, `r ≥ 0`); `VgammaCoeff` requires `0 ≤ γ`, so vanishes for `γ < 0`.

Hence each `∑ᶠ γ` collapses to a finite range sum over `[γ₀, γ₀+Γ)` (`γ₀ = -(2n+1)`, U; `γ₀ = 0`, V),
the exact outer shape of `UfamOn_eq_finsum`/`VfamOn_eq_finsum`.  This is the depth-`n` lift of the
base-mode-range bookkeeping implicit in `ZhuAssociator.USide_eq3`/`VSide_eq`'s passage to `Ufam`/`Vfam`
(which carry a finite base-mode range `Bv`/`Bu`).  After this bridge, `HU`/`HV` reduce to the per-`γ`
SCALAR tower-collapse `UgammaModeColl = towerCoeff M n (wU γ) Δ μ` (resp. V), with the
Mathematica-verified uniform tower depth `Δ = 2n+2 + max(γ-γ₀, 0)` (grade `M` for U, grade `P` for V;
the per-FZ-index-`j` inner `i`-sum is itself an `M`-independent grade-`M` tower — exact-`Solve`
verified, `n = 1,2`, `M,P ≤ 3`, all contributing `γ`). -/

/-- `UgammaCoeff` vanishes below `γ = -(2n+1)`: its guard `N ≤ γ` with
`N = r-(n+j+1) ≥ -(n+j+1) ≥ -(2n+1)` fails (`j ≤ n`, `r ≥ 0`). -/
theorem UgammaCoeff_zero_below (M P n : ℕ) (G : ℕ → ℕ) (i j r : ℕ) (γ : ℤ)
    (hj : j ≤ n) (hγ : γ < -(2 * (n : ℤ) + 1)) : UgammaCoeff M P n G i j r γ = 0 := by
  rw [UgammaCoeff, if_neg]
  have hr : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
  have hj' : (j : ℤ) ≤ (n : ℤ) := by exact_mod_cast hj
  omega

/-- The collected U scalar `UgammaModeColl` vanishes for `γ < -(2n+1)`. -/
theorem UgammaModeColl_zero_below (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ)
    (hγ : γ < -(2 * (n : ℤ) + 1)) : UgammaModeColl M P n G γ μ = 0 := by
  rw [UgammaModeColl]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj =>
    Finset.sum_eq_zero fun r _ => ?_
  rw [UgammaCoeff_zero_below M P n G i j r γ (by have := Finset.mem_range.mp hj; omega) hγ]
  simp only [ite_self]

/-- The U-side double-finsum body in `γ` vanishes once the base `d₍γ₎a = 0` (`W.regularity d a`). -/
theorem USide_gammaBody_zero_above (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱)
    (G : ℕ → ℕ) {Nd : ℤ} (hNd : ∀ γ : ℤ, Nd ≤ γ → W.smul d γ a = 0) (γ : ℤ) (hγ : Nd ≤ γ) :
    (∑ᶠ μ : ℤ, UgammaModeColl M P n G γ μ • W.smul c μ (W.smul d γ a)) = 0 := by
  rw [show W.smul d γ a = (0 : 𝒱) from hNd γ hγ]
  simp only [PreVertexAlgebra.smul_zero_right, smul_zero, finsum_zero]

/-- The U-side double-finsum body has finite `γ`-support (contained in `[-(2n+1), N_d)`). -/
theorem USide_gammaBody_finsupp (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱)
    (G : ℕ → ℕ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      ∑ᶠ μ : ℤ, UgammaModeColl M P n G γ μ • W.smul c μ (W.smul d γ a)) := by
  obtain ⟨Nd, hNd⟩ := W.regularity d a
  apply Set.Finite.subset (Set.finite_Icc (-(2 * (n : ℤ) + 1)) Nd)
  intro γ hγ
  rw [Function.mem_support] at hγ
  simp only [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    apply hγ
    refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
    rw [UgammaModeColl_zero_below M P n G γ μ (by omega), zero_smul]
  · by_contra h
    exact hγ (USide_gammaBody_zero_above W M P n c d a G hNd γ (by omega))

/-- **The U-side as a finite base-mode range double sum.**  Restricting the outer `∑ᶠ γ` of
`USideR_eq_gammaModeFinsum` to the contributing window (`γ₀ = -(2n+1)`), `USideR` is a finite
base-mode sum of mode-value finsums of `c₍μ₎(d₍γ₎a)` — the exact outer shape of
`UfamOn_eq_finsum` (`ZhuVermaAnDescent9`).  The remaining content of `HU` is then the per-`γ`
SCALAR collapse `UgammaModeColl … = towerCoeff M n (wU γ) Δ μ`. -/
theorem USideR_eq_finiteGammaSum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱)
    (G : ℕ → ℕ) :
    ∃ Γ : ℕ, USideR W M P n c d a G
      = ∑ g ∈ Finset.range Γ,
          ∑ᶠ μ : ℤ, UgammaModeColl M P n G (-(2 * (n : ℤ) + 1) + (g : ℤ)) μ
            • W.smul c μ (W.smul d (-(2 * (n : ℤ) + 1) + (g : ℤ)) a) := by
  obtain ⟨Nd, hNd⟩ := W.regularity d a
  set γ₀ : ℤ := -(2 * (n : ℤ) + 1) with hγ₀
  set emb : ℕ ↪ ℤ := ⟨fun g => γ₀ + (g : ℤ), fun a b h => by simpa using h⟩ with hemb
  refine ⟨(Nd - γ₀).toNat, ?_⟩
  rw [USideR_eq_gammaModeFinsum]
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (Nd - γ₀).toNat).map emb) ?_]
  · rw [Finset.sum_map]; rfl
  · intro γ hγ
    rw [Function.mem_support] at hγ
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range, hemb,
      Function.Embedding.coeFn_mk]
    have hub : γ < Nd := by
      by_contra h
      exact hγ (USide_gammaBody_zero_above W M P n c d a G hNd γ (by omega))
    have hlb : γ₀ ≤ γ := by
      by_contra h
      replace h : γ < γ₀ := not_le.mp h
      apply hγ
      refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
      rw [UgammaModeColl_zero_below M P n G γ μ (by rw [hγ₀] at h; exact h), zero_smul]
    refine ⟨(γ - γ₀).toNat, by omega, by omega⟩

/-- `VgammaCoeff` vanishes below `γ = 0`: its guard is `0 ≤ γ`. -/
theorem VgammaCoeff_zero_below (M P n : ℕ) (G : ℕ → ℕ) (i j r : ℕ) (γ : ℤ)
    (hγ : γ < 0) : VgammaCoeff M P n G i j r γ = 0 := by
  rw [VgammaCoeff, if_neg (by omega)]

/-- The collected V scalar `VgammaModeColl` vanishes for `γ < 0`. -/
theorem VgammaModeColl_zero_below (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ) (hγ : γ < 0) :
    VgammaModeColl M P n G γ μ = 0 := by
  rw [VgammaModeColl]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
    Finset.sum_eq_zero fun r _ => ?_
  rw [VgammaCoeff_zero_below M P n G i j r γ hγ]
  simp only [ite_self]

/-- The V-side double-finsum body in `γ` vanishes once the base `c₍γ₎a = 0` (`W.regularity c a`). -/
theorem VSide_gammaBody_zero_above (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱)
    (G : ℕ → ℕ) {Nc : ℤ} (hNc : ∀ γ : ℤ, Nc ≤ γ → W.smul c γ a = 0) (γ : ℤ) (hγ : Nc ≤ γ) :
    (∑ᶠ μ : ℤ, VgammaModeColl M P n G γ μ • W.smul d μ (W.smul c γ a)) = 0 := by
  rw [show W.smul c γ a = (0 : 𝒱) from hNc γ hγ]
  simp only [PreVertexAlgebra.smul_zero_right, smul_zero, finsum_zero]

/-- The V-side double-finsum body has finite `γ`-support (contained in `[0, N_c)`). -/
theorem VSide_gammaBody_finsupp (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱)
    (G : ℕ → ℕ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      ∑ᶠ μ : ℤ, VgammaModeColl M P n G γ μ • W.smul d μ (W.smul c γ a)) := by
  obtain ⟨Nc, hNc⟩ := W.regularity c a
  apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) Nc)
  intro γ hγ
  rw [Function.mem_support] at hγ
  simp only [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    apply hγ
    refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
    rw [VgammaModeColl_zero_below M P n G γ μ (by omega), zero_smul]
  · by_contra h
    exact hγ (VSide_gammaBody_zero_above W M P n c d a G hNc γ (by omega))

/-- **The V-side as a finite base-mode range double sum** (`γ₀ = 0`).  The V mirror of
`USideR_eq_finiteGammaSum`; remaining content of `HV` is the per-`γ` scalar collapse
`VgammaModeColl … = towerCoeff P n (wV γ) Δ μ`. -/
theorem VSideR_eq_finiteGammaSum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d a : 𝒱)
    (G : ℕ → ℕ) :
    ∃ Γ : ℕ, VSideR W M P n c d a G
      = ∑ g ∈ Finset.range Γ,
          ∑ᶠ μ : ℤ, VgammaModeColl M P n G ((g : ℤ)) μ
            • W.smul d μ (W.smul c (g : ℤ) a) := by
  obtain ⟨Nc, hNc⟩ := W.regularity c a
  set emb : ℕ ↪ ℤ := ⟨fun g => (g : ℤ), fun a b h => by simpa using h⟩ with hemb
  refine ⟨Nc.toNat, ?_⟩
  rw [VSideR_eq_gammaModeFinsum]
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range Nc.toNat).map emb) ?_]
  · rw [Finset.sum_map]; rfl
  · intro γ hγ
    rw [Function.mem_support] at hγ
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range, hemb,
      Function.Embedding.coeFn_mk]
    have hub : γ < Nc := by
      by_contra h
      exact hγ (VSide_gammaBody_zero_above W M P n c d a G hNc γ (by omega))
    have hlb : 0 ≤ γ := by
      by_contra h
      replace h : γ < 0 := not_le.mp h
      apply hγ
      refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
      rw [VgammaModeColl_zero_below M P n G γ μ h, zero_smul]
    refine ⟨γ.toNat, by omega, by omega⟩

/-! ## `RightCircTowerEq` from the per-`(γ,μ)` scalar tower-collapse.

The double-finsum forms `USideR_eq_gammaModeFinsum`/`VSideR_eq_gammaModeFinsum` and the `UfamOn`/
`VfamOn` mode-value forms `UfamOn_eq_finsum`/`VfamOn_eq_finsum` (`ZhuVermaAnDescent9`) are the
*same shape* — a base-mode `γ` outer finsum/sum of mode-value finsums — so matching the two sides is
a pure SCALAR identity: the per-`(γ,μ)` collected coefficient `UgammaModeColl`/`VgammaModeColl` equals
the per-`(γ,μ)` tower coefficient `towerCoeff M n (wU γ) Δ μ`/`towerCoeff P n (wV γ) Δ μ`, AFTER the
base-mode finsum-over-`ℤ` is identified with the finite range `[γ₀, γ₀+Γ)` (the regularity-bounded
contributing modes, the tail acting as `0` on `d₍γ₎a` / `c₍γ₎a`).  We package that scalar matching as
the side-collapse hypotheses `HU`/`HV` and close `RightCircTowerEq` through `RightCircTowerEq_of_sides`
(proved).  `HU`/`HV` are exactly the depth-`n` `ZhuUCore.u_core`/`ZhuVCore.v_core`
(`gen_vandermonde` per FZ index `j` + `gen_jsum`), mirroring `coeffSn_eq_coeffPn`
(`ZhuVermaAnDescent4`) — NOT axioms. -/

/-- **`RightCircTowerEq` from the per-`(γ,μ)` collapse.**  If, for the grade witness `G`, the
collected per-`(γ,μ)` U-side scalar form equals the `UfamOn` mode-value form and the V-side the
negated `VfamOn` mode-value form (the `HU`/`HV` scalar matchings, on the proved double-finsum forms),
then `RightCircTowerEq W n M P c d a` holds.  This is the precise reduction of the predicate to the
two per-`(γ,μ)` scalar tower-collapses. -/
theorem RightCircTowerEq_of_collapse (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (a : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + n + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (wU wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ)
    (HU : (∑ᶠ γ : ℤ, ∑ᶠ μ : ℤ, UgammaModeColl M P n G γ μ • W.smul c μ (W.smul d γ a))
        = UfamOn W M n c d a wU γ₀ Γ Δ)
    (HV : (∑ᶠ γ : ℤ, ∑ᶠ μ : ℤ, VgammaModeColl M P n G γ μ • W.smul d μ (W.smul c γ a))
        = -VfamOn W P n c d a wV γ₀ Γ Δ) :
    RightCircTowerEq W n M P c d a :=
  RightCircTowerEq_of_sides W n hc hd a G hG wU wV γ₀ Γ Δ
    (by rw [USideR_eq_gammaModeFinsum, HU]) (by rw [VSideR_eq_gammaModeFinsum, HV])

/-!
## PRECISE remaining target (NOT `sorry`, NOT axiomatized)

`RightCircTowerEq_holds (W) (n) (M P : ℕ) (c d a) (hc : c ∈ 𝒱_M) (hd : d ∈ 𝒱_P) (ha : a ∈ 𝒱_K)
  : RightCircTowerEq W n M P c d a` (∀ args) is reduced — by the proved, axiom-clean master split
`rightProd_circ_eq_USideR_sub_VSideR` and the criterion `RightCircTowerEq_of_sides` (this file) — to
the **two side tower-collapses**:

  (U)  `USideR W M P n c d a G = UfamOn W M n c d a wU γ₀ Γ Δ`,
  (V)  `VSideR W M P n c d a G = − VfamOn W P n c d a wV γ₀ Γ Δ`,

for SOME finite tower weights `wU, wV : ℤ → ℕ → ℂ` and ranges `γ₀, Γ, Δ` (and the grade witness `G`,
e.g. `G i = (M+P-(i-2n-2)-1).toNat`).  Via the proved mode-value forms `UfamOn_eq_finsum`/
`VfamOn_eq_finsum` + `presOnFamily_eq_finsum`/`towerCoeff` (`ZhuVermaAnDescent9`), each side-collapse
is the depth-`n` lift of `ZhuAssociator.USide_eq`/`VSide_eq` (the finsum-swap pulling the `∑ᶠ s`
`mode_iterate` index out as the U-base-mode or V-base-mode, then collecting the i,j,r,s-summed
scalar coefficient of each `c₍μ₎(d₍γ₎a)` resp. `d₍μ₎(c₍γ₎a)`) followed by the per-base-mode scalar
tower-collapse
core (the depth-`n` `ZhuUCore.u_core`/`ZhuVCore.v_core`, whose dual-Hahn tower weights are the `wU`/
`wV`).  The KEY structural fact (Mathematica-verified, `ZhuVermaAnDescent6/7/8/9`): the per-FZ-index
`j` inner `i`-sum is already an `M`-independent tower (collapsing through `ZhuRes.gen_vandermonde` per
`j`, then `ZhuRes.gen_jsum`), so both side-collapses are reachable from the already-proved
combinatorial certificates; their existence (not the weights' closed form) is all that is required,
and `RightCircTowerEq_of_sides` then closes the predicate, with membership carried by the proved
`UfamOn_mem_On`/`VfamOn_mem_On`.

With the full depth-`n` iterate-reindexing AND per-`(γ,μ)` mode-collection chains proved here
(`Uword_reindex`/`Vword_reindex` → `USideR_eq_gammaSum`/`VSideR_eq_gammaSum` →
`gammaBody_eq_muSum_U`/`_V` → `USideR_eq_gammaModeFinsum`/`VSideR_eq_gammaModeFinsum`), both sides now
sit in the EXACT base-mode `γ` ⊗ mode `μ` double-finsum shape `∑ᶠ γ, ∑ᶠ μ, (scalar) • c₍μ₎(d₍γ₎a)`
(U) resp. `∑ᶠ γ, ∑ᶠ μ, (scalar) • d₍μ₎(c₍γ₎a)` (V) — the very shape produced by the proved
`UfamOn_eq_finsum`/`VfamOn_eq_finsum` (`ZhuVermaAnDescent9`).  The criterion `RightCircTowerEq_of_collapse`
(this file) closes `RightCircTowerEq` from the two SCALAR matchings

  (HU)  `∑ᶠ γ, ∑ᶠ μ, UgammaModeColl M P n G γ μ • c₍μ₎(d₍γ₎a) = UfamOn W M n c d a wU γ₀ Γ Δ`,
  (HV)  `∑ᶠ γ, ∑ᶠ μ, VgammaModeColl M P n G γ μ • d₍μ₎(c₍γ₎a) = − VfamOn W P n c d a wV γ₀ Γ Δ`,

for SOME finite weights `wU, wV : ℤ → ℕ → ℂ` and ranges `γ₀, Γ, Δ`.  `HU`/`HV` are PURE per-`γ`
scalar identities (NOT axioms): identifying the base-mode finsum-over-`ℤ` with the finite range
`[γ₀, γ₀+Γ)` (the regularity-bounded contributing modes, tail acting as `0` on `d₍γ₎a` / `c₍γ₎a`),
and then per fixed `γ` matching `UgammaModeColl M P n G γ μ = towerCoeff M n (wU γ) Δ μ` (resp.
`VgammaModeColl … = towerCoeff P n (wV γ) Δ μ`) for each mode `μ`.  This per-`(γ,μ)` scalar collapse is
the depth-`n` `ZhuUCore.u_core`/`ZhuVCore.v_core`: the `(i,j,r)`-sum collected at fixed `(γ,μ)`
collapses through `ZhuRes.gen_vandermonde` (per FZ index `j`, on the inner `i`-sum) then
`ZhuRes.gen_jsum` (the FZ `j`-sum), exactly mirroring `coeffSn_eq_coeffPn` (`ZhuVermaAnDescent4`) — the
same engine, with the `mode_iterate` base-mode `γ` / mode `μ` reindexing (proved here) in place of the
commutator reindexing `inner_reindexN`.  At `n = 0` `RightCircTowerEq_of_collapse` reduces to the
`ZhuAssociator.assoc_eq` route (`USide_eq3`/`Ufam_eq` matching).

Proved here (axiom-clean: `[propext, Classical.choice, Quot.sound]`):

* `assemblyLead`, `USideR`, `VSideR` — the depth-`n` U-side / V-side targets.
* `USideR_s_fin` / `VSideR_s_fin` — finite support of the per-`(i,j,r)` `mode_iterate` `s`-finsums
  (`W.regularity`).
* **`rightProd_circ_eq_USideR_sub_VSideR`** — the depth-`n` master split
  `rightProd W n (circ W n c d) a = USideR − VSideR` (lift of `ZhuAssociator.lhs_split`).
* **`RightCircTowerEq_of_sides`** — the reduction of `RightCircTowerEq` to the two side-collapses.
* **`Uword_reindex` / `Vword_reindex`** — the depth-`n` `mode_iterate` base-mode reindexing of the
  per-`(i,j,r)` U/V finsums (`finsum_nat_to_int` + integer shift), lift of
  `ZhuAssociator.vside_r_reindex`'s reindex step.
* `Ugamma_fin` / `Vgamma_fin` / `UgammaCoeff_body_fin` / `VgammaCoeff_body_fin` — finite support of
  the γ-reindexed bodies (`W.regularity`); `hasFinSupp_finsetSum` — support of a finite sum.
* `UgammaCoeff` / `VgammaCoeff` — the per-`(i,j,r)` γ-reindexed scalar coefficients.
* **`USideR_eq_gammaSum` / `VSideR_eq_gammaSum`** — the depth-`n` γ-outer mode-value forms of
  `USideR`/`VSideR` (the `∑ᶠ γ` pulled outermost past the finite `(i,j,r)`-sum).  Lift of the
  reindexing step of `ZhuAssociator.USide_eq`/`VSide_eq`.
* `UgammaModeColl` / `VgammaModeColl` — the net per-`(γ,μ)` collected U/V scalars (the depth-`n` lift
  of `ZhuAssociator.uSideScalar`, collected by base-mode `γ` and mode `μ`).
* `usingle_eq_muFinsum` / `vsingle_eq_muFinsum` (single word → one-point `∑ᶠ μ`),
  `umu_indicator_fin` / `vmu_indicator_fin` (singleton support).
* **`gammaBody_eq_muSum_U` / `gammaBody_eq_muSum_V`** — the per-`γ` mode-value collection (the finite
  `(i,j,r)`-sum → `∑ᶠ μ, (collected scalar) • word`), depth-`n` lift of the inner `μ`-finsum form of
  `ZhuAssociator.USide_eq3`.
* **`USideR_eq_gammaModeFinsum` / `VSideR_eq_gammaModeFinsum`** — `USideR`/`VSideR` as the base-mode
  `γ` ⊗ mode `μ` double finsum, the exact shape `UfamOn_eq_finsum`/`VfamOn_eq_finsum` consume.
* `UgammaCoeff_zero_below` / `UgammaModeColl_zero_below` (`γ < -(2n+1) ⟹ 0`), `VgammaCoeff_zero_below`
  / `VgammaModeColl_zero_below` (`γ < 0 ⟹ 0`) — the lower base-mode bounds from the `mode_iterate`
  guards.
* `USide_gammaBody_zero_above` / `VSide_gammaBody_zero_above` (`W.regularity`),
  `USide_gammaBody_finsupp` / `VSide_gammaBody_finsupp` — finite `γ`-support of the double-finsum
  bodies (`[-(2n+1), N_d)` resp. `[0, N_c)`).
* **`USideR_eq_finiteGammaSum` / `VSideR_eq_finiteGammaSum`** — `USideR`/`VSideR` as a FINITE
  base-mode range `∑ g ∈ range Γ` of mode-value finsums (the `∑ᶠ γ → ∑ g` bridge to the exact outer
  shape of `UfamOn_eq_finsum`/`VfamOn_eq_finsum`), with `γ₀ = -(2n+1)` (U) / `γ₀ = 0` (V).
* **`RightCircTowerEq_of_collapse`** — closes `RightCircTowerEq` from the two per-`(γ,μ)` scalar
  matchings `HU`/`HV` on the proved double-finsum forms.

Nothing is `sorry`'d or axiomatized; `RightCircTowerEq_holds` is the stated remaining target above,
reduced (by `RightCircTowerEq_of_collapse` + the finite-base-mode-range bridge
`USideR_eq_finiteGammaSum`/`VSideR_eq_finiteGammaSum`) to the single per-`γ` SCALAR tower-collapse
identity, for each contributing base-mode `γ` and each mode `μ`:

  (U-core)  `UgammaModeColl M P n G γ μ = towerCoeff M n (wU γ) Δ μ`,  grade `M`,
  (V-core)  `VgammaModeColl M P n G γ μ = towerCoeff P n (wV γ) Δ μ`,  grade `P`,

with the Mathematica-verified (exact `Solve`, `n = 1,2`, `M,P ≤ 3`, all contributing `γ`) uniform
tower depth `Δ = 2n+2 + max(γ-γ₀, 0)` and finite weights `wU, wV : ℤ → ℕ → ℂ`.  The KEY structural
fact (also exact-`Solve` verified): for each fixed FZ index `j` the inner `i`-sum of `UgammaModeColl`
is ALREADY an `M`-INDEPENDENT grade-`M` tower in `μ` — so the U-core collapses through
`ZhuRes.gen_vandermonde` per `j` (the inner `i`-sum), then `ZhuRes.gen_jsum` (the FZ `j`-sum),
EXACTLY mirroring `coeffSn_eq_coeffPn` (`ZhuVermaAnDescent4`), with the `mode_iterate` base-mode `γ` /
mode `μ` reindexing (proved here) in place of the commutator reindexing `inner_reindexN`.  These are
pure `cbz`-coefficient identities reachable from the proved combinatorial certificates
`ZhuRes.gen_vandermonde`/`gen_jsum`, NOT a VOA-level obligation and NOT axioms.
-/

end VOA
