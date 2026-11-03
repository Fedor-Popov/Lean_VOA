/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcirc
import VOA.Modules.ZhuVermaAnArchL1
import VOA.Modules.ZhuVermaAnDescent6
import VOA.Modules.ZhuVermaAnDescent9
import VOA.Modules.ZhuVermaAnDescent16
import VOA.Modules.ZhuVermaAnDescent19

/-!
# Game One — closing **`AnmCircTowerEq`** (the `m = 0`, shift-`0` circle tower decomposition).

This is the `m = 0` (single-residue, NO FZ `j`-sum) shift-`0` mirror of the proven left-circle chain
`ZhuVermaAnArchL1` + `ZhuVermaAnArchL1Close.hLcirc_closed` (`leftProd W n (circ W n c d) b`, pole
`2n+2`).  Here the target is

  `anmRight W n 0 (anmCirc W n 0 c d) v = resHom W 0 (n+1) (resHom W 0 (n+2) c d) v`,

the residue-of-residue with inner pole `n+2` (circle weight `cbz M i`, mode `i-(n+2)`) and outer pole
`n+1` (inner residue weight `cbz G_i p`, mode `p-(n+1)`), with `G_i = M+P-(i-(n+2))-1`.

## What is proved here (axiom-clean)

* `USideAnm`/`VSideAnm` — the shift-`0` U/V sides (the `c`-first / `d`-first iterate words).
* `anmCirc_resOfRes_homog` — the residue-of-residue distributed over the inner circle index `i` then
  the outer residue index `p`, with the negative-inner-grade `i` carried by an `if`-guard.
* `anmRight_zero_anmCirc_eq_USideAnm_sub_VSideAnm` — **the shift-`0` master split** `=
  USideAnm − VSideAnm` (mirror of `leftProd_circ_eq_USideLn_sub_VSideLn`).
* `USideAnm_eq_gammaModeFinsum`/`VSideAnm_eq_gammaModeFinsum` — each side as a base-mode `γ` ⊗ mode
  `μ` double finsum, weights `UgammaModeCollAnm`/`VgammaModeCollAnm`.
* `AnmCircTowerEq_of_sides` — the criterion reducing the predicate to the two side-collapses
  `USideAnm = UfamAnm` / `VSideAnm = −VfamAnm` (mirror of `LeftCircTowerEqn_of_sides`).

## The PRECISE remaining content (NOT `sorry`'d / NOT axiomatized) — the two scalar cores

`AnmCircTowerEq` reduces, via `AnmCircTowerEq_of_sides` + `UfamAnm_eq_finsum`/`VfamAnm_eq_finsum`, to
the two per-`(γ,μ)` scalar tower-collapse cores

  (U-core)  `UgammaModeCollAnm M P n G γ μ = towerCoeffAnm M n (wU γ) Δ μ`     for some `wU, Δ`,
  (V-core)  `VgammaModeCollAnm M P n G γ μ = -towerCoeffAnm P n (wV γ) Δ μ`    for some `wV, Δ`,

with `towerCoeffAnm M n wt Δ μ = ∑_{δ<Δ} wt δ · cbz(M+δ, μ+(n+2)+δ)` (the shift-`0` analogue of
`towerCoeff`).  Both are engine-verified TRUE on the rank-1 free boson
(`certificates/mathematica/anmcirc_close.wl`): each side IS such a tower with weights independent of `M`
(U-side) resp. `P` (V-side).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Step 0 — the inner circle factor grade. -/

/-- The shift-`0` circle inner factor `c₍ᵢ₋₍ₙ₊₂₎₎d` lands in `𝒱_{M+P-(i-(n+2))-1}`. -/
theorem anmCirc_inner_mem_grading (W : VertexOperatorAlgebra 𝒱) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (n i : ℕ) :
    W.smul c ((i : ℤ) - ((n : ℤ) + 2)) d
      ∈ W.grading ((M : ℤ) + (P : ℤ) - ((i : ℤ) - ((n : ℤ) + 2)) - 1) :=
  W.smul_mem_grading hc hd ((i : ℤ) - ((n : ℤ) + 2))

/-! ## Step 1 — the residue-of-residue distributed over the inner circle index `i`. -/

/-- For homogeneous `c ∈ 𝒱_M`, the inner circle residue `resHom W 0 (n+2) c d` is
`∑ᵢ cbz M i • c₍ᵢ₋₍ₙ₊₂₎₎d` (`resHom_homogeneous`, `s = 0`, pole `n+2`); the outer residue
`resHom W 0 (n+1) (·) v` distributes (`resHom_add_left`/`resHom_smul_left`) into
`∑ᵢ cbz M i • resHom W 0 (n+1) (c₍ᵢ₋₍ₙ₊₂₎₎d) v`. -/
theorem anmCirc_resOfRes_distrib (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (d v : 𝒱) :
    resHom W 0 ((n : ℤ) + 1) (resHom W 0 ((n : ℤ) + 2) c d) v
      = ∑ i ∈ Finset.range (M + 1),
          cbz (M : ℤ) (i : ℤ)
            • resHom W 0 ((n : ℤ) + 1) (W.smul c ((i : ℤ) - ((n : ℤ) + 2)) d) v := by
  rw [resHom_homogeneous W 0 ((n : ℤ) + 2) hc d]
  simp only [add_zero]
  rw [show ((M : ℤ)).toNat + 1 = M + 1 from by simp]
  have hres0 : resHom W 0 ((n : ℤ) + 1) (0 : 𝒱) v = 0 := by
    have h := resHom_smul_left W 0 ((n : ℤ) + 1) (0 : ℂ) (0 : 𝒱) v
    rwa [zero_smul, zero_smul] at h
  induction (Finset.range (M + 1)) using Finset.induction with
  | empty => simp [hres0]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, resHom_add_left, resHom_smul_left, ih]

/-! ## Step 2 — the per-`i` inner residue iterate split (shift-`0`, NO `j`-sum). -/

/-- The per-`i` inner residue `resHom W 0 (n+1) (c₍ℓ₎d) v` (with `ℓ = i-(n+2)`), when the inner grade
`G := M+P-ℓ-1 ≥ 0`, expanded by `resHom_homogeneous` (single residue, pole `n+1`, weight `cbz G p`,
mode `p-(n+1)`) and split into the U/V `mode_iterate` finsum via `iterate_UV_split`.  The shift-`0`,
`j`-free mirror of `leftProd_circ_inner_UVterm`. -/
theorem anmCirc_inner_UVterm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P G : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (i : ℕ)
    (hG : (G : ℤ) = (M : ℤ) + (P : ℤ) - ((i : ℤ) - ((n : ℤ) + 2)) - 1) (v : 𝒱) :
    resHom W 0 ((n : ℤ) + 1) (W.smul c ((i : ℤ) - ((n : ℤ) + 2)) d) v
      = ∑ p ∈ Finset.range (G + 1),
          cbz (G : ℤ) (p : ℤ) •
            (∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - ((n : ℤ) + 2)) s) •
              (W.smul c (((i : ℤ) - ((n : ℤ) + 2)) - s)
                  (W.smul d (((p : ℤ) - ((n : ℤ) + 1)) + s) v)
                - ((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2)))
                  • W.smul d
                      (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - s)
                      (W.smul c (s : ℤ) v))) := by
  have hmem : W.smul c ((i : ℤ) - ((n : ℤ) + 2)) d ∈ W.grading (G : ℤ) := by
    rw [hG]; exact anmCirc_inner_mem_grading W hc hd n i
  rw [resHom_homogeneous W 0 ((n : ℤ) + 1) hmem v]
  simp only [add_zero]
  rw [show ((G : ℤ)).toNat + 1 = G + 1 from by simp]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  exact iterate_UV_split W c d v ((i : ℤ) - ((n : ℤ) + 2)) ((p : ℤ) - ((n : ℤ) + 1))

/-! ## Step 3 — the assembled residue-of-residue with negative-inner-grade guard. -/

/-- The full assembled U/V split of `resHom W 0 (n+1) (resHom W 0 (n+2) c d) v` over the circle index
`i`, residue index `p`, and `mode_iterate` index `s`, with the negative-inner-grade indices `i` (where
`c₍ᵢ₋₍ₙ₊₂₎₎d` vanishes) carried by an explicit `if`-guard.  The shift-`0`, `j`-free mirror of
`leftProd_circ_UV_assembly`. -/
theorem anmCirc_resOfRes_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (v : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1) :
    resHom W 0 ((n : ℤ) + 1) (resHom W 0 ((n : ℤ) + 2) c d) v
      = ∑ i ∈ Finset.range (M + 1),
          cbz (M : ℤ) (i : ℤ) •
            (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 then
              ∑ p ∈ Finset.range (G i + 1),
                cbz ((G i : ℤ)) (p : ℤ) •
                  (∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - ((n : ℤ) + 2)) s) •
                    (W.smul c (((i : ℤ) - ((n : ℤ) + 2)) - s)
                        (W.smul d (((p : ℤ) - ((n : ℤ) + 1)) + s) v)
                      - ((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2)))
                        • W.smul d
                            (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - s)
                            (W.smul c (s : ℤ) v)))
            else 0) := by
  rw [anmCirc_resOfRes_distrib W n hc d v]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  rcases lt_or_ge ((M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1) 0 with hlt | hge
  · rw [if_neg (not_le.mpr hlt)]
    have hmem : W.smul c ((i : ℤ) - ((n : ℤ) + 2)) d
        ∈ W.grading ((M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1) :=
      anmCirc_inner_mem_grading W hc hd n i
    rw [W.positivity _ hlt, Submodule.mem_bot] at hmem
    rw [hmem]
    have h := resHom_smul_left W 0 ((n : ℤ) + 1) (0 : ℂ) (0 : 𝒱) v
    rwa [zero_smul, zero_smul] at h
  · rw [if_pos hge]
    exact anmCirc_inner_UVterm W n hc hd i (G := G i) (hG i hi hge) v

/-! ## Step 4 — the U/V sides and the master split. -/

/-- The per-`(i,p)` leading scalar of the shift-`0` assembly body (shared U/V), guarded by the `if`
that kills the negative-inner-grade circle indices `i`.  Shift-`0` circle weight `cbz M i`, mode
`i-(n+2)`; NO FZ scalar; inner residue `cbz(G_i, p)`, mode `p-(n+1)`. -/
noncomputable def assemblyLeadAnm (M P n : ℕ) (G : ℕ → ℕ) (i p : ℕ) : ℂ :=
  if 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 then
    cbz (M : ℤ) (i : ℤ) * cbz ((G i : ℤ)) (p : ℤ)
  else 0

/-- The shift-`0` **U-side**: all `c₍(i-(n+2))-s₎(d₍(p-(n+1))+s₎v)` terms.  Base-mode
`γ = (p-(n+1))+s`, mode `μ = (i-(n+2))-s`; `mode_iterate` coefficient `(-1)^s · gBinom (i-(n+2)) s`. -/
noncomputable def USideAnm (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱) (G : ℕ → ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (M + 1),
    ∑ p ∈ Finset.range (G i + 1),
      ∑ᶠ s : ℕ,
        (assemblyLeadAnm M P n G i p * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - ((n : ℤ) + 2)) s))
          • W.smul c (((i : ℤ) - ((n : ℤ) + 2)) - s)
              (W.smul d (((p : ℤ) - ((n : ℤ) + 1)) + s) v)

/-- The shift-`0` **V-side**: all `d₍(i-(n+2))+(p-(n+1))-s₎(c₍s₎v)` terms (sign `(-1)^(i-(n+2))`).
Base-mode `γ = s` (`s : ℕ`, so `≥ 0`), mode `μ = (i-(n+2))+(p-(n+1))-s`. -/
noncomputable def VSideAnm (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱) (G : ℕ → ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (M + 1),
    ∑ p ∈ Finset.range (G i + 1),
      ∑ᶠ s : ℕ,
        (assemblyLeadAnm M P n G i p * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - ((n : ℤ) + 2)) s)
            * ((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2))))
          • W.smul d (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - s)
              (W.smul c (s : ℤ) v)

/-- **The shift-`0` master split** `resHom W 0 (n+1) (resHom W 0 (n+2) c d) v = USideAnm − VSideAnm`.
Shift-`0`, `j`-free mirror of `leftProd_circ_eq_USideLn_sub_VSideLn`.  From `anmCirc_resOfRes_homog`,
pull the leading per-`(i,p)` scalars into the `∑ᶠ s`-finsum, then split each finsum body
`coef_s • (Uword − sv•Vword)` into the U-part and the V-part (`smul_finsum'` + `finsum_sub_distrib`,
valid by `USideL_s_fin`/`VSideL_s_fin`). -/
theorem anmRight_zero_anmCirc_eq_USideAnm_sub_VSideAnm (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    {M P : ℕ} {c d : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (v : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1) :
    resHom W 0 ((n : ℤ) + 1) (resHom W 0 ((n : ℤ) + 2) c d) v
      = USideAnm W M P n c d v G - VSideAnm W M P n c d v G := by
  rw [anmCirc_resOfRes_homog W n hc hd v G hG, USideAnm, VSideAnm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases lt_or_ge ((M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1) 0 with hlt | hge
  · rw [if_neg (not_le.mpr hlt), smul_zero]
    simp only [assemblyLeadAnm, if_neg (not_le.mpr hlt), zero_mul, zero_smul,
      finsum_zero, Finset.sum_const_zero]
    rw [sub_zero]
  · rw [if_pos hge, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    set ℓ : ℤ := (i : ℤ) - ((n : ℤ) + 2) with hℓ
    set N : ℤ := (p : ℤ) - ((n : ℤ) + 1) with hN
    set lead : ℂ := assemblyLeadAnm M P n G i p with hlead
    have hlead_val : assemblyLeadAnm M P n G i p
        = cbz (M : ℤ) (i : ℤ) * cbz ((G i : ℤ)) (p : ℤ) := by
      rw [assemblyLeadAnm, if_pos hge]
    rw [show cbz (M : ℤ) (i : ℤ)
            • (cbz ((G i : ℤ)) (p : ℤ)
                • ∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ℓ s) •
                    (W.smul c (ℓ - s) (W.smul d (N + s) v)
                      - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) v)))
          = lead • ∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ℓ s) •
                (W.smul c (ℓ - s) (W.smul d (N + s) v)
                  - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) v)) from by
        rw [smul_smul, hlead, hlead_val]]
    have hfin_body : Function.HasFiniteSupport (fun s : ℕ =>
        ((-1 : ℂ) ^ s * gBinom ℓ s) •
          (W.smul c (ℓ - s) (W.smul d (N + s) v)
            - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) v))) := by
      obtain ⟨Nd, hNd⟩ := W.regularity d v
      obtain ⟨Nc, hNc⟩ := W.regularity c v
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
      rw [show W.smul d (N + (s : ℤ)) v = (0 : 𝒱) from hNd _ (by omega),
        show W.smul c (s : ℤ) v = (0 : 𝒱) from hNc _ (by omega)]
      simp only [PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero]
    rw [smul_finsum' lead hfin_body]
    rw [show (∑ᶠ s : ℕ, lead • ((-1 : ℂ) ^ s * gBinom ℓ s) •
              (W.smul c (ℓ - s) (W.smul d (N + s) v)
                - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) v)))
          = ∑ᶠ s : ℕ, ((lead * ((-1 : ℂ) ^ s * gBinom ℓ s)) • W.smul c (ℓ - s) (W.smul d (N + s) v)
              - (lead * ((-1 : ℂ) ^ s * gBinom ℓ s) * ((-1 : ℂ) ^ ℓ))
                  • W.smul d (ℓ + N - s) (W.smul c (s : ℤ) v)) from
        finsum_congr fun s => by
          rw [smul_smul, smul_sub, smul_smul, mul_assoc]]
    rw [finsum_sub_distrib
        (USideL_s_fin W c d v (fun s => lead * ((-1 : ℂ) ^ s * gBinom ℓ s)) ℓ N)
        (VSideL_s_fin W c d v
          (fun s => lead * ((-1 : ℂ) ^ s * gBinom ℓ s) * ((-1 : ℂ) ^ ℓ)) (ℓ + N))]

/-! ## Step 5 — the γ-outer mode-value forms (base-mode `γ` ⊗ mode `μ`). -/

/-- The per-`(i,p)` shift-`0` U-side coefficient of `c₍ℓ+N-γ₎(d₍γ₎v)` (`ℓ = i-(n+2)`, `N = p-(n+1)`)
after the `UwordL_reindex` base-mode reindex.  Shift-`0` mirror of `UgammaCoeffLn`. -/
noncomputable def UgammaCoeffAnm (M P n : ℕ) (G : ℕ → ℕ) (i p : ℕ) (γ : ℤ) : ℂ :=
  if (p : ℤ) - ((n : ℤ) + 1) ≤ γ then
    assemblyLeadAnm M P n G i p
      * ((-1 : ℂ) ^ ((γ - ((p : ℤ) - ((n : ℤ) + 1))).toNat)
          * gBinom ((i : ℤ) - ((n : ℤ) + 2))
              (γ - ((p : ℤ) - ((n : ℤ) + 1))).toNat)
  else 0

/-- The per-`(i,p)` U-word γ-body has finite support. -/
theorem UgammaCoeffAnm_body_fin (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱) (G : ℕ → ℕ)
    (i p : ℕ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      UgammaCoeffAnm M P n G i p γ
        • W.smul c (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
            (W.smul d γ v)) :=
  UgammaL_fin W c d v
    (fun s => assemblyLeadAnm M P n G i p
      * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - ((n : ℤ) + 2)) s))
    ((i : ℤ) - ((n : ℤ) + 2)) ((p : ℤ) - ((n : ℤ) + 1))

/-- The per-`(i,p)` shift-`0` V-side coefficient of `d₍ℓ+N-γ₎(c₍γ₎v)` (`M₀ = ℓ+N`).  Shift-`0`
mirror of `VgammaCoeffLn`. -/
noncomputable def VgammaCoeffAnm (M P n : ℕ) (G : ℕ → ℕ) (i p : ℕ) (γ : ℤ) : ℂ :=
  if 0 ≤ γ then
    assemblyLeadAnm M P n G i p
      * ((-1 : ℂ) ^ γ.toNat * gBinom ((i : ℤ) - ((n : ℤ) + 2)) γ.toNat)
      * ((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2)))
  else 0

/-- The per-`(i,p)` V-word γ-body has finite support. -/
theorem VgammaCoeffAnm_body_fin (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱) (G : ℕ → ℕ)
    (i p : ℕ) :
    Function.HasFiniteSupport (fun γ : ℤ =>
      VgammaCoeffAnm M P n G i p γ
        • W.smul d (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
            (W.smul c γ v)) :=
  VgammaL_fin W c d v
    (fun s => assemblyLeadAnm M P n G i p
      * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - ((n : ℤ) + 2)) s)
      * ((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2))))
    (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)))

/-- **The shift-`0` U-side γ-outer mode-value form.** -/
theorem USideAnm_eq_gammaSum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱) (G : ℕ → ℕ) :
    USideAnm W M P n c d v G
      = ∑ᶠ γ : ℤ, ∑ i ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (G i + 1),
          UgammaCoeffAnm M P n G i p γ
            • W.smul c (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
                (W.smul d γ v) := by
  rw [USideAnm]
  rw [show (∑ i ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (G i + 1),
            ∑ᶠ s : ℕ,
              (assemblyLeadAnm M P n G i p
                  * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - ((n : ℤ) + 2)) s))
                • W.smul c (((i : ℤ) - ((n : ℤ) + 2)) - s)
                    (W.smul d (((p : ℤ) - ((n : ℤ) + 1)) + s) v))
        = ∑ i ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (G i + 1),
            ∑ᶠ γ : ℤ, UgammaCoeffAnm M P n G i p γ
              • W.smul c (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
                  (W.smul d γ v) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by
        rw [UwordL_reindex W c d v
          (fun s => assemblyLeadAnm M P n G i p
            * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - ((n : ℤ) + 2)) s))
          ((i : ℤ) - ((n : ℤ) + 2)) ((p : ℤ) - ((n : ℤ) + 1))]
        exact finsum_congr fun γ => by rw [UgammaCoeffAnm]]
  rw [finsum_sum_comm (Finset.range (M + 1))
      (fun γ i => ∑ p ∈ Finset.range (G i + 1),
        UgammaCoeffAnm M P n G i p γ
          • W.smul c (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
              (W.smul d γ v))
      (fun i _ => hasFinSupp_finsetSumL (Finset.range (G i + 1)) _ (fun p _ =>
        UgammaCoeffAnm_body_fin W M P n c d v G i p))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_sum_comm (Finset.range (G i + 1))
      (fun γ p => UgammaCoeffAnm M P n G i p γ
          • W.smul c (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
              (W.smul d γ v))
      (fun p _ => UgammaCoeffAnm_body_fin W M P n c d v G i p)]

/-- **The shift-`0` V-side γ-outer mode-value form.** -/
theorem VSideAnm_eq_gammaSum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱) (G : ℕ → ℕ) :
    VSideAnm W M P n c d v G
      = ∑ᶠ γ : ℤ, ∑ i ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (G i + 1),
          VgammaCoeffAnm M P n G i p γ
            • W.smul d (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
                (W.smul c γ v) := by
  rw [VSideAnm]
  rw [show (∑ i ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (G i + 1),
            ∑ᶠ s : ℕ,
              (assemblyLeadAnm M P n G i p
                  * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - ((n : ℤ) + 2)) s)
                  * ((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2))))
                • W.smul d (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - s)
                    (W.smul c (s : ℤ) v))
        = ∑ i ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (G i + 1),
            ∑ᶠ γ : ℤ, VgammaCoeffAnm M P n G i p γ
              • W.smul d (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
                  (W.smul c γ v) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by
        rw [VwordL_reindex W c d v
          (fun s => assemblyLeadAnm M P n G i p
            * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - ((n : ℤ) + 2)) s)
            * ((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2))))
          (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)))]
        exact finsum_congr fun γ => by rw [VgammaCoeffAnm]]
  rw [finsum_sum_comm (Finset.range (M + 1))
      (fun γ i => ∑ p ∈ Finset.range (G i + 1),
        VgammaCoeffAnm M P n G i p γ
          • W.smul d (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
              (W.smul c γ v))
      (fun i _ => hasFinSupp_finsetSumL (Finset.range (G i + 1)) _ (fun p _ =>
        VgammaCoeffAnm_body_fin W M P n c d v G i p))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_sum_comm (Finset.range (G i + 1))
      (fun γ p => VgammaCoeffAnm M P n G i p γ
          • W.smul d (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
              (W.smul c γ v))
      (fun p _ => VgammaCoeffAnm_body_fin W M P n c d v G i p)]

/-! ## Step 6 — the per-`γ` mode collection and the double-finsum forms. -/

/-- The net per-`(γ,μ)` shift-`0` U-side scalar: the finite `(i,p)`-sum of `UgammaCoeffAnm` whose
`mode_iterate` mode value `(i-(n+2))+(p-(n+1))-γ` equals `μ`.  Shift-`0` mirror of
`UgammaModeCollLn`. -/
noncomputable def UgammaModeCollAnm (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (G i + 1),
    (if μ = ((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ
      then UgammaCoeffAnm M P n G i p γ else 0)

/-- The net per-`(γ,μ)` shift-`0` V-side scalar.  Shift-`0` mirror of `VgammaModeCollLn`. -/
noncomputable def VgammaModeCollAnm (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (G i + 1),
    (if μ = ((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ
      then VgammaCoeffAnm M P n G i p γ else 0)

/-- **Per-`γ` shift-`0` U-side mode collection.**  Shift-`0` mirror of `gammaBodyL_eq_muSum_U`. -/
theorem gammaBodyAnm_eq_muSum_U (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱) (G : ℕ → ℕ)
    (γ : ℤ) :
    (∑ i ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (G i + 1),
        UgammaCoeffAnm M P n G i p γ
          • W.smul c (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
              (W.smul d γ v))
      = ∑ᶠ μ : ℤ, UgammaModeCollAnm M P n G γ μ • W.smul c μ (W.smul d γ v) := by
  rw [show (∑ i ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (G i + 1),
            UgammaCoeffAnm M P n G i p γ
              • W.smul c (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
                  (W.smul d γ v))
        = ∑ i ∈ Finset.range (M + 1),
            ∑ᶠ μ : ℤ, ∑ p ∈ Finset.range (G i + 1),
                (if μ = ((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ
                  then UgammaCoeffAnm M P n G i p γ else 0)
                  • W.smul c μ (W.smul d γ v) from
      Finset.sum_congr rfl fun i _ => by
        rw [show (∑ p ∈ Finset.range (G i + 1),
                  UgammaCoeffAnm M P n G i p γ
                    • W.smul c (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
                        (W.smul d γ v))
              = ∑ p ∈ Finset.range (G i + 1),
                  ∑ᶠ μ : ℤ, (if μ = ((i : ℤ) - ((n : ℤ) + 2))
                        + ((p : ℤ) - ((n : ℤ) + 1)) - γ
                      then UgammaCoeffAnm M P n G i p γ else 0) • W.smul c μ (W.smul d γ v) from
            Finset.sum_congr rfl fun p _ =>
              usingleL_eq_muFinsum W c d v (UgammaCoeffAnm M P n G i p γ)
                (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ) γ]
        rw [← finsum_sum_comm (Finset.range (G i + 1))
            (fun μ p => (if μ = ((i : ℤ) - ((n : ℤ) + 2))
                  + ((p : ℤ) - ((n : ℤ) + 1)) - γ
                then UgammaCoeffAnm M P n G i p γ else 0) • W.smul c μ (W.smul d γ v))
            (fun p _ => umuL_indicator_fin W c d v (UgammaCoeffAnm M P n G i p γ) _ γ)]]
  rw [← finsum_sum_comm (Finset.range (M + 1))
      (fun μ i => ∑ p ∈ Finset.range (G i + 1),
          (if μ = ((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ
            then UgammaCoeffAnm M P n G i p γ else 0) • W.smul c μ (W.smul d γ v))
      (fun i _ => hasFinSupp_finsetSumL (Finset.range (G i + 1)) _ (fun p _ =>
        umuL_indicator_fin W c d v (UgammaCoeffAnm M P n G i p γ) _ γ))]
  refine finsum_congr fun μ => ?_
  rw [UgammaModeCollAnm, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]

/-- **Per-`γ` shift-`0` V-side mode collection.**  Shift-`0` mirror of `gammaBodyL_eq_muSum_V`. -/
theorem gammaBodyAnm_eq_muSum_V (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱) (G : ℕ → ℕ)
    (γ : ℤ) :
    (∑ i ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (G i + 1),
        VgammaCoeffAnm M P n G i p γ
          • W.smul d (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
              (W.smul c γ v))
      = ∑ᶠ μ : ℤ, VgammaModeCollAnm M P n G γ μ • W.smul d μ (W.smul c γ v) := by
  rw [show (∑ i ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (G i + 1),
            VgammaCoeffAnm M P n G i p γ
              • W.smul d (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
                  (W.smul c γ v))
        = ∑ i ∈ Finset.range (M + 1),
            ∑ᶠ μ : ℤ, ∑ p ∈ Finset.range (G i + 1),
                (if μ = ((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ
                  then VgammaCoeffAnm M P n G i p γ else 0)
                  • W.smul d μ (W.smul c γ v) from
      Finset.sum_congr rfl fun i _ => by
        rw [show (∑ p ∈ Finset.range (G i + 1),
                  VgammaCoeffAnm M P n G i p γ
                    • W.smul d (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
                        (W.smul c γ v))
              = ∑ p ∈ Finset.range (G i + 1),
                  ∑ᶠ μ : ℤ, (if μ = ((i : ℤ) - ((n : ℤ) + 2))
                        + ((p : ℤ) - ((n : ℤ) + 1)) - γ
                      then VgammaCoeffAnm M P n G i p γ else 0) • W.smul d μ (W.smul c γ v) from
            Finset.sum_congr rfl fun p _ =>
              vsingleL_eq_muFinsum W c d v (VgammaCoeffAnm M P n G i p γ)
                (((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ) γ]
        rw [← finsum_sum_comm (Finset.range (G i + 1))
            (fun μ p => (if μ = ((i : ℤ) - ((n : ℤ) + 2))
                  + ((p : ℤ) - ((n : ℤ) + 1)) - γ
                then VgammaCoeffAnm M P n G i p γ else 0) • W.smul d μ (W.smul c γ v))
            (fun p _ => vmuL_indicator_fin W c d v (VgammaCoeffAnm M P n G i p γ) _ γ)]]
  rw [← finsum_sum_comm (Finset.range (M + 1))
      (fun μ i => ∑ p ∈ Finset.range (G i + 1),
          (if μ = ((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ
            then VgammaCoeffAnm M P n G i p γ else 0) • W.smul d μ (W.smul c γ v))
      (fun i _ => hasFinSupp_finsetSumL (Finset.range (G i + 1)) _ (fun p _ =>
        vmuL_indicator_fin W c d v (VgammaCoeffAnm M P n G i p γ) _ γ))]
  refine finsum_congr fun μ => ?_
  rw [VgammaModeCollAnm, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]

/-- **`USideAnm` as a base-mode ⊗ mode double finsum.** -/
theorem USideAnm_eq_gammaModeFinsum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱)
    (G : ℕ → ℕ) :
    USideAnm W M P n c d v G
      = ∑ᶠ γ : ℤ, ∑ᶠ μ : ℤ, UgammaModeCollAnm M P n G γ μ • W.smul c μ (W.smul d γ v) := by
  rw [USideAnm_eq_gammaSum]
  exact finsum_congr fun γ => gammaBodyAnm_eq_muSum_U W M P n c d v G γ

/-- **`VSideAnm` as a base-mode ⊗ mode double finsum.** -/
theorem VSideAnm_eq_gammaModeFinsum (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱)
    (G : ℕ → ℕ) :
    VSideAnm W M P n c d v G
      = ∑ᶠ γ : ℤ, ∑ᶠ μ : ℤ, VgammaModeCollAnm M P n G γ μ • W.smul d μ (W.smul c γ v) := by
  rw [VSideAnm_eq_gammaSum]
  exact finsum_congr fun γ => gammaBodyAnm_eq_muSum_V W M P n c d v G γ

/-! ## Step 7 — the shift-`0` tower-family mode-value forms (mirror of Descent9). -/

/-- The shift-`0` per-`(γ,μ)` tower weight collected from a `δ`-indexed `PresAnm`-tower family
(depth `< Δ`, grade `M`, level `n`).  Shift-`0` analogue of `towerCoeff` (weight `cbz(M+δ,
μ+(n+2)+δ)`, NOT `cbz(M+n+δ, μ+2n+2+δ)`). -/
noncomputable def towerCoeffAnm (M n : ℕ) (wt : ℕ → ℂ) (Δ : ℕ) (μ : ℤ) : ℂ :=
  ∑ δ ∈ Finset.range Δ, wt δ * cbz ((M : ℤ) + δ) (μ + (n + 2) + δ)

/-- `PresAnm W M n d u v` in mode-value finsum form (mode `μ = i-(n+2)-d`):
`∑ᶠ μ, cbz(M+d, μ+(n+2)+d) • u₍μ₎v`.  Shift-`0` analogue of `PresOn_eq_finsum`. -/
theorem PresAnm_eq_finsum (W : VertexOperatorAlgebra 𝒱) (M n d : ℕ) (u v : 𝒱) :
    PresAnm W M n d u v
      = ∑ᶠ μ : ℤ, cbz ((M : ℤ) + d) (μ + (n + 2) + d) • W.smul u μ v := by
  unfold PresAnm
  rw [show (∑ i ∈ Finset.range (M + d + 1),
            cbz ((M : ℤ) + d) (i : ℤ) • W.smul u ((i : ℤ) - ((n : ℤ) + 2) - d) v)
        = ∑ i ∈ Finset.range (M + d + 1),
            cbz ((M : ℤ) + d) (i : ℤ) • W.smul u ((i : ℤ) + (-((n : ℤ) + 2) - d)) v from
      Finset.sum_congr rfl fun i _ => by
        rw [show (i : ℤ) - ((n : ℤ) + 2) - d = (i : ℤ) + (-((n : ℤ) + 2) - d) from by ring]]
  rw [ZhuHR.rangeSmul_eq_finsumZ (fun q : ℤ => cbz ((M : ℤ) + d) q)
      (fun q => W.smul u q v) (-((n : ℤ) + 2) - d)
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by positivity) (by push_cast at hq ⊢; omega))]
  rw [← finsum_comp_equiv (Equiv.addRight (-((n : ℤ) + 2) - (d : ℤ)))
      (f := fun μ : ℤ => cbz ((M : ℤ) + d) (μ + (n + 2) + d) • W.smul u μ v)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + (-((n : ℤ) + 2) - (d : ℤ))) + (n + 2) + d = q from by push_cast; ring]

/-- **Per-base-mode `PresAnm`-tower-family collapse.**  A finite `δ`-indexed `PresAnm`-tower family
based at a fixed vector `base` collapses to `∑ᶠ μ, towerCoeffAnm … μ • w₍μ₎base`.  Shift-`0` analogue
of `presOnFamily_eq_finsum`. -/
theorem presAnmFamily_eq_finsum (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (w base : 𝒱)
    (wt : ℕ → ℂ) (Δ : ℕ) :
    (∑ δ ∈ Finset.range Δ, wt δ • PresAnm W M n δ w base)
      = ∑ᶠ μ : ℤ, towerCoeffAnm M n wt Δ μ • W.smul w μ base := by
  rw [show (∑ δ ∈ Finset.range Δ, wt δ • PresAnm W M n δ w base)
        = ∑ δ ∈ Finset.range Δ,
            ∑ᶠ μ : ℤ, (wt δ * cbz ((M : ℤ) + δ) (μ + (n + 2) + δ)) • W.smul w μ base from
      Finset.sum_congr rfl fun δ _ => by
        rw [PresAnm_eq_finsum W M n δ w base]
        have hfin : Function.HasFiniteSupport
            (fun μ : ℤ => cbz ((M : ℤ) + δ) (μ + (n + 2) + δ) • W.smul w μ base) :=
          ZhuHR.smul_support_of_scalar W w base _
            (Set.Finite.subset
              (ZhuHR.cbz_shift_support_fin (d := (M : ℤ) + δ) (by positivity)
                ((n : ℤ) + 2 + δ))
              (fun μ hμ => by
                rw [Function.mem_support] at hμ ⊢
                intro h; apply hμ
                rwa [show μ + ((n : ℤ) + 2) + (δ : ℤ) = μ + ((n : ℤ) + 2 + (δ : ℤ)) from
                  by ring]))
        rw [smul_finsum' (wt δ) hfin]
        refine finsum_congr fun μ => ?_
        rw [smul_smul]]
  rw [← finsum_sum_comm (Finset.range Δ)
      (fun μ δ => (wt δ * cbz ((M : ℤ) + δ) (μ + (n + 2) + δ)) • W.smul w μ base)
      (fun δ _ => ZhuHR.smul_support_of_scalar W w base _
        (Set.Finite.subset
          (ZhuHR.cbz_shift_support_fin (d := (M : ℤ) + δ) (by positivity) ((n : ℤ) + 2 + δ))
          (fun μ hμ => by
            rw [Function.mem_support] at hμ ⊢
            intro h; apply hμ
            rw [show μ + ((n : ℤ) + 2) + (δ : ℤ) = μ + ((n : ℤ) + 2 + (δ : ℤ)) from by ring,
              h, mul_zero])))]
  refine finsum_congr fun μ => ?_
  rw [towerCoeffAnm, Finset.sum_smul]

/-- **`UfamAnm` mode-value form.**  `UfamAnm` rewrites as a finite base-mode sum of mode-value finsums
of `c₍μ₎(d₍γ₎v)`, the tower weight at `(γ, μ)` being `towerCoeffAnm M n (wU (γ₀+g)) Δ μ`. -/
theorem UfamAnm_eq_finsum (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (c d v : 𝒱)
    (wU : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) :
    UfamAnm W M n c d v wU γ₀ Γ Δ
      = ∑ g ∈ Finset.range Γ,
          ∑ᶠ μ : ℤ, towerCoeffAnm M n (wU (γ₀ + (g : ℤ))) Δ μ
            • W.smul c μ (W.smul d (γ₀ + (g : ℤ)) v) := by
  rw [UfamAnm]
  refine Finset.sum_congr rfl fun g _ => ?_
  exact presAnmFamily_eq_finsum W M n c (W.smul d (γ₀ + (g : ℤ)) v) (wU (γ₀ + (g : ℤ))) Δ

/-- **`VfamAnm` mode-value form.** -/
theorem VfamAnm_eq_finsum (W : VertexOperatorAlgebra 𝒱) (P n : ℕ) (c d v : 𝒱)
    (wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) :
    VfamAnm W P n c d v wV γ₀ Γ Δ
      = ∑ g ∈ Finset.range Γ,
          ∑ᶠ μ : ℤ, towerCoeffAnm P n (wV (γ₀ + (g : ℤ))) Δ μ
            • W.smul d μ (W.smul c (γ₀ + (g : ℤ)) v) := by
  rw [VfamAnm]
  refine Finset.sum_congr rfl fun g _ => ?_
  exact presAnmFamily_eq_finsum W P n d (W.smul c (γ₀ + (g : ℤ)) v) (wV (γ₀ + (g : ℤ))) Δ

/-! ## Step 8 — `AnmCircTowerEq` from the two side-collapses. -/

/-- **`AnmCircTowerEq` from the U-side / V-side tower-collapse.**  If, for some grade witness `G`
matching the inner circle grades, the U-side `USideAnm` equals the U-family `UfamAnm W M n c d v wU …`
and the V-side `VSideAnm` equals the *negated* V-family `−VfamAnm W P n c d v wV …`, then
`AnmCircTowerEq W n M P c d v` holds (via the master split
`anmRight_zero_anmCirc_eq_USideAnm_sub_VSideAnm` + `anmRight_zero`/`anmCirc_zero`).  Shift-`0` mirror
of `LeftCircTowerEqn_of_sides`. -/
theorem AnmCircTowerEq_of_sides (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (v : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1)
    (wU wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ)
    (hU : USideAnm W M P n c d v G = UfamAnm W M n c d v wU γ₀ Γ Δ)
    (hV : VSideAnm W M P n c d v G = -VfamAnm W P n c d v wV γ₀ Γ Δ) :
    AnmCircTowerEq W n M P c d v := by
  refine ⟨wU, wV, γ₀, Γ, Δ, ?_⟩
  rw [anmRight_zero, anmCirc_zero,
    anmRight_zero_anmCirc_eq_USideAnm_sub_VSideAnm W n hc hd v G hG, hU, hV, sub_neg_eq_add]

/-! ## Step 9 — the U-core scalar collapse `UgammaModeCollAnm = towerCoeffAnm` (`j`-free).

Shift-`0`, `j`-free mirror of `ZhuVermaAnArchL1Close.UgammaModeCollLn_eq_towerCoeff` (ports
`ZhuVermaAnDescent19`).  The inner `p`-finset collapses (single substituted index `p₀ = μ-i+2n+3+γ`,
peeling index `s = (i-(n+2))-μ`) to the single-`i`-sum `InnerIAnm`, then the
`cbz_symm`/`vandermonde_range_top`/`trinom_symm`/`SR_collapse`/`tower_swap` chain (carrier `P+n+1`,
base `M`) collapses it to the grade-`M` tower `towerCoeffAnm M n (wUAnm P n γ) Δ μ`. -/

/-- The substituted residue index `p₀` forced by the mode-match `μ = (i-(n+2))+(p-(n+1))-γ`. -/
private def rSubAnm (n i : ℕ) (γ μ : ℤ) : ℤ := μ - (i : ℤ) + 2 * (n : ℤ) + 3 + γ

/-- The per-`i` direct U-scalar (the `p`-collapsed `UgammaCoeffAnm`): `cbz M i` times the middle
inner-residue binomial `cbz(G_i, p₀)` (guarded by `G_i ≥ 0`) times the peeling reflection
`cbz(-μ-1, (i-(n+2))-μ)` (via `uIter_eq_cbz`). -/
noncomputable def directUCoeffAnm (M P n : ℕ) (G : ℕ → ℕ) (i : ℕ) (γ μ : ℤ) : ℂ :=
  cbz (M : ℤ) (i : ℤ)
    * (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1
        then cbz ((G i : ℤ)) (rSubAnm n i γ μ) else 0)
    * cbz (-μ - 1) (((i : ℤ) - ((n : ℤ) + 2)) - μ)

/-- **Matched-term identity (U).**  When `(p : ℤ) = rSubAnm n i γ μ`, the per-`(i,p)` U-coefficient
`UgammaCoeffAnm M P n G i p γ` equals `directUCoeffAnm M P n G i γ μ`. -/
theorem UgammaCoeffAnm_at_rSub (M P n : ℕ) (G : ℕ → ℕ) (i p : ℕ) (γ μ : ℤ)
    (hr : (p : ℤ) = rSubAnm n i γ μ) :
    UgammaCoeffAnm M P n G i p γ = directUCoeffAnm M P n G i γ μ := by
  have hN : (p : ℤ) - ((n : ℤ) + 1) = γ + (μ - ((i : ℤ) - ((n : ℤ) + 2))) := by
    rw [hr, rSubAnm]; ring
  have hdiff : γ - ((p : ℤ) - ((n : ℤ) + 1)) = ((i : ℤ) - ((n : ℤ) + 2)) - μ := by rw [hN]; ring
  rw [UgammaCoeffAnm, directUCoeffAnm, assemblyLeadAnm]
  by_cases hguard : (p : ℤ) - ((n : ℤ) + 1) ≤ γ
  · rw [if_pos hguard, hdiff]
    have hmu : μ ≤ (i : ℤ) - ((n : ℤ) + 2) := by rw [hN] at hguard; omega
    have hpeel : ((-1 : ℂ) ^ (((i : ℤ) - ((n : ℤ) + 2)) - μ).toNat
          * gBinom ((i : ℤ) - ((n : ℤ) + 2)) (((i : ℤ) - ((n : ℤ) + 2)) - μ).toNat)
        = cbz (-μ - 1) (((i : ℤ) - ((n : ℤ) + 2)) - μ) := by
      have := uIter_eq_cbz ((i : ℤ) - ((n : ℤ) + 2)) μ
      rwa [if_pos hmu] at this
    by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1
    · rw [if_pos hgr, if_pos hgr, hpeel, show (p : ℤ) = rSubAnm n i γ μ from hr]
    · rw [if_neg hgr, if_neg hgr, hpeel]; ring
  · rw [if_neg hguard]
    have hmu : (i : ℤ) - ((n : ℤ) + 2) - μ < 0 := by rw [hN] at hguard; omega
    rw [cbz_apply_neg (-μ - 1) hmu]
    by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1
    · rw [if_pos hgr]; ring
    · rw [if_neg hgr]; ring

/-- **Inner `p`-finset collapse (U).**  The `p`-sum of the mode-matched `UgammaCoeffAnm` collapses to
the single `directUCoeffAnm`.  Shift-`0`, `j`-free mirror of `UinnerLn_collapse`. -/
theorem UinnerAnm_collapse (M P n : ℕ) (G : ℕ → ℕ) (i : ℕ) (γ μ : ℤ)
    (hG : 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1) :
    (∑ p ∈ Finset.range (G i + 1),
        (if μ = ((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ
          then UgammaCoeffAnm M P n G i p γ else 0))
      = directUCoeffAnm M P n G i γ μ := by
  have hcond : ∀ p : ℕ,
      (μ = ((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
        ↔ ((p : ℤ) = rSubAnm n i γ μ) := by
    intro p; rw [rSubAnm]; constructor <;> intro h <;> omega
  rw [Finset.sum_congr rfl fun p _ => by rw [show (if μ = ((i : ℤ) - ((n : ℤ) + 2))
        + ((p : ℤ) - ((n : ℤ) + 1)) - γ then UgammaCoeffAnm M P n G i p γ else 0)
      = (if (p : ℤ) = rSubAnm n i γ μ then UgammaCoeffAnm M P n G i p γ else 0) from by
        simp only [hcond p]]]
  by_cases hpos : 0 ≤ rSubAnm n i γ μ
  · set p₀ : ℕ := (rSubAnm n i γ μ).toNat with hp₀
    have hp₀cast : (p₀ : ℤ) = rSubAnm n i γ μ := by rw [hp₀, Int.toNat_of_nonneg hpos]
    by_cases hmem : p₀ ∈ Finset.range (G i + 1)
    · rw [Finset.sum_eq_single_of_mem p₀ hmem
        (fun p _ hne => by
          rw [if_neg (by
            intro hc; exact hne (by
              have : (p : ℤ) = (p₀ : ℤ) := by rw [hp₀cast, hc]
              exact_mod_cast this))])]
      rw [if_pos hp₀cast, UgammaCoeffAnm_at_rSub M P n G i p₀ γ μ hp₀cast]
    · have hgt : (G i : ℤ) < rSubAnm n i γ μ := by
        rw [Finset.mem_range] at hmem
        have : G i + 1 ≤ p₀ := by omega
        have hle : ((G i + 1 : ℕ) : ℤ) ≤ (p₀ : ℤ) := by exact_mod_cast this
        rw [hp₀cast] at hle; push_cast at hle; omega
      rw [Finset.sum_eq_zero fun p hp => by
        rw [if_neg (by
          rw [Finset.mem_range] at hp
          intro hc
          have hple : p ≤ G i := by omega
          have hle : (p : ℤ) ≤ (G i : ℤ) := by exact_mod_cast hple
          rw [hc] at hle; omega)]]
      rw [directUCoeffAnm]
      by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1
      · rw [if_pos hgr, cbz_zero_off_range (A := (G i : ℤ)) (by rw [hG hgr]; omega)
          (Or.inr (by omega))]; ring
      · rw [if_neg hgr]; ring
  · replace hpos : rSubAnm n i γ μ < 0 := not_le.mp hpos
    rw [Finset.sum_eq_zero fun p _ => by
      rw [if_neg (by
        intro hc
        have : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
        rw [hc] at this; omega)]]
    rw [directUCoeffAnm]
    by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1
    · rw [if_pos hgr, cbz_apply_neg ((G i : ℤ)) (by omega)]; ring
    · rw [if_neg hgr]; ring

/-- **`UgammaModeCollAnm` as the direct single-`i`-sum.** -/
theorem UgammaModeCollAnm_eq_directSum (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1)
    (γ μ : ℤ) :
    UgammaModeCollAnm M P n G γ μ
      = ∑ i ∈ Finset.range (M + 1), directUCoeffAnm M P n G i γ μ := by
  rw [UgammaModeCollAnm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact UinnerAnm_collapse M P n G i γ μ (hG i)

/-- For `i ≤ M` the inner-grade guard `0 ≤ M+P-(i-(n+2))-1` always holds. -/
theorem ucoreAnm_guard (M P n i : ℕ) (hi : i ≤ M) :
    0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 := by
  have : (i : ℤ) ≤ (M : ℤ) := by exact_mod_cast hi
  omega

/-- The reflected single-`i`-sum (`i`-independent middle lower index `M+P-n-2-μ-γ`, via `cbz_symm`).
The shift-`0`, `j`-free analogue of `ZhuVermaAnArchL1Close.InnerILn`. -/
noncomputable def InnerIAnm (M P n : ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + 1),
    cbz (M : ℤ) (i : ℤ)
      * cbz (((M : ℤ) + P + n + 1) - i) ((M : ℤ) + P - n - 2 - μ - γ)
      * cbz (-μ - 1) ((i : ℤ) - ((n : ℤ) + 2) - μ)

/-- **`UgammaModeCollAnm` as `InnerIAnm`** (the middle binomial reflected by `cbz_symm`). -/
theorem UgammaModeCollAnm_eq_InnerIAnm (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1)
    (γ μ : ℤ) :
    UgammaModeCollAnm M P n G γ μ = InnerIAnm M P n γ μ := by
  rw [UgammaModeCollAnm_eq_directSum M P n G hG γ μ, InnerIAnm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hile : i ≤ M := by have := Finset.mem_range.mp hi; omega
  have hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 := ucoreAnm_guard M P n i hile
  rw [directUCoeffAnm, if_pos hgr]
  -- reflect the middle binomial: top `G_i = M+P-(i-(n+2))-1 = (M+P+n+1)-i` is a `ℕ`-cast.
  have hmid : cbz ((G i : ℤ)) (rSubAnm n i γ μ)
      = cbz (((M : ℤ) + P + n + 1) - i) ((M : ℤ) + P - n - 2 - μ - γ) := by
    have hGi : (G i : ℤ) = ((M : ℤ) + P + n + 1) - i := by rw [hG i hgr]; ring
    rw [hGi, show ((M : ℤ) + P + n + 1) - i = (((M + P + n + 1 - i : ℕ)) : ℤ) from by
          rw [Nat.cast_sub (by omega)]; push_cast; ring,
      ZhuMu.cbz_symm (M + P + n + 1 - i) (rSubAnm n i γ μ),
      show (((M + P + n + 1 - i : ℕ)) : ℤ) = ((M : ℤ) + P + n + 1) - i from by
          rw [Nat.cast_sub (by omega)]; push_cast; ring, rSubAnm]
    congr 1 <;> ring
  rw [hmid]

/-- The U `a`-sum (Vandermonde top-split + `IC`-collapse, base `M`). -/
noncomputable def ASumAnm (M P n : ℕ) (γ μ : ℤ) : ℂ :=
  ∑ a ∈ Finset.range (M + 1),
    cbz ((P : ℤ) + n + 1) (((M : ℤ) + P - n - 2 - μ - γ) - a)
      * cbz (M : ℤ) (a : ℤ)
      * cbz ((M : ℤ) - a - μ - 1) ((M : ℤ) - (n + 2) - μ - a)

/-- **`InnerIAnm = ASumAnm`.**  Vandermonde top-split of the middle binomial
`C((M+P+n+1)-i, K0) = ∑_a C(M-i,a)·C(P+n+1, K0-a)`, swap to `a`-outer, `trinom_symm` to pull
`C(M,a)` out, then `SR_collapse` (carrier `P+n+1`, base `M`).  Shift-`0`, `j`-free mirror of
`InnerILn_eq_ASumLn`. -/
theorem InnerIAnm_eq_ASumAnm (M P n : ℕ) (γ μ : ℤ) :
    InnerIAnm M P n γ μ = ASumAnm M P n γ μ := by
  rw [InnerIAnm, ASumAnm]
  rw [show ∑ i ∈ Finset.range (M + 1),
            cbz (M : ℤ) (i : ℤ)
              * cbz (((M : ℤ) + P + n + 1) - i) ((M : ℤ) + P - n - 2 - μ - γ)
              * cbz (-μ - 1) ((i : ℤ) - ((n : ℤ) + 2) - μ)
        = ∑ i ∈ Finset.range (M + 1), ∑ a ∈ Finset.range (M + 1),
            cbz ((P : ℤ) + n + 1) (((M : ℤ) + P - n - 2 - μ - γ) - a)
              * (cbz (M : ℤ) (i : ℤ) * cbz ((M : ℤ) - (i : ℤ)) (a : ℤ)
                  * cbz (-μ - 1) ((i : ℤ) - ((n : ℤ) + 2) - μ)) from
      Finset.sum_congr rfl fun i hi => ?_]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hale : a ≤ M := by have := Finset.mem_range.mp ha; omega
    rw [← Finset.mul_sum]
    -- `IC`-collapse, base `M`: `trinom_symm` then `SR_collapse` (`Q = M-a`, `c = n+2+μ`).
    rw [show (M : ℤ) = ((M : ℕ) : ℤ) from rfl]
    rw [show ∑ i ∈ Finset.range (M + 1),
              cbz ((M : ℕ) : ℤ) (i : ℤ) * cbz (((M : ℕ) : ℤ) - (i : ℤ)) (a : ℤ)
                * cbz (-μ - 1) ((i : ℤ) - ((n : ℤ) + 2) - μ)
          = cbz ((M : ℕ) : ℤ) (a : ℤ)
              * ∑ i ∈ Finset.range (M + 1),
                  cbz (((M : ℕ) : ℤ) - (a : ℤ)) (i : ℤ)
                    * cbz (-μ - 1) ((i : ℤ) - ((n : ℤ) + 2) - μ) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [trinom_symm M (i : ℤ) (a : ℤ)]; ring]
    rw [show ((M : ℕ) : ℤ) - (a : ℤ) = ((M - a : ℕ) : ℤ) from by rw [Nat.cast_sub hale]]
    rw [show ∑ i ∈ Finset.range (M + 1),
              cbz ((M - a : ℕ) : ℤ) (i : ℤ) * cbz (-μ - 1) ((i : ℤ) - ((n : ℤ) + 2) - μ)
          = ∑ i ∈ Finset.range (M + 1),
              cbz ((M - a : ℕ) : ℤ) (i : ℤ) * cbz (-μ - 1) ((i : ℤ) - (((n : ℤ) + 2) + μ)) from
        Finset.sum_congr rfl fun i _ => by rw [show (i : ℤ) - ((n : ℤ) + 2) - μ
          = (i : ℤ) - (((n : ℤ) + 2) + μ) from by ring]]
    rw [SR_collapse (M - a) μ (((n : ℤ) + 2) + μ) (N := M + 1) (by omega)]
    rw [show ((M - a : ℕ) : ℤ) = (M : ℤ) - a from by rw [Nat.cast_sub hale]]
    push_cast
    ring_nf
  · have hile : i ≤ M := by have := Finset.mem_range.mp hi; omega
    have hmid : cbz (((M : ℤ) + P + n + 1) - i) ((M : ℤ) + P - n - 2 - μ - γ)
        = ∑ a ∈ Finset.range (M + 1),
            cbz ((M - i : ℕ) : ℤ) (a : ℤ)
              * cbz ((P : ℤ) + n + 1) (((M : ℤ) + P - n - 2 - μ - γ) - a) := by
      rw [vandermonde_range_top (M - i) ((P : ℤ) + n + 1)
        ((M : ℤ) + P - n - 2 - μ - γ) (N := M + 1) (by omega)]
      congr 1
      rw [Nat.cast_sub hile]; push_cast; ring
    rw [hmid, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show ((M - i : ℕ) : ℤ) = (M : ℤ) - i from by rw [Nat.cast_sub hile]]
    ring

/-- The U per-`k` weight kernel `HkerAnm_k = C(P+n+1, k+P-γ)·C(n+1+k, k)`. -/
noncomputable def HkerAnm (P n : ℕ) (γ : ℤ) (k : ℤ) : ℂ :=
  cbz ((P : ℤ) + n + 1) (k + P - γ) * cbz ((n : ℤ) + 1 + k) k

/-- **`ASumAnm` as a `cbz(M, (μ+(n+2))+k)`-finsum** (mirror of `ASumLn_eq_kFinsum`, base `M`). -/
theorem ASumAnm_eq_kFinsum (M P n : ℕ) (γ μ : ℤ) :
    ASumAnm M P n γ μ
      = ∑ᶠ k : ℤ, cbz (M : ℤ) (((μ : ℤ) + (n + 2)) + k) * HkerAnm P n γ k := by
  rw [ASumAnm]
  rw [← Finset.sum_range_reflect
      (fun a => cbz ((P : ℤ) + n + 1) (((M : ℤ) + P - n - 2 - μ - γ) - a)
          * cbz (M : ℤ) (a : ℤ)
          * cbz ((M : ℤ) - a - μ - 1) ((M : ℤ) - (n + 2) - μ - a)) (M + 1)]
  rw [show (∑ a ∈ Finset.range (M + 1),
            cbz ((P : ℤ) + n + 1) (((M : ℤ) + P - n - 2 - μ - γ) - ((M + 1 - 1 - a : ℕ) : ℤ))
                * cbz (M : ℤ) ((M + 1 - 1 - a : ℕ) : ℤ)
                * cbz ((M : ℤ) - ((M + 1 - 1 - a : ℕ) : ℤ) - μ - 1)
                    ((M : ℤ) - (n + 2) - μ - ((M + 1 - 1 - a : ℕ) : ℤ)))
        = ∑ a ∈ Finset.range (M + 1),
            cbz (M : ℤ) (a : ℤ)
              * (cbz ((P : ℤ) + n + 1) (((P : ℤ) - n - 2 - μ - γ) + a)
                  * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - (n + 2) - μ)) from
      Finset.sum_congr rfl fun a ha => ?_]
  · rw [show (∑ a ∈ Finset.range (M + 1),
              cbz (M : ℤ) (a : ℤ)
                * (cbz ((P : ℤ) + n + 1) (((P : ℤ) - n - 2 - μ - γ) + a)
                    * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - (n + 2) - μ)))
          = ∑ᶠ a : ℤ, cbz (M : ℤ) a
                * (cbz ((P : ℤ) + n + 1) (((P : ℤ) - n - 2 - μ - γ) + a)
                    * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - (n + 2) - μ)) from ?_]
    · rw [← finsum_comp_equiv (Equiv.addLeft ((μ : ℤ) + (n + 2)))
          (f := fun a : ℤ => cbz (M : ℤ) a
              * (cbz ((P : ℤ) + n + 1) (((P : ℤ) - n - 2 - μ - γ) + a)
                  * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - (n + 2) - μ)))]
      simp only [Equiv.coe_addLeft]
      refine finsum_congr fun k => ?_
      rw [HkerAnm,
        show ((μ : ℤ) + (n + 2) + k) = (μ : ℤ) + ((n : ℤ) + 2) + k from by push_cast; ring,
        show ((P : ℤ) - n - 2 - μ - γ) + ((μ : ℤ) + ((n : ℤ) + 2) + k) = k + P - γ from by ring,
        show ((μ : ℤ) + ((n : ℤ) + 2) + k) - μ - 1 = (n : ℤ) + 1 + k from by ring,
        show ((μ : ℤ) + ((n : ℤ) + 2) + k) - (n + 2) - μ = k from by push_cast; ring]
    · refine (ZhuRes.finsumZ_eq_range_sum (N := M + 1)
        (fun a : ℤ => cbz (M : ℤ) a
            * (cbz ((P : ℤ) + n + 1) (((P : ℤ) - n - 2 - μ - γ) + a)
                * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - (n + 2) - μ)))
        (fun p hp => by dsimp only; rw [cbz_apply_neg (M : ℤ) hp, zero_mul])
        (fun p hp => by
          dsimp only
          rw [cbz_lt (by positivity) (by
            have : (M + 1 : ℤ) ≤ p := by exact_mod_cast hp
            omega), zero_mul])).symm
  · have hale : a ≤ M := by have := Finset.mem_range.mp ha; omega
    rw [show M + 1 - 1 - a = M - a from by omega]
    have hca : (((M - a : ℕ) : ℤ)) = (M : ℤ) - a := by rw [Nat.cast_sub hale]
    rw [hca]
    rw [show cbz (M : ℤ) ((M : ℤ) - a) = cbz (M : ℤ) (a : ℤ) from by
        rw [show (M : ℤ) = ((M : ℕ) : ℤ) from rfl, ← ZhuMu.cbz_symm M (a : ℤ)]]
    rw [show ((M : ℤ) + P - n - 2 - μ - γ) - ((M : ℤ) - a) = ((P : ℤ) - n - 2 - μ - γ) + a from by ring,
      show (M : ℤ) - ((M : ℤ) - a) - μ - 1 = (a : ℤ) - μ - 1 from by ring,
      show (M : ℤ) - (n + 2) - μ - ((M : ℤ) - a) = (a : ℤ) - (n + 2) - μ from by ring]
    ring

/-- `HkerAnm` vanishes for `k < 0` (the `C(n+1+k, k)` factor). -/
theorem HkerAnm_lo (P n : ℕ) (γ : ℤ) {k : ℤ} (hk : k < 0) : HkerAnm P n γ k = 0 := by
  rw [HkerAnm, cbz_apply_neg ((n : ℤ) + 1 + k) hk, mul_zero]

/-- `HkerAnm` vanishes for `n+2+γ ≤ k` (the `C(P+n+1, k+P-γ)` factor: top `< lower`). -/
theorem HkerAnm_hi (P n : ℕ) (γ : ℤ) {k : ℤ} (hk : (n : ℤ) + 2 + γ ≤ k) :
    HkerAnm P n γ k = 0 := by
  rw [HkerAnm, cbz_lt (by positivity) (by omega : (P : ℤ) + n + 1 < k + P - γ), zero_mul]

/-- The U per-tower weight (`tower_swap` weight, base `M`, support `[0,Δ)`):
`wUAnm(ν) = ∑_{k<Δ} (-1)^(k-ν)·C(k,ν)·HkerAnm(k)`, `Δ = (n+2+γ).toNat`. -/
noncomputable def wUAnm (P n : ℕ) (γ : ℤ) (ν : ℕ) : ℂ :=
  ∑ k ∈ Finset.range ((n : ℤ) + 2 + γ).toNat,
    (-1 : ℂ) ^ (k - ν) * cbz (k : ℤ) (ν : ℤ) * HkerAnm P n γ (k : ℤ)

/-- **The U-core scalar collapse.**  `UgammaModeCollAnm` equals the grade-`M` `towerCoeffAnm` tower
with the `M`-independent weights `wUAnm` and depth `Δ = (n+2+γ).toNat`.  Shift-`0`, `j`-free mirror of
`UgammaModeCollLn_eq_towerCoeff`. -/
theorem UgammaModeCollAnm_eq_towerCoeff (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1)
    (γ μ : ℤ) :
    UgammaModeCollAnm M P n G γ μ
      = towerCoeffAnm M n (wUAnm P n γ) ((n : ℤ) + 2 + γ).toNat μ := by
  rw [UgammaModeCollAnm_eq_InnerIAnm M P n G hG γ μ, InnerIAnm_eq_ASumAnm, ASumAnm_eq_kFinsum]
  rw [show (∑ᶠ k : ℤ, cbz (M : ℤ) (((μ : ℤ) + (n + 2)) + k) * HkerAnm P n γ k)
        = ∑ᶠ k : ℤ, cbz (((M : ℕ)) : ℤ) (((μ : ℤ) + (n + 2)) + k) * HkerAnm P n γ k from by rfl]
  rw [tower_swap M (μ + (n + 2)) (HkerAnm P n γ) ((n : ℤ) + 2 + γ).toNat
      (fun k hk => HkerAnm_lo P n γ hk)
      (fun k hk => HkerAnm_hi P n γ (by
        have hh : (((n : ℤ) + 2 + γ).toNat : ℤ) ≤ k := hk
        rcases lt_or_ge ((n : ℤ) + 2 + γ) 0 with h | h
        · rw [Int.toNat_of_nonpos (by omega)] at hh; omega
        · rw [Int.toNat_of_nonneg h] at hh; omega))]
  rw [towerCoeffAnm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [wUAnm,
    show ((μ : ℤ) + (n + 2)) + (ν : ℤ) = μ + (n + 2) + ν from by push_cast; ring]

/-! ## Step 10 — the V-core inner `p`-collapse and reduced single-`i`-sum (`j`-free).

The `d`-first mirror of Step 9.  The inner `p`-finset collapses to the single substituted index
`p₀ = μ-i+2n+3+γ`; the V `gBinom` factor reflects via `vIter_core` to a single `cbz`; the middle
binomial reflects via `cbz_symm` to the `i`-independent-lower-index frame.  The final base-`P`
collapse (`VgammaModeCollAnm = -towerCoeffAnm P n …`) is the precise remaining V-core piece — the
`j`-free analogue of `ZhuVermaAnArchL1Close.VgammaModeCollLn_eq_towerCoeff` (`ZhuVermaAnDescent20`). -/

/-- The per-`i` direct V-scalar (the `p`-collapsed `VgammaCoeffAnm`): `cbz M i` times the middle
inner-residue binomial `cbz(G_i, p₀)` (guarded), the V-sign peeling `cbz(γ-1-(i-(n+2)), γ)` (via
`vIter_core`) and the retained V-sign `(-1)^(i-(n+2))`, guarded by `0 ≤ γ`. -/
noncomputable def directVCoeffAnm (M P n : ℕ) (G : ℕ → ℕ) (i : ℕ) (γ μ : ℤ) : ℂ :=
  if 0 ≤ γ then
    cbz (M : ℤ) (i : ℤ)
      * (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1
          then cbz ((G i : ℤ)) (rSubAnm n i γ μ) else 0)
      * cbz (γ - 1 - ((i : ℤ) - ((n : ℤ) + 2))) γ
      * ((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2)))
  else 0

/-- **Matched-term identity (V).**  When `(p : ℤ) = rSubAnm n i γ μ`, the per-`(i,p)` V-coefficient
`VgammaCoeffAnm M P n G i p γ` equals `directVCoeffAnm M P n G i γ μ`. -/
theorem VgammaCoeffAnm_at_rSub (M P n : ℕ) (G : ℕ → ℕ) (i p : ℕ) (γ μ : ℤ)
    (hr : (p : ℤ) = rSubAnm n i γ μ) :
    VgammaCoeffAnm M P n G i p γ = directVCoeffAnm M P n G i γ μ := by
  rw [VgammaCoeffAnm, directVCoeffAnm, assemblyLeadAnm]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, if_pos hγ]
    have hγn : (γ.toNat : ℤ) = γ := Int.toNat_of_nonneg hγ
    have hpeel : ((-1 : ℂ) ^ γ.toNat * gBinom ((i : ℤ) - ((n : ℤ) + 2)) γ.toNat)
        = cbz (γ - 1 - ((i : ℤ) - ((n : ℤ) + 2))) γ := by
      rw [vIter_core ((i : ℤ) - ((n : ℤ) + 2)) γ.toNat,
        show ((γ.toNat : ℤ) - 1 - ((i : ℤ) - ((n : ℤ) + 2)))
            = γ - 1 - ((i : ℤ) - ((n : ℤ) + 2)) from by rw [hγn], hγn]
    by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1
    · rw [if_pos hgr, if_pos hgr, hpeel, show (p : ℤ) = rSubAnm n i γ μ from hr]
    · rw [if_neg hgr, if_neg hgr, hpeel]; ring
  · rw [if_neg hγ, if_neg hγ]

/-- **Inner `p`-finset collapse (V).** -/
theorem VinnerAnm_collapse (M P n : ℕ) (G : ℕ → ℕ) (i : ℕ) (γ μ : ℤ)
    (hG : 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1) :
    (∑ p ∈ Finset.range (G i + 1),
        (if μ = ((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ
          then VgammaCoeffAnm M P n G i p γ else 0))
      = directVCoeffAnm M P n G i γ μ := by
  have hcond : ∀ p : ℕ,
      (μ = ((i : ℤ) - ((n : ℤ) + 2)) + ((p : ℤ) - ((n : ℤ) + 1)) - γ)
        ↔ ((p : ℤ) = rSubAnm n i γ μ) := by
    intro p; rw [rSubAnm]; constructor <;> intro h <;> omega
  rw [Finset.sum_congr rfl fun p _ => by rw [show (if μ = ((i : ℤ) - ((n : ℤ) + 2))
        + ((p : ℤ) - ((n : ℤ) + 1)) - γ then VgammaCoeffAnm M P n G i p γ else 0)
      = (if (p : ℤ) = rSubAnm n i γ μ then VgammaCoeffAnm M P n G i p γ else 0) from by
        simp only [hcond p]]]
  by_cases hpos : 0 ≤ rSubAnm n i γ μ
  · set p₀ : ℕ := (rSubAnm n i γ μ).toNat with hp₀
    have hp₀cast : (p₀ : ℤ) = rSubAnm n i γ μ := by rw [hp₀, Int.toNat_of_nonneg hpos]
    by_cases hmem : p₀ ∈ Finset.range (G i + 1)
    · rw [Finset.sum_eq_single_of_mem p₀ hmem
        (fun p _ hne => by
          rw [if_neg (by
            intro hc; exact hne (by
              have : (p : ℤ) = (p₀ : ℤ) := by rw [hp₀cast, hc]
              exact_mod_cast this))])]
      rw [if_pos hp₀cast, VgammaCoeffAnm_at_rSub M P n G i p₀ γ μ hp₀cast]
    · have hgt : (G i : ℤ) < rSubAnm n i γ μ := by
        rw [Finset.mem_range] at hmem
        have : G i + 1 ≤ p₀ := by omega
        have hle : ((G i + 1 : ℕ) : ℤ) ≤ (p₀ : ℤ) := by exact_mod_cast this
        rw [hp₀cast] at hle; push_cast at hle; omega
      rw [Finset.sum_eq_zero fun p hp => by
        rw [if_neg (by
          rw [Finset.mem_range] at hp
          intro hc
          have hple : p ≤ G i := by omega
          have hle : (p : ℤ) ≤ (G i : ℤ) := by exact_mod_cast hple
          rw [hc] at hle; omega)]]
      rw [directVCoeffAnm]
      by_cases hγ : 0 ≤ γ
      · rw [if_pos hγ]
        by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1
        · rw [if_pos hgr, cbz_zero_off_range (A := (G i : ℤ)) (by rw [hG hgr]; omega)
            (Or.inr (by omega))]; ring
        · rw [if_neg hgr]; ring
      · rw [if_neg hγ]
  · replace hpos : rSubAnm n i γ μ < 0 := not_le.mp hpos
    rw [Finset.sum_eq_zero fun p _ => by
      rw [if_neg (by
        intro hc
        have : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
        rw [hc] at this; omega)]]
    rw [directVCoeffAnm]
    by_cases hγ : 0 ≤ γ
    · rw [if_pos hγ]
      by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1
      · rw [if_pos hgr, cbz_apply_neg ((G i : ℤ)) (by omega)]; ring
      · rw [if_neg hgr]; ring
    · rw [if_neg hγ]

/-- **`VgammaModeCollAnm` as the direct single-`i`-sum.** -/
theorem VgammaModeCollAnm_eq_directSum (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1)
    (γ μ : ℤ) :
    VgammaModeCollAnm M P n G γ μ
      = ∑ i ∈ Finset.range (M + 1), directVCoeffAnm M P n G i γ μ := by
  rw [VgammaModeCollAnm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact VinnerAnm_collapse M P n G i γ μ (hG i)

/-- The reflected single-`i`-sum (V): `i`-independent middle lower index `M+P-n-2-μ-γ` (via
`cbz_symm`), guarded by `0 ≤ γ`.  The shift-`0`, `j`-free analogue of
`ZhuVermaAnArchL1Close.VInnerILn` — the precise remaining V-core base-`P` tower-collapse input. -/
noncomputable def VInnerIAnm (M P n : ℕ) (γ μ : ℤ) : ℂ :=
  if 0 ≤ γ then
    ∑ i ∈ Finset.range (M + 1),
      cbz (M : ℤ) (i : ℤ)
        * cbz (((M : ℤ) + P + n + 1) - i) ((M : ℤ) + P - n - 2 - μ - γ)
        * (((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2)))
            * cbz (γ - 1 - ((i : ℤ) - ((n : ℤ) + 2))) γ)
  else 0

/-- **`VgammaModeCollAnm` as `VInnerIAnm`** (the middle binomial reflected by `cbz_symm`). -/
theorem VgammaModeCollAnm_eq_VInnerIAnm (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1)
    (γ μ : ℤ) :
    VgammaModeCollAnm M P n G γ μ = VInnerIAnm M P n γ μ := by
  rw [VgammaModeCollAnm_eq_directSum M P n G hG γ μ, VInnerIAnm]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hile : i ≤ M := by have := Finset.mem_range.mp hi; omega
    have hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 := ucoreAnm_guard M P n i hile
    rw [directVCoeffAnm, if_pos hγ, if_pos hgr]
    have hmid : cbz ((G i : ℤ)) (rSubAnm n i γ μ)
        = cbz (((M : ℤ) + P + n + 1) - i) ((M : ℤ) + P - n - 2 - μ - γ) := by
      have hGi : (G i : ℤ) = ((M : ℤ) + P + n + 1) - i := by rw [hG i hgr]; ring
      rw [hGi, show ((M : ℤ) + P + n + 1) - i = (((M + P + n + 1 - i : ℕ)) : ℤ) from by
            rw [Nat.cast_sub (by omega)]; push_cast; ring,
        ZhuMu.cbz_symm (M + P + n + 1 - i) (rSubAnm n i γ μ),
        show (((M + P + n + 1 - i : ℕ)) : ℤ) = ((M : ℤ) + P + n + 1) - i from by
            rw [Nat.cast_sub (by omega)]; push_cast; ring, rSubAnm]
      congr 1 <;> ring
    rw [hmid]; ring
  · rw [if_neg hγ]
    refine (Finset.sum_eq_zero fun i _ => ?_).trans rfl
    rw [directVCoeffAnm, if_neg hγ]

/-!
## Status — the PRECISE remaining content (NOT `sorry`, NOT axiomatized).

Everything above is axiom-clean (`[propext, Classical.choice, Quot.sound]`).
`AnmCircTowerEq W n M P c d v` (⟹ `hcirc_of_towerEq`, ⟹ `AnmRightModule_of_towerEq`, the Game-One
`M(U)` `V`-action crux) is reduced — via `AnmCircTowerEq_of_sides` + `USideAnm_eq_gammaModeFinsum`/
`VSideAnm_eq_gammaModeFinsum` + `UfamAnm_eq_finsum`/`VfamAnm_eq_finsum` — to the two per-`(γ,μ)`
scalar tower-collapse cores

  (U-core)  `UgammaModeCollAnm M P n G γ μ = towerCoeffAnm M n (wU γ) Δ μ`     for some `wU, Δ`,
  (V-core)  `VgammaModeCollAnm M P n G γ μ = -towerCoeffAnm P n (wV γ) Δ μ`    for some `wV, Δ`.

These are the shift-`0` (pole `n+2`/`n+1`, `j`-free) mirror of the proven shift-`n` cores
`UgammaModeCollLn_eq_towerCoeff`/`VgammaModeCollLn_eq_towerCoeff` (`ZhuVermaAnArchL1Close`, ports
`ZhuVermaAnDescent19/20`), but DRAMATICALLY simpler because at `m = 0` there is NO FZ `j`-sum (the
`*^n_0` sum has only the `i = 0` term, `anmRight_zero`).

### The U-core is closed — `UgammaModeCollAnm_eq_towerCoeff`.

`UgammaModeCollAnm M P n G γ μ = towerCoeffAnm M n (wUAnm P n γ) ((n+2+γ).toNat) μ` is **fully proved
here** (axiom-clean), via the chain `UinnerAnm_collapse` (inner `p`-finset → single substituted index
`p₀ = μ-i+2n+3+γ`, peeling `uIter_eq_cbz`) → `UgammaModeCollAnm_eq_InnerIAnm` (`cbz_symm` middle
reflection to the `i`-independent-lower-index frame) → `InnerIAnm_eq_ASumAnm`
(`vandermonde_range_top` + `trinom_symm` + `SR_collapse`, carrier `P+n+1`, base `M`) →
`ASumAnm_eq_kFinsum` (reflect `a ↦ M-a`, shift) → `tower_swap` (base `M`, support `[0,Δ)` from
`HkerAnm_lo`/`HkerAnm_hi`).  The kernel is `HkerAnm P n γ k = C(P+n+1, k+P-γ)·C(n+1+k, k)`.

### The PRECISE remaining V-core piece — `VInnerIAnm = -towerCoeffAnm P n …`.

The V-core is reduced (all green here) to its reflected single-`i`-sum

  `VgammaModeCollAnm M P n G γ μ = VInnerIAnm M P n γ μ`  (`VgammaModeCollAnm_eq_VInnerIAnm`),

via `VinnerAnm_collapse` (inner `p`-collapse) + `vIter_core` (V-sign peeling
`(-1)^γ gBinom(i-(n+2),γ) = cbz(γ-1-(i-(n+2)), γ)`) + `cbz_symm` (middle reflection).  The single
remaining step is the base-`P` tower collapse `VInnerIAnm M P n γ μ = -towerCoeffAnm P n (wV γ) Δ μ`
(depth `Δ = (n+2+γ).toNat`, the V-weights `M`-dependent — harmless, `VfamAnm` admits ANY weights and
`Pres_mem_Onm` carries the tower into `Onm`).  Engine-verified (`certificates/mathematica/anmcirc_vcore*.wl`):
the Vandermonde top-split `(M+P+n+1)-i = (M-i)+(P+n+1)` + `trinom_symm` give the `a`-sum `VASumAnm`
(`VInnerI == VASum` verified TRUE), and the `(n+1)`-Vandermonde `(P+n+1) = (n+1)+P` to base `P` then
`tower_swap` gives the grade-`P` tower — the `j`-free analogue of the `GvLn` route in
`ZhuVermaAnArchL1Close`/`ZhuVermaAnDescent20`.  Discharging it (then `AnmCircTowerEq_of_sides` with
`G i := (M+P-(i-(n+2))-1).toNat`, `wU := wUAnm`, `wV := -(V-weights)`, `Δ := (n+2+γ).toNat`, the
finite base-mode window `Γ` from `W.regularity`) closes `AnmCircTowerEq`, hence `hcirc_of_towerEq`,
hence `AnmRightModule_of_towerEq`.  Nothing here is `sorry`'d or axiomatized.
-/

end VOA
