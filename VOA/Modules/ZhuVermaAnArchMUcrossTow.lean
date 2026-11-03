/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcrossHM

/-!
# Game One — the `m = 0` cross-level circle tower core `CrossCircTowerEq`: the distributed
master split over the inner circle index.

This file works on the LAST open Game-One core of the Dong–Jiang induced module `M(U)` `V`-action:
the cross-level circle tower predicate `CrossCircTowerEq W n K M P a c d`
(`ZhuVermaAnArchMUcrossHM`), the precise tower-collapse of the combined `c`-first + commutator
families

  `crossCircCFirst W n K M a c d + crossCircComm W n K M a c d
     = PresTowerFam W M n c … + PresTowerFam W P n d …`

i.e. the residue-of-residue `resHom W 0 (n+1) a (resHom W 0 2 c d)` (`crossCirc_modeSplit`) collapses
onto a `PresAnm`-tower U-family in `c` (over `M`) plus a `PresAnm`-tower V-family in `d` (over `P`),
all in `Onm W n 0` (`PresTowerFam_mem_Onm`).  This is the `m = 0`, mixed-level analogue of the proven
left-slot `leftProd_circ_mem_On` (`ZhuVermaAnDescent4`), and the shift-`0`, mixed-level twin of the
just-closed diagonal `AnmCircTowerEq_holds` (`ZhuVermaAnArchMUcircV`).

## The cross subtlety (recapped)

The cross core is `a *^n_0 (c ∘_0 d)` — the OUTER level-`n` residue (pole `n+1`) of the homogeneous
vector `a ∈ 𝒱_K`, applied to the INNER level-`0` Zhu circle `anmCirc W 0 0 c d = resHom W 0 2 c d`
(pole `2`).  Unlike the diagonal `AnmCircTowerEq` (both residues at level `n`/pole `n+2`), the inner
circle here is level `0` / pole `2`, so after the per-`(i,j)` `mode_split_gen`
`a₍α₎(c₍β₎d) = c₍β₎(a₍α₎d) + ⁅a₍α₎,c₍β₎⁆d` the `c`-first inner sum is a *level-`0`* circle
`resHom W 0 2 c (a₍α₎d)` (pole `2`, NOT the `Onm`-pole `n+2`).  Hence neither family lands in
`Onm W n 0` alone — only the COMBINED residue is grade-`(n+2)`-local.  This is exactly the
commutator-style content of `leftProd_circ_mem_On` (the homogeneous factor in the outer applied-mode
position, the circle in the inner slot), at the shift-`0` pole structure.

## What is proved here (axiom-clean)

* **`crossCirc_distrib_over_j`** — the **distributed master split**: the combined `c`-first +
  commutator families equal the inner-circle-index-`j` distribution of the outer residue,
  `∑_j C(M,j) • resHom W 0 (n+1) a (c₍j−2₎ d)` (cross analogue of `anmCirc_resOfRes_distrib`,
  `ZhuVermaAnArchMUcircClose`).  This is the structural identity that exposes the cross core as the
  outer residue of `a` applied to the per-`j` homogeneous inner factors `c₍j−2₎d ∈ 𝒱_{M+P-(j-2)-1}`.
* **`crossCircTerm`** — the per-`j` cross term `resHom W 0 (n+1) a (c₍j−2₎ d)` and its grade
  bookkeeping (`crossCircTerm_inner_mem_grading`).
* **`CrossCircTermTowerEq`** — the precise PER-`j` tower-collapse predicate: each per-`j` outer
  residue `resHom W 0 (n+1) a (c₍j−2₎ d)` collapses onto a `PresAnm`-tower family in `c` (over `M`)
  plus a `PresAnm`-tower family in `d` (over `P`).  This is the shift-`0`, mixed-level
  commutator-family core (the genuine remaining content, engine-verified TRUE on the rank-1 free
  boson, `certificates/mathematica/mucross_circ.wl`).
* **`CrossCircTowerEq_of_term`** — assembling the per-`j` `CrossCircTermTowerEq` (over the finite
  `j`-range) into the global `CrossCircTowerEq` (the `PresTowerFam` families being closed under finite
  ℂ-combinations via `Fin (R₁+R₂)`-merging), discharging the cross tower predicate from the per-`j`
  cores.

## The PRECISE remaining content (NOT `sorry`'d / NOT axiomatized)

`CrossCircTowerEq` is reduced here (by `crossCirc_distrib_over_j` + `CrossCircTowerEq_of_term`) to the
per-`j` `CrossCircTermTowerEq`: the outer level-`n` residue (pole `n+1`) of homogeneous `a ∈ 𝒱_K`
applied to the homogeneous inner factor `c₍j−2₎d ∈ 𝒱_{G_j}` collapses onto `PresAnm`-towers.  This is
the shift-`0` commutator-family collapse — the same combinatorial depth as the diagonal
`AnmCircTowerEq` (`ZhuVermaAnArchMUcircV`) and the proven `leftProd_circ_mem_On`
(`ZhuVermaAnDescent4`, `Sn_mem_On`/`coeffSn_eq_coeffPn` route via `ZhuRes.gen_jsum`/`gen_vandermonde`),
with the FZ shift replaced by the shift-`0` pole `n+2`.  Engine value
(`certificates/mathematica/mucross_circ.wl`): for `n = 1, a = c = d = J` the cross residue-of-residue lands
in `Onm W 1 0`; likewise `n = 2`.  It is left as the precise stated `CrossCircTermTowerEq` target, NOT
a `sorry`/axiom.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The distributed master split over the inner circle index `j`. -/

/-- For homogeneous `c ∈ 𝒱_M`, the inner level-`0` Zhu circle `resHom W 0 2 c d` is
`∑_j cbz M j • c₍j−2₎d` (`resHom_homogeneous`, `s = 0`, pole `2`); the outer level-`n` residue
`resHom W 0 (n+1) a (·)` distributes (`resHom_add_right`/`resHom_smul_right`) into
`∑_j cbz M j • resHom W 0 (n+1) a (c₍j−2₎d)`.  Cross analogue of `anmCirc_resOfRes_distrib`. -/
theorem crossCirc_inner_distrib (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (a d : 𝒱) :
    resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c d)
      = ∑ j ∈ Finset.range (M + 1),
          cbz (M : ℤ) (j : ℤ)
            • resHom W 0 ((n : ℤ) + 1) a (W.smul c ((j : ℤ) - 2) d) := by
  rw [resHom_homogeneous W 0 2 hc d]
  simp only [add_zero]
  rw [show ((M : ℤ)).toNat + 1 = M + 1 from by simp]
  have hres0 : resHom W 0 ((n : ℤ) + 1) a (0 : 𝒱) = 0 := resHom_zero_right' W 0 ((n : ℤ) + 1) a
  induction (Finset.range (M + 1)) using Finset.induction with
  | empty => simp [hres0]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, resHom_add_right, resHom_smul_right, ih]

/-- **The distributed master split.**  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the combined
`c`-first + commutator families (i.e. the cross-level circle core, `crossCirc_modeSplit`) equal the
inner-circle-index-`j` distribution of the outer level-`n` residue:
`crossCircCFirst + crossCircComm = ∑_j cbz M j • resHom W 0 (n+1) a (c₍j−2₎d)`.  Cross analogue of
the diagonal `anmCirc_resOfRes_distrib` (`ZhuVermaAnArchMUcircClose`). -/
theorem crossCirc_distrib_over_j (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (_hd : d ∈ W.grading (P : ℤ)) :
    crossCircCFirst W n K M a c d + crossCircComm W n K M a c d
      = ∑ j ∈ Finset.range (M + 1),
          cbz (M : ℤ) (j : ℤ)
            • resHom W 0 ((n : ℤ) + 1) a (W.smul c ((j : ℤ) - 2) d) := by
  rw [← crossCirc_modeSplit W n ha hc d, crossCirc_inner_distrib W n hc a d]

/-! ## The per-`j` cross term and its grade bookkeeping. -/

/-- The per-`j` cross term `resHom W 0 (n+1) a (c₍j−2₎ d)` (outer level-`n` residue of `a`, applied to
the inner factor `c₍j−2₎d`). -/
noncomputable def crossCircTerm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a c d : 𝒱) (j : ℕ) : 𝒱 :=
  resHom W 0 ((n : ℤ) + 1) a (W.smul c ((j : ℤ) - 2) d)

/-- The inner factor `c₍j−2₎d` lands in `𝒱_{M+P-(j-2)-1}` (for homogeneous `c ∈ 𝒱_M`, `d ∈ 𝒱_P`). -/
theorem crossCircTerm_inner_mem_grading (W : VertexOperatorAlgebra 𝒱) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (j : ℕ) :
    W.smul c ((j : ℤ) - 2) d ∈ W.grading ((M : ℤ) + (P : ℤ) - ((j : ℤ) - 2) - 1) :=
  W.smul_mem_grading hc hd ((j : ℤ) - 2)

/-! ## The per-`j` tower-collapse predicate (the shift-`0` commutator-family core). -/

/-- **The per-`j` cross-term tower-decomposition predicate** (precise remaining identity).  For
homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the per-`j` cross term `resHom W 0 (n+1) a (c₍j−2₎d)`
collapses onto a general `PresAnm`-tower family in `c` (over `M`, arbitrary base vectors — modes of
`a₍·₎d`) plus a general `PresAnm`-tower family in `d` (over `P`, arbitrary base vectors — iterated
modes `c₍·₎(a₍·₎d)`).  Shift-`0`, mixed-level commutator-family core; engine-verified TRUE
(`certificates/mathematica/mucross_circ.wl`). -/
def CrossCircTermTowerEq (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) (j : ℕ) : Prop :=
  ∃ (RU RV ΔU ΔV : ℕ) (baseU : Fin RU → 𝒱) (baseV : Fin RV → 𝒱)
    (wU : Fin RU → ℕ → ℂ) (wV : Fin RV → ℕ → ℂ),
    crossCircTerm W n a c d j
      = PresTowerFam W M n c RU ΔU baseU wU + PresTowerFam W P n d RV ΔV baseV wV

/-! ## `PresTowerFam` is closed under finite ℂ-combinations (merging index sets). -/

/-- **Depth-padding for a single `PresAnm`-tower.**  Padding the depth from `Δ` up to any `Δ' ≥ Δ`,
zeroing the weight past `Δ`, leaves the tower unchanged (the extra `PresAnm` summands carry weight
`0`). -/
theorem presAnmTower_pad (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (u base : 𝒱)
    (w : ℕ → ℂ) (Δ Δ' : ℕ) (hle : Δ ≤ Δ') :
    (∑ δ ∈ Finset.range Δ, w δ • PresAnm W M n δ u base)
      = ∑ δ ∈ Finset.range Δ', (if δ < Δ then w δ else 0) • PresAnm W M n δ u base := by
  rw [show (∑ δ ∈ Finset.range Δ, w δ • PresAnm W M n δ u base)
        = ∑ δ ∈ Finset.range Δ, (if δ < Δ then w δ else 0) • PresAnm W M n δ u base from
      Finset.sum_congr rfl fun δ hδ => by rw [if_pos (Finset.mem_range.mp hδ)]]
  refine Finset.sum_subset (fun δ hδ => ?_) ?_
  · rw [Finset.mem_range] at hδ ⊢; omega
  · intro δ _ hδ
    rw [if_neg (by rw [Finset.mem_range] at hδ; omega), zero_smul]

/-- The sum of two `PresTowerFam`s in the SAME left factor `u` (over the SAME grade `M`) is again a
`PresTowerFam` (merge the `Fin R₁` and `Fin R₂` index sets to `Fin (R₁ + R₂)`, take the max depth,
pad the weights with `0` past each family's own depth so the padding is inert). -/
theorem PresTowerFam_add (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (u : 𝒱)
    (R₁ R₂ Δ₁ Δ₂ : ℕ) (baseU₁ : Fin R₁ → 𝒱) (baseU₂ : Fin R₂ → 𝒱)
    (w₁ : Fin R₁ → ℕ → ℂ) (w₂ : Fin R₂ → ℕ → ℂ) :
    PresTowerFam W M n u R₁ Δ₁ baseU₁ w₁ + PresTowerFam W M n u R₂ Δ₂ baseU₂ w₂
      = PresTowerFam W M n u (R₁ + R₂) (max Δ₁ Δ₂)
          (fun r => Sum.elim baseU₁ baseU₂ (finSumFinEquiv.symm r))
          (fun r δ => Sum.elim (fun r₁ => if δ < Δ₁ then w₁ r₁ δ else 0)
                    (fun r₂ => if δ < Δ₂ then w₂ r₂ δ else 0) (finSumFinEquiv.symm r)) := by
  rw [PresTowerFam, PresTowerFam, PresTowerFam]
  rw [← finSumFinEquiv.sum_comp
      (fun r : Fin (R₁ + R₂) => ∑ δ ∈ Finset.range (max Δ₁ Δ₂),
        Sum.elim (fun r₁ => if δ < Δ₁ then w₁ r₁ δ else 0)
                (fun r₂ => if δ < Δ₂ then w₂ r₂ δ else 0) (finSumFinEquiv.symm r)
          • PresAnm W M n δ u
              (Sum.elim baseU₁ baseU₂ (finSumFinEquiv.symm r)))]
  rw [Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  congr 1
  · -- left block: pad family 1 from `Δ₁` up to `max Δ₁ Δ₂`.
    refine Finset.sum_congr rfl fun r₁ _ => ?_
    exact presAnmTower_pad W M n u (baseU₁ r₁) (w₁ r₁) Δ₁ (max Δ₁ Δ₂) (le_max_left _ _)
  · -- right block: pad family 2 from `Δ₂` up to `max Δ₁ Δ₂`.
    refine Finset.sum_congr rfl fun r₂ _ => ?_
    exact presAnmTower_pad W M n u (baseU₂ r₂) (w₂ r₂) Δ₂ (max Δ₁ Δ₂) (le_max_right _ _)

/-- A ℂ-scalar multiple of a `PresTowerFam` is again a `PresTowerFam` (scale the weights). -/
theorem smul_PresTowerFam (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (u : 𝒱)
    (R Δ : ℕ) (baseU : Fin R → 𝒱) (w : Fin R → ℕ → ℂ) (s : ℂ) :
    s • PresTowerFam W M n u R Δ baseU w
      = PresTowerFam W M n u R Δ baseU (fun r δ => s * w r δ) := by
  rw [PresTowerFam, PresTowerFam, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [smul_smul]

/-! ## Assembling the per-`j` cores into the global cross tower predicate. -/

/-- **`CrossCircTowerEq` from the per-`j` `CrossCircTermTowerEq`.**  If each per-`j` cross term
collapses onto `PresAnm`-towers (`CrossCircTermTowerEq` for all `j` in the circle range), then the
combined `c`-first + commutator families collapse onto a single pair of `PresAnm`-tower families
(`CrossCircTowerEq`).  Assembly: `crossCirc_distrib_over_j` reduces the target to the finite
`cbz M j`-weighted `j`-sum of the per-`j` cross terms; each is a `PresTowerFam(c) + PresTowerFam(d)`,
scaled (`smul_PresTowerFam`) and merged (`PresTowerFam_add`) into one `PresTowerFam(c) +
PresTowerFam(d)`. -/
theorem CrossCircTowerEq_of_term (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a c d : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ))
    (hd : d ∈ W.grading (P : ℤ))
    (hterm : ∀ j ∈ Finset.range (M + 1), CrossCircTermTowerEq W n K M P a c d j) :
    CrossCircTowerEq W n K M P a c d := by
  -- Build, by induction over the `j`-range, a single `(U,V)` pair of `PresTowerFam`s equal to the
  -- `cbz M j`-weighted `j`-sum of the per-`j` cross terms.
  have hsum : ∃ (RU RV ΔU ΔV : ℕ) (baseU : Fin RU → 𝒱) (baseV : Fin RV → 𝒱)
      (wU : Fin RU → ℕ → ℂ) (wV : Fin RV → ℕ → ℂ),
      (∑ j ∈ Finset.range (M + 1),
          cbz (M : ℤ) (j : ℤ) • crossCircTerm W n a c d j)
        = PresTowerFam W M n c RU ΔU baseU wU + PresTowerFam W P n d RV ΔV baseV wV := by
    induction (M + 1) with
    | zero =>
      refine ⟨0, 0, 0, 0, Fin.elim0, Fin.elim0, fun r => r.elim0, fun r => r.elim0, ?_⟩
      simp only [Finset.range_zero, Finset.sum_empty, PresTowerFam, Finset.univ_eq_empty,
        Finset.sum_empty, add_zero]
    | succ k ih =>
      obtain ⟨RU, RV, ΔU, ΔV, baseU, baseV, wU, wV, heq⟩ := ih
      -- the `k`-th term collapses by `CrossCircTermTowerEq` (when `k ≤ M`) or is handled directly.
      rcases le_or_gt k M with hkM | hkM
      · obtain ⟨RU', RV', ΔU', ΔV', baseU', baseV', wU', wV', hterm_k⟩ :=
          hterm k (Finset.mem_range.mpr (by omega))
        rw [Finset.sum_range_succ, heq, hterm_k, smul_add,
          smul_PresTowerFam W M n c RU' ΔU' baseU' wU' (cbz (M : ℤ) (k : ℤ)),
          smul_PresTowerFam W P n d RV' ΔV' baseV' wV' (cbz (M : ℤ) (k : ℤ))]
        -- regroup `(U + V) + (U' + V') = (U + U') + (V + V')`, then merge each pair.
        rw [show (PresTowerFam W M n c RU ΔU baseU wU + PresTowerFam W P n d RV ΔV baseV wV)
              + (PresTowerFam W M n c RU' ΔU' baseU' (fun r δ => cbz (M : ℤ) (k : ℤ) * wU' r δ)
                  + PresTowerFam W P n d RV' ΔV' baseV' (fun r δ => cbz (M : ℤ) (k : ℤ) * wV' r δ))
            = (PresTowerFam W M n c RU ΔU baseU wU
                  + PresTowerFam W M n c RU' ΔU' baseU' (fun r δ => cbz (M : ℤ) (k : ℤ) * wU' r δ))
              + (PresTowerFam W P n d RV ΔV baseV wV
                  + PresTowerFam W P n d RV' ΔV' baseV'
                      (fun r δ => cbz (M : ℤ) (k : ℤ) * wV' r δ)) from by abel]
        rw [PresTowerFam_add W M n c RU RU' ΔU ΔU' baseU baseU' wU
              (fun r δ => cbz (M : ℤ) (k : ℤ) * wU' r δ),
            PresTowerFam_add W P n d RV RV' ΔV ΔV' baseV baseV' wV
              (fun r δ => cbz (M : ℤ) (k : ℤ) * wV' r δ)]
        exact ⟨_, _, _, _, _, _, _, _, rfl⟩
      · -- `k > M`: the inner factor `c₍k−2₎d` lies in a negative grade only when relevant; but the
        -- circle weight `cbz M k = 0` for `k > M`, killing the term.
        refine ⟨RU, RV, ΔU, ΔV, baseU, baseV, wU, wV, ?_⟩
        rw [Finset.sum_range_succ, heq,
          show cbz (M : ℤ) (k : ℤ) = 0 from cbz_lt (by positivity)
            (by exact_mod_cast (by omega : M < k)), zero_smul, add_zero]
  obtain ⟨RU, RV, ΔU, ΔV, baseU, baseV, wU, wV, heq⟩ := hsum
  refine ⟨RU, RV, ΔU, ΔV, baseU, baseV, wU, wV, ?_⟩
  rw [crossCirc_distrib_over_j W n ha hc hd]
  rw [show (∑ j ∈ Finset.range (M + 1),
            cbz (M : ℤ) (j : ℤ) • resHom W 0 ((n : ℤ) + 1) a (W.smul c ((j : ℤ) - 2) d))
        = ∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) • crossCircTerm W n a c d j from
      Finset.sum_congr rfl fun j _ => by rw [crossCircTerm]]
  exact heq

/-! ## Status — the cross tower predicate reduced to the per-`j` shift-`0` commutator-family core.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossCirc_inner_distrib`** / **`crossCirc_distrib_over_j`** — the distributed master split of the
  combined cross families over the inner circle index `j`.
* **`crossCircTerm`** / **`crossCircTerm_inner_mem_grading`** — the per-`j` cross term and its grade.
* **`PresTowerFam_add`** / **`smul_PresTowerFam`** — `PresTowerFam` is closed under finite
  ℂ-combinations (index-set merge + weight scaling).
* **`CrossCircTermTowerEq`** — the per-`j` tower-decomposition predicate (the shift-`0`, mixed-level
  commutator-family core).
* **`CrossCircTowerEq_of_term`** — `CrossCircTermTowerEq` (all `j`) ⟹ `CrossCircTowerEq`.

**Remaining core (engine-verified TRUE, free boson; NOT faked):** `CrossCircTermTowerEq W n K M P a c d j`
— the per-`j` shift-`0` commutator-family collapse of the outer level-`n` residue (pole `n+1`) of
homogeneous `a ∈ 𝒱_K` applied to the homogeneous inner factor `c₍j−2₎d ∈ 𝒱_{M+P-(j-2)-1}` onto
`PresAnm`-towers in `c` (over `M`) and `d` (over `P`).  This is the same combinatorial depth as the
diagonal `AnmCircTowerEq` (`ZhuVermaAnArchMUcircV`) and the proven `leftProd_circ_mem_On`
(`ZhuVermaAnDescent4`, the `Sn_mem_On`/`coeffSn_eq_coeffPn` commutator route via `ZhuRes.gen_jsum`/
`gen_vandermonde`), with the FZ shift replaced by the shift-`0` pole `n+2`.  Engine value
(`certificates/mathematica/mucross_circ.wl`): for `n = 1, a = c = d = J` and `n = 2`, the cross
residue-of-residue lands in `Onm W n 0`.  Discharging `CrossCircTermTowerEq` (per `j`) yields
`CrossCircTowerEq` (via `CrossCircTowerEq_of_term`), hence the last `MUGradedAction` family via
`MUGradedAction_of_crossTower` (`ZhuVermaAnArchMUcrossHM`).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCirc_inner_distrib
  #print axioms VOA.crossCirc_distrib_over_j
  #print axioms VOA.crossCircTerm_inner_mem_grading
  #print axioms VOA.PresTowerFam_add
  #print axioms VOA.smul_PresTowerFam
  #print axioms VOA.CrossCircTowerEq_of_term
-/
