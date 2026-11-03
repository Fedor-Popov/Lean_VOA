/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent23
import VOA.Modules.ZhuVermaAnDescent4
import VOA.Modules.ZhuRightIdeal

/-!
# The LEFT circle-`0` **finite-level Borcherds recombination** (the live (L-circ0) path).

The prior LEFT cross-assembly worked at the γ-mode-finsum level (`USideL_eq_gammaModeFinsum`,
`ZhuVermaAnDescent23`), which is DIVERGENT for the V-side transposition (the transposed scalar's
`s`-finsum has infinite support).  This file works at the **finite-assembly level** instead: it
applies the Borcherds commutator `mode_split_gen` (`v₍A₎(u₍C₎b) = u₍C₎(v₍A₎b) + ∑ₖ cbz(A,k)·(v₍k₎u)₍A+C−k₎b`)
to each V-word of `VSideL` *after truncating the `∑ᶠ s` to the regularity range* (`Vbody_trunc`,
the divergence-avoidance key), giving the master finite decomposition

  **`leftProd_circ0_master_decomp`** : `leftProd W n (circ W 0 u v) b = (USideL − uTransL) − commL`,

where `uTransL` collects the transposed `u₍s₎(v₍·₎b)` words and `commL` the `(v₍k₎u)`-commutator family
(`commL_expand` gives its explicit `(v₍k₎u)`-mode form).  `Lcirc0_mem_of_pieces` discharges (L-circ0)
from the joint membership of the two pieces.

## The PRECISE remaining gate (NOT `sorry`'d / NOT axiomatized)

`Lcirc0_mem` reduces to the JOINT membership `(USideL − uTransL) − commL ∈ On W n`.  The two pieces are
NOT separable: Mathematica-verified (exact `LeastSquares`), the combined-`u` part `USideL − uTransL` is
a grade-`M` tower with the depth-`0`-circle shift `2` (NOT a `PresOn` shift-`2n+2` tower for `n ≥ 1`),
and the `commL` per-`k` scalar is not a shift-`2n+2` tower in `v₍k₎u` either; they recombine JOINTLY
via the single depth-`n` `cbz` cross-assembly identity (the LEFT-circ0 analog of `ZhuRes.gen_jsum` /
`ZhuMu.mu_identity`, carrying the circle-`0` weight `cbz M i` and the LEFT FZ weight `cbz(j+n,n)`)
converting pole-`2` → pole-`2n+2`.  Formalising that one identity discharges both hypotheses jointly,
hence (L-circ0) and the left `gen_mem` via the proved `leftProd_genL_mem_On_of_circ0`
(`ZhuVermaAnDescent22`).  The R-mirror (R-circ0) follows the same template with `rightProd`.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.2; Dong–Li–Mason.
-/
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Step L1 — the single-V-word `mode_split_gen` rewrite (recombination entry point). -/

theorem Vword_split (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (A C : ℤ) :
    W.smul v A (W.smul u C b)
      = W.smul u C (W.smul v A b)
        + ⁅mode (W.Y v) A, mode (W.Y u) C⁆ b :=
  mode_split_gen W v u b A C

theorem Vword_comm_expand (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    ∃ N : ℕ, ∀ (A C : ℤ) (b : 𝒱),
      ⁅mode (W.Y v) A, mode (W.Y u) C⁆ b
        = ∑ k ∈ Finset.range N,
            cbz A (k : ℤ) • W.smul (W.smul v k u) (A + C - (k : ℤ)) b :=
  ZhuHR.mode_commutator_uniform W v u

/-! ## Step L2 — truncate the per-`(i,j,p)` V-body finsum to a finite range, then split. -/

/-- The V-body finsum equals its truncation to `range Nu` (regularity of `u` on `b`). -/
theorem Vbody_trunc (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (co : ℕ → ℂ) (μ : ℤ)
    {Nu : ℤ} (hNu : ∀ k : ℤ, Nu ≤ k → W.smul u k b = 0) :
    (∑ᶠ s : ℕ, co s • W.smul v (μ - s) (W.smul u (s : ℤ) b))
      = ∑ s ∈ Finset.range Nu.toNat, co s • W.smul v (μ - s) (W.smul u (s : ℤ) b) := by
  refine finsum_eq_finsetSum_of_support_subset _ (fun s hs => ?_)
  rw [Function.mem_support] at hs
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hge
  apply hs
  have hsge : Nu ≤ (s : ℤ) := by
    have h1 : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat _
    have h2 : (Nu.toNat : ℤ) ≤ (s : ℤ) := by exact_mod_cast (by omega : Nu.toNat ≤ s)
    omega
  rw [show W.smul u (s : ℤ) b = (0 : 𝒱) from hNu _ hsge,
    PreVertexAlgebra.smul_zero_right, smul_zero]

/-- **The finite per-`(i,j,p)` V-body split.**  On the finite truncation range, the V-body splits
into the u-transposed finite sum plus the commutator finite sum.  Each is a genuine `Finset.sum`. -/
theorem Vbody_finite_split (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (co : ℕ → ℂ) (μ : ℤ) (Ns : ℕ) :
    (∑ s ∈ Finset.range Ns, co s • W.smul v (μ - s) (W.smul u (s : ℤ) b))
      = (∑ s ∈ Finset.range Ns, co s • W.smul u (s : ℤ) (W.smul v (μ - s) b))
        + (∑ s ∈ Finset.range Ns,
            co s • ⁅mode (W.Y v) (μ - s), mode (W.Y u) (s : ℤ)⁆ b) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Vword_split W u v b (μ - s) (s : ℤ), smul_add]

/-- **Per-`(i,j,p)` V-body recombination (finsum form).**  Combining `Vbody_trunc` and
`Vbody_finite_split`: the per-`(i,j,p)` V-body finsum equals the truncated u-transposed sum plus the
truncated commutator sum, with `Nu` the uniform regularity bound of `u` on `b`. -/
theorem Vbody_recombine (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) (co : ℕ → ℂ) (μ : ℤ)
    {Nu : ℤ} (hNu : ∀ k : ℤ, Nu ≤ k → W.smul u k b = 0) :
    (∑ᶠ s : ℕ, co s • W.smul v (μ - s) (W.smul u (s : ℤ) b))
      = (∑ s ∈ Finset.range Nu.toNat, co s • W.smul u (s : ℤ) (W.smul v (μ - s) b))
        + (∑ s ∈ Finset.range Nu.toNat,
            co s • ⁅mode (W.Y v) (μ - s), mode (W.Y u) (s : ℤ)⁆ b) := by
  rw [Vbody_trunc W u v b co μ hNu, Vbody_finite_split W u v b co μ Nu.toNat]

/-! ## Step L3 — the assembled `VSideL` recombination `VSideL = uTransL + commL`.

`VSideL` (Descent23) is `∑_{i,j,p} ∑ᶠ s, vcoeff • v₍μ-s₎(u₍s₎b)` with `μ = (i-2)+(p-n-j-1)` and
`vcoeff = assemblyLeadL · (-1)^s gBinom(i-2) s · (-1)^(i-2)`.  Applying `Vbody_recombine` to each
`(i,j,p)`-body recombines it into the **u-transposed assembly** `uTransL` plus the **commutator
assembly** `commL`, both genuine finite triple-`(i,j,p)`-plus-`s`-sums (`Nu` = the uniform regularity
bound of `u` on `b`). -/

/-- The per-`(i,j,p,s)` V-coefficient of `VSideL` (extracted from the Descent23 `VSideL` body). -/
noncomputable def vcoeffL (M P n : ℕ) (G : ℕ → ℕ) (i j p s : ℕ) : ℂ :=
  assemblyLeadL M P n G i j p * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2) s)
    * ((-1 : ℂ) ^ ((i : ℤ) - 2))

/-- The **u-transposed assembly**: `∑_{i,j,p} ∑_{s<Nu} vcoeffL • u₍s₎(v₍μ-s₎b)`. -/
noncomputable def uTransL (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ)
    (Nu : ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ p ∈ Finset.range (G i + n + 1),
      ∑ s ∈ Finset.range Nu,
        vcoeffL M P n G i j p s
          • W.smul u (s : ℤ)
              (W.smul v (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - s) b)

/-- The **commutator assembly**: `∑_{i,j,p} ∑_{s<Nu} vcoeffL • ⁅v₍μ-s₎, u₍s₎⁆b`. -/
noncomputable def commL (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ)
    (Nu : ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
    ∑ p ∈ Finset.range (G i + n + 1),
      ∑ s ∈ Finset.range Nu,
        vcoeffL M P n G i j p s
          • ⁅mode (W.Y v) (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - s),
              mode (W.Y u) (s : ℤ)⁆ b

/-- **`VSideL = uTransL + commL`.**  The assembled finite-level recombination of `VSideL` via
`Vbody_recombine` applied to each `(i,j,p)`-body (uniform regularity bound `Nu`). -/
theorem VSideL_recombine (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ)
    {Nu : ℤ} (hNu : ∀ k : ℤ, Nu ≤ k → W.smul u k b = 0) :
    VSideL W M P n u v b G = uTransL W M P n u v b G Nu.toNat + commL W M P n u v b G Nu.toNat := by
  rw [VSideL, uTransL, commL, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  -- the inner ∑ᶠ s body matches `Vbody_recombine` with co = vcoeffL, μ = (i-2)+(p-n-j-1)
  set μ : ℤ := ((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) with hμ
  rw [show (∑ᶠ s : ℕ,
            (assemblyLeadL M P n G i j p * ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2) s)
                * ((-1 : ℂ) ^ ((i : ℤ) - 2)))
              • W.smul v (((i : ℤ) - 2) + (p - ((n : ℤ) + (j : ℤ) + 1)) - s)
                  (W.smul u (s : ℤ) b))
        = ∑ᶠ s : ℕ, vcoeffL M P n G i j p s • W.smul v (μ - s) (W.smul u (s : ℤ) b) from
      finsum_congr fun s => by rw [vcoeffL, hμ]]
  rw [Vbody_recombine W u v b (fun s => vcoeffL M P n G i j p s) μ hNu]

/-! ## Step L4 — the master finite-level decomposition of `leftProd W n (circ W 0 u v) b`.

Combining the proved Descent23 master split `leftProd W n (circ W 0 u v) b = USideL − VSideL` with the
`VSideL` recombination `VSideL = uTransL + commL`:

  `leftProd W n (circ W 0 u v) b = (USideL − uTransL) − commL`,

where `USideL − uTransL` is the **combined-u part** (all words `u₍μ₎(v₍γ₎b)`) and `commL` is the
**`(v₍k₎u)`-commutator family**.  This is the honest finite-level Borcherds recombination — assembled WITHOUT any per-piece divergence (each side is a genuine finite sum after the
`Nu`-truncation). -/
theorem leftProd_circ0_master_decomp (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (b : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2) - 1)
    {Nu : ℤ} (hNu : ∀ k : ℤ, Nu ≤ k → W.smul u k b = 0) :
    leftProd W n (circ W 0 u v) b
      = (USideL W M P n u v b G - uTransL W M P n u v b G Nu.toNat)
        - commL W M P n u v b G Nu.toNat := by
  rw [leftProd_circ0_eq_USideL_sub_VSideL W n hu hv b G hG,
    VSideL_recombine W M P n u v b G hNu]
  abel

/-! ## Step L5 — the `commL` commutator family expanded to the `(v₍k₎u)`-mode form.

Expanding each `⁅v₍μ-s₎, u₍s₎⁆ b` via `mode_commutator_uniform` (`Vword_comm_expand`) gives, with
`Nk` the uniform commutator-locality bound for `(v, u)`:

  `commL = ∑_{i,j,p} ∑_{s<Nu} vcoeffL • ∑_{k<Nk} cbz(μ-s, k) • (v₍k₎u)₍μ-k₎ b`,

with `μ = (i-2)+(p-n-j-1)`.  Each `v₍k₎u` is homogeneous of grade `P+M-k-1` (`circ`-base for the
`(B)` family).  This is the genuine `(v₍k₎u)`-commutator residue: a finite ℂ-combination of single
modes `(v₍k₎u)₍γ₎b` whose membership in `On W n` is the LEFT-circ0 analog of `Sn_mem_On`
(`ZhuVermaAnDescent4`) — the depth-`n` `gen_vandermonde`/`gen_jsum` collapse onto `PresOn`-towers in
the homogeneous `v₍k₎u`. -/
theorem commL_expand (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (u v b : 𝒱) (G : ℕ → ℕ) (Nu : ℕ)
    {Nk : ℕ}
    (hNk : ∀ (A C : ℤ) (c : 𝒱),
      ⁅mode (W.Y v) A, mode (W.Y u) C⁆ c
        = ∑ k ∈ Finset.range Nk,
            cbz A (k : ℤ) • W.smul (W.smul v k u) (A + C - (k : ℤ)) c) :
    commL W M P n u v b G Nu
      = ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (n + 1),
          ∑ p ∈ Finset.range (G i + n + 1),
            ∑ s ∈ Finset.range Nu,
              vcoeffL M P n G i j p s •
                ∑ k ∈ Finset.range Nk,
                  cbz (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - s) (k : ℤ)
                    • W.smul (W.smul v k u)
                        ((((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - s)
                            + (s : ℤ) - (k : ℤ)) b := by
  rw [commL]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ => ?_
  rw [hNk (((i : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - s) (s : ℤ) b]

/-! ## Step L6 — the conditional discharge of (L-circ0) and the precise remaining gate.

The master decomposition `leftProd_circ0_master_decomp` reduces the TARGET

  `Lcirc0_mem : leftProd W n (circ W 0 u v) b ∈ On W n`

to the membership of the two finite-level pieces
  `(USideL − uTransL) ∈ On W n`   — the **combined-u part** (all `u₍μ₎(v₍γ₎b)` words), and
  `commL ∈ On W n`                — the **`(v₍k₎u)`-commutator family**.
We record this discharge (conditional on the two membership inputs), and below document precisely why
neither piece closes individually — the genuine depth-`n` cross-assembly gate. -/

/-- **(L-circ0) from the two finite-level pieces.**  Supplying `(USideL − uTransL) ∈ On` and
`commL ∈ On` for a uniform regularity bound `Nu` discharges the target. -/
theorem Lcirc0_mem_of_pieces (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (b : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2) - 1)
    {Nu : ℤ} (hNu : ∀ k : ℤ, Nu ≤ k → W.smul u k b = 0)
    (hUcomb : (USideL W M P n u v b G - uTransL W M P n u v b G Nu.toNat) ∈ On W n)
    (hComm : commL W M P n u v b G Nu.toNat ∈ On W n) :
    leftProd W n (circ W 0 u v) b ∈ On W n := by
  rw [leftProd_circ0_master_decomp W n hu hv b G hG hNu]
  exact (On W n).sub_mem hUcomb hComm

/-!
## State of (L-circ0): the PRECISE remaining gate (NOT `sorry`, NOT axiomatized).

Everything above is axiom-clean (`[propext, Classical.choice, Quot.sound]`).  The honest
finite-level Borcherds recombination is fully proved:

  `leftProd_circ0_master_decomp` :
    `leftProd W n (circ W 0 u v) b = (USideL − uTransL) − commL`,

assembled WITHOUT any per-piece divergence.  The divergence (that the
γ-mode-finsum route `USideL_eq_gammaModeFinsum` hits) is avoided by the **`Nu`-truncation**
(`Vbody_trunc`): the per-`(i,j,p)` V-body `∑ᶠ s, vco s • v₍μ-s₎(u₍s₎b)` is supported on `s < Nu`
(regularity of `u` on `b`), so it is a genuine `Finset.sum` on which `mode_split_gen` (`Vword_split`)
splits term-by-term into the u-transposed sum (`uTransL`) plus the commutator sum (`commL`).  The
naive finsum split into `∑ᶠ s, u₍s₎(v₍μ-s₎b)` plus `∑ᶠ s, ⁅v₍μ-s₎,u₍s₎⁆b` is INVALID — for the
low circle indices `i ∈ {0,1}` (`ℓ = i-2 ∈ {-2,-1}`) the weight `(-1)^s gBinom(i-2) s` has INFINITE
support in `s`, so neither piece converges individually; only the `Nu`-truncated finite sums do.

### Why neither piece closes individually (Mathematica-verified, exact `LeastSquares`)

The two output bases `u₍μ₎(v₍γ₎b)` (from `USideL` and `uTransL`) and `(v₍k₎u)₍γ₎b` (from `commL`) are
independent, so the membership splits along them:

* **Combined-u part** `USideL − uTransL`.  Per fixed base-mode `γ`, the net `u₍μ₎(v₍γ₎b)`-coefficient
  is a grade-`M` tower in `u` **with the depth-`0`-circle shift `2`** (`∑_δ wU δ · cbz(M+n+δ,μ+2+δ)`),
  verified residual-`0` at shift `2`, residual-`≠0` at shift `4`.  But a `PresOn W M n δ` tower carries
  shift `2n+2+δ ≥ 2n+2 > 2` for `n ≥ 1`; a shift-`2` tower can NOT be written as a ℂ-combination of
  shift-`≥2n+2` `PresOn`-towers (the leading `μ`-degree differs).  So no per-`γ` `UfamOn`-collapse
  exists — exactly the "pole-`2` overshoot" of `ZhuVermaAnDescent23`.

* **Commutator part** `commL`.  After `mode_commutator_uniform` (`commL_expand`), the `(v₍k₎u)₍μ-k₎b`
  mode is `s`-independent (`A+C-k = μ-k`), so `commL = ∑_{i,j,p,k} [∑_{s<Nu} vcoeffL·cbz(μ-s,k)] ·
  (v₍k₎u)₍μ-k₎b`.  Per fixed `k`, the net `(v₍k₎u)₍M₀₎b`-coefficient is NOT a shift-`2n+2` tower in
  the grade-`(P+M-k-1)` homogeneous `v₍k₎u` (verified residual-`≠0`, all `n,k`).

Hence the membership is genuinely a CROSS-assembly: the shift-`2` combined-u tower and the
non-tower commutator family recombine — via the depth-`n` `cbz` identity that converts pole-`2` →
pole-`2n+2` (the LEFT-circ0 analog of `ZhuRes.gen_jsum` / `ZhuMu.mu_identity`, carrying the circle-`0`
weight `cbz M i` and the left FZ weight `cbz(j+n,n)` in place of the right-circle weights) — into
genuine shift-`2n+2` `PresOn`-towers (`∈ On` by `Pres_mem_On`).  Formalising that one combinatorial
identity is the single remaining input; it discharges BOTH `hUcomb` and `hComm` jointly (they are not
separable), hence (L-circ0) via `Lcirc0_mem_of_pieces`, hence the left `gen_mem` via the proved
`leftProd_genL_mem_On_of_circ0` (`ZhuVermaAnDescent22`).

The proved, axiom-clean foundation here (`leftProd_circ0_master_decomp` + `commL_expand` +
`Lcirc0_mem_of_pieces`) is the exact finite-level entry point for that identity; no `sorry`, no
`axiom`, no `pbw`.
-/

end VOA
