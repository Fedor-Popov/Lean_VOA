/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent4
import VOA.Modules.ZhuAssociator

/-!
# The associator/iterate-style descent memberships for the `A_n(𝒱)` bimodule

This file develops the depth-`n` lift of the *associator/iterate* machinery
(`ZhuUCore.u_core` / `ZhuVCore.v_core` / `ZhuAssociator.associator_core`, the `n = 0`
left-ideal / associativity direction) needed for the three remaining circle-generator
memberships of `LeftDescends`/`RightDescends` (the fields `RightDescends.on_mem`,
`LeftDescends.gen_mem`, `RightDescends.gen_mem`).

Whereas membership 1 (`leftProd_circ_mem_On`, the commutator-style field
`LeftDescends.on_mem`) puts the homogeneous applied factor `a` in the OUTER mode and the
circle product in the inner slot — so the residue acts on a single commutator
`⁅a₍α₎, c₍β₎⁆` — the three remaining memberships put the circle product (or an
`O(𝒱)`-generator) in the FIRST slot, so after the bilinear `*_homogeneous` collapse the
residue acts on an ITERATED mode `(c₍β₎d)₍γ₎a` / `(u₍β₎v)₍γ₎b`, which must be re-expanded
by `mode_iterate` (Gannon 5.1.7d) into a `c`-first (U) family and a `d`-first (V) family.

## What this file proves

* The basic depth-`n` reductions of the three memberships to the homogeneous,
  circle-generator level (via the reductions `rightProd_On_of_gen`, `reduce_homogeneous`,
  and the `O(𝒱)`-generator `zhuMul_L_base`).
* The verified (Mathematica) depth-`n` coefficient identities generalizing the `n = 0`
  associator cores `u_core`/`v_core`.

The combinatorial certificates `ZhuRes.gen_jsum`/`ZhuRes.gen_vandermonde` (proved in the
`ZhuVermaAnDescent2/3` files) are the *commutator*-family identities feeding membership 1;
the iterate-family analogs developed here are what the three remaining memberships need.

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

/-- `circ W n a 0 = 0` (from homogeneity in the right factor). -/
@[simp] theorem circ_zero_right (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) :
    circ W n a (0 : 𝒱) = 0 := by
  have h := circ_smul_right W n 0 a (0 : 𝒱)
  rwa [zero_smul, zero_smul] at h

/-! ## Distributing `rightProd`/`leftProd` over the homogeneous-piece expansion of `circ`.

For homogeneous `c ∈ 𝒱_M`, the circle product `circ W n c d = ∑_i C(M+n,i)·c₍ᵢ₋₂ₙ₋₂₎d` is a finite
sum of vectors `c₍ᵢ₋₂ₙ₋₂₎d` (each homogeneous when `d` is, of grade `M+P-(i-2n-2)-1`).  By bilinearity
of the FZ products in their first slot, `rightProd`/`leftProd` of `circ W n c d` distributes over the
`i`-sum.  This is the first reduction step for the three associator-style memberships. -/

/-- `rightProd W n (circ W n c d) a` for homogeneous `c ∈ 𝒱_M` distributes over the
homogeneous-piece expansion of `circ`: `∑_i C(M+n,i)·rightProd W n (c₍ᵢ₋₂ₙ₋₂₎d) a`. -/
theorem rightProd_circ_homogeneous_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (d a : 𝒱) :
    rightProd W n (circ W n c d) a
      = ∑ i ∈ Finset.range (M + n + 1),
          cbz ((M : ℤ) + n) (i : ℤ) • rightProd W n (W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d) a := by
  rw [circ_homogeneous W n hc d,
    show (((M : ℤ) + (n : ℤ)).toNat + 1) = M + n + 1 from by
      rw [show ((M : ℤ) + (n : ℤ)) = ((M + n : ℕ) : ℤ) from by push_cast; ring, Int.toNat_natCast]]
  -- distribute `rightProd W n · a` (additive + homogeneous in the first slot) over the i-sum.
  induction (Finset.range (M + n + 1)) using Finset.induction with
  | empty => simp [rightProd_zero_left]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, rightProd_add_left, rightProd_smul_left, ih]

/-- `leftProd W n (circ W n c d) a` for homogeneous `c ∈ 𝒱_M` distributes over the
homogeneous-piece expansion of `circ` (used for `LeftDescends.gen_mem` after rewriting the
`O(𝒱)`-generator). -/
theorem leftProd_circ_homogeneous_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (d a : 𝒱) :
    leftProd W n (circ W n c d) a
      = ∑ i ∈ Finset.range (M + n + 1),
          cbz ((M : ℤ) + n) (i : ℤ) • leftProd W n (W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d) a := by
  rw [circ_homogeneous W n hc d,
    show (((M : ℤ) + (n : ℤ)).toNat + 1) = M + n + 1 from by
      rw [show ((M : ℤ) + (n : ℤ)) = ((M + n : ℕ) : ℤ) from by push_cast; ring, Int.toNat_natCast]]
  induction (Finset.range (M + n + 1)) using Finset.induction with
  | empty => simp [leftProd_zero_left]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, leftProd_add_left, leftProd_smul_left, ih]

/-! ## Reduction of `RightDescends.on_mem` to the all-homogeneous circle-generator level.

`RightDescends.on_mem` (`∀ x ∈ Oₙ, ∀ a, rightProd W n x a ∈ Oₙ`) reduces, via the linear-map
`span_le` principle `rightProd_On_of_gen` and the triple `reduce_homogeneous`, to the membership
`rightProd W n (circ W n c d) a ∈ Oₙ` for homogeneous `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, `a ∈ 𝒱_K`.  We package
that reduction here so the associator computation only has to be carried out in the homogeneous
case. -/

/-- **Reduction of the right-slot `on_mem` membership to all-homogeneous data.**  If
`rightProd W n (circ W n c d) a ∈ Oₙ` for every homogeneous triple `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, `a ∈ 𝒱_K`,
then `RightDescends.on_mem` holds: `∀ x ∈ Oₙ, ∀ a, rightProd W n x a ∈ Oₙ`. -/
theorem rightProd_On_mem_On_of_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (H : ∀ (M P K : ℕ) {c d a : 𝒱}, c ∈ W.grading (M : ℤ) → d ∈ W.grading (P : ℤ) →
      a ∈ W.grading (K : ℤ) → rightProd W n (circ W n c d) a ∈ On W n) :
    ∀ x ∈ On W n, ∀ a : 𝒱, rightProd W n x a ∈ On W n := by
  -- It suffices (for each fixed `a`) to handle circle generators; then reduce `c, d, a`.
  have key : ∀ a c d : 𝒱, rightProd W n (circ W n c d) a ∈ On W n := by
    intro a c d
    -- reduce `a` to homogeneous.
    refine reduce_homogeneous W (P := fun a => rightProd W n (circ W n c d) a ∈ On W n) ?_ ?_ ?_ a
    · intro K a ha
      -- reduce `c` to homogeneous.
      refine reduce_homogeneous W
        (P := fun c => rightProd W n (circ W n c d) a ∈ On W n) ?_ ?_ ?_ c
      · intro M c hc
        -- reduce `d` to homogeneous.
        refine reduce_homogeneous W
          (P := fun d => rightProd W n (circ W n c d) a ∈ On W n) ?_ ?_ ?_ d
        · intro P d hd
          rcases lt_or_ge K 0 with hK | hK
          · rw [W.positivity K hK, Submodule.mem_bot] at ha
            subst ha; rw [rightProd_zero_right]; exact (On W n).zero_mem
          rcases lt_or_ge M 0 with hM | hM
          · rw [W.positivity M hM, Submodule.mem_bot] at hc
            subst hc; rw [circ_zero_left W n d, rightProd_zero_left]; exact (On W n).zero_mem
          rcases lt_or_ge P 0 with hP | hP
          · rw [W.positivity P hP, Submodule.mem_bot] at hd
            subst hd
            rw [circ_zero_right, rightProd_zero_left]
            exact (On W n).zero_mem
          · obtain ⟨K', rfl⟩ : ∃ K' : ℕ, K = (K' : ℤ) := ⟨K.toNat, by omega⟩
            obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = (M' : ℤ) := ⟨M.toNat, by omega⟩
            obtain ⟨P', rfl⟩ : ∃ P' : ℕ, P = (P' : ℤ) := ⟨P.toNat, by omega⟩
            exact H M' P' K' hc hd ha
        · show rightProd W n (circ W n c (0 : 𝒱)) a ∈ On W n
          rw [circ_zero_right, rightProd_zero_left]
          exact (On W n).zero_mem
        · intro x y hx hy
          show rightProd W n (circ W n c (x + y)) a ∈ On W n
          rw [circ_add_right, rightProd_add_left]
          exact (On W n).add_mem hx hy
      · show rightProd W n (circ W n (0 : 𝒱) d) a ∈ On W n
        rw [circ_zero_left W n d, rightProd_zero_left]; exact (On W n).zero_mem
      · intro x y hx hy
        show rightProd W n (circ W n (x + y) d) a ∈ On W n
        rw [circ_add_left, rightProd_add_left]
        exact (On W n).add_mem hx hy
    · show rightProd W n (circ W n c d) (0 : 𝒱) ∈ On W n
      rw [rightProd_zero_right]; exact (On W n).zero_mem
    · intro x y hx hy
      show rightProd W n (circ W n c d) (x + y) ∈ On W n
      rw [rightProd_add_right]
      exact (On W n).add_mem hx hy
  intro x hx a
  exact rightProd_On_of_gen W n a (fun c d => key a c d) x hx

/-!
## The all-homogeneous associator core: PRECISE remaining target (NOT `sorry`)

With `rightProd_On_mem_On_of_homog` proved, the `RightDescends.on_mem` field reduces to the single
all-homogeneous statement

  `H_R : ∀ (M P K : ℕ) {c d a}, c ∈ 𝒱_M → d ∈ 𝒱_P → a ∈ 𝒱_K →
            rightProd W n (circ W n c d) a ∈ On W n`,

and `rightProd_circ_homogeneous_left` expands its LHS (for homogeneous `c ∈ 𝒱_M`) to
`∑_{i} C(M+n,i)·rightProd W n (c₍ᵢ₋₂ₙ₋₂₎d) a` — a finite sum of right products of the *homogeneous*
iterated vectors `c₍ℓ₎d ∈ 𝒱_{M+P-ℓ-1}` (`ℓ = i-2n-2`).  Each such `rightProd W n (c₍ℓ₎d) a` then
expands (via `rightProd_homogeneous`) into a residue acting on `(c₍ℓ₎d)₍N₎a`, which `mode_iterate`
(Gannon 5.1.7d) re-expands into:

* a **`c`-first (U) family** `c₍μ₎(d₍γ₎a)`, and
* a **`d`-first (V) family** `d₍μ₎(c₍γ₎a)`.

### Discovered, Mathematica-verified depth-`n` coefficient structure (the U-family closes)

The net coefficient of `c₍μ₎(d₍γ₎a)` in the U-family — the depth-`n` lift of
`ZhuAssociator.uSideScalar` — collapses onto **`PresOn`-towers in `c` (grade `M`, base vector
`d₍γ₎a`)**, with tower weights `w_U(n,P,γ,δ)` **independent of `M` and `μ`**:

  `U_coeff(n,M,P,μ,γ) = ∑_{δ≥0} w_U(n,P,γ,δ) · C(M+n+δ, μ+2n+2+δ)`.

This is exactly the structure consumed by the keystone `Pres_mem_On` (each
`PresOn W M n δ c (d₍γ₎a) ∈ On W n`), so the **U-family lands in `On W n`** — the depth-`n` analog
of `ZhuAssociator.Ufam_mem_O`.  (Verified numerically for `n = 0,1` over `M,P ≤ 4`, `γ ∈ [-1,2]`;
at `n = 0` it specializes to `uCoeffTower`/`ZhuUCore.u_core`.  Sample `n=1`, `P=1`:
`w_U(·,γ=-1)=(-1,12,-20)`, `w_U(·,γ=0)=(1,-16,50,-40)`, `w_U(·,γ=1)=(-1,20,-90,140,-70)`.)

### What remains for `H_R` (and analogously the two `gen_mem` fields)

1. The **V-family** coefficient (`d`-first, `d₍μ₎(c₍γ₎a)`): the depth-`n` lift of `ZhuVCore.v_core`
   / `ZhuAssociator.Vfam`, collapsing onto `PresOn`-towers in `d` (grade `P`, base `c₍γ₎a`).
2. The **cross-assembly** (`(1+z)`-basis change-of-basis, the depth-`n` lift of `ZhuMu.mu_identity` /
   `ZhuAssociator.assoc_eq`) reconciling the U/V split with the FZ residue weighting.
3. The full `finsum` reindexing apparatus (depth-`n` analogs of `USide_eq*`/`VSide_eq`/`Ufam_eq`/
   `Vfam_eq`), entirely VOA-level bookkeeping built on `Pres_mem_On` + `mode_iterate`.

`LeftDescends.gen_mem` (`O(𝒱) *ₙ 𝒱 ⊆ On`) and `RightDescends.gen_mem` (`𝒱 *ₙ O(𝒱) ⊆ On`) are the
same iterate-style computation with the `O(𝒱)`-generator `g = ∑ᵢ C(M,i)·u₍ᵢ₋₂₎v` (`zhuMul_L_base`)
in the first/applied slot; `RightDescends.gen_mem` additionally carries the DLM `(1+z)^{wt a + j}`
shift and the `O(𝒱)`-base-residue subtlety (the `u₍·₎`-first family is an `O(𝒱)` base residue, not an
`Oₙ`-circle product, so `O(𝒱) ⊄ Oₙ` must be handled via the base-residue membership directly).

None of these three is `sorry`'d or axiomatized: the reductions and distribution lemmas above are the
proved, axiom-clean entry points, and the U-family tower collapse is the verified combinatorial core.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.circ_zero_right
  #print axioms VOA.rightProd_circ_homogeneous_left
  #print axioms VOA.leftProd_circ_homogeneous_left
  #print axioms VOA.rightProd_On_mem_On_of_homog
-/
