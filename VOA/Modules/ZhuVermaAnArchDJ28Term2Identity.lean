/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ28Term2
import VOA.Modules.ZhuRingResidue
import VOA.Modules.ZhuRightIdeal

/-!
# `Term2Level` — the DLM Part-3 commutator scalar collapse.

The `Term₂` commutator identity (`ZhuVermaAnArchDJ28Term2.Term2Level_of_commIdentity`) reduces
`Term2Level` to the explicit vector identity

  `anmRight W n 0 a (anmCirc W n 0 c d)
     = anmCirc W n 0 c (anmRight W n 0 a d)
       + ∑_j ∑_{p≤j} cbz(-(n+1), j-p)·cbz(K,p)·resHom W (j+1-p) (2n+3+j-p) (a₍ⱼ₎c) d`.

The *scalar* heart of that reorganization — collapsing the `(a₍ⱼ₎c)`-mode double `(p,i)`-sum onto the
off-diagonal residue rows — is the Vandermonde identity `coeffST2_collapse` proved here (engine-verified
exact, `certificates/mathematica/term2_coeff.wl`, `0/5440` mismatches).  It is proven from the three
Frenkel–Zhu Vandermonde convolutions `ZhuRes.vandermonde_range` (splitting the shifted top row
`cbz(p-(n+1), s)`), `ZhuRes.stepB` (`cbz(K,p)·cbz(p,i) = cbz(K,i)·cbz(K-i,p-i)`) and `ZhuRes.stepC`
(the shifted Vandermonde `∑_p cbz(K-i,p-i)·cbz(M,T-p) = cbz(K+M-i,T-i)`) — the same route as
`ZhuRes.zhu_right_binom` / `gen_vandermonde`, at the `(n,0)` poles `n+1` (outer) / `n+2` (inner).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.
-/

namespace VOA

open scoped BigOperators

/-- **The `Term₂` commutator mode-coefficient collapse** (three Vandermonde convolutions).  The
`(a₍ₛ₎c)`-mode coefficient of the level-`n` commutator double `(p,i)`-sum collapses onto the
off-diagonal residue rows:

  `∑_{p≤K} cbz(K,p)·cbz(M,X-p)·cbz(p-(n+1), s)
     = ∑_{t≤s} cbz(-(n+1), s-t)·cbz(K,t)·cbz(K+M-t, X-t)`

(here `X = m + (2n+3) + s`, the collected inner mode value).  Engine-verified exact
(`certificates/mathematica/term2_coeff.wl`).  Proof: split `cbz(p-(n+1),s)` by `vandermonde_range` into
`∑_i cbz(p,i)·cbz(-(n+1),s-i)`, swap the `p`/`i` sums, then collapse the inner `p`-sum per `i` by
`stepB` + `stepC` (the `i > K` terms vanish, `cbz(K,i) = 0`). -/
theorem coeffST2_collapse (K M n s : ℕ) (X : ℤ) :
    (∑ p ∈ Finset.range (K + 1),
      cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (X - (p : ℤ)) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
      = ∑ t ∈ Finset.range (s + 1),
        cbz (-(n : ℤ) - 1) ((s : ℤ) - (t : ℤ)) * cbz (K : ℤ) (t : ℤ)
          * cbz ((K : ℤ) + (M : ℤ) - (t : ℤ)) (X - (t : ℤ)) := by
  -- Step 1: split the shifted top row `cbz(p-(n+1), s)` by Vandermonde.
  have hexp : ∀ p : ℕ, cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
      = ∑ i ∈ Finset.range (s + 1), cbz (p : ℤ) (i : ℤ) * cbz (-(n : ℤ) - 1) ((s : ℤ) - (i : ℤ)) := by
    intro p
    rw [show (p : ℤ) - ((n : ℤ) + 1) = (p : ℤ) + (-(n : ℤ) - 1) from by ring]
    exact (ZhuRes.vandermonde_range (p : ℤ) (-(n : ℤ) - 1) (s : ℤ)
      (N := s + 1) (by push_cast; omega)).symm
  -- Rewrite the LHS: distribute the `i`-sum and swap `∑_p ∑_i ↦ ∑_i ∑_p`.
  rw [show (∑ p ∈ Finset.range (K + 1),
            cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (X - (p : ℤ)) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
        = ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (s + 1),
            cbz (-(n : ℤ) - 1) ((s : ℤ) - (i : ℤ))
              * (cbz (K : ℤ) (p : ℤ) * cbz (p : ℤ) (i : ℤ) * cbz (M : ℤ) (X - (p : ℤ))) from
      Finset.sum_congr rfl fun p _ => by
        rw [hexp p, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring]
  rw [Finset.sum_comm]
  -- Per `i`: collapse the inner `p`-sum via `stepB` + `stepC`.
  refine Finset.sum_congr rfl fun i hi => ?_
  have his : (i : ℤ) ≤ (s : ℤ) := by have := Finset.mem_range.mp hi; exact_mod_cast Nat.lt_succ_iff.mp this
  rw [← Finset.mul_sum]
  by_cases hiK : i ≤ K
  · -- `i ≤ K`: `∑_p cbz(K,p)cbz(p,i)cbz(M,X-p) = cbz(K,i)·cbz(K+M-i, X-i)` (`stepB` + `stepC`).
    rw [show (∑ p ∈ Finset.range (K + 1),
              cbz (K : ℤ) (p : ℤ) * cbz (p : ℤ) (i : ℤ) * cbz (M : ℤ) (X - (p : ℤ)))
          = cbz (K : ℤ) (i : ℤ)
              * ∑ p ∈ Finset.range (K + 1), cbz ((K : ℤ) - (i : ℤ)) ((p : ℤ) - (i : ℤ))
                  * cbz (M : ℤ) (X - (p : ℤ)) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => by
          rw [ZhuRes.stepB K (p : ℤ) (i : ℤ)]; ring]
    rw [ZhuRes.stepC ((K : ℤ) - (i : ℤ)) (M : ℤ) X (i : ℤ) (N := K + 1)
        (by omega) (by positivity) (by push_cast; omega)]
    rw [show ((K : ℤ) - (i : ℤ)) + (M : ℤ) = (K : ℤ) + (M : ℤ) - (i : ℤ) from by ring]
    ring
  · -- `i > K`: both sides vanish (`cbz(K,i) = 0`).
    have hKi : cbz (K : ℤ) (i : ℤ) = 0 :=
      cbz_lt (by positivity) (by exact_mod_cast Nat.lt_of_not_le hiK)
    rw [show (∑ p ∈ Finset.range (K + 1),
              cbz (K : ℤ) (p : ℤ) * cbz (p : ℤ) (i : ℤ) * cbz (M : ℤ) (X - (p : ℤ)))
          = 0 from by
        refine Finset.sum_eq_zero fun p hp => ?_
        rw [ZhuRes.stepB K (p : ℤ) (i : ℤ), hKi, zero_mul, zero_mul]]
    rw [mul_zero, hKi]; ring

open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- General mode bracket split: `a₍α₎(c₍β₎d) = c₍β₎(a₍α₎d) + ⁅a₍α₎, c₍β₎⁆ d`. -/
theorem term2_bracket_split (W : VertexOperatorAlgebra 𝒱) (a c d : 𝒱) (α β : ℤ) :
    W.smul a α (W.smul c β d)
      = W.smul c β (W.smul a α d) + ⁅mode (W.Y a) α, mode (W.Y c) β⁆ d := by
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply]
  simp only [PreVertexAlgebra.smul_def, mode_apply]
  abel

/-- **The `Term₂` ordered/commutator split** (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).  Expanding both the
level-`n` outer action and inner circle and applying `term2_bracket_split` per `(p,i)`:

  `anmRight W n 0 a (anmCirc W n 0 c d)
     = anmCirc W n 0 c (anmRight W n 0 a d)
       + ∑_p ∑_i (cbz K p · cbz M i) • ⁅a₍p-(n+1)₎, c₍i-(n+2)₎⁆ d`.

The ordered term is a level-`n` circle (`∈ Onm`, `anmCirc_mem_Onm`); the commutator sum is the DLM
Part-3 family, `∈ Onm` via `mode_commutator_uniform` + `coeffST2_collapse` + `resHom_offdiag_mem_Onm`. -/
theorem term2_split (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    anmRight W n 0 a (anmCirc W n 0 c d)
      = anmCirc W n 0 c (anmRight W n 0 a d)
        + ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
              • ⁅mode (W.Y a) ((p : ℤ) - ((n : ℤ) + 1)),
                  mode (W.Y c) ((i : ℤ) - ((n : ℤ) + 2))⁆ d := by
  -- Expand the LHS: `anmRight n 0 a (anmCirc n 0 c d)` as a `(p,i)` double sum of `a₍·₎(c₍·₎d)`.
  have hLHS : anmRight W n 0 a (anmCirc W n 0 c d)
      = ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
          (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
            • W.smul a ((p : ℤ) - ((n : ℤ) + 1)) (W.smul c ((i : ℤ) - ((n : ℤ) + 2)) d) := by
    rw [anmRight_zero, anmCirc_zero, resHom_homogeneous W 0 ((n : ℤ) + 1) ha,
      show ((K : ℤ) + 0).toNat + 1 = K + 1 from by simp]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [resHom_homogeneous W 0 ((n : ℤ) + 2) hc, show ((M : ℤ) + 0).toNat + 1 = M + 1 from by simp,
      PreVertexAlgebra.smul_def, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, smul_smul, ← PreVertexAlgebra.smul_def]
    congr 1 <;> simp only [add_zero, mul_comm]
  -- Expand the ordered term: `anmCirc n 0 c (anmRight n 0 a d)` as a `(p,i)` double sum of `c₍·₎(a₍·₎d)`.
  have hORD : anmCirc W n 0 c (anmRight W n 0 a d)
      = ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
          (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
            • W.smul c ((i : ℤ) - ((n : ℤ) + 2)) (W.smul a ((p : ℤ) - ((n : ℤ) + 1)) d) := by
    rw [anmCirc_zero, anmRight_zero, resHom_homogeneous W 0 ((n : ℤ) + 2) hc,
      show ((M : ℤ) + 0).toNat + 1 = M + 1 from by simp, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [resHom_homogeneous W 0 ((n : ℤ) + 1) ha, show ((K : ℤ) + 0).toNat + 1 = K + 1 from by simp,
      PreVertexAlgebra.smul_def, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, smul_smul, ← PreVertexAlgebra.smul_def]
    congr 1 <;> simp only [add_zero, mul_comm]
  rw [hLHS, hORD, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [term2_bracket_split W a c d ((p : ℤ) - ((n : ℤ) + 1)) ((i : ℤ) - ((n : ℤ) + 2)), smul_add]

/-- Inner `i`-sum reindex onto the mode value (`m = p+i-(2n+3)-s`). -/
theorem term2_inner_reindex (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (w d : 𝒱) (s p : ℤ) :
    (∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ)
        • W.smul w ((p : ℤ) + (i : ℤ) - (2 * (n : ℤ) + 3) - s) d)
      = ∑ᶠ m : ℤ, cbz (M : ℤ) (m + (2 * (n : ℤ) + 3) + s - p) • W.smul w m d := by
  rw [show (∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ)
          • W.smul w ((p : ℤ) + (i : ℤ) - (2 * (n : ℤ) + 3) - s) d)
        = ∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ)
            • W.smul w ((i : ℤ) + (p - (2 * (n : ℤ) + 3) - s)) d from
      Finset.sum_congr rfl fun i _ => by
        rw [show (p : ℤ) + (i : ℤ) - (2 * (n : ℤ) + 3) - s = (i : ℤ) + (p - (2 * (n : ℤ) + 3) - s)
          from by ring]]
  rw [ZhuHR.rangeSmul_eq_finsumZ (fun q : ℤ => cbz (M : ℤ) q) (fun q => W.smul w q d)
      (p - (2 * (n : ℤ) + 3) - s) (fun q hq => cbz_apply_neg (M : ℤ) hq)
      (fun q hq => cbz_lt (by positivity) (by exact_mod_cast hq))]
  rw [← finsum_comp_equiv (Equiv.addRight (p - (2 * (n : ℤ) + 3) - s))
      (f := fun m : ℤ => cbz (M : ℤ) (m + (2 * (n : ℤ) + 3) + s - p) • W.smul w m d)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + (p - (2 * (n : ℤ) + 3) - s)) + (2 * (n : ℤ) + 3) + s - p = q from by ring]

/-- **The `S_s` double `(p,i)`-sum collapses onto `∑ᶠ_m`** (mirror of `ZhuHR.S_eq_finsum`, poles
`n+1`/`n+2`). -/
theorem term2_S_eq_finsum (W : VertexOperatorAlgebra 𝒱) (n K M s : ℕ) (w d : 𝒱) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
          • W.smul w ((p : ℤ) + (i : ℤ) - (2 * (n : ℤ) + 3) - (s : ℤ)) d)
      = ∑ᶠ m : ℤ,
          (∑ p ∈ Finset.range (K + 1),
              cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ))
                * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) • W.smul w m d := by
  rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
              • W.smul w ((p : ℤ) + (i : ℤ) - (2 * (n : ℤ) + 3) - (s : ℤ)) d)
        = ∑ p ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
              • ∑ᶠ m : ℤ, cbz (M : ℤ) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ)) • W.smul w m d from
      Finset.sum_congr rfl fun p _ => by
        rw [← term2_inner_reindex W M n w d (s : ℤ) (p : ℤ), Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]; ring_nf]
  rw [show (∑ p ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
              • ∑ᶠ m : ℤ, cbz (M : ℤ) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ)) • W.smul w m d)
        = ∑ p ∈ Finset.range (K + 1),
            ∑ᶠ m : ℤ,
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ))
                * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) • W.smul w m d from
      Finset.sum_congr rfl fun p _ => by
        have hfin : Function.HasFiniteSupport
            (fun m : ℤ => cbz (M : ℤ) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ)) • W.smul w m d) :=
          ZhuHR.smul_support_of_scalar W w d _
            (Set.Finite.subset
              (ZhuHR.cbz_shift_support_fin (d := (M : ℤ)) (by positivity)
                ((2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ)))
              (fun m hm => by
                rw [Function.mem_support] at hm ⊢
                intro h; apply hm
                rw [show m + (2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ)
                    = m + ((2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ)) from by ring]; exact h))
        rw [smul_finsum' (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) hfin]
        refine finsum_congr fun m => ?_
        rw [smul_smul]; ring_nf]
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun m p => (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ))
          * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) • W.smul w m d)
      (fun p _ => ?_)]
  · exact finsum_congr fun m => by rw [Finset.sum_smul]
  · refine ZhuHR.smul_support_of_scalar W w d _ (Set.Finite.subset
      (ZhuHR.cbz_shift_support_fin (d := (M : ℤ)) (by positivity)
        ((2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ))) ?_)
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h; apply hm
    rw [show (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ))
          * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
        = (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
            * cbz (M : ℤ) (m + ((2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ))) from by
        rw [show m + ((2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ))
            = m + (2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ) from by ring]; ring,
      h, mul_zero]

/-- **A homogeneous residue collapses onto `∑ᶠ_m`** (mirror of `ZhuHR.Pres_eq_finsum`). -/
theorem term2_resHom_finsum (W : VertexOperatorAlgebra 𝒱) {Ws : ℕ} {w : 𝒱}
    (hw : w ∈ W.grading (Ws : ℤ)) (d : 𝒱) (sh po : ℤ) (hsh : 0 ≤ (Ws : ℤ) + sh) :
    resHom W sh po w d = ∑ᶠ m : ℤ, cbz ((Ws : ℤ) + sh) (m + po) • W.smul w m d := by
  rw [resHom_homogeneous W sh po hw d]
  rw [show (∑ i ∈ Finset.range (((Ws : ℤ) + sh).toNat + 1),
            cbz ((Ws : ℤ) + sh) (i : ℤ) • W.smul w ((i : ℤ) - po) d)
        = ∑ i ∈ Finset.range (((Ws : ℤ) + sh).toNat + 1),
            cbz ((Ws : ℤ) + sh) (i : ℤ) • W.smul w ((i : ℤ) + (-po)) d from
      Finset.sum_congr rfl fun i _ => by rw [show (i : ℤ) - po = (i : ℤ) + (-po) from by ring]]
  rw [ZhuHR.rangeSmul_eq_finsumZ (fun q : ℤ => cbz ((Ws : ℤ) + sh) q) (fun q => W.smul w q d) (-po)
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt hsh (by omega))]
  rw [← finsum_comp_equiv (Equiv.addRight (-po))
      (f := fun m : ℤ => cbz ((Ws : ℤ) + sh) (m + po) • W.smul w m d)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + -po) + po = q from by ring]

/-- **The resHom-row combination collapses onto `∑ᶠ_m`** (mirror of `ZhuHR.PresCombo_eq_finsum`).
Here `w := a₍ₛ₎c ∈ 𝒱_Ws`, `Ws = K+M-s-1`, so the row shift `s+1-t`, pole `2n+3+s-t` give the top
`cbz(Ws+(s+1-t), m+(2n+3+s-t)) = cbz(K+M-t, m+(2n+3)+s-t)`. -/
theorem term2_PresCombo_eq_finsum (W : VertexOperatorAlgebra 𝒱) (n K M s Ws : ℕ) {w : 𝒱}
    (hw : w ∈ W.grading (Ws : ℤ)) (d : 𝒱) (hWs : (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1) :
    (∑ t ∈ Finset.range (s + 1),
        (cbz (-(n : ℤ) - 1) ((s : ℤ) - (t : ℤ)) * cbz (K : ℤ) (t : ℤ))
          • resHom W ((s : ℤ) + 1 - (t : ℤ)) ((2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ)) w d)
      = ∑ᶠ m : ℤ,
          (∑ t ∈ Finset.range (s + 1),
              cbz (-(n : ℤ) - 1) ((s : ℤ) - (t : ℤ)) * cbz (K : ℤ) (t : ℤ)
                * cbz ((K : ℤ) + (M : ℤ) - (t : ℤ)) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ)))
            • W.smul w m d := by
  rw [show (∑ t ∈ Finset.range (s + 1),
            (cbz (-(n : ℤ) - 1) ((s : ℤ) - (t : ℤ)) * cbz (K : ℤ) (t : ℤ))
              • resHom W ((s : ℤ) + 1 - (t : ℤ)) ((2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ)) w d)
        = ∑ t ∈ Finset.range (s + 1),
            ∑ᶠ m : ℤ,
              (cbz (-(n : ℤ) - 1) ((s : ℤ) - (t : ℤ)) * cbz (K : ℤ) (t : ℤ)
                * cbz ((K : ℤ) + (M : ℤ) - (t : ℤ)) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ)))
                • W.smul w m d from
      Finset.sum_congr rfl fun t ht => by
        have hts : (t : ℤ) ≤ (s : ℤ) := by
          exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
        rw [term2_resHom_finsum W hw d ((s : ℤ) + 1 - (t : ℤ))
            ((2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ)) (by omega)]
        have hfin : Function.HasFiniteSupport
            (fun m : ℤ => cbz ((Ws : ℤ) + ((s : ℤ) + 1 - (t : ℤ)))
                (m + ((2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ))) • W.smul w m d) :=
          ZhuHR.smul_support_of_scalar W w d _
            (ZhuHR.cbz_shift_support_fin (d := (Ws : ℤ) + ((s : ℤ) + 1 - (t : ℤ))) (by omega)
              ((2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ)))
        rw [smul_finsum' (cbz (-(n : ℤ) - 1) ((s : ℤ) - (t : ℤ)) * cbz (K : ℤ) (t : ℤ)) hfin]
        refine finsum_congr fun m => ?_
        rw [smul_smul,
          show (Ws : ℤ) + ((s : ℤ) + 1 - (t : ℤ)) = (K : ℤ) + (M : ℤ) - (t : ℤ) from by rw [hWs]; ring,
          show m + ((2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ))
              = m + (2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ) from by ring,
          mul_assoc]]
  rw [← finsum_sum_comm (Finset.range (s + 1))
      (fun m t => (cbz (-(n : ℤ) - 1) ((s : ℤ) - (t : ℤ)) * cbz (K : ℤ) (t : ℤ)
          * cbz ((K : ℤ) + (M : ℤ) - (t : ℤ)) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ)))
        • W.smul w m d) (fun t _ => ?_)]
  · exact finsum_congr fun m => by rw [Finset.sum_smul]
  · refine ZhuHR.smul_support_of_scalar W w d _ (Set.Finite.subset
      (ZhuHR.cbz_shift_support_fin (d := (K : ℤ) + (M : ℤ) - (t : ℤ))
        (by have : (t : ℤ) ≤ (s : ℤ) := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp ‹_›)
            omega)
        ((2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ))) ?_)
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h; apply hm
    rw [show (cbz (-(n : ℤ) - 1) ((s : ℤ) - (t : ℤ)) * cbz (K : ℤ) (t : ℤ)
          * cbz ((K : ℤ) + (M : ℤ) - (t : ℤ)) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ)))
        = (cbz (-(n : ℤ) - 1) ((s : ℤ) - (t : ℤ)) * cbz (K : ℤ) (t : ℤ))
            * cbz ((K : ℤ) + (M : ℤ) - (t : ℤ)) (m + ((2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ))) from by
        rw [show m + ((2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ))
            = m + (2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ) from by ring],
      h, mul_zero]

/-- **The per-commutator-index term `S_s ∈ Onm`** (`Term₂` off-diagonal analogue of
`ZhuHR.S_mem_O`).  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M` and `s : ℕ`, with `w := a₍ₛ₎c ∈ 𝒱_{K+M-s-1}`,
`S_s := ∑_{p,i} (cbz K p · cbz M i · cbz(p-(n+1), s)) • w₍ₚ₊ᵢ₋(2n+3)₋ₛ₎ d ∈ Onm W n 0`.  The double
sum collapses onto `∑ᶠ_m` (`term2_S_eq_finsum`); the `(a₍ₛ₎c)`-mode coefficient reorganizes onto the
off-diagonal residue rows (`coeffST2_collapse` + `← term2_PresCombo_eq_finsum`); each row is
`resHom_offdiag_mem_Onm` (shift `s+1-t`, pole excess `n+1+s-t`, `t − s = n ≥ 0`). -/
theorem term2_Ss_mem (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) (s : ℕ) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
          • W.smul (W.smul a (s : ℤ) c) ((p : ℤ) + (i : ℤ) - (2 * (n : ℤ) + 3) - (s : ℤ)) d)
      ∈ Onm W n 0 := by
  set w := W.smul a (s : ℤ) c with hwdef
  have hwmem : w ∈ W.grading ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) := W.smul_mem_grading ha hc (s : ℤ)
  rw [term2_S_eq_finsum W n K M s w d]
  rcases lt_or_ge ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) 0 with hneg | hpos
  · -- `w ∈ 𝒱_{<0} = ⊥`, so `w = 0` and the collapsed finsum is `0`
    rw [W.positivity _ hneg, Submodule.mem_bot] at hwmem
    rw [show (∑ᶠ m : ℤ,
          (∑ p ∈ Finset.range (K + 1),
              cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ))
                * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) • W.smul w m d) = 0 from by
        refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
        rw [hwmem, PreVertexAlgebra.smul_zero_left, smul_zero]]
    exact (Onm W n 0).zero_mem
  · -- `Ws := K+M-s-1 : ℕ`; reorganize onto the off-diagonal residue rows
    obtain ⟨Ws, hWs⟩ : ∃ Ws : ℕ, (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 :=
      ⟨((K : ℤ) + (M : ℤ) - (s : ℤ) - 1).toNat, by omega⟩
    have hwmem' : w ∈ W.grading (Ws : ℤ) := by rwa [hWs]
    rw [show (∑ᶠ m : ℤ,
            (∑ p ∈ Finset.range (K + 1),
                cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (p : ℤ))
                  * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) • W.smul w m d)
          = ∑ᶠ m : ℤ,
            (∑ t ∈ Finset.range (s + 1),
                cbz (-(n : ℤ) - 1) ((s : ℤ) - (t : ℤ)) * cbz (K : ℤ) (t : ℤ)
                  * cbz ((K : ℤ) + (M : ℤ) - (t : ℤ)) (m + (2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ)))
              • W.smul w m d from
        finsum_congr fun m => by
          rw [coeffST2_collapse K M n s (m + (2 * (n : ℤ) + 3) + (s : ℤ))]]
    rw [← term2_PresCombo_eq_finsum W n K M s Ws hwmem' d hWs]
    apply Submodule.sum_mem
    intro t ht
    have hts : t ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    apply Submodule.smul_mem
    rw [show ((s : ℤ) + 1 - (t : ℤ)) = ((s + 1 - t : ℕ) : ℤ) from by omega,
      show ((2 * (n : ℤ) + 3) + (s : ℤ) - (t : ℤ)) = (n : ℤ) + 2 + ((n + 1 + s - t : ℕ) : ℤ) from by
        omega]
    exact resHom_offdiag_mem_Onm W n hwmem' d (by omega : s + 1 - t ≤ n + 1 + s - t)

/-- **The `Term₂` commutator family lies in `Onm`** (analogue of `ZhuHR.commutator_family_mem_O`).
For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
`∑_{p,i} (cbz K p · cbz M i) • ⁅a₍ₚ₋(n+1)₎, c₍ᵢ₋(n+2)₎⁆ d ∈ Onm W n 0`.  Each bracket expands
(`mode_commutator_uniform`) into `∑_{s<N} cbz(p-(n+1),s) • (a₍ₛ₎c)₍…₎ d`; merging the `s`-sum into
each `(p,i)`-summand and pulling it outermost reduces to `∑_s S_s`, each `S_s ∈ Onm` (`term2_Ss_mem`). -/
theorem term2_commutator_mem (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
          • ⁅mode (W.Y a) ((p : ℤ) - ((n : ℤ) + 1)),
              mode (W.Y c) ((i : ℤ) - ((n : ℤ) + 2))⁆ d) ∈ Onm W n 0 := by
  obtain ⟨N, hN⟩ := ZhuHR.mode_commutator_uniform W a c
  rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
              • ⁅mode (W.Y a) ((p : ℤ) - ((n : ℤ) + 1)),
                  mode (W.Y c) ((i : ℤ) - ((n : ℤ) + 2))⁆ d)
        = ∑ s ∈ Finset.range N, ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
              • W.smul (W.smul a (s : ℤ) c)
                  ((p : ℤ) + (i : ℤ) - (2 * (n : ℤ) + 3) - (s : ℤ)) d from ?_]
  · apply Submodule.sum_mem
    intro s _
    exact term2_Ss_mem W n ha hc d s
  · -- merge the `s`-sum into each `(p,i)`-summand, then pull `∑_s` outermost
    rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
                • ⁅mode (W.Y a) ((p : ℤ) - ((n : ℤ) + 1)),
                    mode (W.Y c) ((i : ℤ) - ((n : ℤ) + 2))⁆ d)
          = ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1), ∑ s ∈ Finset.range N,
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
                • W.smul (W.smul a (s : ℤ) c)
                    ((p : ℤ) + (i : ℤ) - (2 * (n : ℤ) + 3) - (s : ℤ)) d from
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => by
          rw [hN ((p : ℤ) - ((n : ℤ) + 1)) ((i : ℤ) - ((n : ℤ) + 2)) d, Finset.smul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [smul_smul,
            show (p : ℤ) - ((n : ℤ) + 1) + ((i : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)
                = (p : ℤ) + (i : ℤ) - (2 * (n : ℤ) + 3) - (s : ℤ) from by ring]]
    rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1), ∑ s ∈ Finset.range N,
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
                • W.smul (W.smul a (s : ℤ) c)
                    ((p : ℤ) + (i : ℤ) - (2 * (n : ℤ) + 3) - (s : ℤ)) d)
          = ∑ p ∈ Finset.range (K + 1), ∑ s ∈ Finset.range N, ∑ i ∈ Finset.range (M + 1),
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
                • W.smul (W.smul a (s : ℤ) c)
                    ((p : ℤ) + (i : ℤ) - (2 * (n : ℤ) + 3) - (s : ℤ)) d from
        Finset.sum_congr rfl fun p _ =>
          Finset.sum_comm (s := Finset.range (M + 1)) (t := Finset.range N)]
    rw [Finset.sum_comm (s := Finset.range (K + 1)) (t := Finset.range N)]

/-- **`Term₂` homogeneous membership.**  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
`anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0` — the ordered level-`n` circle
(`anmCirc_mem_Onm`) plus the commutator family (`term2_commutator_mem`), split by `term2_split`. -/
theorem term2_homog_mem (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0 := by
  rw [term2_split W n ha hc d]
  exact Submodule.add_mem _ (anmCirc_mem_Onm W n 0 c _) (term2_commutator_mem W n ha hc d)

/-- **`Term2Level W n`** — the matched-level (inner level-`n` circle) half of the DJ 2.8 keystone,
proved unconditionally.  Reducing both `a` and `c` to homogeneous slices (`reduce_homogeneous`;
negative grades give `⊥`, hence `0 ∈ Onm`) applies `term2_homog_mem`. -/
theorem Term2Level_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Term2Level W n := by
  intro a c d
  refine reduce_homogeneous W
    (P := fun a => anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0) ?_ ?_ ?_ a
  · intro kA a haA
    refine reduce_homogeneous W
      (P := fun c => anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0) ?_ ?_ ?_ c
    · intro kC c hcC
      rcases lt_or_ge kA 0 with hkA | hkA
      · rw [W.positivity _ hkA, Submodule.mem_bot] at haA
        rw [haA, anmRight_zero_left']; exact (Onm W n 0).zero_mem
      · rcases lt_or_ge kC 0 with hkC | hkC
        · rw [W.positivity _ hkC, Submodule.mem_bot] at hcC
          rw [hcC, anmCirc_zero_left, anmRight_zero_right']; exact (Onm W n 0).zero_mem
        · obtain ⟨K, rfl⟩ : ∃ K : ℕ, (K : ℤ) = kA := ⟨kA.toNat, by omega⟩
          obtain ⟨M, rfl⟩ : ∃ M : ℕ, (M : ℤ) = kC := ⟨kC.toNat, by omega⟩
          exact term2_homog_mem W n haA hcC d
    · show anmRight W n 0 a (anmCirc W n 0 0 d) ∈ Onm W n 0
      rw [anmCirc_zero_left, anmRight_zero_right']; exact (Onm W n 0).zero_mem
    · intro x y hx hy
      rw [anmCirc_add_left, anmRight_add_right]; exact Submodule.add_mem _ hx hy
  · show anmRight W n 0 0 (anmCirc W n 0 c d) ∈ Onm W n 0
    rw [anmRight_zero_left']; exact (Onm W n 0).zero_mem
  · intro x y hx hy
    rw [anmRight_add_left]; exact Submodule.add_mem _ hx hy

end VOA
