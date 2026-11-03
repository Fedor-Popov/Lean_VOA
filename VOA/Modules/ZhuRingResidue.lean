/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuModule

/-!
# The Zhu right-ideal residue identity (Frenkel–Zhu / Zhu Thm 2.1.1)

The generalized-binomial coefficient identity at the heart of the right-ideal direction of Zhu's
two-sided-ideal theorem.  Writing the right-ideal target `u * (a∘b)` (`u ∈ 𝒱_K`, `a ∈ 𝒱_M`) via the
commutator split, its per-commutator-index term `S_j` collapses into the proved higher-pole residue
family `Pres` (`Modules.ZhuModule.Pres_mem_O`) exactly because of the coefficient identity

  `∑_p C(K,p) C(M, m+3+j-p) C(p-1,j) = ∑_{t} (-1)^t C(K,j-t) C(K+M-j+t, m+3+t)`

(equivalently `S_j = ∑_{n=1}^{j+1} (-1)^{n-1} C(K,j-n+1) Pres(u₍ⱼ₎a, K+M-j-1, b, n) ∈ O`).

Proved here by a clean direct route (no closed-form induction): expand `C(p-1,j)` by the
alternating-top-row Vandermonde (`stepA`, off `cbz_neg_one`), swap the order of summation, factor
out `C(K,j-t)` by the trinomial revision (`stepB`, off `Nat.choose_mul`), and collapse the inner
`p`-sum by the shifted generalized Vandermonde (`stepC`, off `cbz_vandermonde`).

## Status
`sorry`-free, with no project axioms.  `zhu_right_binom` is
`[propext, Classical.choice, Quot.sound]`.

## References
* Gannon §5.3.2; Zhu [574] Thm 2.1.1; Frenkel–Zhu.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace ZhuRes

/-! ## Bridge: a `∑ᶠ p : ℤ` of a lower-truncated family equals a `Finset.range` sum. -/

/-- If `F : ℤ → ℂ` vanishes for `p < 0` and for `p ≥ N`, then `∑ᶠ p : ℤ, F p = ∑ i ∈ range N, F i`. -/
theorem finsumZ_eq_range_sum (F : ℤ → ℂ) {N : ℕ}
    (hlo : ∀ p : ℤ, p < 0 → F p = 0) (hhi : ∀ p : ℤ, (N : ℤ) ≤ p → F p = 0) :
    ∑ᶠ p : ℤ, F p = ∑ i ∈ Finset.range N, F (i : ℤ) := by
  have hsubset : Function.support F ⊆ ↑((Finset.range N).map ⟨(Int.ofNat ·), by
      intro a b h; simpa using h⟩) := by
    intro p hp
    rw [Function.mem_support] at hp
    have hp0 : 0 ≤ p := by by_contra h; exact hp (hlo p (by omega))
    have hpN : p < (N : ℤ) := by by_contra h; exact hp (hhi p (by omega))
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Function.Embedding.coeFn_mk]
    exact ⟨p.toNat, by omega, by simp [Int.toNat_of_nonneg hp0]⟩
  rw [finsum_eq_finsetSum_of_support_subset F hsubset, Finset.sum_map]
  rfl

/-! ## A range form of the generalized-binomial Vandermonde. -/

/-- Vandermonde `∑ᶠ i, C(m,i)·C(n,k-i) = C(m+n,k)` repackaged as a `Finset.range` sum,
valid whenever the range covers `[0,k]` (here `k < N`). -/
theorem vandermonde_range (m n k : ℤ) {N : ℕ} (hk : k < (N : ℤ)) :
    ∑ i ∈ Finset.range N, cbz m (i : ℤ) * cbz n (k - (i : ℤ)) = cbz (m + n) k := by
  rw [← cbz_vandermonde m n k, cbzConvol,
    finsumZ_eq_range_sum (N := N) (fun i : ℤ => cbz m i * cbz n (k - i))
      (fun p hp => by dsimp only; rw [cbz_apply_neg m hp, zero_mul])
      (fun p hp => by dsimp only; rw [cbz_apply_neg n (by omega), mul_zero])]

/-! ## The sign row `C(-1, t) = (-1)^t`. -/

/-- `C(-1, t) = (-1)^t` for `t : ℕ` (the alternating top row), via `0`-row Pascal. -/
theorem cbz_neg_one (t : ℕ) : cbz (-1 : ℤ) (t : ℤ) = (-1 : ℂ) ^ t := by
  induction t with
  | zero => simp
  | succ n ih =>
    have hp := cbz_pascal (0 : ℤ) ((n : ℤ) + 1)
    rw [show (0 - 1 : ℤ) = -1 from by ring, show ((n : ℤ) + 1 - 1) = (n : ℤ) from by ring,
      cbz_zero_left, if_neg (by omega)] at hp
    have key : cbz (-1 : ℤ) ((n : ℤ) + 1) = -cbz (-1 : ℤ) (n : ℤ) := by linear_combination -hp
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 from by push_cast; ring, key, ih, pow_succ]
    ring

/-! ## (A)  `C(p-1, j) = ∑_{t≤j} (-1)^t C(p, j-t)` (Vandermonde with the alternating top row). -/

theorem stepA (p : ℤ) (j : ℕ) :
    cbz (p - 1) (j : ℤ)
      = ∑ t ∈ Finset.range (j + 1), (-1 : ℂ) ^ t * cbz p ((j : ℤ) - (t : ℤ)) := by
  have hv := vandermonde_range (-1 : ℤ) p (j : ℤ) (N := j + 1) (by push_cast; omega)
  rw [show (-1 + p : ℤ) = p - 1 from by ring] at hv
  rw [← hv]
  exact Finset.sum_congr rfl (fun t _ => by rw [cbz_neg_one t])

/-! ## (B)  Trinomial revision `C(K,p)·C(p,s) = C(K,s)·C(K-s, p-s)`  (`K : ℕ`). -/

theorem stepB (K : ℕ) (p s : ℤ) :
    cbz (K : ℤ) p * cbz p s = cbz (K : ℤ) s * cbz ((K : ℤ) - s) (p - s) := by
  rcases lt_or_ge s 0 with hs | hs
  · rw [cbz_apply_neg p hs, cbz_apply_neg (K : ℤ) hs, mul_zero, zero_mul]
  rcases lt_or_ge p s with hps | hps
  · rw [cbz_apply_neg ((K : ℤ) - s) (by omega : p - s < 0), mul_zero]
    rcases lt_or_ge p 0 with hp | hp
    · rw [cbz_apply_neg (K : ℤ) hp, zero_mul]
    · rw [cbz_lt hp (by omega : p < s), mul_zero]
  have hp0 : 0 ≤ p := le_trans hs hps
  rcases lt_or_ge (K : ℤ) p with hKp | hKp
  · rw [cbz_lt (by positivity) hKp, zero_mul]
    rcases lt_or_ge (K : ℤ) s with hKs | hKs
    · rw [cbz_lt (by positivity) hKs, zero_mul]
    · rw [cbz_lt (by omega : 0 ≤ (K : ℤ) - s) (by omega : (K : ℤ) - s < p - s), mul_zero]
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, p = (P : ℤ) := ⟨p.toNat, by omega⟩
  obtain ⟨S, rfl⟩ : ∃ S : ℕ, s = (S : ℤ) := ⟨s.toNat, by omega⟩
  have hSP : S ≤ P := by exact_mod_cast hps
  have hPK : P ≤ K := by exact_mod_cast hKp
  have hSK : S ≤ K := le_trans hSP hPK
  rw [show ((K : ℤ) - (S : ℤ)) = ((K - S : ℕ) : ℤ) from by rw [Nat.cast_sub hSK],
      show ((P : ℤ) - (S : ℤ)) = ((P - S : ℕ) : ℤ) from by rw [Nat.cast_sub hSP],
      cbz_natCast_eq_choose hPK, cbz_natCast_eq_choose hSP, cbz_natCast_eq_choose hSK,
      cbz_natCast_eq_choose (Nat.sub_le_sub_right hPK S),
      ← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul hSP]

/-! ## (C)  Shifted Vandermonde `∑_p C(a, p-s)·C(M, T-p) = C(a+M, T-s)`. -/

theorem stepC (a M T s : ℤ) {N : ℕ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hN : a + s < (N : ℤ)) :
    ∑ p ∈ Finset.range N, cbz a ((p : ℤ) - s) * cbz M (T - (p : ℤ)) = cbz (a + M) (T - s) := by
  rw [← finsumZ_eq_range_sum (N := N) (fun p : ℤ => cbz a (p - s) * cbz M (T - p))
      (fun p hp => by dsimp only; rw [cbz_apply_neg a (by omega : p - s < 0), zero_mul])
      (fun p hp => by dsimp only; rw [cbz_lt ha (by omega : a < p - s), zero_mul])]
  rw [← finsum_comp_equiv (Equiv.addRight s)
      (f := fun p : ℤ => cbz a (p - s) * cbz M (T - p))]
  simp only [Equiv.coe_addRight]
  rw [show (∑ᶠ q : ℤ, cbz a (q + s - s) * cbz M (T - (q + s)))
        = ∑ᶠ q : ℤ, cbz a q * cbz M ((T - s) - q) from
      finsum_congr fun q => by
        rw [show q + s - s = q from by ring, show T - (q + s) = (T - s) - q from by ring]]
  rw [← cbzConvol, cbz_vandermonde]

/-! ## The main identity. -/

/-- **The Zhu right-ideal residue identity** (Zhu Thm 2.1.1, the right-ideal coefficient core):
`∑_p C(K,p) C(M, m+3+j-p) C(p-1,j) = ∑_t (-1)^t C(K,j-t) C(K+M-j+t, m+3+t)`.  This is exactly the
generalized-binomial identity making the per-commutator-index term `S_j` of `u * (a∘b)` collapse
into the proved `Pres` residue family. -/
theorem zhu_right_binom (K M j : ℕ) (m : ℤ) :
    ∑ p ∈ Finset.range (K + 1),
        cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + (j : ℤ) - (p : ℤ)) * cbz ((p : ℤ) - 1) (j : ℤ)
      = ∑ t ∈ Finset.range (j + 1),
        (-1 : ℂ) ^ t * cbz (K : ℤ) ((j : ℤ) - (t : ℤ))
          * cbz ((K : ℤ) + (M : ℤ) - (j : ℤ) + (t : ℤ)) (m + 3 + (t : ℤ)) := by
  rw [show (∑ p ∈ Finset.range (K + 1),
            cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + (j : ℤ) - (p : ℤ)) * cbz ((p : ℤ) - 1) (j : ℤ))
        = ∑ p ∈ Finset.range (K + 1), ∑ t ∈ Finset.range (j + 1),
            (-1 : ℂ) ^ t
              * (cbz (K : ℤ) (p : ℤ) * cbz (p : ℤ) ((j : ℤ) - (t : ℤ)))
              * cbz (M : ℤ) (m + 3 + (j : ℤ) - (p : ℤ)) from
      Finset.sum_congr rfl fun p _ => by
        rw [stepA (p : ℤ) j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htj : (t : ℤ) ≤ (j : ℤ) := by
    have := Finset.mem_range.mp ht; exact_mod_cast Nat.lt_succ_iff.mp this
  rw [show (∑ p ∈ Finset.range (K + 1),
            (-1 : ℂ) ^ t
              * (cbz (K : ℤ) (p : ℤ) * cbz (p : ℤ) ((j : ℤ) - (t : ℤ)))
              * cbz (M : ℤ) (m + 3 + (j : ℤ) - (p : ℤ)))
        = (-1 : ℂ) ^ t * cbz (K : ℤ) ((j : ℤ) - (t : ℤ))
            * ∑ p ∈ Finset.range (K + 1),
                cbz ((K : ℤ) - ((j : ℤ) - (t : ℤ))) ((p : ℤ) - ((j : ℤ) - (t : ℤ)))
                  * cbz (M : ℤ) ((m + 3 + (j : ℤ)) - (p : ℤ)) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [stepB K (p : ℤ) ((j : ℤ) - (t : ℤ))]
      ring]
  rcases le_or_gt ((j : ℤ) - (t : ℤ)) (K : ℤ) with hjtK | hjtK
  · rw [stepC ((K : ℤ) - ((j : ℤ) - (t : ℤ))) (M : ℤ) (m + 3 + (j : ℤ)) ((j : ℤ) - (t : ℤ))
          (N := K + 1) (by omega) (by omega) (by push_cast; omega)]
    rw [show ((K : ℤ) - ((j : ℤ) - (t : ℤ))) + (M : ℤ) = (K : ℤ) + (M : ℤ) - (j : ℤ) + (t : ℤ) from by ring,
      show (m + 3 + (j : ℤ)) - ((j : ℤ) - (t : ℤ)) = m + 3 + (t : ℤ) from by ring]
  · rw [cbz_lt (by positivity) hjtK]; ring

end ZhuRes

/-! ## Bilinear/homogeneous reductions of the three Zhu Thm 2.1.1/2.1.2 goals.

`zhuMul` is `ℂ`-bilinear, so each of the left-ideal/right-ideal/associator goals holds in general
iff it holds for homogeneous arguments.  These `iSup`-induction reductions are exactly where the Frenkel–Zhu residue cores
plug in. -/

section Reductions
variable (W : VertexOperatorAlgebra 𝒱)

/-- Reduce a single argument to homogeneous: a predicate closed under `0`/`+` holding on each
homogeneous slice holds for all `u`. -/
theorem reduce_homogeneous {P : 𝒱 → Prop}
    (hhom : ∀ k : ℤ, ∀ u ∈ W.grading k, P u)
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (u : 𝒱) : P u := by
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := P) hutop ?_ hzero hadd
  intro i x hx; exact hhom i x hx

/-- **(left-ideal) reduced**: the left-ideal generator condition holds for all `(a,b,v)` if it
holds for homogeneous `a`. -/
theorem left_ideal_gen_of_homogeneous
    (H : ∀ M : ℤ, ∀ a ∈ W.grading M, ∀ b v : 𝒱,
      zhuMul W (zhuMul W (W.L (-1) a + W.L 0 a) b) v ∈ O W) :
    ∀ a b v : 𝒱, zhuMul W (zhuMul W (W.L (-1) a + W.L 0 a) b) v ∈ O W := by
  intro a b v
  refine reduce_homogeneous W (P := fun a =>
    zhuMul W (zhuMul W (W.L (-1) a + W.L 0 a) b) v ∈ O W) ?_ ?_ ?_ a
  · intro k a ha; exact H k a ha b v
  · simp only [map_zero, add_zero, zhuMul_zero_left]; exact (O W).zero_mem
  · intro x y hx hy
    rw [show (W.L (-1)) (x + y) + (W.L 0) (x + y)
        = ((W.L (-1)) x + (W.L 0) x) + ((W.L (-1)) y + (W.L 0) y) from by
      simp only [map_add]; abel, zhuMul_add_left, zhuMul_add_left]
    exact (O W).add_mem hx hy

/-- **(right-ideal) reduced**: holds for all `(u,a,b)` if it holds for homogeneous `u` and `a`. -/
theorem right_ideal_gen_of_homogeneous
    (H : ∀ K : ℤ, ∀ u ∈ W.grading K, ∀ M : ℤ, ∀ a ∈ W.grading M, ∀ b : 𝒱,
      zhuMul W u (zhuMul W (W.L (-1) a + W.L 0 a) b) ∈ O W) :
    ∀ u a b : 𝒱, zhuMul W u (zhuMul W (W.L (-1) a + W.L 0 a) b) ∈ O W := by
  intro u a b
  refine reduce_homogeneous W (P := fun u =>
    zhuMul W u (zhuMul W (W.L (-1) a + W.L 0 a) b) ∈ O W) ?_ ?_ ?_ u
  · intro K u hu
    refine reduce_homogeneous W (P := fun a =>
      zhuMul W u (zhuMul W (W.L (-1) a + W.L 0 a) b) ∈ O W) ?_ ?_ ?_ a
    · intro M a ha; exact H K u hu M a ha b
    · simp only [map_zero, add_zero, zhuMul_zero_left, zhuMul_zero_right]
      exact (O W).zero_mem
    · intro x y hx hy
      rw [show (W.L (-1)) (x + y) + (W.L 0) (x + y)
          = ((W.L (-1)) x + (W.L 0) x) + ((W.L (-1)) y + (W.L 0) y) from by
        simp only [map_add]; abel, zhuMul_add_left, zhuMul_add_right]
      exact (O W).add_mem hx hy
  · simp only [zhuMul_zero_left, (O W).zero_mem]
  · intro x y hx hy; rw [zhuMul_add_left]; exact (O W).add_mem hx hy

/-- **(associator) reduced**: holds for all `(u,v,w)` if it holds for homogeneous `u, v, w`. -/
theorem assoc_of_homogeneous
    (H : ∀ K : ℤ, ∀ u ∈ W.grading K, ∀ L : ℤ, ∀ v ∈ W.grading L, ∀ J : ℤ, ∀ w ∈ W.grading J,
      zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w) ∈ O W) :
    ∀ u v w : 𝒱, zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w) ∈ O W := by
  intro u v w
  refine reduce_homogeneous W (P := fun u =>
    zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w) ∈ O W) ?_ ?_ ?_ u
  · intro K u hu
    refine reduce_homogeneous W (P := fun v =>
      zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w) ∈ O W) ?_ ?_ ?_ v
    · intro L v hv
      refine reduce_homogeneous W (P := fun w =>
        zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w) ∈ O W) ?_ ?_ ?_ w
      · intro J w hw; exact H K u hu L v hv J w hw
      · simp only [zhuMul_zero_right, sub_self, (O W).zero_mem]
      · intro x y hx hy
        rw [zhuMul_add_right, zhuMul_add_right, zhuMul_add_right,
          show zhuMul W (zhuMul W u v) x + zhuMul W (zhuMul W u v) y
            - (zhuMul W u (zhuMul W v x) + zhuMul W u (zhuMul W v y))
            = (zhuMul W (zhuMul W u v) x - zhuMul W u (zhuMul W v x))
              + (zhuMul W (zhuMul W u v) y - zhuMul W u (zhuMul W v y)) from by abel]
        exact (O W).add_mem hx hy
    · simp only [zhuMul_zero_right, zhuMul_zero_left, sub_self]; exact (O W).zero_mem
    · intro x y hx hy
      simp only [zhuMul_add_right, zhuMul_add_left]
      rw [show zhuMul W (zhuMul W u x) w + zhuMul W (zhuMul W u y) w
          - (zhuMul W u (zhuMul W x w) + zhuMul W u (zhuMul W y w))
          = (zhuMul W (zhuMul W u x) w - zhuMul W u (zhuMul W x w))
            + (zhuMul W (zhuMul W u y) w - zhuMul W u (zhuMul W y w)) from by abel]
      exact (O W).add_mem hx hy
  · simp only [zhuMul_zero_left, zhuMul_zero_right, sub_self, (O W).zero_mem]
  · intro x y hx hy
    rw [zhuMul_add_left, zhuMul_add_left, zhuMul_add_left,
      show zhuMul W (zhuMul W x v) w + zhuMul W (zhuMul W y v) w
        - (zhuMul W x (zhuMul W v w) + zhuMul W y (zhuMul W v w))
        = (zhuMul W (zhuMul W x v) w - zhuMul W x (zhuMul W v w))
          + (zhuMul W (zhuMul W y v) w - zhuMul W y (zhuMul W v w)) from by abel]
    exact (O W).add_mem hx hy

/-- **Double-residue expansion** of the right-ideal target for homogeneous `u ∈ 𝒱_K`, `a ∈ 𝒱_M`:
`u * ((L₋₁a+L₀a)*b) = ∑_{p,i} C(K,p)·C(M,i) · u₍ₚ₋₁₎(a₍ᵢ₋₂₎b)`. -/
theorem right_target_expand {K M : ℕ} {u a : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) :
    zhuMul W u (zhuMul W (W.L (-1) a + W.L 0 a) b)
      = ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
          (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
            • W.smul u ((p : ℤ) - 1) (W.smul a ((i : ℤ) - 2) b) := by
  rw [zhuMul_homogeneous' W hu, show (K : ℤ).toNat + 1 = K + 1 from by simp]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [zhuMul_L_base W ha b]
  have hdist : W.smul u ((p : ℤ) - 1)
        (∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - 2) b)
      = ∑ i ∈ Finset.range (M + 1),
          cbz (M : ℤ) (i : ℤ) • W.smul u ((p : ℤ) - 1) (W.smul a ((i : ℤ) - 2) b) := by
    rw [show W.smul u ((p : ℤ) - 1)
          = (mode (W.Y u) ((p : ℤ) - 1) : 𝒱 →ₗ[ℂ] 𝒱) from rfl]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  rw [hdist, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_smul]

/-- **The left ideal is free from associativity.**  Given that `*` is associative mod `O` (`hA`),
every left-ideal generator `g*v` (`g = (L₋₁a+L₀a)*b ∈ Ogen`) lies in `O`:
`((L₋₁a+L₀a)*b)*v = (L₋₁a+L₀a)*(b*v) + [associator] ∈ O`, the first summand being an `O`-generator
(`gen_mem_O`) and the second `∈ O` by `hA`.  So Zhu Thm 2.1.1's *left*-ideal direction needs no
separate residue computation — only the associator. -/
theorem left_ideal_gen_of_assoc
    (hA : ∀ u v w : 𝒱, zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w) ∈ O W) :
    ∀ g ∈ Ogen W, ∀ v, zhuMul W g v ∈ O W := by
  rintro g ⟨a, b, rfl⟩ v
  have h1 : zhuMul W (W.L (-1) a + W.L 0 a) (zhuMul W b v) ∈ O W := gen_mem_O W a _
  have h2 := hA (W.L (-1) a + W.L 0 a) b v
  have heq : zhuMul W (zhuMul W (W.L (-1) a + W.L 0 a) b) v
      = zhuMul W (W.L (-1) a + W.L 0 a) (zhuMul W b v)
        + (zhuMul W (zhuMul W (W.L (-1) a + W.L 0 a) b) v
            - zhuMul W (W.L (-1) a + W.L 0 a) (zhuMul W b v)) := by abel
  rw [heq]; exact (O W).add_mem h1 h2

end Reductions

end VOA
