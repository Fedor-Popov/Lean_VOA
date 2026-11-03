/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BelowCriticalFlag
import VOA.Examples.AffineSl2BelowCriticalNoWall
import VOA.Examples.AffineSl2VacuumChevalleyGram
import VOA.Examples.AffineSl2JointGram
import VOA.Examples.AffineSl2L0Cov

/-!
# Compact real structures on `V^k(sl₂)` and the Hermitian Sugawara identity

A real structure `R` on the universal affine VOA is **compact** (`IsCompactRealStructure`) if it
sends each Chevalley current state to minus the current of the opposite colour,
`ρ(J^e_{-1}|0⟩) = -J^f_{-1}|0⟩`, `ρ(J^f_{-1}|0⟩) = -J^e_{-1}|0⟩`, `ρ(J^h_{-1}|0⟩) = -J^h_{-1}|0⟩`
(the compact real form `su(2)`), and its parity scalars are invertible.

From this predicate alone we prove:

* `IsCompactRealStructure.rho_J` — `ρ J^a_m = -J^{a*}_m ρ`;
* `IsCompactRealStructure.sesq_J_adj` — the Hermitian adjoint of `J^a_m` for `h(x,y) = B(ρx,y)`
  is `J^{a*}_{-m}`, with `B` the normalized canonical universal form;
* `IsCompactRealStructure.rho_mem_grading`, `rho_mem_ordinaryPiece` — `ρ` preserves weights and
  the ordinary flag;
* `IsCompactRealStructure.sugawara_sesq` — the **Hermitian Sugawara energy identity**
  `2(k+2) E h(v,v) = Σ_c w_c h(J^c_0 v, J^c_0 v) + Σ_c Σ_{1≤m≤E} 2 w_c h(J^c_m v, J^c_m v)`
  on `V_E`, with `w = (1, 1, 1/2)` in the colour order `(e, f, h)`;
* `currentSystem` — the abstract `CurrentSystem` of the no-wall lemma, instantiated for
  `(universal k hk, universalForm k hk, R, ordinaryFlag k hk)`.

Every result here is stated for an arbitrary `R` with `IsCompactRealStructure R`.  Such an `R`
is constructed for every real noncritical `k` in `AffineSl2BelowCriticalRealStructure`
(`compactRealStructure`, PBW conjugation composed with the Chevalley involution).
-/

namespace VOA

namespace AffineSl2BelowCritical

open AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity AffineVOA.HighestModule
open AffineVOA.SugawaraCov BelowCriticalNoWall

noncomputable section

variable {k : ℂ} {hk : k + 2 ≠ 0}

/-- **Compactness** of a real structure on `V^k(sl₂)`: `ρ` acts on the current states as the
compact (Chevalley-twisted) conjugation, and its parity scalars are invertible. -/
structure IsCompactRealStructure (R : RealStructure (universal k hk)) : Prop where
  current : ∀ a : Fin 3, R.rho (currentState k a) = -currentState k (adjointColour a)
  parity_ne_zero : ∀ n : ℤ, R.parity n ≠ 0

namespace IsCompactRealStructure

variable {R : RealStructure (universal k hk)} (hR : IsCompactRealStructure R)
include hR

/-- `ρ J^a_m = -J^{a*}_m ρ`. -/
theorem rho_J (a : Fin 3) (m : ℤ) (x : WakModule k) :
    R.rho (J k a m x) = -J k (adjointColour a) m (R.rho x) := by
  rw [← smul_currentState_eq_J k hk, R.map_smul, hR.current, ← neg_one_smul ℂ (currentState k _),
    PreVertexAlgebra.smul_smul_left, smul_currentState_eq_J, neg_one_smul]

/-- `ρ` sends a creation word to a signed creation word of the same length. -/
theorem rho_wordStateA_mem (w : List (Fin 3 × ℕ)) :
    R.rho (wordStateA k w) ∈ ordinaryPiece k w.length := by
  induction w with
  | nil =>
      rw [wordStateA_nil]
      have h := R.map_vacuum
      change R.rho (vacuumA k) = vacuumA k at h
      rw [h]
      exact wordStateA_mem_ordinaryPiece (w := []) le_rfl
  | cons b w ih =>
      rw [wordStateA_cons, hR.rho_J]
      exact Submodule.neg_mem _ (J_mem_ordinaryPiece_succ_of_neg _ (by omega) ih)

/-- `ρ` preserves each ordinary piece. -/
theorem rho_mem_ordinaryPiece {p : ℕ} {x : WakModule k} (hx : x ∈ ordinaryPiece k p) :
    R.rho x ∈ ordinaryPiece k p := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨w, hw⟩, rfl⟩ := hz
      exact ordinaryPiece_mono hw (hR.rho_wordStateA_mem w)
  | zero => rw [R.map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [R.map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [R.antilinear]; exact Submodule.smul_mem _ _ hx

/-- `ρ` preserves each conformal weight space. -/
theorem rho_mem_grading {n : ℤ} {x : WakModule k} (hx : x ∈ (universal k hk).grading n) :
    R.rho x ∈ (universal k hk).grading n := by
  have hL : (universal k hk).L 0 (R.rho x) = (n : ℂ) • R.rho x := by
    rw [← R.rho_L, (universal k hk).L_zero_grading x hx, R.antilinear]
    simp
  have hE : ell0OpA k = -Lsug k 0 := by rw [Lsug0_eq_negEll0OpA k hk, neg_neg]
  change R.rho x ∈ gradingZA k n
  rw [gradingZA_def, Module.End.mem_eigenspace_iff, hE, LinearMap.neg_apply,
    ← closed_L k hk 0]
  change -((universal k hk).L 0 (R.rho x)) = _
  rw [hL, neg_smul]

/-- `ρ` preserves each piece of the ordinary flag. -/
theorem rho_mem_ordinaryFlag {p : ℕ} {n : ℤ} {x : WakModule k}
    (hx : x ∈ (ordinaryFlag k hk).piece p n) : R.rho x ∈ (ordinaryFlag k hk).piece p n :=
  ⟨hR.rho_mem_ordinaryPiece hx.1, hR.rho_mem_grading hx.2⟩

/-- **Hermitian adjointness of the currents**: for `h(x,y) = B(ρx, y)` with the normalized
canonical universal form, `h(J^a_m x, y) = h(x, J^{a*}_{-m} y)`. -/
theorem sesq_J_adj (a : Fin 3) (m : ℤ) (x y : WakModule k) :
    sesqForm (universalForm k hk) R (J k a m x) y =
      sesqForm (universalForm k hk) R x (J k (adjointColour a) (-m) y) := by
  have hadj := LQ43.weightOne_adj (universalForm_invariant k hk)
    (currentState_mem_grading k hk (adjointColour a))
    (LQ43.L1_grading_one k hk _ (currentState_mem_grading k hk (adjointColour a))) m
    (R.rho x) y
  rw [smul_currentState_eq_J, smul_currentState_eq_J] at hadj
  rw [sesqForm_apply, sesqForm_apply, hR.rho_J, map_neg, LinearMap.neg_apply, hadj, neg_neg]

/-- The adjunction read in the other direction. -/
theorem sesq_J_adj' (a : Fin 3) (m : ℤ) (x y : WakModule k) :
    sesqForm (universalForm k hk) R x (J k a m y) =
      sesqForm (universalForm k hk) R (J k (adjointColour a) (-m) x) y := by
  rw [hR.sesq_J_adj, neg_neg, adjointColour_involutive]

end IsCompactRealStructure

/-- The Sugawara colour weights `(1, 1, 1/2)` in the colour order `(e, f, h)`. -/
def sugawaraWeight : Fin 3 → ℝ := ![1, 1, 1 / 2]

theorem sugawaraWeight_pos (c : Fin 3) : 0 < sugawaraWeight c := by
  fin_cases c <;> norm_num [sugawaraWeight]

namespace IsCompactRealStructure

variable {R : RealStructure (universal k hk)} (hR : IsCompactRealStructure R)
include hR

omit hR in
private theorem adjointColour_zero : adjointColour 0 = 1 := rfl
omit hR in
private theorem adjointColour_one : adjointColour 1 = 0 := rfl
omit hR in
private theorem adjointColour_two : adjointColour 2 = 2 := rfl

/-- The colour-summed norm of the `m`-th modes. -/
private def modeNorm (v : WakModule k) (m : ℤ) : ℂ :=
  ∑ c : Fin 3, (sugawaraWeight c : ℂ) *
    sesqForm (universalForm k hk) R (J k c m v) (J k c m v)

omit hR in
private theorem modeNorm_expand (v : WakModule k) (m : ℤ) :
    modeNorm (hk := hk) (R := R) v m =
      sesqForm (universalForm k hk) R (J k 0 m v) (J k 0 m v) +
      sesqForm (universalForm k hk) R (J k 1 m v) (J k 1 m v) +
      (1 / 2 : ℂ) * sesqForm (universalForm k hk) R (J k 2 m v) (J k 2 m v) := by
  simp [modeNorm, Fin.sum_univ_three, sugawaraWeight]

/-- The `p ≥ 0` Sugawara term, paired against `v`, is the norm of the `(p+1)`-st modes. -/
private theorem pair_L0sum_nonneg (v : WakModule k) (m : ℕ) :
    (universalForm k hk).form (R.rho v) (L0sum k (m : ℤ) v) = modeNorm (hk := hk) (R := R) v
      ((m : ℤ) + 1) := by
  rw [L0sum_apply, modeNorm_expand]
  simp only [map_sum, map_smul, smul_eq_mul, sug0TermJ_apply,
    if_pos (show (0 : ℤ) ≤ m by positivity)]
  have key : ∀ aa bb : Fin 3,
      (universalForm k hk).form (R.rho v) (J k aa (-(m : ℤ) - 1) (J k bb ((m : ℤ) + 1) v)) =
        sesqForm (universalForm k hk) R (J k (adjointColour aa) ((m : ℤ) + 1) v)
          (J k bb ((m : ℤ) + 1) v) := by
    intro aa bb
    have h := hR.sesq_J_adj' aa (-(m : ℤ) - 1) v (J k bb ((m : ℤ) + 1) v)
    rw [show -(-(m : ℤ) - 1) = (m : ℤ) + 1 by ring] at h
    exact h
  simp only [key, Fin.sum_univ_three, kappaInv, adjointColour_zero, adjointColour_one,
    adjointColour_two]
  norm_num
  ring

/-- The `p = -m-1 < 0` Sugawara term, paired against `v`, is the norm of the `m`-th modes. -/
private theorem pair_L0sum_neg (v : WakModule k) (m : ℕ) :
    (universalForm k hk).form (R.rho v) (L0sum k (-(m : ℤ) - 1) v) =
      modeNorm (hk := hk) (R := R) v (m : ℤ) := by
  rw [L0sum_apply, modeNorm_expand]
  simp only [map_sum, map_smul, smul_eq_mul, sug0TermJ_apply,
    if_neg (show ¬ (0 : ℤ) ≤ -(m : ℤ) - 1 by omega)]
  have key : ∀ aa bb : Fin 3,
      (universalForm k hk).form (R.rho v)
          (J k bb (-(m : ℤ) - 1 + 1) (J k aa (-(-(m : ℤ) - 1) - 1) v)) =
        sesqForm (universalForm k hk) R (J k (adjointColour bb) (m : ℤ) v)
          (J k aa (m : ℤ) v) := by
    intro aa bb
    have h := hR.sesq_J_adj' bb (-(m : ℤ)) v (J k aa (m : ℤ) v)
    rw [neg_neg] at h
    rw [show -(m : ℤ) - 1 + 1 = -(m : ℤ) by ring,
      show -(-(m : ℤ) - 1) - 1 = (m : ℤ) by ring]
    exact h
  simp only [key, Fin.sum_univ_three, kappaInv, adjointColour_zero, adjointColour_one,
    adjointColour_two]
  norm_num

/-- **The Hermitian Sugawara energy identity** on `V_E`:
`2(k+2) E h(v,v) = Σ_c w_c h(J^c_0 v, J^c_0 v) + Σ_c Σ_{1≤m≤E} 2 w_c h(J^c_m v, J^c_m v)`. -/
theorem sugawara_sesq {E : ℤ} {v : WakModule k} (hv : v ∈ (universal k hk).grading E) :
    (2 * (k + 2) * (E : ℂ)) * sesqForm (universalForm k hk) R v v =
      (∑ c : Fin 3, (sugawaraWeight c : ℂ) *
          sesqForm (universalForm k hk) R (J k c 0 v) (J k c 0 v)) +
        ∑ c : Fin 3, ∑ m ∈ Finset.Icc 1 E.toNat, ((2 * sugawaraWeight c : ℝ) : ℂ) *
          sesqForm (universalForm k hk) R (J k c (m : ℤ) v) (J k c (m : ℤ) v) := by
  rcases lt_or_ge E 0 with hneg | hnn
  · have hv0 : v = 0 := by
      have := (universal k hk).positivity E hneg
      rw [this] at hv
      exact (Submodule.mem_bot ℂ).mp hv
    subst hv0
    simp [sesqForm]
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
  simp only [Int.toNat_natCast]
  set φ : WakModule k →ₗ[ℂ] ℂ := (universalForm k hk).form (R.rho v) with hφ
  -- modes above the weight kill `v`
  have hJzero : ∀ (a : Fin 3) (n : ℤ), (N : ℤ) < n → J k a n v = 0 := by
    intro a n hn
    have h := J_mem_grading hk a n hv
    rw [(universal k hk).positivity _ (by omega)] at h
    exact (Submodule.mem_bot ℂ).mp h
  -- energy as a pairing
  have hE : ((N : ℤ) : ℂ) * sesqForm (universalForm k hk) R v v =
      φ ((universal k hk).L 0 v) := by
    rw [(universal k hk).L_zero_grading v hv, map_smul, smul_eq_mul]
    rfl
  rw [closed_L k hk 0, Lsug0_eq_finsum_L0sum, map_smul, smul_eq_mul,
    map_finsum φ (L0sum_support_finite k v)] at hE
  -- the finite index set of nonzero Sugawara terms
  let S1 : Finset ℤ := (Finset.range N).map ⟨fun m : ℕ => (m : ℤ), Nat.cast_injective⟩
  let S2 : Finset ℤ := (Finset.range (N + 1)).map
    ⟨fun m : ℕ => -(m : ℤ) - 1, fun a b h => by simp only at h; omega⟩
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [S1, S2, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hp1 hp2
    obtain ⟨a, -, rfl⟩ := hp1
    obtain ⟨b, -, hb⟩ := hp2
    omega
  have hsupp : Function.support (fun p : ℤ => φ (L0sum k p v)) ⊆ ↑(S1 ∪ S2) := by
    intro p hp
    by_contra hpS
    apply hp
    simp only
    have hzero : L0sum k p v = 0 := by
      rw [L0sum_apply]
      refine Finset.sum_eq_zero fun aa _ => Finset.sum_eq_zero fun bb _ => ?_
      rw [sug0TermJ_apply]
      simp only [S1, S2, Finset.coe_union, Finset.coe_map, Function.Embedding.coeFn_mk,
        Finset.coe_range, Set.mem_union, Set.mem_image, Set.mem_Iio, not_or, not_exists,
        not_and] at hpS
      obtain ⟨h1, h2⟩ := hpS
      split_ifs with hp0
      · have hpN : (N : ℤ) < p + 1 := by
          by_contra hc
          exact h1 p.toNat (by omega) (by omega)
        rw [hJzero bb _ hpN, map_zero, smul_zero]
      · have hpN : (N : ℤ) < -p - 1 := by
          by_contra hc
          exact h2 (-p - 1).toNat (by omega) (by omega)
        rw [hJzero aa _ hpN, map_zero, smul_zero]
    rw [hzero, map_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_union hdisj] at hE
  simp only [S1, S2, Finset.sum_map, Function.Embedding.coeFn_mk] at hE
  have hpos : ∀ m ∈ Finset.range N, φ (L0sum k (m : ℤ) v) =
      modeNorm (hk := hk) (R := R) v ((m : ℤ) + 1) := fun m _ => hR.pair_L0sum_nonneg v m
  have hneg' : ∀ m ∈ Finset.range (N + 1), φ (L0sum k (-(m : ℤ) - 1) v) =
      modeNorm (hk := hk) (R := R) v (m : ℤ) := fun m _ => hR.pair_L0sum_neg v m
  rw [Finset.sum_congr rfl hpos, Finset.sum_congr rfl hneg', Finset.sum_range_succ'] at hE
  -- clear the Sugawara prefactor
  have hc0 : (2 * (k + 2)) * c0 k = 1 := by
    rw [c0, dualCoxeter]
    exact mul_inv_cancel₀ (mul_ne_zero two_ne_zero hk)
  -- the right-hand side in terms of `modeNorm`
  have hRHS0 : (∑ c : Fin 3, (sugawaraWeight c : ℂ) *
      sesqForm (universalForm k hk) R (J k c 0 v) (J k c 0 v)) =
      modeNorm (hk := hk) (R := R) v ((0 : ℕ) : ℤ) := by
    simp [modeNorm]
  have hRHS1 : (∑ c : Fin 3, ∑ m ∈ Finset.Icc 1 N, ((2 * sugawaraWeight c : ℝ) : ℂ) *
      sesqForm (universalForm k hk) R (J k c (m : ℤ) v) (J k c (m : ℤ) v)) =
      2 * ∑ m ∈ Finset.range N, modeNorm (hk := hk) (R := R) v ((m : ℤ) + 1) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := rfl
    rw [hIcc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [modeNorm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    push_cast
    rw [show (1 : ℤ) + m = m + 1 by ring]
    ring
  rw [hRHS0, hRHS1]
  have hgoal : (2 * (k + 2) * ((N : ℤ) : ℂ)) * sesqForm (universalForm k hk) R v v =
      (2 * (k + 2)) * (((N : ℤ) : ℂ) * sesqForm (universalForm k hk) R v v) := by ring
  rw [hgoal, hE, ← mul_assoc, hc0, one_mul]
  push_cast
  ring

end IsCompactRealStructure

/-- **The current system of `V^k(sl₂)`** with its ordinary flag and a compact real
structure: the input of the abstract prefix no-wall lemma. -/
def currentSystem {R : RealStructure (universal k hk)} (hR : IsCompactRealStructure R) :
    CurrentSystem (Fin 3) (universalForm k hk) R (ordinaryFlag k hk) where
  mode a m := J k a m
  adj := adjointColour
  adj_adj := adjointColour_involutive
  mode_grading a m _ _ hx := J_mem_grading hk a m hx
  sesq_adj := hR.sesq_J_adj
  nonneg_mem a _ _ _ _ hm hx := J_mem_ordinaryFlag_of_nonneg hk a hm hx
  neg_mem a _ _ _ _ hm hx := J_mem_ordinaryFlag_of_neg hk a hm hx
  creation_span hn := grading_le_span_creation hk hn
  wt c := 2 * sugawaraWeight c
  wt_pos c := by have := sugawaraWeight_pos c; positivity
  lam E := 2 * (k + 2) * (E : ℂ)
  zc c := (sugawaraWeight c : ℂ)
  sugawara hv := hR.sugawara_sesq hv
  rho_piece hx := hR.rho_mem_ordinaryFlag hx
  rho_grading hx := hR.rho_mem_grading hx
  parity_ne_zero := hR.parity_ne_zero

/-- **The prefix no-wall lemma for `V^k(sl₂)` with its ordinary flag**, at any noncritical
level `k` and for any compact real structure: if all lower weights carry the graded-unitary
layer signs and the full weight-`E` form separates, every flag step at weight `E` is
nondegenerate. -/
theorem layerNondegenerate_of_lower {R : RealStructure (universal k hk)}
    (hR : IsCompactRealStructure R) (E : ℤ)
    (hfull : ∀ v ∈ (universal k hk).grading E,
      (∀ x ∈ (universal k hk).grading E, (universalForm k hk).form x v = 0) → v = 0)
    (hlower : ∀ m : ℕ, 0 < m →
      LayerPositive (ordinaryFlag k hk) (E - m) (LiRadical.gradedForm (universalForm k hk) (E - m))
        (gradedSesq (universalForm k hk) R (E - m))) :
    LayerNondegenerate (ordinaryFlag k hk) E (LiRadical.gradedForm (universalForm k hk) E) :=
  (currentSystem hR).layerNondegenerate_of_lower E hfull hlower

end

end AffineSl2BelowCritical

end VOA
