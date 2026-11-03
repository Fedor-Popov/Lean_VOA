/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperNthProduct

/-!
# The super iterate formula 5.1.7d for all `ℓ ∈ ℤ`

Layer 4 of the super Borcherds chain: the negative duality `assoc_negε` (5.1.9a) and the
negative branch of the iterate formula, assembled with the nonnegative branch of
`Core.SuperNthProduct` into `mode_iterateε`.

## Where the sign sits

`normalOrderedε ε a b m n = if 0 ≤ m then aₘbₙ else ε•(bₙaₘ)` — the Koszul factor appears on
the **reordered branch only**.  In the `negProd` expansion of `(u₍₋ₖ₋₁₎v)₍ₙ₎x` the diagonal
`ℤ`-sum splits into an `m = i ≥ 0` half and an `m = -(k+1)-i` half; the first is unsigned and
produces the `u·v` term, the second is signed and produces the `v·u` term.  That is exactly
why the exchanged term of the iterate formula — and hence of the Jacobi identity — carries
`koszul p q` and nothing else does.

## Main results

* `vacuum_recursion_eqε`, `assoc_negε` — the negative duality
  `Y(u₍₋ₖ₋₁₎v,z) = (1/k!):(∂_z^k Y(u,z))Y(v,z):_ε`.
* `iterate_neg_term_Aε` / `iterate_neg_term_Bε` — the two halves of the diagonal split
  (stated for arbitrary formal distributions; sign-free, the `ε` is attached afterwards).
* `mode_iterate_negε` — the `ℓ < 0` branch.
* `mode_iterateε` — the iterate formula for **all** `ℓ ∈ ℤ`, with the exchanged-term
  coefficient `koszul p q * (-1)^ℓ`.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open VertexOperatorAlgebra (deriv_pow_apply posfac_eq negfac_eq neg_one_zpow_negsucc
  finsum_split_nat_neg gBinom_natCast_eq_zero prod_one_add_factorial)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §0  Generic facts about `∂^k a` and the diagonal split -/

/-- On the "middle" band `-(k+1) < m < 0` the `k`-th derivative of any distribution vanishes:
the rising-factorial weight `∏_{j<k}(m+1+j)` has a zero factor. -/
theorem deriv_pow_middle_zero (a : FormalDist (End ℂ 𝒱)) (k : ℕ) {m : ℤ}
    (h1 : -(k : ℤ) - 1 < m) (h2 : m < 0) : ((deriv^[k]) a) m = 0 := by
  rw [deriv_pow_apply,
    show (∏ j ∈ Finset.range k, (m + 1 + (j : ℤ))) = 0 from
      Finset.prod_eq_zero (i := (-m - 1).toNat) (Finset.mem_range.mpr (by omega))
        (by rw [Int.toNat_of_nonneg (by omega)]; ring), zero_smul]

/-- The `A`-half of the diagonal split (`m = i ≥ 0`), for arbitrary distributions. -/
theorem iterate_neg_term_A (a b : FormalDist (End ℂ 𝒱)) (k : ℕ) (N : ℤ) (x : 𝒱) (i : ℕ) :
    (k.factorial : ℂ)⁻¹ • (normalOrdered ((deriv^[k]) a) b (i : ℤ) (-N - 1 - i) x)
      = ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i) •
          (mode a (-(k : ℤ) - 1 - i) (mode b (N + i) x)) := by
  have hu1 : a ((i : ℤ) + k) = mode a (-(k : ℤ) - 1 - i) := by rw [mode_apply]; congr 1; ring
  have hv1 : b (-N - 1 - (i : ℤ)) = mode b (N + i) := by rw [mode_apply]; congr 1; ring
  rw [normalOrdered_apply, if_pos (by exact_mod_cast Nat.zero_le i), Module.End.mul_apply,
    deriv_pow_apply, ← Int.cast_smul_eq_zsmul ℂ, LinearMap.smul_apply, hu1, hv1, smul_smul,
    show ((k.factorial : ℂ)⁻¹ * ((∏ j ∈ Finset.range k, ((i : ℤ) + 1 + (j : ℤ)) : ℤ) : ℂ))
        = (-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i from by
      rw [Int.cast_prod]; push_cast; exact posfac_eq k i]

/-- The `B`-half of the diagonal split (`m = -(k+1)-i < 0`), for arbitrary distributions.
The Koszul factor is *not* here: it is attached by `normalOrderedε_eq` at the call site. -/
theorem iterate_neg_term_B (a b : FormalDist (End ℂ 𝒱)) (k : ℕ) (N : ℤ) (x : 𝒱) (i : ℕ) :
    (k.factorial : ℂ)⁻¹ • (normalOrdered ((deriv^[k]) a) b (-(k : ℤ) - 1 - i)
        (-N - 1 - (-(k : ℤ) - 1 - i)) x)
      = ((-1 : ℂ) ^ k * ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i)) •
          (mode b (-(k : ℤ) - 1 + N - i) (mode a i x)) := by
  have hv2 : b (-N - 1 - (-(k : ℤ) - 1 - i)) = mode b (-(k : ℤ) - 1 + N - i) := by
    rw [mode_apply]; congr 1; ring
  have hu2 : a ((-(k : ℤ) - 1 - i) + (k : ℤ)) = mode a i := by rw [mode_apply]; congr 1; ring
  rw [normalOrdered_apply, if_neg (by omega : ¬ (0 : ℤ) ≤ -(k : ℤ) - 1 - i),
    Module.End.mul_apply, deriv_pow_apply, ← Int.cast_smul_eq_zsmul ℂ, LinearMap.smul_apply,
    map_smul, hv2, hu2, smul_smul,
    show ((k.factorial : ℂ)⁻¹
          * ((∏ j ∈ Finset.range k, ((-(k : ℤ) - 1 - i) + 1 + (j : ℤ)) : ℤ) : ℂ))
        = (-1 : ℂ) ^ k * ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i) from by
      rw [Int.cast_prod]; push_cast; exact negfac_eq k i]

/-- `nprodε` depends only on the underlying distributions, not on the `IsField` witnesses. -/
theorem nprodε_congr (ε : ℂ) {a a' b : FormalDist (End ℂ 𝒱)} (ha : IsField a)
    (ha' : IsField a') (hb : IsField b) (h : a = a') : nprodε ε ha hb = nprodε ε ha' hb := by
  subst h; rfl

namespace SuperNearVOA

/-! ## §1  Translation covariance in `DCovariant` form -/

/-- `L₋₁` covariance of every vertex operator, in the `DCovariant` packaging the
normal-ordered-product machinery consumes. -/
theorem dcov_Yε (V : SuperNearVOA 𝒱) (u : 𝒱) :
    VOA.Reconstruction.DCovariant (V.L (-1)) (V.Y u) := by
  intro m
  rw [← LieRing.of_associative_ring_bracket]
  exact L_comm_Ycoeffε V u m

/-- `L₋₁` maps each parity space to itself (`ω` is even). -/
theorem L_neg_one_mem_parityε (V : SuperNearVOA 𝒱) {p : ZMod 2} {w : 𝒱} (hw : w ∈ V.parity p) :
    V.L (-1) w ∈ V.parity p := by
  have h := V.smul_mem_parity V.conformal_parity hw 0
  rw [zero_add] at h
  have hLe : V.L (-1) w = V.smul V.conformalVector 0 w := by
    rw [L_def, show (-1 : ℤ) + 1 = 0 by ring]; rfl
  rw [hLe]; exact h

/-- Iterated. -/
theorem L_pow_mem_parityε (V : SuperNearVOA 𝒱) {p : ZMod 2} {w : 𝒱} (hw : w ∈ V.parity p)
    (k : ℕ) : (V.L (-1) ^ k) w ∈ V.parity p := by
  induction k with
  | zero => simpa using hw
  | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact L_neg_one_mem_parityε V ih

/-! ## §2  The vacuum recursion -/

/-- **Creation determines a field on the vacuum.**  Sign-free: only the recursion and the
base matter. -/
theorem vacuum_recursion_eqε (V : SuperNearVOA 𝒱) (B : FormalDist (End ℂ 𝒱)) (w : 𝒱)
    (hneg : ∀ s : ℤ, s < 0 → B s V.vacuum = 0)
    (hbase : B 0 V.vacuum = w)
    (hrec : ∀ s : ℤ, V.L (-1) (B s V.vacuum) = (s + 1) • B (s + 1) V.vacuum)
    (s : ℤ) : B s V.vacuum = (V.Y w) s V.vacuum := by
  by_cases hs : s < 0
  · rw [hneg s hs, V.toSuperVertexAlgebra.Y_apply_vacuum_eq_zero w hs]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, s = (j : ℤ) := ⟨s.toNat, by omega⟩
    clear hs
    induction j with
    | zero =>
        rw [Nat.cast_zero, hbase]
        exact (V.toSuperVertexAlgebra.Y_apply_vacuum_zero _).symm
    | succ i ih =>
        have hYrec : V.L (-1) ((V.Y w) (i : ℤ) V.vacuum)
            = ((i : ℤ) + 1) • (V.Y w) ((i : ℤ) + 1) V.vacuum := by
          have h := DFunLike.congr_fun (L_comm_Ycoeffε V w (i : ℤ)) V.vacuum
          rw [LinearMap.smul_apply, LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
            Module.End.mul_apply, Module.End.mul_apply, L_neg_one_vacuumε, map_zero,
            sub_zero] at h
          exact h
        have key : ((i : ℤ) + 1) • B ((i : ℤ) + 1) V.vacuum
            = ((i : ℤ) + 1) • (V.Y w) ((i : ℤ) + 1) V.vacuum := by
          rw [← hrec, ih, hYrec]
        have hc : (((i : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
        rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1),
          ← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1)] at key
        rw [Nat.cast_succ]
        exact smul_right_injective 𝒱 hc key

/-- `∂^k Y(u,z)` annihilates the vacuum below degree `0`. -/
theorem deriv_pow_Y_vacuum_neg (V : SuperNearVOA 𝒱) (u : 𝒱) (k : ℕ) {q : ℤ} (hq : q < 0) :
    ((deriv^[k]) (V.Y u)) q V.vacuum = 0 := by
  rcases lt_or_ge (q + (k : ℤ)) 0 with h | h
  · rw [deriv_pow_apply, LinearMap.smul_apply,
      V.toSuperVertexAlgebra.Y_apply_vacuum_eq_zero u h, smul_zero]
  · rw [deriv_pow_middle_zero (V.Y u) k (by omega) hq]
    rfl

/-! ## §3  The negative duality 5.1.9a -/

/-- **The super negative duality 5.1.9a**:
`Y(u₍₋ₖ₋₁₎v, z) = (1/k!)·:(∂_z^k Y(u,z))Y(v,z):_ε` with `ε = (-1)^{|u||v|}`.

Goddard uniqueness with the `n < 0` super Dong lemma `dong_negε` supplying the candidate's
locality (its composite sign `koszul p r * koszul q r` is `koszul (p+q) r`, exactly the parity
of `u₍₋ₖ₋₁₎v`), and the vacuum recursion supplying the creation condition. -/
theorem assoc_negε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (k : ℕ) :
    V.Y (V.smul u (-(k : ℤ) - 1) v)
      = (k.factorial : ℂ)⁻¹ • nprodε (koszul p q) ((isField_Yε V u).deriv_iterate k)
          (isField_Yε V v) := by
  set ha := (isField_Yε V u).deriv_iterate k with hadef
  set hb := isField_Yε V v with hbdef
  symm
  refine V.toSuperVertexAlgebra.goddard_uniquenessε _ (V.smul u (-(k : ℤ) - 1) v)
    (V.smul_mem_parity hu hv _) (fun r b hb' => ?_) (fun m => ?_)
  · refine Localε.smul_left _ _ ?_
    have hdn := dong_negε (koszul_mul_self p q) ha hb
      ((V.locality u hu v hv).deriv_iterate_left k)
      ((V.locality u hu b hb').deriv_iterate_left k) (V.locality v hv b hb')
    rwa [← koszul_add_left] at hdn
  · refine vacuum_recursion_eqε V ((k.factorial : ℂ)⁻¹ • nprodε (koszul p q) ha hb)
      (V.smul u (-(k : ℤ) - 1) v) (fun s hs => ?_) ?_ (fun s => ?_) m
    · show ((k.factorial : ℂ)⁻¹ • nprodε (koszul p q) ha hb s) V.vacuum = 0
      rw [LinearMap.smul_apply,
        nprodε_vacuum_neg_gen (koszul p q) ha hb V.vacuum
          (fun t ht => deriv_pow_Y_vacuum_neg V u k ht)
          (fun t ht => V.toSuperVertexAlgebra.Y_apply_vacuum_eq_zero v ht) hs, smul_zero]
    · show ((k.factorial : ℂ)⁻¹ • nprodε (koszul p q) ha hb 0) V.vacuum = _
      rw [LinearMap.smul_apply,
        nprodε_vacuum_base_gen (koszul p q) ha hb V.vacuum
          (fun t ht => deriv_pow_Y_vacuum_neg V u k ht)
          (fun t ht => V.toSuperVertexAlgebra.Y_apply_vacuum_eq_zero v ht),
        V.toSuperVertexAlgebra.Y_apply_vacuum_zero v, deriv_pow_apply,
        show (0 : ℤ) + (k : ℤ) = (k : ℤ) from by ring,
        show (∏ i ∈ Finset.range k, ((0 : ℤ) + 1 + (i : ℤ)))
            = (k.factorial : ℤ) from by
          rw [← VertexOperatorAlgebra.prod_one_add_factorial]
          exact Finset.prod_congr rfl (fun i _ => by ring),
        LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℂ (k.factorial : ℤ), Int.cast_natCast,
        smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul,
        SuperVertexAlgebra.smul_def, mode_apply]
      congr 1
      ring
    · show V.L (-1) (((k.factorial : ℂ)⁻¹ • nprodε (koszul p q) ha hb s) V.vacuum)
        = (s + 1) • ((k.factorial : ℂ)⁻¹ • nprodε (koszul p q) ha hb (s + 1)) V.vacuum
      have hcov : VOA.Reconstruction.DCovariant (V.L (-1))
          ((k.factorial : ℂ)⁻¹ • nprodε (koszul p q) ha hb) :=
        VOA.Reconstruction.DCovariant.smul _
          (VOA.DCovariant.nprodε (koszul p q) ha hb
            (VOA.Reconstruction.DCovariant.deriv_iterate (dcov_Yε V u) k)
            (dcov_Yε V v))
      have h := DFunLike.congr_fun (hcov s) V.vacuum
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, L_neg_one_vacuumε,
        map_zero, LinearMap.smul_apply, sub_zero] at h
      exact h

/-! ## §4  The negative branch of the iterate formula -/

/-- Expand `(u₍₋ₖ₋₁₎v)₍ₙ₎x` through the super negative duality. -/
theorem assoc_neg_mode_expandε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱}
    (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) (k : ℕ) (N : ℤ) (x : 𝒱) :
    V.smul (V.smul u (-(k : ℤ) - 1) v) N x
      = (k.factorial : ℂ)⁻¹ • ∑ᶠ m : ℤ,
          normalOrderedε (koszul p q) ((deriv^[k]) (V.Y u)) (V.Y v) m (-N - 1 - m) x := by
  rw [SuperVertexAlgebra.smul_def, mode_apply, assoc_negε V hu hv k]
  show (k.factorial : ℂ)⁻¹ • (nprodε (koszul p q) ((isField_Yε V u).deriv_iterate k)
      (isField_Yε V v) (-N - 1) x)
    = (k.factorial : ℂ)⁻¹ • ∑ᶠ m : ℤ,
        normalOrderedε (koszul p q) ((deriv^[k]) (V.Y u)) (V.Y v) m (-N - 1 - m) x
  rw [nprodε_apply]

/-- **Borcherds iterate, negative branch** (`ℓ = -(k+1) < 0`), with the Koszul sign on the
exchanged term. -/
theorem mode_iterate_negε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (k : ℕ) (N : ℤ) (x : 𝒱) :
    V.smul (V.smul u (-(k : ℤ) - 1) v) N x
      = ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i) •
          (V.smul u (-(k : ℤ) - 1 - i) (V.smul v (N + i) x)
            - (koszul p q * (-1 : ℂ) ^ (-(k : ℤ) - 1)) •
                V.smul v (-(k : ℤ) - 1 + N - i) (V.smul u i x)) := by
  rw [assoc_neg_mode_expandε V hu hv]
  set ha := (isField_Yε V u).deriv_iterate k with hadef
  set hb := isField_Yε V v with hbdef
  have hfin : (Function.support fun m : ℤ =>
      normalOrderedε (koszul p q) ((deriv^[k]) (V.Y u)) (V.Y v) m (-N - 1 - m) x).Finite :=
    normalOrderedε_diag_support_finite (koszul p q) ha hb (-N - 1) x
  have hmid : ∀ m : ℤ, -(k : ℤ) - 1 < m → m < 0 →
      normalOrderedε (koszul p q) ((deriv^[k]) (V.Y u)) (V.Y v) m (-N - 1 - m) x = 0 := by
    intro m hm1 hm2
    rw [normalOrderedε_apply, if_neg (not_le.mpr hm2), LinearMap.smul_apply,
      Module.End.mul_apply, deriv_pow_middle_zero (V.Y u) k hm1 hm2]
    simp
  have hinjA : Function.Injective (fun i : ℕ => (i : ℤ)) := Nat.cast_injective
  have hinjB : Function.Injective (fun i : ℕ => -(k : ℤ) - 1 - (i : ℤ)) :=
    fun a b hab => by simp only at hab; omega
  have hA : (Function.support fun i : ℕ =>
      normalOrderedε (koszul p q) ((deriv^[k]) (V.Y u)) (V.Y v) (i : ℤ)
        (-N - 1 - (i : ℤ)) x).Finite :=
    (hfin.preimage hinjA.injOn).subset (fun i hi => hi)
  have hB : (Function.support fun i : ℕ =>
      normalOrderedε (koszul p q) ((deriv^[k]) (V.Y u)) (V.Y v) (-(k : ℤ) - 1 - (i : ℤ))
        (-N - 1 - (-(k : ℤ) - 1 - (i : ℤ))) x).Finite :=
    (hfin.preimage hinjB.injOn).subset (fun i hi => hi)
  have hsum_fin : (Function.support fun i : ℕ =>
      normalOrderedε (koszul p q) ((deriv^[k]) (V.Y u)) (V.Y v) (i : ℤ) (-N - 1 - (i : ℤ)) x
        + normalOrderedε (koszul p q) ((deriv^[k]) (V.Y u)) (V.Y v) (-(k : ℤ) - 1 - (i : ℤ))
            (-N - 1 - (-(k : ℤ) - 1 - (i : ℤ))) x).Finite := by
    refine (hA.union hB).subset (fun i hi => ?_)
    rw [Function.mem_support] at hi
    by_contra hc
    rw [Set.mem_union, Function.mem_support, Function.mem_support, not_or, not_not,
      not_not] at hc
    exact hi (by rw [hc.1, hc.2, add_zero])
  rw [finsum_split_nat_neg _ k hfin hmid, smul_finsum' (k.factorial : ℂ)⁻¹ hsum_fin]
  refine finsum_congr (fun i => ?_)
  have eA : normalOrderedε (koszul p q) ((deriv^[k]) (V.Y u)) (V.Y v) (i : ℤ)
        (-N - 1 - (i : ℤ)) x
      = normalOrdered ((deriv^[k]) (V.Y u)) (V.Y v) (i : ℤ) (-N - 1 - (i : ℤ)) x := by
    rw [normalOrderedε_eq, if_pos (by exact_mod_cast Nat.zero_le i), one_smul]
  have eB : normalOrderedε (koszul p q) ((deriv^[k]) (V.Y u)) (V.Y v) (-(k : ℤ) - 1 - (i : ℤ))
        (-N - 1 - (-(k : ℤ) - 1 - (i : ℤ))) x
      = koszul p q • normalOrdered ((deriv^[k]) (V.Y u)) (V.Y v) (-(k : ℤ) - 1 - (i : ℤ))
        (-N - 1 - (-(k : ℤ) - 1 - (i : ℤ))) x := by
    rw [normalOrderedε_eq, if_neg (by omega : ¬ (0 : ℤ) ≤ -(k : ℤ) - 1 - (i : ℤ)),
      LinearMap.smul_apply]
  have eBB : (k.factorial : ℂ)⁻¹ • (koszul p q •
        normalOrdered ((deriv^[k]) (V.Y u)) (V.Y v) (-(k : ℤ) - 1 - (i : ℤ))
          (-N - 1 - (-(k : ℤ) - 1 - (i : ℤ))) x)
      = koszul p q • (((-1 : ℂ) ^ k * ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i)) •
          (mode (V.Y v) (-(k : ℤ) - 1 + N - i) (mode (V.Y u) i x))) := by
    rw [smul_comm, iterate_neg_term_B (V.Y u) (V.Y v) k N x i]
  rw [eA, eB, smul_add, iterate_neg_term_A (V.Y u) (V.Y v) k N x i, eBB,
    neg_one_zpow_negsucc]
  simp only [← SuperVertexAlgebra.smul_def]
  module

/-! ## §5  The iterate formula for all `ℓ ∈ ℤ` -/

/-- **The super iterate formula (Gannon 5.1.7d), for ALL `ℓ ∈ ℤ`.**  The exchanged term
carries the single scalar `koszul p q * (-1)^ℓ`. -/
theorem mode_iterateε (V : SuperNearVOA 𝒱) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (ℓ N : ℤ) (x : 𝒱) :
    V.smul (V.smul u ℓ v) N x
      = ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom ℓ i) •
          (V.smul u (ℓ - i) (V.smul v (N + i) x)
            - (koszul p q * (-1 : ℂ) ^ ℓ) • V.smul v (ℓ + N - i) (V.smul u i x)) := by
  rcases lt_or_ge ℓ 0 with hℓ | hℓ
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = -(k : ℤ) - 1 := ⟨(-ℓ - 1).toNat, by omega⟩
    exact mode_iterate_negε V hu hv k N x
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = (k : ℤ) := ⟨ℓ.toNat, by omega⟩
    rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (k + 1)) (by
      intro i hi
      rw [Function.mem_support] at hi
      by_contra hc
      rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
      exact hi (by
        rw [VertexOperatorAlgebra.gBinom_natCast_eq_zero (by omega : k < i), mul_zero,
          zero_smul]))]
    have happ := DFunLike.congr_fun (mode_iterate_borcherds_nonnegε V hu hv k N) x
    rw [show V.smul (V.smul u (k : ℤ) v) N x = mode (V.Y (V.smul u (k : ℤ) v)) N x from rfl,
      happ, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.mul_apply, ← zpow_natCast (-1 : ℂ) k]
    simp only [← SuperVertexAlgebra.smul_def]

end SuperNearVOA

end VOA
