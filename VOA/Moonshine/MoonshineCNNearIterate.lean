import VOA.Moonshine.MoonshineCNNearNthProduct
import VOA.Core.SuperBorcherdsIdentity

/-! Negative normal products and the iterate identity at every integer index.
Port of the translation-covariant field argument in `SuperBorcherdsIdentity`. -/

namespace VOA
open Module (End)
open scoped BigOperators
open VertexOperatorAlgebra (deriv_pow_apply posfac_eq negfac_eq neg_one_zpow_negsucc
  finsum_split_nat_neg gBinom_natCast_eq_zero prod_one_add_factorial)
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace NearVOA

theorem dcov_Y (V : NearVOA 𝒱) (u : 𝒱) :
    VOA.Reconstruction.DCovariant (V.L (-1)) (V.Y u) := by
  intro m
  rw [← LieRing.of_associative_ring_bracket]
  exact L_comm_Ycoeff V u m

theorem vacuum_recursion_eq (V : NearVOA 𝒱) (B : FormalDist (End ℂ 𝒱)) (w : 𝒱)
    (hneg : ∀ s : ℤ, s < 0 → B s V.vacuum = 0)
    (hbase : B 0 V.vacuum = w)
    (hrec : ∀ s : ℤ, V.L (-1) (B s V.vacuum) = (s + 1) • B (s + 1) V.vacuum)
    (s : ℤ) : B s V.vacuum = (V.Y w) s V.vacuum := by
  by_cases hs : s < 0
  · rw [hneg s hs, V.Y_apply_vacuum_eq_zero w hs]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, s = (j : ℤ) := ⟨s.toNat, by omega⟩
    clear hs
    induction j with
    | zero =>
        rw [Nat.cast_zero, hbase]
        exact (V.Y_apply_vacuum_zero _).symm
    | succ i ih =>
        have hYrec : V.L (-1) ((V.Y w) (i : ℤ) V.vacuum)
            = ((i : ℤ) + 1) • (V.Y w) ((i : ℤ) + 1) V.vacuum := by
          have h := DFunLike.congr_fun (L_comm_Ycoeff V w (i : ℤ)) V.vacuum
          rw [LinearMap.smul_apply, LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
            Module.End.mul_apply, Module.End.mul_apply, L_neg_one_vacuum, map_zero,
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

theorem deriv_pow_Y_vacuum_neg (V : NearVOA 𝒱) (u : 𝒱) (k : ℕ) {q : ℤ} (hq : q < 0) :
    ((deriv^[k]) (V.Y u)) q V.vacuum = 0 := by
  rcases lt_or_ge (q + (k : ℤ)) 0 with h | h
  · rw [deriv_pow_apply, LinearMap.smul_apply,
      V.Y_apply_vacuum_eq_zero u h, smul_zero]
  · rw [deriv_pow_middle_zero (V.Y u) k (by omega) hq]
    rfl

theorem assoc_neg (V : NearVOA 𝒱) (u v : 𝒱) (k : ℕ) :
    V.Y (V.smul u (-(k : ℤ) - 1) v)
      = (k.factorial : ℂ)⁻¹ • nprodε ((1 : ℂ)) ((isField_Y V u).deriv_iterate k)
          (isField_Y V v) := by
  set ha := (isField_Y V u).deriv_iterate k with hadef
  set hb := isField_Y V v with hbdef
  symm
  refine V.goddard_uniqueness _ (V.smul u (-(k : ℤ) - 1) v)
    (fun b => ?_) (fun m => ?_)
  · apply (localε_one_iff _ _).mp
    refine Localε.smul_left _ _ ?_
    have hdn := dong_negε (by norm_num : (1 : ℂ) * 1 = 1) ha hb
      ((V.localε_one u v).deriv_iterate_left k)
      ((V.localε_one u b).deriv_iterate_left k) (V.localε_one v b)
    simpa only [one_mul] using hdn
  · refine vacuum_recursion_eq V ((k.factorial : ℂ)⁻¹ • nprodε ((1 : ℂ)) ha hb)
      (V.smul u (-(k : ℤ) - 1) v) (fun s hs => ?_) ?_ (fun s => ?_) m
    · show ((k.factorial : ℂ)⁻¹ • nprodε ((1 : ℂ)) ha hb s) V.vacuum = 0
      rw [LinearMap.smul_apply,
        nprodε_vacuum_neg_gen ((1 : ℂ)) ha hb V.vacuum
          (fun t ht => deriv_pow_Y_vacuum_neg V u k ht)
          (fun t ht => V.Y_apply_vacuum_eq_zero v ht) hs, smul_zero]
    · show ((k.factorial : ℂ)⁻¹ • nprodε ((1 : ℂ)) ha hb 0) V.vacuum = _
      rw [LinearMap.smul_apply,
        nprodε_vacuum_base_gen ((1 : ℂ)) ha hb V.vacuum
          (fun t ht => deriv_pow_Y_vacuum_neg V u k ht)
          (fun t ht => V.Y_apply_vacuum_eq_zero v ht),
        V.Y_apply_vacuum_zero v, deriv_pow_apply,
        show (0 : ℤ) + (k : ℤ) = (k : ℤ) from by ring,
        show (∏ i ∈ Finset.range k, ((0 : ℤ) + 1 + (i : ℤ)))
            = (k.factorial : ℤ) from by
          rw [← VertexOperatorAlgebra.prod_one_add_factorial]
          exact Finset.prod_congr rfl (fun i _ => by ring),
        LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℂ (k.factorial : ℤ), Int.cast_natCast,
        smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul,
        smul_def, mode_apply]
      congr 1
      ring
    · show V.L (-1) (((k.factorial : ℂ)⁻¹ • nprodε ((1 : ℂ)) ha hb s) V.vacuum)
        = (s + 1) • ((k.factorial : ℂ)⁻¹ • nprodε ((1 : ℂ)) ha hb (s + 1)) V.vacuum
      have hcov : VOA.Reconstruction.DCovariant (V.L (-1))
          ((k.factorial : ℂ)⁻¹ • nprodε ((1 : ℂ)) ha hb) :=
        VOA.Reconstruction.DCovariant.smul _
          (VOA.DCovariant.nprodε ((1 : ℂ)) ha hb
            (VOA.Reconstruction.DCovariant.deriv_iterate (dcov_Y V u) k)
            (dcov_Y V v))
      have h := DFunLike.congr_fun (hcov s) V.vacuum
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, L_neg_one_vacuum,
        map_zero, LinearMap.smul_apply, sub_zero] at h
      exact h

theorem assoc_neg_mode_expand (V : NearVOA 𝒱) (u v : 𝒱) (k : ℕ) (N : ℤ) (x : 𝒱) :
    V.smul (V.smul u (-(k : ℤ) - 1) v) N x
      = (k.factorial : ℂ)⁻¹ • ∑ᶠ m : ℤ,
          normalOrderedε ((1 : ℂ)) ((deriv^[k]) (V.Y u)) (V.Y v) m (-N - 1 - m) x := by
  rw [smul_def, mode_apply, assoc_neg V u v k]
  show (k.factorial : ℂ)⁻¹ • (nprodε ((1 : ℂ)) ((isField_Y V u).deriv_iterate k)
      (isField_Y V v) (-N - 1) x)
    = (k.factorial : ℂ)⁻¹ • ∑ᶠ m : ℤ,
        normalOrderedε ((1 : ℂ)) ((deriv^[k]) (V.Y u)) (V.Y v) m (-N - 1 - m) x
  rw [nprodε_apply]

theorem mode_iterate_neg (V : NearVOA 𝒱) (u v : 𝒱) (k : ℕ) (N : ℤ) (x : 𝒱) :
    V.smul (V.smul u (-(k : ℤ) - 1) v) N x
      = ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i) •
          (V.smul u (-(k : ℤ) - 1 - i) (V.smul v (N + i) x)
            - ((1 : ℂ) * (-1 : ℂ) ^ (-(k : ℤ) - 1)) •
                V.smul v (-(k : ℤ) - 1 + N - i) (V.smul u i x)) := by
  rw [assoc_neg_mode_expand V u v]
  set ha := (isField_Y V u).deriv_iterate k with hadef
  set hb := isField_Y V v with hbdef
  have hfin : (Function.support fun m : ℤ =>
      normalOrderedε ((1 : ℂ)) ((deriv^[k]) (V.Y u)) (V.Y v) m (-N - 1 - m) x).Finite :=
    normalOrderedε_diag_support_finite ((1 : ℂ)) ha hb (-N - 1) x
  have hmid : ∀ m : ℤ, -(k : ℤ) - 1 < m → m < 0 →
      normalOrderedε ((1 : ℂ)) ((deriv^[k]) (V.Y u)) (V.Y v) m (-N - 1 - m) x = 0 := by
    intro m hm1 hm2
    rw [normalOrderedε_apply, if_neg (not_le.mpr hm2), LinearMap.smul_apply,
      Module.End.mul_apply, deriv_pow_middle_zero (V.Y u) k hm1 hm2]
    simp
  have hinjA : Function.Injective (fun i : ℕ => (i : ℤ)) := Nat.cast_injective
  have hinjB : Function.Injective (fun i : ℕ => -(k : ℤ) - 1 - (i : ℤ)) :=
    fun a b hab => by simp only at hab; omega
  have hA : (Function.support fun i : ℕ =>
      normalOrderedε ((1 : ℂ)) ((deriv^[k]) (V.Y u)) (V.Y v) (i : ℤ)
        (-N - 1 - (i : ℤ)) x).Finite :=
    (hfin.preimage hinjA.injOn).subset (fun i hi => hi)
  have hB : (Function.support fun i : ℕ =>
      normalOrderedε ((1 : ℂ)) ((deriv^[k]) (V.Y u)) (V.Y v) (-(k : ℤ) - 1 - (i : ℤ))
        (-N - 1 - (-(k : ℤ) - 1 - (i : ℤ))) x).Finite :=
    (hfin.preimage hinjB.injOn).subset (fun i hi => hi)
  have hsum_fin : (Function.support fun i : ℕ =>
      normalOrderedε ((1 : ℂ)) ((deriv^[k]) (V.Y u)) (V.Y v) (i : ℤ) (-N - 1 - (i : ℤ)) x
        + normalOrderedε ((1 : ℂ)) ((deriv^[k]) (V.Y u)) (V.Y v) (-(k : ℤ) - 1 - (i : ℤ))
            (-N - 1 - (-(k : ℤ) - 1 - (i : ℤ))) x).Finite := by
    refine (hA.union hB).subset (fun i hi => ?_)
    rw [Function.mem_support] at hi
    by_contra hc
    rw [Set.mem_union, Function.mem_support, Function.mem_support, not_or, not_not,
      not_not] at hc
    exact hi (by rw [hc.1, hc.2, add_zero])
  rw [finsum_split_nat_neg _ k hfin hmid, smul_finsum' (k.factorial : ℂ)⁻¹ hsum_fin]
  refine finsum_congr (fun i => ?_)
  have eA : normalOrderedε ((1 : ℂ)) ((deriv^[k]) (V.Y u)) (V.Y v) (i : ℤ)
        (-N - 1 - (i : ℤ)) x
      = normalOrdered ((deriv^[k]) (V.Y u)) (V.Y v) (i : ℤ) (-N - 1 - (i : ℤ)) x := by
    rw [normalOrderedε_eq, if_pos (by exact_mod_cast Nat.zero_le i), one_smul]
  have eB : normalOrderedε ((1 : ℂ)) ((deriv^[k]) (V.Y u)) (V.Y v) (-(k : ℤ) - 1 - (i : ℤ))
        (-N - 1 - (-(k : ℤ) - 1 - (i : ℤ))) x
      = (1 : ℂ) • normalOrdered ((deriv^[k]) (V.Y u)) (V.Y v) (-(k : ℤ) - 1 - (i : ℤ))
        (-N - 1 - (-(k : ℤ) - 1 - (i : ℤ))) x := by
    rw [normalOrderedε_eq, if_neg (by omega : ¬ (0 : ℤ) ≤ -(k : ℤ) - 1 - (i : ℤ)),
      LinearMap.smul_apply]
  have eBB : (k.factorial : ℂ)⁻¹ • ((1 : ℂ) •
        normalOrdered ((deriv^[k]) (V.Y u)) (V.Y v) (-(k : ℤ) - 1 - (i : ℤ))
          (-N - 1 - (-(k : ℤ) - 1 - (i : ℤ))) x)
      = (1 : ℂ) • (((-1 : ℂ) ^ k * ((-1 : ℂ) ^ i * gBinom (-(k : ℤ) - 1) i)) •
          (mode (V.Y v) (-(k : ℤ) - 1 + N - i) (mode (V.Y u) i x))) := by
    rw [smul_comm, iterate_neg_term_B (V.Y u) (V.Y v) k N x i]
  rw [eA, eB, smul_add, iterate_neg_term_A (V.Y u) (V.Y v) k N x i, eBB,
    neg_one_zpow_negsucc]
  simp only [← smul_def]
  module

theorem mode_iterate (V : NearVOA 𝒱) (u v : 𝒱) (ℓ N : ℤ) (x : 𝒱) :
    V.smul (V.smul u ℓ v) N x
      = ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom ℓ i) •
          (V.smul u (ℓ - i) (V.smul v (N + i) x)
            - ((1 : ℂ) * (-1 : ℂ) ^ ℓ) • V.smul v (ℓ + N - i) (V.smul u i x)) := by
  rcases lt_or_ge ℓ 0 with hℓ | hℓ
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = -(k : ℤ) - 1 := ⟨(-ℓ - 1).toNat, by omega⟩
    exact mode_iterate_neg V u v k N x
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = (k : ℤ) := ⟨ℓ.toNat, by omega⟩
    rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (k + 1)) (by
      intro i hi
      rw [Function.mem_support] at hi
      by_contra hc
      rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
      exact hi (by
        rw [VertexOperatorAlgebra.gBinom_natCast_eq_zero (by omega : k < i), mul_zero,
          zero_smul]))]
    have happ := DFunLike.congr_fun (mode_iterate_borcherds_nonneg V u v k N) x
    rw [show V.smul (V.smul u (k : ℤ) v) N x = mode (V.Y (V.smul u (k : ℤ) v)) N x from rfl,
      happ, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.mul_apply, ← zpow_natCast (-1 : ℂ) k]
    simp only [← smul_def]

end NearVOA

end VOA
