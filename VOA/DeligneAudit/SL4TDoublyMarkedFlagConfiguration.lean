import VOA.DeligneAudit.SL4TDoublyMarkedFlagRank

/-!
# The deformation lower bound for the doubly marked full flag

A configuration of the doubly marked flag on `B + 2` roots puts one root `a` of the first group
and one root `b` of the second group `V` at the point `0`, and arranges the other `B` roots as a
paired configuration on `B - k` distinct nonzero sites. It is recorded as the position `a ∉ V`
together with a singly marked configuration of the remaining roots with marked group
`deletedGroup a V` (`DoublyMarkedConfiguration`). The points are injective
(`doublyMarkedPoint_injective`) and every generator of the doubly marked ideal is a leading
relation of the points (`doublyMarkedFlagIdeal_le_pointInitialIdeal`). For the power sum
`p_h(V)` the vanishing polynomial is `∑_{i ∈ V} Q(x_i) - Q(0)` with `Q = ∏ (t - ζ_a)`: exactly one
root of `V` sits at `0`.

With the doubly marked upper bound this gives the exact dimension `|Vᶜ| · |V| · B!/2^k`
(`doublyMarkedFlag_finrank_eq`).
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-- A configuration of the doubly marked flag: the first-group root at zero and a singly marked
configuration of the remaining roots. -/
abbrev DoublyMarkedConfiguration (B k : ℕ) (V : Finset (Fin (B + 2))) :=
  Σ a : {a : Fin (B + 2) // a ∉ V}, SinglyMarkedConfiguration B k (deletedGroup a.val V)

/-- The complex point of a doubly marked configuration. -/
def doublyMarkedPoint (B k : ℕ) (V : Finset (Fin (B + 2))) (ζ : Fin (B - k) → ℂ)
    (c : DoublyMarkedConfiguration B k V) : Fin (B + 2) → ℂ :=
  Fin.insertNth (α := fun _ => ℂ) c.1.val 0 (singlyMarkedPoint B k _ ζ c.2)

theorem doublyMarkedPoint_injective (B k : ℕ) (V : Finset (Fin (B + 2)))
    (ζ : Fin (B - k) → ℂ) (hζ : Function.Injective ζ) (hζ0 : ∀ a, ζ a ≠ 0) :
    Function.Injective (doublyMarkedPoint B k V ζ) := by
  rintro ⟨⟨a, ha⟩, c⟩ ⟨⟨a', ha'⟩, c'⟩ hx
  simp only [doublyMarkedPoint] at hx
  have haa : a = a' := by
    by_contra hne
    obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hne
    have h1 := congrFun hx a
    rw [Fin.insertNth_apply_same] at h1
    conv_rhs at h1 => rw [← ht]
    rw [Fin.insertNth_apply_succAbove] at h1
    rcases Fin.eq_self_or_eq_succAbove c'.1.val t with h2 | ⟨s, hs⟩
    · apply ha
      rw [← ht, h2]
      exact (mem_deletedGroup _ _ _).mp c'.1.2
    · rw [hs, singlyMarkedPoint, Fin.insertNth_apply_succAbove] at h1
      exact hζ0 _ h1.symm
  subst haa
  have hc : c = c' := by
    apply singlyMarkedPoint_injective B k _ ζ hζ hζ0
    funext j
    have h1 := congrFun hx (a.succAbove j)
    rwa [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove] at h1
  subst hc
  rfl

/-- The elementary symmetric functions at a doubly marked point are those of its paired
configuration. -/
theorem doublyMarkedPoint_esymm (B k : ℕ) (V : Finset (Fin (B + 2))) (ζ : Fin (B - k) → ℂ)
    (c : DoublyMarkedConfiguration B k V) (s : ℕ) :
    aeval (doublyMarkedPoint B k V ζ c) (esymm (Fin (B + 2)) ℂ s) =
      aeval (fun j => ζ (c.2.2.val j)) (esymm (Fin B) ℂ s) := by
  rw [doublyMarkedPoint, esymm_aeval_insertNth_zero, singlyMarkedPoint,
    esymm_aeval_insertNth_zero]

/-- The coordinates of a doubly marked point are `0` or one of the site values. -/
theorem doublyMarkedPoint_coordinate (B k : ℕ) (V : Finset (Fin (B + 2)))
    (ζ : Fin (B - k) → ℂ) (c : DoublyMarkedConfiguration B k V) (i : Fin (B + 2)) :
    doublyMarkedPoint B k V ζ c i = 0 ∨ ∃ t, doublyMarkedPoint B k V ζ c i = ζ t := by
  rcases Fin.eq_self_or_eq_succAbove c.1.val i with h | ⟨j, rfl⟩
  · left
    rw [h, doublyMarkedPoint, Fin.insertNth_apply_same]
  · rw [doublyMarkedPoint, Fin.insertNth_apply_succAbove, singlyMarkedPoint]
    rcases Fin.eq_self_or_eq_succAbove c.2.1.val j with h | ⟨s, rfl⟩
    · left
      rw [h, Fin.insertNth_apply_same]
    · right
      exact ⟨c.2.2.val s, by rw [Fin.insertNth_apply_succAbove]⟩

/-- A root of the second group sits at `0` exactly when it is the marked root of the
configuration. -/
theorem doublyMarkedPoint_secondGroup_zero (B k : ℕ) (V : Finset (Fin (B + 2)))
    (ζ : Fin (B - k) → ℂ) (hζ0 : ∀ a, ζ a ≠ 0) (c : DoublyMarkedConfiguration B k V)
    (i : Fin (B + 2)) (hi : i ∈ V) :
    doublyMarkedPoint B k V ζ c i = 0 ↔ i = c.1.val.succAbove c.2.1.val := by
  constructor
  · intro h0
    rcases Fin.eq_self_or_eq_succAbove c.1.val i with h | ⟨j, rfl⟩
    · exact absurd (h ▸ hi) c.1.2
    · rw [doublyMarkedPoint, Fin.insertNth_apply_succAbove, singlyMarkedPoint] at h0
      rcases Fin.eq_self_or_eq_succAbove c.2.1.val j with h | ⟨s, rfl⟩
      · rw [h]
      · rw [Fin.insertNth_apply_succAbove] at h0
        exact absurd h0 (hζ0 _)
  · rintro rfl
    rw [doublyMarkedPoint, Fin.insertNth_apply_succAbove, singlyMarkedPoint,
      Fin.insertNth_apply_same]

/-- The power sum `p_h(V)` is a leading relation of the doubly marked points. -/
theorem doublyMarkedPoint_powerSum_mem (B k : ℕ) (V : Finset (Fin (B + 2)))
    (ζ : Fin (B - k) → ℂ) (hζ0 : ∀ a, ζ a ≠ 0) (hh : 1 ≤ B - k) :
    flagGroupPowerSum V (B - k) ∈ pointInitialIdeal (doublyMarkedPoint B k V ζ) := by
  classical
  let Q : Fin (B + 2) → MvPolynomial (Fin (B + 2)) ℂ := fun i =>
    ((List.ofFn ζ).map fun z => X i - MvPolynomial.C z).prod
  let c : ℂ := ((List.ofFn ζ).map fun z => (0 : ℂ) - z).prod
  let P : MvPolynomial (Fin (B + 2)) ℂ := (∑ i ∈ V, Q i) - MvPolynomial.C c
  have htop : ∀ i, (Q i).totalDegree ≤ B - k ∧ homogeneousComponent (B - k) (Q i) =
      X i ^ (B - k) := by
    intro i
    have h := affineRootProduct_top (σ := Fin (B + 2)) i (List.ofFn ζ)
    simpa only [List.length_ofFn] using h
  have heval : ∀ (x : Fin (B + 2) → ℂ) i, aeval x (Q i) =
      ((List.ofFn ζ).map fun z => x i - z).prod := by
    intro x i
    simp only [Q, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro z _
    simp
  have hvan : finitePointEvaluation (doublyMarkedPoint B k V ζ) P = 0 := by
    funext a
    change aeval (doublyMarkedPoint B k V ζ a) P = 0
    simp only [P, map_sub, map_sum, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    have hb : a.1.val.succAbove a.2.1.val ∈ V := (mem_deletedGroup _ _ _).mp a.2.1.2
    rw [Finset.sum_eq_single (a.1.val.succAbove a.2.1.val)]
    · rw [heval, (doublyMarkedPoint_secondGroup_zero B k V ζ hζ0 a _ hb).mpr rfl, sub_self]
    · intro i hi hne
      rw [heval]
      rcases doublyMarkedPoint_coordinate B k V ζ a i with h0 | ⟨t, ht⟩
      · exact absurd ((doublyMarkedPoint_secondGroup_zero B k V ζ hζ0 a i hi).mp h0) hne
      · apply List.prod_eq_zero
        rw [ht, List.mem_map]
        exact ⟨ζ t, List.mem_ofFn.mpr ⟨t, rfl⟩, sub_self _⟩
    · intro hn
      exact absurd hb hn
  have hdeg : P.totalDegree ≤ B - k := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_finset_sum _ _).trans
      exact Finset.sup_le fun i _ => (htop i).1
    · rw [totalDegree_C]
      exact Nat.zero_le _
  have hm := pointInitialIdeal_of_vanishing _ P hvan (B - k) hdeg
  have hc : homogeneousComponent (B - k) P = flagGroupPowerSum V (B - k) := by
    simp only [P, map_sub, map_sum, flagGroupPowerSum]
    rw [homogeneousComponent_eq_zero (B - k) (MvPolynomial.C c) (by rw [totalDegree_C]; omega),
      sub_zero]
    exact Finset.sum_congr rfl (fun i _ => (htop i).2)
  rwa [hc] at hm

/-- **Deformation.** Every generator of the doubly marked ideal is a leading relation of the
doubly marked points. -/
theorem doublyMarkedFlagIdeal_le_pointInitialIdeal (B k : ℕ) (V : Finset (Fin (B + 2)))
    (hV : V.Nonempty) (hU : Vᶜ.Nonempty) (ζ : Fin (B - k) → ℂ) (hζ0 : ∀ a, ζ a ≠ 0) :
    doublyMarkedFlagIdeal (B + 2) V (B - k) ≤
      pointInitialIdeal (doublyMarkedPoint B k V ζ) := by
  have hcut : ∀ i, (X i : MvPolynomial (Fin (B + 2)) ℂ) ^ (B - k + 1) ∈
      pointInitialIdeal (doublyMarkedPoint B k V ζ) := by
    intro i
    apply pointInitialIdeal_coordinate_power_of_exists _ (B - k + 1)
      (Fin.cons (α := fun _ => ℂ) 0 ζ) i
    intro a
    rcases doublyMarkedPoint_coordinate B k V ζ a i with h0 | ⟨t, ht⟩
    · exact ⟨0, by rw [h0]; rfl⟩
    · exact ⟨t.succ, by rw [ht]; rfl⟩
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · apply Ideal.span_le.mpr
    rintro p ⟨s, hs, rfl⟩
    obtain ⟨c, hc⟩ := fullFlagStratumPoint_symmetric_constant B k (k + 1) ∅ ζ
      (esymm (Fin B) ℂ s) (esymm_isSymmetric (Fin B) ℂ s)
    apply pointInitialIdeal_of_constant _ _ s hs (elementarySymmetric_homogeneous s) c
    funext a
    change aeval (doublyMarkedPoint B k V ζ a) (esymm (Fin (B + 2)) ℂ s) = c
    rw [doublyMarkedPoint_esymm]
    exact congrFun hc ⟨a.2.2, lt_of_le_of_lt (fullFlagDoublesIn_le B k ∅ a.2.2)
      (Nat.lt_succ_self k)⟩
  · apply Ideal.span_le.mpr
    rintro p ⟨S, hS, rfl⟩
    have hSne : S.Nonempty ∧ ∀ a : DoublyMarkedConfiguration B k V,
        ∃ i ∈ S, doublyMarkedPoint B k V ζ a i = 0 := by
      rcases hS with hS | hS
      · rw [hS]
        refine ⟨hU, fun a => ⟨a.1.val, Finset.mem_compl.mpr a.1.2, ?_⟩⟩
        rw [doublyMarkedPoint, Fin.insertNth_apply_same]
      · rw [Set.mem_singleton_iff] at hS
        rw [hS]
        refine ⟨hV, fun a => ⟨_, (mem_deletedGroup _ _ _).mp a.2.1.2, ?_⟩⟩
        exact (doublyMarkedPoint_secondGroup_zero B k V ζ hζ0 a _
          ((mem_deletedGroup _ _ _).mp a.2.1.2)).mpr rfl
    apply pointInitialIdeal_of_constant _ _ S.card (Finset.card_pos.mpr hSne.1) _ 0
    · funext a
      change aeval (doublyMarkedPoint B k V ζ a) (flagGroupProduct S) = 0
      simp only [flagGroupProduct, map_prod, aeval_X]
      obtain ⟨i, hi, h0⟩ := hSne.2 a
      exact Finset.prod_eq_zero hi h0
    · have h := IsHomogeneous.prod S (fun i => (X i : MvPolynomial (Fin (B + 2)) ℂ))
        (fun _ => 1) (fun i _ => isHomogeneous_X ℂ i)
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul] using h
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact hcut i
  · apply Ideal.span_le.mpr
    rintro p ⟨s, hs, rfl⟩
    by_cases hsh : B - k + 1 ≤ s
    · apply Ideal.sum_mem
      intro i _
      rw [show s = (B - k + 1) + (s - (B - k + 1)) by omega, pow_add]
      exact Ideal.mul_mem_right _ _ (hcut i)
    · obtain rfl : s = B - k := by omega
      exact doublyMarkedPoint_powerSum_mem B k V ζ hζ0 (by omega)

/-- **The doubly marked lower bound.** -/
theorem doublyMarkedFlag_finrank_ge (B k : ℕ) (V : Finset (Fin (B + 2))) :
    Vᶜ.card * V.card * Nat.card (FullFlagConfiguration B k) ≤
      Module.finrank ℂ (DoublyMarkedFlagRing (B + 2) V (B - k)) := by
  classical
  by_cases hV : V.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hV]
    simp
  by_cases hU : Vᶜ.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hU]
    simp
  let ζ : Fin (B - k) → ℂ := fun a => (a.val : ℂ) + 1
  have hζ : Function.Injective ζ := by
    intro a b h
    apply Fin.ext
    have h' : (a.val : ℂ) = b.val := by simpa [ζ] using h
    exact_mod_cast h'
  have hζ0 : ∀ a, ζ a ≠ 0 := by
    intro a h
    have h' : ((a.val + 1 : ℕ) : ℂ) = 0 := by simpa [ζ] using h
    exact Nat.succ_ne_zero a.val (by exact_mod_cast h')
  letI : Fintype (FullFlagConfiguration B k) := Fintype.ofFinite _
  obtain ⟨hfin, hdim⟩ := pointInitialQuotient_finrank (doublyMarkedPoint B k V ζ)
    (doublyMarkedPoint_injective B k V ζ hζ hζ0)
  letI := hfin
  have hle := doublyMarkedFlagIdeal_le_pointInitialIdeal B k V hV hU ζ hζ0
  have hs := LinearMap.finrank_le_finrank_of_surjective
    (f := (Ideal.Quotient.factorₐ ℂ hle).toLinearMap) (Ideal.Quotient.factor_surjective hle)
  have hcard : Fintype.card (DoublyMarkedConfiguration B k V) =
      Vᶜ.card * V.card * Nat.card (FullFlagConfiguration B k) := by
    rw [Fintype.card_sigma]
    have hterm : ∀ a : {a : Fin (B + 2) // a ∉ V},
        Fintype.card (SinglyMarkedConfiguration B k (deletedGroup a.val V)) =
          V.card * Nat.card (FullFlagConfiguration B k) := by
      intro a
      rw [Fintype.card_prod, Fintype.card_coe, deletedGroup_card_of_notMem V a.val a.2,
        Nat.card_eq_fintype_card]
    rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_const, Finset.card_univ,
      smul_eq_mul,
      Fintype.card_congr (Equiv.subtypeEquivRight (fun a => (Finset.mem_compl (s := V)).symm)),
      Fintype.card_coe, mul_assoc]
  rw [hdim, hcard] at hs
  exact hs

/-- **The doubly marked dimension.** The doubly marked full flag has dimension
`|Vᶜ| · |V| · B!/2^k`. -/
theorem doublyMarkedFlag_finrank_eq (B k : ℕ) (hk : 2 * k ≤ B) (V : Finset (Fin (B + 2))) :
    Module.finrank ℂ (DoublyMarkedFlagRing (B + 2) V (B - k)) =
      Vᶜ.card * V.card * Nat.card (FullFlagConfiguration B k) :=
  le_antisymm (doublyMarkedFlag_finrank_le B k hk V) (doublyMarkedFlag_finrank_ge B k V)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.doublyMarkedPoint_injective
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedPoint_esymm
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedPoint_coordinate
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedPoint_secondGroup_zero
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedPoint_powerSum_mem
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlagIdeal_le_pointInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_finrank_ge
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_finrank_eq
