import VOA.DeligneAudit.SL4TSinglyMarkedFlagRank

/-!
# The deformation lower bound for the singly marked full flag

A configuration of the singly marked flag on `B + 1` roots puts one root of the marked group `V`
at the point `0` and arranges the other `B` roots as a paired configuration on `B - k` distinct
nonzero sites (`SinglyMarkedConfiguration`). The corresponding complex points are injective
(`singlyMarkedPoint_injective`). Every generator of the singly marked ideal is the top homogeneous
part of a polynomial vanishing on these points (`singlyMarkedFlagIdeal_le_pointInitialIdeal`), so
the ring surjects onto the leading-relation algebra of the points, whose dimension is the number
of configurations. With the upper bound of `SL4TSinglyMarkedFlagRank` this gives the exact
dimension `|V| · B!/2^k` (`singlyMarkedFlag_finrank_eq`).
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-- Inserting a zero root does not change the elementary symmetric functions. -/
theorem esymm_aeval_insertNth_zero {n : ℕ} (v : Fin (n + 1)) (g : Fin n → ℂ) (s : ℕ) :
    aeval (Fin.insertNth (α := fun _ => ℂ) v 0 g) (esymm (Fin (n + 1)) ℂ s) =
      aeval g (esymm (Fin n) ℂ s) := by
  have key : ∀ {m : ℕ} (p : Fin m → ℂ),
      (D4Levi.ksEPoly (List.ofFn p)).coeff s = (-1) ^ s * aeval p (esymm (Fin m) ℂ s) := by
    intro m p
    have hm := alphabetElementary_map (aeval p).toRingHom
      (List.ofFn fun i : Fin m => (X i : MvPolynomial (Fin m) ℂ))
    simp only [List.map_ofFn, Function.comp_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_X] at hm
    rw [← hm, Polynomial.coeff_map, elementaryProduct_coeff]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow, map_neg, map_one]
  have hE : D4Levi.ksEPoly (List.ofFn (Fin.insertNth (α := fun _ => ℂ) v 0 g)) =
      D4Levi.ksEPoly (List.ofFn g) := by
    rw [ksEPoly_ofFn_eq_group, ksEPoly_ofFn_eq_group, groupElementaryPolynomial,
      Fin.prod_univ_succAbove _ v, Fin.insertNth_apply_same]
    simp only [Fin.insertNth_apply_succAbove, map_zero, zero_mul, sub_zero, one_mul]
    rfl
  have h1 := key (Fin.insertNth (α := fun _ => ℂ) v 0 g)
  rw [hE, key g] at h1
  exact ((isUnit_neg_one (α := ℂ)).pow s).mul_left_cancel h1.symm

/-- A coordinate taking values in a finite list of sites at every point has its cutoff power as
a leading relation. -/
theorem pointInitialIdeal_coordinate_power_of_exists {ι σ : Type*} (x : ι → σ → ℂ) (N : ℕ)
    (ζ : Fin N → ℂ) (i : σ) (hx : ∀ a, ∃ b, x a i = ζ b) :
    (X i : MvPolynomial σ ℂ) ^ N ∈ pointInitialIdeal x :=
  pointInitialIdeal_coordinate_power x N ζ i (fun a => Classical.choose (hx a))
    (fun a => Classical.choose_spec (hx a))

/-- A configuration of the singly marked flag: the marked root at the zero point and a paired
configuration of the remaining roots. -/
abbrev SinglyMarkedConfiguration (B k : ℕ) (V : Finset (Fin (B + 1))) :=
  {v : Fin (B + 1) // v ∈ V} × FullFlagConfiguration B k

/-- The complex point of a singly marked configuration. -/
def singlyMarkedPoint (B k : ℕ) (V : Finset (Fin (B + 1))) (ζ : Fin (B - k) → ℂ)
    (c : SinglyMarkedConfiguration B k V) : Fin (B + 1) → ℂ :=
  Fin.insertNth (α := fun _ => ℂ) c.1.val 0 fun j => ζ (c.2.val j)

theorem singlyMarkedPoint_injective (B k : ℕ) (V : Finset (Fin (B + 1)))
    (ζ : Fin (B - k) → ℂ) (hζ : Function.Injective ζ) (hζ0 : ∀ a, ζ a ≠ 0) :
    Function.Injective (singlyMarkedPoint B k V ζ) := by
  rintro ⟨⟨v, hv⟩, f⟩ ⟨⟨v', hv'⟩, f'⟩ hx
  simp only [singlyMarkedPoint] at hx
  have hvv : v = v' := by
    by_contra hne
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
    have h1 := congrFun hx v
    rw [Fin.insertNth_apply_same] at h1
    conv_rhs at h1 => rw [← hj]
    rw [Fin.insertNth_apply_succAbove] at h1
    exact hζ0 _ h1.symm
  subst hvv
  have hff : f = f' := by
    apply Subtype.ext
    funext j
    have h1 := congrFun hx (v.succAbove j)
    rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove] at h1
    exact hζ h1
  subst hff
  rfl

/-- Elementary symmetric functions are constant on the singly marked points. -/
theorem singlyMarkedPoint_esymm_constant (B k : ℕ) (V : Finset (Fin (B + 1)))
    (ζ : Fin (B - k) → ℂ) (s : ℕ) :
    ∃ c : ℂ, finitePointEvaluation (singlyMarkedPoint B k V ζ) (esymm (Fin (B + 1)) ℂ s) =
      fun _ => c := by
  obtain ⟨c, hc⟩ := fullFlagStratumPoint_symmetric_constant B k (k + 1) ∅ ζ
    (esymm (Fin B) ℂ s) (esymm_isSymmetric (Fin B) ℂ s)
  refine ⟨c, ?_⟩
  funext a
  change aeval (singlyMarkedPoint B k V ζ a) (esymm (Fin (B + 1)) ℂ s) = c
  rw [singlyMarkedPoint, esymm_aeval_insertNth_zero]
  exact congrFun hc ⟨a.2, lt_of_le_of_lt (fullFlagDoublesIn_le B k ∅ a.2) (Nat.lt_succ_self k)⟩

/-- **Deformation.** Every generator of the singly marked ideal is a leading relation of the
singly marked points. -/
theorem singlyMarkedFlagIdeal_le_pointInitialIdeal (B k : ℕ) (V : Finset (Fin (B + 1)))
    (hV : V.Nonempty) (ζ : Fin (B - k) → ℂ) :
    singlyMarkedFlagIdeal (B + 1) V (B - k) ≤
      pointInitialIdeal (singlyMarkedPoint B k V ζ) := by
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · apply Ideal.span_le.mpr
    rintro p ⟨s, hs, rfl⟩
    obtain ⟨c, hc⟩ := singlyMarkedPoint_esymm_constant B k V ζ s
    exact pointInitialIdeal_of_constant _ _ s hs (elementarySymmetric_homogeneous s) c hc
  · apply Ideal.span_le.mpr
    rintro p ⟨S, hS, rfl⟩
    rw [Set.mem_singleton_iff] at hS
    subst hS
    apply pointInitialIdeal_of_constant _ _ S.card (Finset.card_pos.mpr hV) _ 0
    · funext a
      change aeval (singlyMarkedPoint B k S ζ a) (flagGroupProduct S) = 0
      simp only [flagGroupProduct, map_prod, aeval_X]
      apply Finset.prod_eq_zero a.1.2
      simp [singlyMarkedPoint]
    · have h := IsHomogeneous.prod S (fun i => (X i : MvPolynomial (Fin (B + 1)) ℂ))
        (fun _ => 1) (fun i _ => isHomogeneous_X ℂ i)
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul] using h
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    by_cases hi : i ∈ V
    · simp only [singlyMarkedCutoff, if_pos hi]
      apply pointInitialIdeal_coordinate_power_of_exists _ (B - k + 1)
        (Fin.cons (α := fun _ => ℂ) 0 ζ) i
      intro a
      rcases Fin.eq_self_or_eq_succAbove a.1.val i with h | ⟨j, hj⟩
      · exact ⟨0, by rw [h]; simp [singlyMarkedPoint]⟩
      · exact ⟨(a.2.val j).succ, by rw [hj]; simp [singlyMarkedPoint]⟩
    · simp only [singlyMarkedCutoff, if_neg hi]
      apply pointInitialIdeal_coordinate_power_of_exists _ (B - k) ζ i
      intro a
      have hne : i ≠ a.1.val := fun h => hi (h ▸ a.1.2)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
      exact ⟨a.2.val j, by rw [← hj]; simp [singlyMarkedPoint]⟩
  · apply Ideal.span_le.mpr
    rintro p ⟨s, _, rfl⟩
    simp only [flagGroupPowerSum, Finset.sum_empty]
    exact Ideal.zero_mem _

/-- **The singly marked lower bound.** -/
theorem singlyMarkedFlag_finrank_ge (B k : ℕ) (V : Finset (Fin (B + 1))) (hV : V.Nonempty) :
    V.card * Nat.card (FullFlagConfiguration B k) ≤
      Module.finrank ℂ (SinglyMarkedFlagRing (B + 1) V (B - k)) := by
  classical
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
  obtain ⟨hfin, hdim⟩ := pointInitialQuotient_finrank (singlyMarkedPoint B k V ζ)
    (singlyMarkedPoint_injective B k V ζ hζ hζ0)
  letI := hfin
  have hle := singlyMarkedFlagIdeal_le_pointInitialIdeal B k V hV ζ
  have hs := LinearMap.finrank_le_finrank_of_surjective
    (f := (Ideal.Quotient.factorₐ ℂ hle).toLinearMap) (Ideal.Quotient.factor_surjective hle)
  rw [hdim, Fintype.card_prod, Fintype.card_coe, ← Nat.card_eq_fintype_card] at hs
  exact hs

/-- **The singly marked dimension.** -/
theorem singlyMarkedFlag_finrank_eq (B k : ℕ) (hk : 2 * k ≤ B) (V : Finset (Fin (B + 1)))
    (hV : V.Nonempty) :
    Module.finrank ℂ (SinglyMarkedFlagRing (B + 1) V (B - k)) =
      V.card * Nat.card (FullFlagConfiguration B k) :=
  le_antisymm (singlyMarkedFlag_finrank_le B k hk V hV) (singlyMarkedFlag_finrank_ge B k V hV)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.esymm_aeval_insertNth_zero
#print axioms VOA.DeligneAudit.SL4T.pointInitialIdeal_coordinate_power_of_exists
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedPoint_injective
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedPoint_esymm_constant
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlagIdeal_le_pointInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_finrank_ge
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_finrank_eq
