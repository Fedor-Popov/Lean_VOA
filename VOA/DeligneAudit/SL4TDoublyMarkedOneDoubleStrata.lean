import VOA.DeligneAudit.SL4TSinglyMarkedMixedDoubleStratum

/-!
# The doubly marked strata with one double

Let `C` be the doubly marked full flag on `m + 3` roots with one double (common cutoff `m + 1`,
both group products zero). Its configurations put a zero pair (one root of each group) at zero,
two roots at the double point and one root at each of the `m - 1` simple points. For a set `Y` of
roots with complement `Z`, with `a = |U ∩ Y|`, `b = |V ∩ Y|`, `c = |V ∖ Y|`, `d = |U ∖ Y|`:

* **One T-point.** The ideal `(∏ Z, c(Z))` (`doublyMarkedStratumIdeal`; `c(Z)` the subleading
  coefficient, `± e_(|Z|-1)(Z)`) has dimension at least the number of configurations whose zero
  pair or double point lies in `Y`:
  `(a b C(m + 1, 2) + (a c + d b) C(a + b - 1, 2) + d c C(a + b, 2)) (m - 1)!`
  (`doublyMarkedFlag_oneDouble_stratum_finrank_ge`).
* **Two T-points.** The ideal `((∏ Z)²)` has dimension at least the number of configurations whose
  zero pair and double point both lie in `Y`: `a b C(a + b - 2, 2) (m - 1)!`
  (`doublyMarkedFlag_twoDouble_stratum_finrank_ge`).

Both proofs delete a root `u ∉ Y` of one group; the two groups play symmetric roles
(`doublyMarkedFlagIdeal_compl`). For the first statement the zero layer of `u` (`u` at the double
point) is the weak flag and receives `∏ (Z ∖ u)` (`weakMarkedFlag_stratum_finrank_ge`); the
layer `1` (`u` at zero) is the singly marked flag modulo its unmarked product and receives the
singly marked stratum (`singlyMarkedProduct_stratum_finrank_ge`); the later layers (`u` at a
simple point) receive the child stratum. All transfers are exact polynomial identities.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-! ### The symmetry of the two groups -/

theorem doublyMarkedFlagIdeal_compl_le (n : ℕ) (V : Finset (Fin n)) (h : ℕ) :
    doublyMarkedFlagIdeal n Vᶜ h ≤ doublyMarkedFlagIdeal n V h := by
  classical
  unfold doublyMarkedFlagIdeal markedFlagIdeal
  refine sup_le (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) ?_)
    (le_sup_right.trans le_sup_left)) ?_
  · rw [compl_compl, Set.pair_comm]
    exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  · apply Ideal.span_le.mpr
    rintro p ⟨s, hs, rfl⟩
    have hs1 : 0 < s := Nat.lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right h 1) hs)
    have hsplit : flagGroupPowerSum Vᶜ s = psum (Fin n) ℂ s - flagGroupPowerSum V s := by
      rw [eq_sub_iff_add_eq]
      exact Finset.sum_compl_add_sum V _
    rw [SetLike.mem_coe, hsplit]
    apply Ideal.sub_mem
    · exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_sup_left
        (psum_mem_fullFlagSymmetricIdeal n s hs1)))
    · exact Ideal.mem_sup_right (Ideal.subset_span ⟨s, hs, rfl⟩)

/-- The doubly marked ideal does not depend on which group is called the first. -/
theorem doublyMarkedFlagIdeal_compl (n : ℕ) (V : Finset (Fin n)) (h : ℕ) :
    doublyMarkedFlagIdeal n Vᶜ h = doublyMarkedFlagIdeal n V h := by
  apply le_antisymm (doublyMarkedFlagIdeal_compl_le n V h)
  have h2 := doublyMarkedFlagIdeal_compl_le n Vᶜ h
  rwa [compl_compl] at h2

/-! ### Stratum ideals and their transport through layer maps -/

/-- The doubly marked stratum ideal `(∏ Z, c(Z))`, `Z = Yᶜ`. -/
def doublyMarkedStratumIdeal {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (Y : Finset (Fin n)) : Ideal (MvPolynomial (Fin n) ℂ ⧸ I) :=
  Ideal.span {∏ i ∈ Yᶜ, quotientRoot I i, groupSubtopCoefficient (quotientRoot I) Yᶜ}

theorem doublyStratum_finrank_le_layer {C : Type*} [CommRing C] [Algebra ℂ C]
    [FiniteDimensional ℂ C] {n : ℕ} (r : Fin (n + 1) → C) (u : Fin (n + 1)) (i : ℕ)
    (I' : Ideal (MvPolynomial (Fin n) ℂ))
    (hI' : I' ≤ RingHom.ker (aeval (deletedLayerRoot r u i)).toRingHom)
    (hinj : Function.Injective (deletedLayerMap r u i I' hI')) (Y' : Finset (Fin n)) :
    Module.finrank ℂ ((doublyMarkedStratumIdeal I' Y').restrictScalars ℂ) ≤
      Module.finrank ℂ (((Ideal.span {∏ j ∈ Y'ᶜ, r (u.succAbove j),
        groupSubtopCoefficient (fun j => r (u.succAbove j)) Y'ᶜ}).restrictScalars ℂ).map
        (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r u) i)).toLinearMap) := by
  have hl := childPair_finrank_le_layer r u i I' hI' hinj (∏ j ∈ Y'ᶜ, X j)
    (groupSubtopCoefficient X Y'ᶜ)
  have h1 : aeval (fun j => r (u.succAbove j)) (∏ j ∈ Y'ᶜ, (X j : MvPolynomial (Fin n) ℂ)) =
      ∏ j ∈ Y'ᶜ, r (u.succAbove j) := by
    simp
  have h2 : aeval (fun j => r (u.succAbove j))
      (groupSubtopCoefficient (X : Fin n → MvPolynomial (Fin n) ℂ) Y'ᶜ) =
      groupSubtopCoefficient (fun j => r (u.succAbove j)) Y'ᶜ := by
    have h := groupSubtopCoefficient_map (aeval (fun j => r (u.succAbove j))).toRingHom
      (X : Fin n → MvPolynomial (Fin n) ℂ) Y'ᶜ
    simpa using h
  have h3 : doublyMarkedStratumIdeal I' Y' = Ideal.span {Ideal.Quotient.mk I' (∏ j ∈ Y'ᶜ, X j),
      Ideal.Quotient.mk I' (groupSubtopCoefficient X Y'ᶜ)} := by
    rw [doublyMarkedStratumIdeal, groupSubtopCoefficient_map, map_prod]
    rfl
  rw [h1, h2, ← h3] at hl
  exact hl

theorem childSingleton_finrank_le_layer {C : Type*} [CommRing C] [Algebra ℂ C]
    [FiniteDimensional ℂ C] {n : ℕ} (r : Fin (n + 1) → C) (u : Fin (n + 1)) (i : ℕ)
    (I' : Ideal (MvPolynomial (Fin n) ℂ))
    (hI' : I' ≤ RingHom.ker (aeval (deletedLayerRoot r u i)).toRingHom)
    (hinj : Function.Injective (deletedLayerMap r u i I' hI')) (p : MvPolynomial (Fin n) ℂ) :
    Module.finrank ℂ ((Ideal.span {Ideal.Quotient.mk I' p}).restrictScalars ℂ) ≤
      Module.finrank ℂ (((Ideal.span {aeval (fun j => r (u.succAbove j)) p}).restrictScalars
        ℂ).map (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r u) i)).toLinearMap) := by
  let ψ := deletedLayerMap r u i I' hI'
  haveI : FiniteDimensional ℂ (C ⧸ rootPowerLayerIdeal (r u) i) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℂ _).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℂ _)
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective ψ.toLinearMap hinj
    ((Ideal.span {Ideal.Quotient.mk I' p}).restrictScalars ℂ))]
  apply Submodule.finrank_mono
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hx
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (ψ a)
  refine ⟨c * aeval (fun j => r (u.succAbove j)) p, ?_, ?_⟩
  · rw [SetLike.mem_coe, Submodule.restrictScalars_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · have hp : ψ (Ideal.Quotient.mk I' p) =
        Ideal.Quotient.mk _ (aeval (fun j => r (u.succAbove j)) p) :=
      aeval_deletedLayerRoot r u i p
    change Ideal.Quotient.mk _ (c * aeval (fun j => r (u.succAbove j)) p) =
      ψ (a * Ideal.Quotient.mk I' p)
    rw [map_mul, map_mul, hp, hc]

theorem aeval_prod_sq {C : Type*} [CommRing C] [Algebra ℂ C] {n : ℕ} (f : Fin n → C)
    (S : Finset (Fin n)) :
    aeval f ((∏ i ∈ S, (X i : MvPolynomial (Fin n) ℂ)) ^ 2) = (∏ i ∈ S, f i) ^ 2 := by
  rw [map_pow, map_prod]
  simp only [aeval_X]

theorem mk_prod_sq {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (S : Finset (Fin n)) :
    Ideal.Quotient.mk I ((∏ i ∈ S, (X i : MvPolynomial (Fin n) ℂ)) ^ 2) =
      (∏ i ∈ S, quotientRoot I i) ^ 2 := by
  rw [map_pow, map_prod]
  rfl

/-- If `Z = {u}`, the subleading coefficient of `Z` is `1`. -/
theorem groupSubtopCoefficient_eq_one_of_deleted_empty {A : Type*} [CommRing A] {n : ℕ}
    (x : Fin (n + 1) → A) (Z : Finset (Fin (n + 1))) (u : Fin (n + 1)) (hu : u ∈ Z)
    (he : deletedGroup u Z = ∅) : groupSubtopCoefficient x Z = 1 := by
  have hE : groupElementaryPolynomial x Z = 1 - Polynomial.C (x u) * Polynomial.X := by
    rw [groupElementaryPolynomial, prod_eq_deletedGroup _ Z u, if_pos hu, he, Finset.prod_empty,
      mul_one]
  have hc : Z.card = 1 := by
    have := deletedGroup_card_of_mem Z u hu
    rw [he, Finset.card_empty] at this
    omega
  rw [groupSubtopCoefficient, hE, hc]
  simp

/-! ### The counts -/

/-- `(a c + d b) C(a + b - 1, 2) + d c C(a + b, 2)`: configurations whose double lies in `Y` and
whose zero pair does not. -/
def doublyMarkedResidualCount (a b c d : ℕ) : ℕ :=
  (a * c + d * b) * (a + b - 1).choose 2 + d * c * (a + b).choose 2

/-- `a b C(m + 1, 2) + (a c + d b) C(a + b - 1, 2) + d c C(a + b, 2)`; times `(m - 1)!` it counts
the configurations with at least one T-point. -/
def doublyMarkedOneDoubleCount (m a b c d : ℕ) : ℕ :=
  a * b * (m + 1).choose 2 + doublyMarkedResidualCount a b c d

theorem doublyMarkedResidualCount_succ (a b c d : ℕ) :
    doublyMarkedResidualCount a b c (d + 1) =
      doublyMarkedResidualCount a b c d + singlyMarkedOneDoubleCount a b c := by
  unfold doublyMarkedResidualCount singlyMarkedOneDoubleCount
  ring

theorem doublyMarkedResidualCount_eq_zero (a b c d : ℕ) (h : a + b + c + d ≤ 3) :
    doublyMarkedResidualCount a b c d = 0 := by
  unfold doublyMarkedResidualCount
  rcases (show a + b ≤ 1 ∨ (a + b = 2 ∧ (c = 0 ∨ d = 0)) ∨ (a + b = 3 ∧ c = 0 ∧ d = 0) by
    omega) with h1 | ⟨h1, h2 | h2⟩ | ⟨h1, h2, h3⟩
  · rw [Nat.choose_eq_zero_of_lt (by omega : a + b - 1 < 2),
      Nat.choose_eq_zero_of_lt (by omega : a + b < 2)]
    simp
  · rw [h1, h2, Nat.choose_eq_zero_of_lt (show (2 : ℕ) - 1 < 2 by norm_num)]
    simp
  · rw [h1, h2, Nat.choose_eq_zero_of_lt (show (2 : ℕ) - 1 < 2 by norm_num)]
    simp
  · rw [h2, h3]
    simp

theorem doublyMarkedOneDoubleCount_symm (m a b c d : ℕ) :
    doublyMarkedOneDoubleCount m a b c d = doublyMarkedOneDoubleCount m b a d c := by
  unfold doublyMarkedOneDoubleCount doublyMarkedResidualCount
  rw [Nat.add_comm b a]
  ring

/-- `C(m + 1, 2) (m - 1)! = (m + 1)!/2`. -/
theorem choose_two_mul_factorial_eq_card (m : ℕ) (hm : 1 ≤ m) :
    (m + 1).choose 2 * (m - 1).factorial = Nat.card (FullFlagConfiguration (m + 1) 1) := by
  have h1 := fullFlagConfiguration_card_closed (m + 1) 1 (by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show 2 ≤ m + 1 by omega)
  rw [show m + 1 - 2 = m - 1 by omega, Nat.factorial_two] at h2
  rw [pow_one] at h1
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
  rw [h1, ← h2]
  ring

/-! ### One T-point -/

set_option maxHeartbeats 1600000 in
-- Three kinds of layer, each through a layer isomorphism of a presented quotient.
/-- **The doubly marked stratum with one T-point.** -/
theorem doublyMarkedFlag_oneDouble_stratum_finrank_ge (m : ℕ) (hm : 1 ≤ m)
    (V Y : Finset (Fin (m + 3))) :
    doublyMarkedOneDoubleCount m (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card (Vᶜ \ Y).card *
        (m - 1).factorial ≤
      Module.finrank ℂ ((doublyMarkedStratumIdeal (doublyMarkedFlagIdeal (m + 3) V m) Y
        ).restrictScalars ℂ) := by
  classical
  induction m with
  | zero => omega
  | succ B ih =>
      have hk : 2 * 1 ≤ B + 1 + 1 := by omega
      have hmain : ∀ V Y : Finset (Fin (B + 1 + 3)), (∃ u, u ∉ V ∧ u ∉ Y) →
          doublyMarkedOneDoubleCount (B + 1) (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card
              (Vᶜ \ Y).card * (B + 1 - 1).factorial ≤
            Module.finrank ℂ ((doublyMarkedStratumIdeal
              (doublyMarkedFlagIdeal (B + 1 + 3) V (B + 1 + 1 - 1)) Y).restrictScalars ℂ) := by
        intro V Y ⟨u, hu, huY⟩
        by_cases hVe : V = ∅
        · subst hVe
          simp [doublyMarkedOneDoubleCount, doublyMarkedResidualCount]
        have hV : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr hVe
        set ρ := quotientRoot (doublyMarkedFlagIdeal (B + 1 + 3) V (B + 1 + 1 - 1)) with hρ
        set G := doublyMarkedStratumIdeal (doublyMarkedFlagIdeal (B + 1 + 3) V (B + 1 + 1 - 1))
          Y with hG
        have hGgen : G = Ideal.span {∏ i ∈ Yᶜ, ρ i, groupSubtopCoefficient ρ Yᶜ} := rfl
        have hVprod : ∏ i ∈ V, ρ i = 0 := doublyMarkedFlag_product_zero _ _ _
        have hcut : ρ u ^ (B + 2) = 0 := doublyMarkedFlag_cutoff _ _ _ u
        have hY' : u ∈ Yᶜ := Finset.mem_compl.mpr huY
        have hprodZ : ∏ i ∈ Yᶜ, ρ i = ρ u * ∏ j ∈ (deletedGroup u Y)ᶜ, ρ (u.succAbove j) := by
          rw [prod_eq_mul_deletedGroup_of_mem ρ Yᶜ u hY', deletedGroup_compl]
        have hZG : ∏ i ∈ Yᶜ, ρ i ∈ G := Ideal.subset_span (Set.mem_insert _ _)
        have hcG : groupSubtopCoefficient ρ Yᶜ ∈ G :=
          Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
        have hG1 : ¬ ((deletedGroup u Y)ᶜ).Nonempty → (1 : DoublyMarkedFlagRing (B + 1 + 3) V
            (B + 1 + 1 - 1)) ∈ G := by
          intro hne
          have he : deletedGroup u Yᶜ = ∅ := by
            rw [deletedGroup_compl]
            exact Finset.not_nonempty_iff_eq_empty.mp hne
          have h1 := groupSubtopCoefficient_eq_one_of_deleted_empty ρ Yᶜ u hY' he
          rw [h1] at hcG
          exact hcG
        -- the subleading coefficient after deleting `u`
        have hsub : ((deletedGroup u Y)ᶜ).Nonempty →
            groupSubtopCoefficient ρ Yᶜ =
              (groupElementaryPolynomial (fun j => ρ (u.succAbove j)) (deletedGroup u Y)ᶜ).coeff
                  ((deletedGroup u Y)ᶜ).card -
                ρ u * groupSubtopCoefficient (fun j => ρ (u.succAbove j)) (deletedGroup u Y)ᶜ := by
          intro hne
          have h := groupSubtopCoefficient_deleted_of_mem ρ Yᶜ u hY'
            (by rw [deletedGroup_compl]; exact hne)
          rw [deletedGroup_compl] at h
          exact h
        have htop := groupElementaryPolynomial_coeff_card (fun j => ρ (u.succAbove j))
          (deletedGroup u Y)ᶜ
        set P := ∏ j ∈ (deletedGroup u Y)ᶜ, ρ (u.succAbove j) with hP
        set c' := groupSubtopCoefficient (fun j => ρ (u.succAbove j)) (deletedGroup u Y)ᶜ
          with hc'
        set s := ((-1 : DoublyMarkedFlagRing (B + 1 + 3) V (B + 1 + 1 - 1)) ^
          ((deletedGroup u Y)ᶜ).card) with hs
        have hsq : s ^ 2 = 1 := by
          rw [hs, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
        let W : ℕ → Submodule ℂ (DoublyMarkedFlagRing (B + 1 + 3) V (B + 1 + 1 - 1)) :=
          fun j => match j with
            | 0 => (Ideal.span {P}).restrictScalars ℂ
            | 1 => (Ideal.span {P, (∏ j ∈ deletedGroup u V ∩ deletedGroup u Y,
                ρ (u.succAbove j)) * c'}).restrictScalars ℂ
            | _ + 2 => (Ideal.span {P, c'}).restrictScalars ℂ
        have hW : ∀ j < B + 2, ∀ c ∈ W j, ρ u ^ j * c ∈
            G.restrictScalars ℂ ⊔ (Ideal.span {ρ u ^ (j + 1)}).restrictScalars ℂ := by
          intro j _ c hc
          by_cases hne : ((deletedGroup u Y)ᶜ).Nonempty
          swap
          · apply Submodule.mem_sup_left
            rw [Submodule.restrictScalars_mem]
            have h1 := G.mul_mem_left (ρ u ^ j * c) (hG1 hne)
            rwa [mul_one] at h1
          have hsub' := hsub hne
          rcases j with _ | _ | j
          · -- `u` at the double point: `∏ (Z ∖ u) ∈ G + (u)`
            change c ∈ (Ideal.span {P}).restrictScalars ℂ at hc
            rw [Submodule.restrictScalars_mem] at hc
            obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hc
            have hx : t * s * groupSubtopCoefficient ρ Yᶜ ∈ G.restrictScalars ℂ := by
              rw [Submodule.restrictScalars_mem]
              exact G.mul_mem_left _ hcG
            have hy : (t * s * c') * ρ u ^ (0 + 1) ∈
                (Ideal.span {ρ u ^ (0 + 1)}).restrictScalars ℂ := by
              rw [Submodule.restrictScalars_mem]
              exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
            refine Submodule.mem_sup.mpr ⟨_, hx, _, hy, ?_⟩
            linear_combination (t * s) * hsub' + (t * s) * htop + (t * P) * hsq
          · -- `u` at zero: the singly marked stratum
            change c ∈ (Ideal.span {P, (∏ j ∈ deletedGroup u V ∩ deletedGroup u Y,
              ρ (u.succAbove j)) * c'}).restrictScalars ℂ at hc
            rw [Submodule.restrictScalars_mem] at hc
            have hm := stratumPair_deleted_mul_mem ρ V Y u hVprod hu huY c hc
            apply Submodule.mem_sup_left
            rw [Submodule.restrictScalars_mem, zero_add, pow_one]
            refine (Ideal.span_le.mpr ?_) hm
            intro x hx
            rcases hx with rfl | hx
            · exact hZG
            · rw [Set.mem_singleton_iff] at hx
              rw [hx]
              exact G.mul_mem_left _ hcG
          · -- `u` at a simple point: the child stratum
            change c ∈ (Ideal.span {P, c'}).restrictScalars ℂ at hc
            rw [Submodule.restrictScalars_mem] at hc
            obtain ⟨α, β, rfl⟩ := Ideal.mem_span_pair.mp hc
            apply Submodule.mem_sup_left
            rw [Submodule.restrictScalars_mem]
            have heq : ρ u ^ (j + 1 + 1) * (α * P + β * c') =
                (ρ u ^ (j + 1) * α + ρ u ^ j * β * s) * ∏ i ∈ Yᶜ, ρ i +
                  (-(ρ u ^ (j + 1) * β)) * groupSubtopCoefficient ρ Yᶜ := by
              linear_combination (-(ρ u ^ (j + 1) * α + ρ u ^ j * β * s)) * hprodZ +
                (ρ u ^ (j + 1) * β) * hsub' + (ρ u ^ (j + 1) * β) * htop
            rw [heq]
            exact G.add_mem (G.mul_mem_left _ hZG) (G.mul_mem_left _ hcG)
        have hsum := layer_finrank_sum_le (ρ u) (B + 2) hcut (G.restrictScalars ℂ) W hW
        rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hsum
        refine le_trans ?_ hsum
        -- counts of the children
        have hV' : (deletedGroup u V).Nonempty := by
          rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
          exact Finset.card_pos.mpr hV
        have haV : (deletedGroup u V)ᶜ ∩ deletedGroup u Y = deletedGroup u (Vᶜ ∩ Y) := by
          rw [deletedGroup_inter, deletedGroup_compl]
        have hacard : (deletedGroup u (Vᶜ ∩ Y)).card = (Vᶜ ∩ Y).card :=
          deletedGroup_card_of_notMem _ u (fun h => huY (Finset.mem_inter.mp h).2)
        have hbV : (deletedGroup u V ∩ deletedGroup u Y).card = (V ∩ Y).card := by
          rw [← deletedGroup_inter]
          exact deletedGroup_card_of_notMem _ u (fun h => hu (Finset.mem_inter.mp h).1)
        have hcV : (deletedGroup u V \ deletedGroup u Y).card = (V \ Y).card := by
          rw [← deletedGroup_sdiff]
          exact deletedGroup_card_of_notMem _ u (fun h => hu (Finset.mem_sdiff.mp h).1)
        have hdV : ((deletedGroup u V)ᶜ \ deletedGroup u Y).card + 1 = (Vᶜ \ Y).card := by
          rw [← deletedGroup_compl, ← deletedGroup_sdiff]
          exact deletedGroup_card_of_mem _ u
            (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hu, huY⟩)
        have hchildCard2 : (Vᶜ ∩ Y).card + (V ∩ Y).card + (V \ Y).card +
            ((deletedGroup u V)ᶜ \ deletedGroup u Y).card ≤ B + 3 := by
          have h2 := Finset.card_compl (deletedGroup u V)
          have h3 := Finset.card_inter_add_card_sdiff (deletedGroup u V) (deletedGroup u Y)
          have h4 := Finset.card_inter_add_card_sdiff (deletedGroup u V)ᶜ (deletedGroup u Y)
          rw [Fintype.card_fin] at h2
          rw [haV, hacard] at h4
          rw [hbV, hcV] at h3
          have h5 := Finset.card_le_univ (deletedGroup u V)
          rw [Fintype.card_fin] at h5
          omega
        -- layer `0`: the weak stratum
        have h0 : (Vᶜ ∩ Y).card * (V ∩ Y).card * (B + 1).factorial +
            singlyMarkedOneDoubleCount 0 (V ∩ Y).card (V \ Y).card * B.factorial ≤
            Module.finrank ℂ ((W 0).map
              (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (ρ u) 0)).toLinearMap) := by
          have hws := weakMarkedFlag_stratum_finrank_ge (B + 1) (by omega) (deletedGroup u V)
            (deletedGroup u Y) hV'
          rw [haV, hacard, hbV, hcV, Nat.add_sub_cancel] at hws
          have hl := childProduct_finrank_le_layer ρ u 0 _ _
            (doublyMarkedLayerMap_injective_weak (B + 1) 1 le_rfl hk V hV u hu)
            (deletedGroup u Y)ᶜ
          exact hws.trans hl
        -- layer `1`: the singly marked stratum modulo the unmarked product
        have h1 : singlyMarkedMixedDoubleCount (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card *
            B.factorial ≤ Module.finrank ℂ ((W (0 + 1)).map
              (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (ρ u) (0 + 1))).toLinearMap) := by
          have hr3 := singlyMarkedProduct_stratum_finrank_ge (B + 1) (by omega)
            (deletedGroup u V) (deletedGroup u Y) hV'
          rw [haV, hacard, hbV, hcV, Nat.add_sub_cancel] at hr3
          have hl := stratumPair_finrank_le_layer ρ u 1 _ _
            (doublyMarkedLayerMap_injective_singlyProduct (B + 1) 1 le_rfl hk V hV u hu)
            (deletedGroup u V) (deletedGroup u Y)
          exact hr3.trans hl
        -- layers `j + 2`: the child stratum
        have hpos : ∀ j ∈ Finset.range B,
            doublyMarkedOneDoubleCount B (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card
                ((deletedGroup u V)ᶜ \ deletedGroup u Y).card * (B - 1).factorial ≤
              Module.finrank ℂ ((W (j + 1 + 1)).map
                (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (ρ u) (j + 1 + 1))).toLinearMap) := by
          intro j hj
          have hB : 1 ≤ B := by have := Finset.mem_range.mp hj; omega
          have hrec := ih hB (deletedGroup u V) (deletedGroup u Y)
          rw [haV, hacard, hbV, hcV] at hrec
          have hl := doublyStratum_finrank_le_layer ρ u (j + 1 + 1) _ _
            (doublyMarkedLayerMap_injective_lower (B + 1) 1 le_rfl hk V hV u hu (j + 1 + 1)
              (by omega) (by have := Finset.mem_range.mp hj; omega)) (deletedGroup u Y)
          exact hrec.trans hl
        have hx0 : B = 0 → doublyMarkedOneDoubleCount B (Vᶜ ∩ Y).card (V ∩ Y).card
            (V \ Y).card ((deletedGroup u V)ᶜ \ deletedGroup u Y).card = 0 := by
          intro hB
          rw [doublyMarkedOneDoubleCount, doublyMarkedResidualCount_eq_zero (Vᶜ ∩ Y).card
            (V ∩ Y).card (V \ Y).card ((deletedGroup u V)ᶜ \ deletedGroup u Y).card (by omega),
            Nat.choose_eq_zero_of_lt (show B + 1 < 2 by omega)]
          ring
        refine le_trans (le_of_eq ?_) (Nat.add_le_add (Nat.add_le_add
          (Finset.sum_le_sum hpos) h1) h0)
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul,
          factorial_mul_pred_of_zero B _ hx0,
          ← hdV, doublyMarkedOneDoubleCount, doublyMarkedOneDoubleCount,
          doublyMarkedResidualCount_succ,
          singlyMarkedOneDoubleCount_eq_add_mixed (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card,
          Nat.add_sub_cancel, Nat.factorial_succ, stratumChoose_two_succ (B + 1)]
        ring
      -- the three cases
      change doublyMarkedOneDoubleCount (B + 1) (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card
          (Vᶜ \ Y).card * (B + 1 - 1).factorial ≤
        Module.finrank ℂ ((doublyMarkedStratumIdeal
          (doublyMarkedFlagIdeal (B + 1 + 3) V (B + 1 + 1 - 1)) Y).restrictScalars ℂ)
      by_cases h1 : ∃ u, u ∉ V ∧ u ∉ Y
      · exact hmain V Y h1
      by_cases h2 : ∃ u, u ∈ V ∧ u ∉ Y
      · obtain ⟨u, huV, huY⟩ := h2
        have h := hmain Vᶜ Y ⟨u, fun h => (Finset.mem_compl.mp h) huV, huY⟩
        rw [doublyMarkedFlagIdeal_compl, compl_compl] at h
        refine le_trans (le_of_eq ?_) h
        rw [doublyMarkedOneDoubleCount_symm]
      · -- `Y` is everything: the whole ring
        obtain rfl : Y = Finset.univ := Finset.eq_univ_iff_forall.mpr fun u => by
          by_contra huY
          by_cases huV : u ∈ V
          · exact h2 ⟨u, huV, huY⟩
          · exact h1 ⟨u, huV, huY⟩
        have htopI : doublyMarkedStratumIdeal
            (doublyMarkedFlagIdeal (B + 1 + 3) V (B + 1 + 1 - 1)) Finset.univ = ⊤ := by
          apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
          have h : ∏ i ∈ (Finset.univ : Finset (Fin (B + 1 + 3)))ᶜ,
              quotientRoot (doublyMarkedFlagIdeal (B + 1 + 3) V (B + 1 + 1 - 1)) i ∈
            doublyMarkedStratumIdeal (doublyMarkedFlagIdeal (B + 1 + 3) V (B + 1 + 1 - 1))
              Finset.univ := Ideal.subset_span (Set.mem_insert _ _)
          rw [Finset.compl_univ, Finset.prod_empty] at h
          exact h
        rw [htopI, Submodule.restrictScalars_top, finrank_top]
        have hdim : Module.finrank ℂ (DoublyMarkedFlagRing (B + 1 + 3) V (B + 1 + 1 - 1)) =
            Vᶜ.card * V.card * Nat.card (FullFlagConfiguration (B + 1 + 1) 1) :=
          doublyMarkedFlag_finrank_eq (B + 1 + 1) 1 (by omega) V
        rw [hdim, Finset.inter_univ, Finset.inter_univ,
          Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ V),
          Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ Vᶜ), Finset.card_empty,
          ← choose_two_mul_factorial_eq_card (B + 1) (by omega)]
        apply le_of_eq
        simp only [doublyMarkedOneDoubleCount, doublyMarkedResidualCount]
        ring

/-! ### Two T-points -/

set_option maxHeartbeats 800000 in
-- The positive layers only, each through a layer isomorphism.
/-- **The doubly marked stratum with two T-points.** -/
theorem doublyMarkedFlag_twoDouble_stratum_finrank_ge (m : ℕ) (hm : 1 ≤ m)
    (V Y : Finset (Fin (m + 3))) :
    (Vᶜ ∩ Y).card * (V ∩ Y).card * ((Vᶜ ∩ Y).card + (V ∩ Y).card - 2).choose 2 *
        (m - 1).factorial ≤
      Module.finrank ℂ ((Ideal.span {(∏ i ∈ Yᶜ,
        quotientRoot (doublyMarkedFlagIdeal (m + 3) V m) i) ^ 2}).restrictScalars ℂ) := by
  classical
  induction m with
  | zero => omega
  | succ B ih =>
      have hk : 2 * 1 ≤ B + 1 + 1 := by omega
      have hmain : ∀ V Y : Finset (Fin (B + 1 + 3)), (∃ u, u ∉ V ∧ u ∉ Y) →
          (Vᶜ ∩ Y).card * (V ∩ Y).card * ((Vᶜ ∩ Y).card + (V ∩ Y).card - 2).choose 2 *
              (B + 1 - 1).factorial ≤
            Module.finrank ℂ ((Ideal.span {(∏ i ∈ Yᶜ, quotientRoot
              (doublyMarkedFlagIdeal (B + 1 + 3) V (B + 1 + 1 - 1)) i) ^ 2}).restrictScalars
                ℂ) := by
        intro V Y ⟨u, hu, huY⟩
        by_cases hVe : V = ∅
        · subst hVe
          simp
        have hV : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr hVe
        set ρ := quotientRoot (doublyMarkedFlagIdeal (B + 1 + 3) V (B + 1 + 1 - 1)) with hρ
        have hcut : ρ u ^ (B + 2) = 0 := doublyMarkedFlag_cutoff _ _ _ u
        have hY' : u ∈ Yᶜ := Finset.mem_compl.mpr huY
        have hprodZ : ∏ i ∈ Yᶜ, ρ i = ρ u * ∏ j ∈ (deletedGroup u Y)ᶜ, ρ (u.succAbove j) := by
          rw [prod_eq_mul_deletedGroup_of_mem ρ Yᶜ u hY', deletedGroup_compl]
        set P := ∏ j ∈ (deletedGroup u Y)ᶜ, ρ (u.succAbove j) with hP
        let W : ℕ → Submodule ℂ (DoublyMarkedFlagRing (B + 1 + 3) V (B + 1 + 1 - 1)) :=
          fun j => match j with
            | 0 => ⊥
            | 1 => ⊥
            | _ + 2 => (Ideal.span {P ^ 2}).restrictScalars ℂ
        have hW : ∀ j < B + 2, ∀ c ∈ W j, ρ u ^ j * c ∈
            (Ideal.span {(∏ i ∈ Yᶜ, ρ i) ^ 2}).restrictScalars ℂ ⊔
              (Ideal.span {ρ u ^ (j + 1)}).restrictScalars ℂ := by
          intro j _ c hc
          rcases j with _ | _ | j
          · rw [show c = 0 from (Submodule.mem_bot ℂ).mp hc, mul_zero]
            exact Submodule.zero_mem _
          · rw [show c = 0 from (Submodule.mem_bot ℂ).mp hc, mul_zero]
            exact Submodule.zero_mem _
          · change c ∈ (Ideal.span {P ^ 2}).restrictScalars ℂ at hc
            rw [Submodule.restrictScalars_mem] at hc
            obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hc
            apply Submodule.mem_sup_left
            rw [Submodule.restrictScalars_mem]
            have heq : ρ u ^ (j + 1 + 1) * (t * P ^ 2) = (ρ u ^ j * t) * (∏ i ∈ Yᶜ, ρ i) ^ 2 := by
              rw [hprodZ]
              ring
            rw [heq]
            exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
        have hsum := layer_finrank_sum_le (ρ u) (B + 2) hcut _ W hW
        rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hsum
        refine le_trans ?_ (le_trans (Nat.le_add_right _ _)
          (le_trans (Nat.le_add_right _ _) hsum))
        have hV' : (deletedGroup u V).Nonempty := by
          rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
          exact Finset.card_pos.mpr hV
        have haV : (deletedGroup u V)ᶜ ∩ deletedGroup u Y = deletedGroup u (Vᶜ ∩ Y) := by
          rw [deletedGroup_inter, deletedGroup_compl]
        have hacard : (deletedGroup u (Vᶜ ∩ Y)).card = (Vᶜ ∩ Y).card :=
          deletedGroup_card_of_notMem _ u (fun h => huY (Finset.mem_inter.mp h).2)
        have hbV : (deletedGroup u V ∩ deletedGroup u Y).card = (V ∩ Y).card := by
          rw [← deletedGroup_inter]
          exact deletedGroup_card_of_notMem _ u (fun h => hu (Finset.mem_inter.mp h).1)
        have hYcard : (Vᶜ ∩ Y).card + (V ∩ Y).card ≤ B + 3 := by
          have h1 := compl_inter_card_add_inter_card V Y
          have hsub : Y ⊆ Finset.univ.erase u := fun x hx =>
            Finset.mem_erase.mpr ⟨fun h => huY (h ▸ hx), Finset.mem_univ x⟩
          have := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
            Fintype.card_fin] at this
          omega
        have hpos : ∀ j ∈ Finset.range B,
            (Vᶜ ∩ Y).card * (V ∩ Y).card * ((Vᶜ ∩ Y).card + (V ∩ Y).card - 2).choose 2 *
                (B - 1).factorial ≤
              Module.finrank ℂ ((W (j + 1 + 1)).map
                (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (ρ u) (j + 1 + 1))).toLinearMap) := by
          intro j hj
          have hB : 1 ≤ B := by have := Finset.mem_range.mp hj; omega
          have hrec := ih hB (deletedGroup u V) (deletedGroup u Y)
          rw [haV, hacard, hbV] at hrec
          have hl := childSingleton_finrank_le_layer ρ u (j + 1 + 1) _ _
            (doublyMarkedLayerMap_injective_lower (B + 1) 1 le_rfl hk V hV u hu (j + 1 + 1)
              (by omega) (by have := Finset.mem_range.mp hj; omega))
            ((∏ i ∈ (deletedGroup u Y)ᶜ, X i) ^ 2)
          rw [aeval_prod_sq, mk_prod_sq] at hl
          exact hrec.trans hl
        have hx0 : B = 0 → (Vᶜ ∩ Y).card * (V ∩ Y).card *
            ((Vᶜ ∩ Y).card + (V ∩ Y).card - 2).choose 2 = 0 := by
          intro hB
          rw [Nat.choose_eq_zero_of_lt
            (show (Vᶜ ∩ Y).card + (V ∩ Y).card - 2 < 2 by omega), mul_zero]
        refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hpos)
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul,
          factorial_mul_pred_of_zero B _ hx0, Nat.add_sub_cancel]
      change (Vᶜ ∩ Y).card * (V ∩ Y).card * ((Vᶜ ∩ Y).card + (V ∩ Y).card - 2).choose 2 *
          (B + 1 - 1).factorial ≤
        Module.finrank ℂ ((Ideal.span {(∏ i ∈ Yᶜ, quotientRoot
          (doublyMarkedFlagIdeal (B + 1 + 3) V (B + 1 + 1 - 1)) i) ^ 2}).restrictScalars ℂ)
      by_cases h1 : ∃ u, u ∉ V ∧ u ∉ Y
      · exact hmain V Y h1
      by_cases h2 : ∃ u, u ∈ V ∧ u ∉ Y
      · obtain ⟨u, huV, huY⟩ := h2
        have h := hmain Vᶜ Y ⟨u, fun h => (Finset.mem_compl.mp h) huV, huY⟩
        rw [doublyMarkedFlagIdeal_compl, compl_compl] at h
        refine le_trans (le_of_eq ?_) h
        rw [Nat.add_comm (V ∩ Y).card (Vᶜ ∩ Y).card]
        ring
      · obtain rfl : Y = Finset.univ := Finset.eq_univ_iff_forall.mpr fun u => by
          by_contra huY
          by_cases huV : u ∈ V
          · exact h2 ⟨u, huV, huY⟩
          · exact h1 ⟨u, huV, huY⟩
        rw [Ideal.span_singleton_eq_top.mpr ?_, Submodule.restrictScalars_top, finrank_top]
        swap
        · apply IsUnit.pow
          rw [Finset.prod_eq_one (fun i hi => absurd (Finset.mem_univ i)
            (Finset.mem_compl.mp hi))]
          exact isUnit_one
        have hdim : Module.finrank ℂ (DoublyMarkedFlagRing (B + 1 + 3) V (B + 1 + 1 - 1)) =
            Vᶜ.card * V.card * Nat.card (FullFlagConfiguration (B + 1 + 1) 1) :=
          doublyMarkedFlag_finrank_eq (B + 1 + 1) 1 (by omega) V
        have hpq : Vᶜ.card + V.card = B + 1 + 3 := by
          rw [Finset.card_compl, Fintype.card_fin]
          have := Finset.card_le_univ V
          rw [Fintype.card_fin] at this
          omega
        rw [hdim, Finset.inter_univ, Finset.inter_univ, hpq,
          show B + 1 + 3 - 2 = B + 1 + 1 by omega, mul_assoc,
          choose_two_mul_factorial_eq_card (B + 1) (by omega)]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlagIdeal_compl_le
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlagIdeal_compl
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedStratumIdeal
#print axioms VOA.DeligneAudit.SL4T.doublyStratum_finrank_le_layer
#print axioms VOA.DeligneAudit.SL4T.childSingleton_finrank_le_layer
#print axioms VOA.DeligneAudit.SL4T.aeval_prod_sq
#print axioms VOA.DeligneAudit.SL4T.mk_prod_sq
#print axioms VOA.DeligneAudit.SL4T.groupSubtopCoefficient_eq_one_of_deleted_empty
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedResidualCount
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedOneDoubleCount
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedResidualCount_succ
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedResidualCount_eq_zero
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedOneDoubleCount_symm
#print axioms VOA.DeligneAudit.SL4T.choose_two_mul_factorial_eq_card
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_oneDouble_stratum_finrank_ge
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_twoDouble_stratum_finrank_ge
