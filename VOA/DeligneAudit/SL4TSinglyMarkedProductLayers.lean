import VOA.DeligneAudit.SL4TWeakMarkedFlagStratum

/-!
# The singly marked full flag modulo the product of its unmarked roots: exact layers

Let `S` be the singly marked full flag on `m + 2` roots with one double (cutoff `m` on `U = Vᶜ`,
`m + 1` on `V`) and `π = ∏ U`. The quotient `S/πS` is presented by `singlyMarkedProductIdeal`;
it is the layer of the doubly marked flag where a first-group root sits at zero.

* Its dimension: `dim S/πS + q C(q - 1, 2) (m - 1)! = q (m + 1)!/2`, `q = |V|`
  (`singlyMarkedProduct_finrank_add`); `dim πS` is the number of configurations whose double
  point carries two marked roots.
* For a root `w ∈ U`, the layers of `w` in `S/πS` are: the singly marked flag without doubles
  (layer `0`), and `S'/π'S'` for the singly marked flag `S'` with one root fewer and cutoff lowered
  by one (layers `i ≥ 1`), because `w^i π' = w^(i-1) π = 0`. The bounds add up to the dimension,
  so every layer map is an isomorphism (`singlyProductLayerMap_injective_zero`,
  `singlyProductLayerMap_injective_lower`). This is fact (F6) of the note.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-- The singly marked ideal together with the product of the unmarked roots. -/
def singlyMarkedProductIdeal (n : ℕ) (V : Finset (Fin n)) (h : ℕ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  singlyMarkedFlagIdeal n V h ⊔ Ideal.span {flagGroupProduct Vᶜ}

/-- The singly marked ring modulo the product of the unmarked roots. -/
abbrev SinglyMarkedProductRing (n : ℕ) (V : Finset (Fin n)) (h : ℕ) :=
  MvPolynomial (Fin n) ℂ ⧸ singlyMarkedProductIdeal n V h

instance singlyMarkedProduct_finite (n : ℕ) (V : Finset (Fin n)) (h : ℕ) :
    FiniteDimensional ℂ (MvPolynomial (Fin n) ℂ ⧸ singlyMarkedProductIdeal n V h) :=
  Module.Finite.of_surjective (Ideal.Quotient.factorₐ ℂ le_sup_left).toLinearMap
    (Ideal.Quotient.factor_surjective le_sup_left)

/-- The projection from the singly marked ring. -/
def singlyMarkedProductFactor (n : ℕ) (V : Finset (Fin n)) (h : ℕ) :
    SinglyMarkedFlagRing n V h →ₐ[ℂ] SinglyMarkedProductRing n V h :=
  Ideal.Quotient.factorₐ ℂ le_sup_left

section Roots

variable (n : ℕ) (V : Finset (Fin n)) (h : ℕ)

theorem singlyMarkedProductFactor_root (j : Fin n) :
    singlyMarkedProductFactor n V h (quotientRoot (singlyMarkedFlagIdeal n V h) j) =
      quotientRoot (singlyMarkedProductIdeal n V h) j :=
  rfl

theorem singlyMarkedProduct_product_zero :
    ∏ i ∈ V, quotientRoot (singlyMarkedProductIdeal n V h) i = 0 := by
  have h0 := congrArg (singlyMarkedProductFactor n V h) (singlyMarkedFlag_product_zero n V h)
  rwa [map_prod, map_zero] at h0

theorem singlyMarkedProduct_compl_product_zero :
    ∏ i ∈ Vᶜ, quotientRoot (singlyMarkedProductIdeal n V h) i = 0 := by
  rw [show (∏ i ∈ Vᶜ, quotientRoot (singlyMarkedProductIdeal n V h) i) =
    Ideal.Quotient.mk _ (flagGroupProduct Vᶜ) by simp [flagGroupProduct, quotientRoot]]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((le_sup_right :
    Ideal.span {flagGroupProduct Vᶜ} ≤ singlyMarkedProductIdeal n V h) (Ideal.subset_span rfl))

theorem singlyMarkedProduct_unmarked_cutoff (i : Fin n) (hi : i ∉ V) :
    quotientRoot (singlyMarkedProductIdeal n V h) i ^ h = 0 := by
  have h0 := congrArg (singlyMarkedProductFactor n V h)
    (singlyMarkedFlag_unmarked_cutoff n V h i hi)
  rwa [map_pow, map_zero] at h0

end Roots

/-- Layer relations pass to a quotient: if a child ideal vanishes in a layer of `r u`, it
vanishes in the corresponding layer of the image of `r` under an algebra homomorphism. -/
theorem deletedLayer_le_ker_map {C D : Type*} [CommRing C] [Algebra ℂ C] [CommRing D]
    [Algebra ℂ D] {n : ℕ} (q : C →ₐ[ℂ] D) (r : Fin (n + 1) → C) (ρ : Fin (n + 1) → D)
    (hρ : ∀ j, q (r j) = ρ j) (u : Fin (n + 1)) (i : ℕ) (I' : Ideal (MvPolynomial (Fin n) ℂ))
    (hI' : I' ≤ RingHom.ker (aeval (deletedLayerRoot r u i)).toRingHom) :
    I' ≤ RingHom.ker (aeval (deletedLayerRoot ρ u i)).toRingHom := by
  obtain rfl : ρ = fun j => q (r j) := funext fun j => (hρ j).symm
  intro p hp
  have h : aeval (deletedLayerRoot r u i) p = 0 := RingHom.mem_ker.mp (hI' hp)
  apply RingHom.mem_ker.mpr
  change aeval (deletedLayerRoot (fun j => q (r j)) u i) p = 0
  rw [aeval_deletedLayerRoot] at h ⊢
  rw [Ideal.Quotient.eq_zero_iff_mem, rootPowerLayerIdeal_mem] at h ⊢
  have hq := AlgHom.congr_fun (MvPolynomial.comp_aeval (R := ℂ) (fun j => r (u.succAbove j)) q) p
  rw [AlgHom.comp_apply] at hq
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨q a, ?_⟩
  have h2 := congrArg q ha
  rw [map_mul, map_mul, map_pow, map_pow, hq] at h2
  exact h2

/-! ### Layer relations -/

section LayerRelations

variable (n : ℕ) (V : Finset (Fin (n + 1))) (h : ℕ) (u : Fin (n + 1)) (hu : u ∉ V)
include hu

theorem singlyProductLayer_same_le_ker (i : ℕ) :
    singlyMarkedFlagIdeal n (deletedGroup u V) h ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (singlyMarkedProductIdeal (n + 1) V h)) u i)).toRingHom :=
  deletedLayer_le_ker_map (singlyMarkedProductFactor (n + 1) V h) _ _
    (singlyMarkedProductFactor_root (n + 1) V h) u i _
    (singlyMarkedLayer_same_le_ker n V h u hu i)

theorem singlyProductLayer_lower_le_ker (k : ℕ) (hn : n = h + k) (hh : 1 ≤ h) (i : ℕ)
    (hi : k ≤ i) (hi1 : 1 ≤ i) :
    singlyMarkedProductIdeal n (deletedGroup u V) (h - 1) ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (singlyMarkedProductIdeal (n + 1) V h)) u i)).toRingHom := by
  set ρ := quotientRoot (singlyMarkedProductIdeal (n + 1) V h) with hρ
  refine sup_le (deletedLayer_le_ker_map (singlyMarkedProductFactor (n + 1) V h) _ _
    (singlyMarkedProductFactor_root (n + 1) V h) u i _
    (singlyMarkedLayer_lower_le_ker n V h k hn hh u hu i hi)) ?_
  apply Ideal.span_le.mpr
  rintro p rfl
  change aeval (deletedLayerRoot ρ u i) (flagGroupProduct (deletedGroup u V)ᶜ) = 0
  have h0 := layer_mk_eq_zero ρ u i _
    (deletedComplProduct_mem ρ V u hu (singlyMarkedProduct_compl_product_zero _ _ _) i hi1)
  simpa [flagGroupProduct, deletedLayerRoot, map_prod] using h0

end LayerRelations

/-! ### The dimension -/

/-- `dim S/πS + q C(q - 1, 2) (m - 1)! = q (m + 1)!/2`. -/
theorem singlyMarkedProduct_finrank_add (m : ℕ) (hm : 1 ≤ m) (V : Finset (Fin (m + 2)))
    (hV : V.Nonempty) :
    Module.finrank ℂ (SinglyMarkedProductRing (m + 2) V m) +
        V.card * (V.card - 1).choose 2 * (m - 1).factorial =
      V.card * Nat.card (FullFlagConfiguration (m + 1) 1) := by
  classical
  set W := V.map (Fin.succEmb (m + 2)) with hW
  have hW0 : (0 : Fin (m + 3)) ∉ W := by
    rw [hW, Finset.mem_map]
    rintro ⟨a, _, ha⟩
    exact Fin.succ_ne_zero a ha
  have hWne : W.Nonempty := hV.map
  have hdel : deletedGroup 0 W = V := deletedGroup_zero_map_succ V
  have hcard : W.card = V.card := Finset.card_map _
  have hprod := (doublyMarkedLayer_childProduct_finrank_eq m 1 le_rfl (by omega) W hWne 0
    hW0).1
  rw [hdel, hcard, show m + 1 - 1 = m by omega, show (1 : ℕ) - 1 = 0 from rfl] at hprod
  have hc0 := fullFlagConfiguration_card_closed (m - 1) 0 (by omega)
  rw [pow_zero, one_mul] at hc0
  rw [hc0] at hprod
  have hsplit := quotient_sup_span_finrank (singlyMarkedFlagIdeal (m + 2) V m)
    (flagGroupProduct Vᶜ)
  have hπS : Ideal.Quotient.mk (singlyMarkedFlagIdeal (m + 2) V m) (flagGroupProduct Vᶜ) =
      ∏ j ∈ Vᶜ, quotientRoot (singlyMarkedFlagIdeal (m + 2) V m) j := by
    simp [flagGroupProduct, quotientRoot]
  rw [hπS, hprod] at hsplit
  have hS := singlyMarkedFlag_finrank_eq (m + 1) 1 (by omega) V hV
  exact hsplit.trans hS

/-! ### Exact layers -/

section Layers

variable (m : ℕ) (V : Finset (Fin (m + 3))) (hV : V.Nonempty) (w : Fin (m + 3)) (hw : w ∉ V)
include hV hw

/-- Every layer bound of a first-group root of `S/πS` is attained. -/
theorem singlyProductLayer_finrank_eq (i : ℕ) (hi : i < m + 1) :
    Module.finrank ℂ (SinglyMarkedProductRing (m + 3) V (m + 1) ⧸ rootPowerLayerIdeal
        (quotientRoot (singlyMarkedProductIdeal (m + 3) V (m + 1)) w) i) =
      if i = 0 then Module.finrank ℂ (SinglyMarkedFlagRing (m + 2) (deletedGroup w V) (m + 1))
      else Module.finrank ℂ (SinglyMarkedProductRing (m + 2) (deletedGroup w V) m) := by
  classical
  set ρ := quotientRoot (singlyMarkedProductIdeal (m + 3) V (m + 1)) with hρ
  have hV' : (deletedGroup w V).Nonempty := by
    rw [← Finset.card_pos, deletedGroup_card_of_notMem V w hw]
    exact Finset.card_pos.mpr hV
  have hq := deletedGroup_card_of_notMem V w hw
  have hcut : ρ w ^ (m + 1) = 0 := singlyMarkedProduct_unmarked_cutoff _ _ _ w hw
  let a : ℕ → ℕ := fun j => Module.finrank ℂ (SinglyMarkedProductRing (m + 3) V (m + 1) ⧸
    rootPowerLayerIdeal (ρ w) j)
  let b : ℕ → ℕ := fun j => if j = 0 then
    Module.finrank ℂ (SinglyMarkedFlagRing (m + 2) (deletedGroup w V) (m + 1))
    else Module.finrank ℂ (SinglyMarkedProductRing (m + 2) (deletedGroup w V) m)
  have hab : ∀ j ∈ Finset.range (m + 1), a j ≤ b j := by
    intro j hj
    simp only [a, b]
    split_ifs with hj0
    · subst hj0
      exact deletedLayer_finrank_le ρ (quotientRoot_aeval_surjective _) w 0 _
        (singlyProductLayer_same_le_ker (m + 2) V (m + 1) w hw 0)
    · exact deletedLayer_finrank_le ρ (quotientRoot_aeval_surjective _) w j _
        (singlyProductLayer_lower_le_ker (m + 2) V (m + 1) w hw 1 (by omega) (by omega) j
          (by omega) (by omega))
  have hsum : ∑ j ∈ Finset.range (m + 1), a j = ∑ j ∈ Finset.range (m + 1), b j := by
    simp only [a]
    rw [← rootPowerFiltration_finrank (ρ w) (m + 1) hcut, Finset.sum_range_succ']
    simp only [b, Nat.add_one_ne_zero, ↓reduceIte, Finset.sum_const, Finset.card_range,
      smul_eq_mul]
    have hS := singlyMarkedFlag_finrank_eq (m + 1) 0 (by omega) (deletedGroup w V) hV'
    rw [hq, Nat.sub_zero] at hS
    have hD := singlyMarkedProduct_finrank_add (m + 1) (by omega) V hV
    have hrec := fullFlagConfiguration_card_recursion (m + 1) 1 (by omega)
    rw [show m + 1 + 1 - 1 - 1 = m by omega, show (1 : ℕ) - 1 = 0 from rfl] at hrec
    change Module.finrank ℂ (SinglyMarkedProductRing (m + 3) V (m + 1)) =
      m * Module.finrank ℂ (SinglyMarkedProductRing (m + 2) (deletedGroup w V) m) +
        Module.finrank ℂ (SinglyMarkedFlagRing (m + 2) (deletedGroup w V) (m + 1))
    have hS' : Module.finrank ℂ (SinglyMarkedFlagRing (m + 2) (deletedGroup w V) (m + 1)) =
        V.card * Nat.card (FullFlagConfiguration (m + 1) 0) := hS
    have hD' : Module.finrank ℂ (SinglyMarkedProductRing (m + 3) V (m + 1)) +
        V.card * (V.card - 1).choose 2 * m.factorial =
          V.card * Nat.card (FullFlagConfiguration (m + 1 + 1) 1) := hD
    rw [hS']
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · -- one simple point: the product ideal vanishes for lack of room
      subst hm0
      have hq2 : V.card ≤ 2 := by
        have hsub : V ⊆ Finset.univ.erase w := fun x hx =>
          Finset.mem_erase.mpr ⟨fun h => hw (h ▸ hx), Finset.mem_univ x⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ,
          Fintype.card_fin] at this
        omega
      rw [Nat.choose_eq_zero_of_lt (by omega : V.card - 1 < 2), mul_zero, zero_mul,
        add_zero] at hD'
      rw [hD', hrec]
      ring
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hD2 := singlyMarkedProduct_finrank_add (m' + 1) (by omega) (deletedGroup w V) hV'
      rw [hq, Nat.add_sub_cancel] at hD2
      have hfac : (m' + 1).factorial = (m' + 1) * m'.factorial := Nat.factorial_succ m'
      zify at hD' hD2 hrec hfac ⊢
      linear_combination hD' - (↑m' + 1) * hD2 + (↑V.card : ℤ) * hrec -
        (↑V.card : ℤ) * ↑((V.card - 1).choose 2) * hfac
  exact ((Finset.sum_eq_sum_iff_of_le hab).mp hsum) i (Finset.mem_range.mpr hi)

theorem singlyProductLayerMap_injective_zero :
    Function.Injective (deletedLayerMap
      (quotientRoot (singlyMarkedProductIdeal (m + 3) V (m + 1))) w 0 _
      (singlyProductLayer_same_le_ker (m + 2) V (m + 1) w hw 0)) := by
  apply deletedLayerMap_injective_of_finrank_le _ (quotientRoot_aeval_surjective _)
  rw [singlyProductLayer_finrank_eq m V hV w hw 0 (by omega), if_pos rfl]

theorem singlyProductLayerMap_injective_lower (i : ℕ) (hi1 : 1 ≤ i) (hi : i < m + 1) :
    Function.Injective (deletedLayerMap
      (quotientRoot (singlyMarkedProductIdeal (m + 3) V (m + 1))) w i _
      (singlyProductLayer_lower_le_ker (m + 2) V (m + 1) w hw 1 (by omega) (by omega) i hi1
        hi1)) := by
  apply deletedLayerMap_injective_of_finrank_le _ (quotientRoot_aeval_surjective _)
  rw [singlyProductLayer_finrank_eq m V hV w hw i hi, if_neg (by omega)]
  all_goals exact le_rfl

end Layers

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProductIdeal
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProduct_finite
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProductFactor
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProductFactor_root
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProduct_product_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProduct_compl_product_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProduct_unmarked_cutoff
#print axioms VOA.DeligneAudit.SL4T.deletedLayer_le_ker_map
#print axioms VOA.DeligneAudit.SL4T.singlyProductLayer_same_le_ker
#print axioms VOA.DeligneAudit.SL4T.singlyProductLayer_lower_le_ker
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProduct_finrank_add
#print axioms VOA.DeligneAudit.SL4T.singlyProductLayer_finrank_eq
#print axioms VOA.DeligneAudit.SL4T.singlyProductLayerMap_injective_zero
#print axioms VOA.DeligneAudit.SL4T.singlyProductLayerMap_injective_lower
