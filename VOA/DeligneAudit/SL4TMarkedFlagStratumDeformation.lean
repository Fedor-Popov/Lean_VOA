import VOA.DeligneAudit.SL4TMarkedFlagConfigurationCount

/-!
# The deformation of the marked full-flag strata and their exact point algebras

The subject is the deformation lower bound `dim C/G_j ≥ #X_{<j}`.

A configuration of a marked full flag has a *selected double* at every point carrying two roots of
the selected set `Y` (`singlyMarkedSelectedDoubles`, `doublyMarkedSelectedDoubles`). Deform the
remainder columns `t^(h+1+c)` modulo `P_Y = ∏_Y (t - x)` to `t^c · t ∏_a (t - ζ_a)`: at a
configuration point, `P_Y` and `t ∏ (t - ζ_a)` share the factor `t^[zero point occupied in Y] ·
∏ (t - ζ)` over the occupied sites of `Y`, of degree `|Y|` minus the number of selected doubles.
Hence every top-row `j`-minor of these columns is the top homogeneous part of a polynomial
vanishing at all configurations with fewer than `j` selected doubles
(`singlyMarked_remainderTopIdeal_le`, `doublyMarked_remainderTopIdeal_le`). For the singly
marked flag the columns `s t^(h+c)`, `s = ∏ (V ∩ Y)`, are deformed by `∏ (t - ζ_a)` alone;
the factor `s` vanishes when the zero root is selected
(`singlyMarked_markedRemainderMinor_mem`).

In the quotient by the leading relations these minors vanish, and the complement forms of the
stratum ideals turn this into the vanishing of their explicit generators `∏ Z`, `s · c(Z)`
(singly marked, `j = 1`), `∏ Z`, `c(Z)` (doubly marked, `j = 1`) and `(∏ Z)²` (doubly marked,
`j = 2`).
So the stratum quotient surjects onto the graded point algebra of the configurations with fewer
than `j` selected doubles. Together with the exact dimensions of the marked flags, the lower
bounds for the stratum ideals and the configuration counts of `SL4TMarkedFlagConfigurationCount`,
the surjection is an isomorphism: the polynomial stratum ideal **equals** the leading-relation
ideal of those configurations (`singlyMarkedSelectedStratumIdeal_eq`,
`doublyMarkedOneSelectedStratumIdeal_eq`, `doublyMarkedTwoSelectedStratumIdeal_eq`), and the
stratum quotient has dimension exactly the number of those configurations.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-! ### Leading relations from deformed minors -/

/-- Leading relations shrink when the point set is restricted. -/
theorem pointInitialIdeal_le_comp {ι ι' σ : Type*} (x : ι → σ → ℂ) (e : ι' → ι) :
    pointInitialIdeal x ≤ pointInitialIdeal (fun i => x (e i)) := by
  rw [pointInitialIdeal_eq_span_vanishing x, pointInitialIdeal_eq_span_vanishing]
  apply Ideal.span_mono
  rintro p ⟨q, n, hq, hd, rfl⟩
  refine ⟨q, n, ?_, hd, rfl⟩
  funext i
  exact congrFun hq (e i)

/-- A deformed remainder minor vanishing at every point puts the remainder minor among the
leading relations. -/
theorem remainderRowMinor_mem_pointInitialIdeal {ι σ : Type*} (x : ι → σ → ℂ)
    (xs : List (MvPolynomial σ ℂ))
    (hxs : ∀ y ∈ xs, y.IsWeightedHomogeneous (fun _ => (1 : ℤ)) 1)
    (N j : ℕ) (q : Polynomial ℂ) (hq : q.coeff N = 1) (rows cols : Fin j → ℕ)
    (hvanish : ∀ i, aeval (x i) (deformedRemainderMinor xs N j q rows cols) = 0) :
    remainderRowMinor xs N j rows cols ∈ pointInitialIdeal x := by
  let d := remainderMinorDegree N j rows cols
  have hhom := remainderRowMinor_homogeneous (fun _ => (1 : ℤ)) xs hxs N j rows cols
  by_cases hd : d < 0
  · rw [integerHomogeneous_eq_zero _ d hhom hd]
    exact Ideal.zero_mem _
  · have he : d = (d.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    obtain ⟨hdegree, htop⟩ := deformedRemainderMinor_top xs hxs N j q hq rows cols d.toNat he
    rw [← htop]
    apply pointInitialIdeal_of_vanishing _ _ _ _ hdegree
    funext i
    exact hvanish i

/-- The same with a homogeneous factor in front, when the product vanishes at every point. -/
theorem mul_remainderRowMinor_mem_pointInitialIdeal {ι σ : Type*} (x : ι → σ → ℂ)
    (xs : List (MvPolynomial σ ℂ))
    (hxs : ∀ y ∈ xs, y.IsWeightedHomogeneous (fun _ => (1 : ℤ)) 1)
    (N j : ℕ) (q : Polynomial ℂ) (hq : q.coeff N = 1) (rows cols : Fin j → ℕ)
    (s : MvPolynomial σ ℂ) (b : ℕ) (hs : s.IsHomogeneous b)
    (hvanish : ∀ i, aeval (x i) s * aeval (x i) (deformedRemainderMinor xs N j q rows cols) = 0) :
    s * remainderRowMinor xs N j rows cols ∈ pointInitialIdeal x := by
  let d := remainderMinorDegree N j rows cols
  have hhom := remainderRowMinor_homogeneous (fun _ => (1 : ℤ)) xs hxs N j rows cols
  by_cases hd : d < 0
  · rw [integerHomogeneous_eq_zero _ d hhom hd, mul_zero]
    exact Ideal.zero_mem _
  · have he : d = (d.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    obtain ⟨hdegree, htop⟩ := deformedRemainderMinor_top xs hxs N j q hq rows cols d.toNat he
    have hcomp := homogeneousComponent_mul_top s (deformedRemainderMinor xs N j q rows cols) b
      d.toNat hs.totalDegree_le hdegree
    rw [homogeneousComponent_of_mem hs, if_pos rfl, htop] at hcomp
    rw [← hcomp]
    apply pointInitialIdeal_of_vanishing _ _ _ _
      ((totalDegree_mul _ _).trans (add_le_add hs.totalDegree_le hdegree))
    funext i
    change aeval (x i) (s * _) = 0
    rw [map_mul]
    exact hvanish i

/-- The selected characteristic polynomial at a point is the product of its root factors. -/
theorem alphabetCharacteristic_evaluate_points {n : ℕ} (Y : Finset (Fin n)) (z : Fin n → ℂ) :
    alphabetCharacteristic ((fullFlagSubalphabet Y).map (aeval z)) =
      ∏ i ∈ Y, (Polynomial.X - Polynomial.C (z i)) := by
  classical
  simp only [fullFlagSubalphabet, List.map_map, Function.comp_def, MvPolynomial.aeval_X,
    alphabetCharacteristic_product, List.map_map]
  simpa only [Finset.toList_toFinset] using
    (List.prod_toFinset (fun i => Polynomial.X - Polynomial.C (z i))
      (Finset.nodup_toList Y)).symm

/-- The product of root factors of a deleted subalphabet at an unmarked configuration. -/
theorem selectedSitePolynomial_dvd_product (B k : ℕ) (Y : Finset (Fin B))
    (f : FullFlagConfiguration B k) (ζ : Fin (B - k) → ℂ) :
    selectedSitePolynomial B k Y f ζ ∣
      ∏ i ∈ Y, (Polynomial.X - Polynomial.C (ζ (f.val i))) := by
  have h := selectedSitePolynomial_dvd_characteristic B k Y f ζ
  rwa [selectedAlphabetCharacteristic_evaluate] at h

/-- At a singly marked point the selected root factors split off the zero root. -/
theorem singlyMarkedPoint_characteristic (B k : ℕ) (V Y : Finset (Fin (B + 1)))
    (ζ : Fin (B - k) → ℂ) (c : SinglyMarkedConfiguration B k V) :
    ∏ i ∈ Y, (Polynomial.X - Polynomial.C (singlyMarkedPoint B k V ζ c i)) =
      (if c.1.val ∈ Y then Polynomial.X else 1) *
        ∏ j ∈ deletedGroup c.1.val Y, (Polynomial.X - Polynomial.C (ζ (c.2.val j))) := by
  rw [prod_eq_deletedGroup _ Y c.1.val]
  simp only [singlyMarkedPoint, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    map_zero, sub_zero]

/-- At a doubly marked point the selected root factors split off the zero pair. -/
theorem doublyMarkedPoint_characteristic (B k : ℕ) (V Y : Finset (Fin (B + 2)))
    (ζ : Fin (B - k) → ℂ) (c : DoublyMarkedConfiguration B k V) :
    ∏ i ∈ Y, (Polynomial.X - Polynomial.C (doublyMarkedPoint B k V ζ c i)) =
      (if c.1.val ∈ Y then Polynomial.X else 1) *
        ((if c.2.1.val ∈ deletedGroup c.1.val Y then Polynomial.X else 1) *
          ∏ j ∈ deletedGroup c.2.1.val (deletedGroup c.1.val Y),
            (Polynomial.X - Polynomial.C (ζ (c.2.2.val j)))) := by
  rw [prod_eq_deletedGroup _ Y c.1.val]
  simp only [doublyMarkedPoint, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    map_zero, sub_zero]
  rw [singlyMarkedPoint_characteristic]

/-- The cutoff polynomial `t ∏ (t - ζ_a)` is monic of degree `h + 1`. -/
theorem zeroSitePolynomial_coeff (h : ℕ) (ζ : Fin h → ℂ) :
    (Polynomial.X * alphabetCharacteristic (List.ofFn ζ)).coeff (h + 1) = 1 := by
  rw [Polynomial.coeff_X_mul]
  have hn : (alphabetCharacteristic (List.ofFn ζ)).natDegree = h := by
    rw [alphabetCharacteristic_natDegree, List.length_ofFn]
  have h1 := (alphabetCharacteristic_monic (List.ofFn ζ)).coeff_natDegree
  rwa [hn] at h1

theorem zeroSitePolynomial_natDegree_le (h : ℕ) (ζ : Fin h → ℂ) :
    (Polynomial.X * alphabetCharacteristic (List.ofFn ζ)).natDegree ≤ h + 1 := by
  refine Polynomial.natDegree_mul_le.trans ?_
  have := alphabetCharacteristic_natDegree_le (List.ofFn ζ)
  rw [List.length_ofFn] at this
  rw [Polynomial.natDegree_X]
  omega

theorem sitePolynomial_coeff (h : ℕ) (ζ : Fin h → ℂ) :
    (alphabetCharacteristic (List.ofFn ζ)).coeff h = 1 := by
  have hn : (alphabetCharacteristic (List.ofFn ζ)).natDegree = h := by
    rw [alphabetCharacteristic_natDegree, List.length_ofFn]
  have h1 := (alphabetCharacteristic_monic (List.ofFn ζ)).coeff_natDegree
  rwa [hn] at h1

theorem sitePolynomial_natDegree_le (h : ℕ) (ζ : Fin h → ℂ) :
    (alphabetCharacteristic (List.ofFn ζ)).natDegree ≤ h := by
  have := alphabetCharacteristic_natDegree_le (List.ofFn ζ)
  rwa [List.length_ofFn] at this

/-- `t^[selected]` is monic, of degree `[selected]`, and divides `t`. -/
theorem selectedZeroFactor (P : Prop) [Decidable P] :
    (if P then (Polynomial.X : Polynomial ℂ) else 1).Monic ∧
      (if P then (Polynomial.X : Polynomial ℂ) else 1).natDegree = (if P then 1 else 0) ∧
        (if P then (Polynomial.X : Polynomial ℂ) else 1) ∣ Polynomial.X := by
  by_cases hP : P <;> simp [hP, Polynomial.monic_X]

/-- `t^[P ∨ Q]` divides `t^[P] t^[Q]`. -/
theorem selectedZeroFactor_dvd (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∨ Q then (Polynomial.X : Polynomial ℂ) else 1) ∣
      (if P then Polynomial.X else 1) * (if Q then Polynomial.X else 1) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-! ### Vanishing of the deformed minors -/

/-- **Singly marked deformation.** The deformed `j`-minors of the columns `t^(h+1+c)` vanish at
every singly marked configuration with fewer than `j` selected doubles. -/
theorem singlyMarked_deformedMinor_zero (B k j : ℕ) (V Y : Finset (Fin (B + 1)))
    (ζ : Fin (B - k) → ℂ) (rows cols : Fin j → ℕ) (c : SinglyMarkedConfiguration B k V)
    (hc : singlyMarkedSelectedDoubles Y c < j) :
    aeval (singlyMarkedPoint B k V ζ c) (deformedRemainderMinor (fullFlagSubalphabet Y)
      (B - k + 1) j (Polynomial.X * alphabetCharacteristic (List.ofFn ζ)) rows cols) = 0 := by
  classical
  rw [deformedRemainderMinor_evaluate _ _ _ _ (zeroSitePolynomial_natDegree_le _ ζ)]
  obtain ⟨he_monic, he_deg, he_dvd⟩ := selectedZeroFactor (c.1.val ∈ Y)
  have hsel := selectedSitePolynomial_monic B k (deletedGroup c.1.val Y) c.2 ζ
  apply scalarRemainderMinor_eq_zero _ _
    ((if c.1.val ∈ Y then Polynomial.X else 1) *
      selectedSitePolynomial B k (deletedGroup c.1.val Y) c.2 ζ) j
    (alphabetCharacteristic_monic _) (he_monic.mul hsel)
  · rw [alphabetCharacteristic_evaluate_points, singlyMarkedPoint_characteristic]
    exact mul_dvd_mul (dvd_refl _) (selectedSitePolynomial_dvd_product _ _ _ _ _)
  · exact mul_dvd_mul he_dvd (selectedSitePolynomial_dvd_sites _ _ _ _ _)
  · rw [alphabetCharacteristic_natDegree, List.length_map, fullFlagSubalphabet, List.length_map,
      Finset.length_toList, he_monic.natDegree_mul hsel, he_deg,
      selectedSitePolynomial_natDegree]
    have h1 := card_eq_deletedGroup Y c.1.val
    have h2 := fullFlag_selected_card B k (deletedGroup c.1.val Y) c.2
    have h3 : singlyMarkedSelectedDoubles Y c = fullFlagDoublesIn (deletedGroup c.1.val Y) c.2 :=
      rfl
    split_ifs at h1 ⊢ <;> omega

/-- **Singly marked deformation of the marked columns.** The factor `∏ (V ∩ Y)` times the
deformed `j`-minors of the columns `t^(h+c)` vanishes at every singly marked configuration with
fewer than `j` selected doubles. -/
theorem singlyMarked_markedDeformedMinor_zero (B k j : ℕ) (V Y : Finset (Fin (B + 1)))
    (ζ : Fin (B - k) → ℂ) (rows cols : Fin j → ℕ) (c : SinglyMarkedConfiguration B k V)
    (hc : singlyMarkedSelectedDoubles Y c < j) :
    aeval (singlyMarkedPoint B k V ζ c)
        (∏ i ∈ V ∩ Y, (X i : MvPolynomial (Fin (B + 1)) ℂ)) *
      aeval (singlyMarkedPoint B k V ζ c) (deformedRemainderMinor (fullFlagSubalphabet Y)
        (B - k) j (alphabetCharacteristic (List.ofFn ζ)) rows cols) = 0 := by
  classical
  by_cases hv : c.1.val ∈ Y
  · have h0 : aeval (singlyMarkedPoint B k V ζ c)
        (∏ i ∈ V ∩ Y, (X i : MvPolynomial (Fin (B + 1)) ℂ)) = 0 := by
      rw [map_prod]
      apply Finset.prod_eq_zero (Finset.mem_inter.mpr ⟨c.1.property, hv⟩)
      simp [singlyMarkedPoint]
    rw [h0, zero_mul]
  · rw [deformedRemainderMinor_evaluate _ _ _ _ (sitePolynomial_natDegree_le _ ζ)]
    have hsel := selectedSitePolynomial_monic B k (deletedGroup c.1.val Y) c.2 ζ
    rw [scalarRemainderMinor_eq_zero _ _
      (selectedSitePolynomial B k (deletedGroup c.1.val Y) c.2 ζ) j
      (alphabetCharacteristic_monic _) hsel, mul_zero]
    · rw [alphabetCharacteristic_evaluate_points, singlyMarkedPoint_characteristic, if_neg hv,
        one_mul]
      exact selectedSitePolynomial_dvd_product _ _ _ _ _
    · exact selectedSitePolynomial_dvd_sites _ _ _ _ _
    · rw [alphabetCharacteristic_natDegree, List.length_map, fullFlagSubalphabet,
        List.length_map, Finset.length_toList, selectedSitePolynomial_natDegree]
      have h1 := card_eq_deletedGroup Y c.1.val
      have h2 := fullFlag_selected_card B k (deletedGroup c.1.val Y) c.2
      have h3 : singlyMarkedSelectedDoubles Y c =
          fullFlagDoublesIn (deletedGroup c.1.val Y) c.2 := rfl
      rw [if_neg hv] at h1
      omega

/-- **Doubly marked deformation.** The deformed `j`-minors of the columns `t^(h+1+c)` vanish at
every doubly marked configuration with fewer than `j` selected doubles. -/
theorem doublyMarked_deformedMinor_zero (B k j : ℕ) (V Y : Finset (Fin (B + 2)))
    (ζ : Fin (B - k) → ℂ) (rows cols : Fin j → ℕ) (c : DoublyMarkedConfiguration B k V)
    (hc : doublyMarkedSelectedDoubles Y c < j) :
    aeval (doublyMarkedPoint B k V ζ c) (deformedRemainderMinor (fullFlagSubalphabet Y)
      (B - k + 1) j (Polynomial.X * alphabetCharacteristic (List.ofFn ζ)) rows cols) = 0 := by
  classical
  rw [deformedRemainderMinor_evaluate _ _ _ _ (zeroSitePolynomial_natDegree_le _ ζ)]
  obtain ⟨he_monic, he_deg, he_dvd⟩ :=
    selectedZeroFactor (c.1.val ∈ Y ∨ c.2.1.val ∈ deletedGroup c.1.val Y)
  have hsel := selectedSitePolynomial_monic B k
    (deletedGroup c.2.1.val (deletedGroup c.1.val Y)) c.2.2 ζ
  apply scalarRemainderMinor_eq_zero _ _
    ((if c.1.val ∈ Y ∨ c.2.1.val ∈ deletedGroup c.1.val Y then Polynomial.X else 1) *
      selectedSitePolynomial B k (deletedGroup c.2.1.val (deletedGroup c.1.val Y)) c.2.2 ζ) j
    (alphabetCharacteristic_monic _) (he_monic.mul hsel)
  · rw [alphabetCharacteristic_evaluate_points, doublyMarkedPoint_characteristic, ← mul_assoc]
    exact mul_dvd_mul (selectedZeroFactor_dvd _ _) (selectedSitePolynomial_dvd_product _ _ _ _ _)
  · exact mul_dvd_mul he_dvd (selectedSitePolynomial_dvd_sites _ _ _ _ _)
  · rw [alphabetCharacteristic_natDegree, List.length_map, fullFlagSubalphabet, List.length_map,
      Finset.length_toList, he_monic.natDegree_mul hsel, he_deg,
      selectedSitePolynomial_natDegree]
    have h1 := card_eq_deletedGroup Y c.1.val
    have h1' := card_eq_deletedGroup (deletedGroup c.1.val Y) c.2.1.val
    have h2 := fullFlag_selected_card B k (deletedGroup c.2.1.val (deletedGroup c.1.val Y)) c.2.2
    have hmem : c.2.1.val ∈ deletedGroup c.1.val Y ↔ c.1.val.succAbove c.2.1.val ∈ Y :=
      mem_deletedGroup c.1.val Y c.2.1.val
    have h3 : doublyMarkedSelectedDoubles Y c =
        (if c.1.val ∈ Y ∧ c.1.val.succAbove c.2.1.val ∈ Y then 1 else 0) +
          fullFlagDoublesIn (deletedGroup c.2.1.val (deletedGroup c.1.val Y)) c.2.2 := rfl
    simp only [hmem] at h1' ⊢
    by_cases hu : c.1.val ∈ Y <;> by_cases hw : c.1.val.succAbove c.2.1.val ∈ Y <;>
      simp only [hu, hw, or_true, or_false, true_or, and_true, and_false, if_true,
        if_false] at h1 h1' h3 ⊢ <;> omega

/-! ### The deformed ideals -/

/-- The singly marked configurations with fewer than `j` selected doubles, as points. -/
def singlyMarkedStratumPoint (B k j : ℕ) (V Y : Finset (Fin (B + 1))) (ζ : Fin (B - k) → ℂ)
    (c : {c : SinglyMarkedConfiguration B k V // singlyMarkedSelectedDoubles Y c < j}) :
    Fin (B + 1) → ℂ :=
  singlyMarkedPoint B k V ζ c.val

/-- The doubly marked configurations with fewer than `j` selected doubles, as points. -/
def doublyMarkedStratumPoint (B k j : ℕ) (V Y : Finset (Fin (B + 2))) (ζ : Fin (B - k) → ℂ)
    (c : {c : DoublyMarkedConfiguration B k V // doublyMarkedSelectedDoubles Y c < j}) :
    Fin (B + 2) → ℂ :=
  doublyMarkedPoint B k V ζ c.val

theorem singlyMarked_remainderTopIdeal_le (B k j N : ℕ) (hN : N = B - k + 1)
    (V Y : Finset (Fin (B + 1))) (ζ : Fin (B - k) → ℂ) :
    remainderTopIdeal (fullFlagSubalphabet Y) N j ≤
      pointInitialIdeal (singlyMarkedStratumPoint B k j V Y ζ) := by
  subst hN
  apply Ideal.span_le.mpr
  rintro _ ⟨cols, rfl⟩
  exact remainderRowMinor_mem_pointInitialIdeal _ _ (fullFlagSubalphabet_integerHomogeneous Y)
    (B - k + 1) j _ (zeroSitePolynomial_coeff _ ζ)
    (fun a => (fullFlagSubalphabet Y).length - j + a.val) cols
    (fun c => singlyMarked_deformedMinor_zero B k j V Y ζ _ cols c.val c.property)

theorem singlyMarked_markedRemainderMinor_mem (B k j N : ℕ) (hN : N = B - k)
    (V Y : Finset (Fin (B + 1))) (ζ : Fin (B - k) → ℂ) (cols : Fin j → ℕ) :
    (∏ i ∈ V ∩ Y, (X i : MvPolynomial (Fin (B + 1)) ℂ)) *
        remainderTopMinor (fullFlagSubalphabet Y) N j cols ∈
      pointInitialIdeal (singlyMarkedStratumPoint B k j V Y ζ) := by
  subst hN
  have hs : (∏ i ∈ V ∩ Y, (X i : MvPolynomial (Fin (B + 1)) ℂ)).IsHomogeneous
      (V ∩ Y).card := by
    have h := IsHomogeneous.prod (V ∩ Y) (fun i => (X i : MvPolynomial (Fin (B + 1)) ℂ))
      (fun _ => 1) (fun i _ => isHomogeneous_X ℂ i)
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using h
  exact mul_remainderRowMinor_mem_pointInitialIdeal _ _
    (fullFlagSubalphabet_integerHomogeneous Y) (B - k) j _ (sitePolynomial_coeff _ ζ)
    (fun a => (fullFlagSubalphabet Y).length - j + a.val) cols
    _ _ hs
    (fun c => singlyMarked_markedDeformedMinor_zero B k j V Y ζ _ cols c.val c.property)

theorem doublyMarked_remainderTopIdeal_le (B k j N : ℕ) (hN : N = B - k + 1)
    (V Y : Finset (Fin (B + 2))) (ζ : Fin (B - k) → ℂ) :
    remainderTopIdeal (fullFlagSubalphabet Y) N j ≤
      pointInitialIdeal (doublyMarkedStratumPoint B k j V Y ζ) := by
  subst hN
  apply Ideal.span_le.mpr
  rintro _ ⟨cols, rfl⟩
  exact remainderRowMinor_mem_pointInitialIdeal _ _ (fullFlagSubalphabet_integerHomogeneous Y)
    (B - k + 1) j _ (zeroSitePolynomial_coeff _ ζ)
    (fun a => (fullFlagSubalphabet Y).length - j + a.val) cols
    (fun c => doublyMarked_deformedMinor_zero B k j V Y ζ _ cols c.val c.property)

/-! ### The top ideal of a power submodule is the remainder top ideal -/

section PowerTopIdeal

open Polynomial

theorem polynomialSubmoduleTopIdeal_power_eq {A : Type*} [CommRing A] (xs : List A)
    (N j : ℕ) :
    polynomialSubmoduleTopIdeal (alphabetCharacteristic xs) xs.length j
        ((Ideal.span {(Polynomial.X : A[X]) ^ N}).restrictScalars A) =
      remainderTopIdeal xs N j := by
  apply le_antisymm
  · refine topIdeal_le_of_span _ _ _ _ {u | ∃ c, u = Polynomial.X ^ c * Polynomial.X ^ N} ?_ _ ?_
    · intro f hf
      rw [Submodule.restrictScalars_mem] at hf
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      exact mul_mem_span_X_pow_mul _ g
    · intro u hu
      choose c hc using hu
      have he : (fun i b => topRowFunctional (alphabetCharacteristic xs) xs.length j i (u b)) =
          fun a b => alphabetPowerRemainder xs (N + c b) (xs.length - j + a.val) := by
        ext a b
        rw [topRowFunctional_apply, hc b, ← pow_add, add_comm (c b) N]
        rfl
      rw [he]
      exact remainderTopMinor_mem xs N j c
  · apply Ideal.span_le.mpr
    rintro _ ⟨cols, rfl⟩
    exact topIdeal_det_mem (alphabetCharacteristic xs) xs.length j
      ((Ideal.span {(Polynomial.X : A[X]) ^ N}).restrictScalars A)
      (fun b => Polynomial.X ^ (N + cols b))
      (fun b => by
        rw [Submodule.restrictScalars_mem]
        dsimp only
        rw [pow_add]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

end PowerTopIdeal

/-! ### Exactness from the dimension count -/

/-- A finite presented quotient below a leading-relation ideal, of dimension at most the number of
points, equals it; the dimension is read off from the quotient by a further ideal. -/
theorem sup_eq_pointInitialIdeal_of_count {ι σ : Type*} [Fintype ι] (x : ι → σ → ℂ)
    (hx : Function.Injective x) (I₀ J : Ideal (MvPolynomial σ ℂ))
    [FiniteDimensional ℂ (MvPolynomial σ ℂ ⧸ I₀)]
    (hle : I₀ ⊔ J ≤ pointInitialIdeal x) (D L : ℕ)
    (hC : Module.finrank ℂ (MvPolynomial σ ℂ ⧸ I₀) = D)
    (hG : L ≤ Module.finrank ℂ ((J.map (Ideal.Quotient.mk I₀)).restrictScalars ℂ))
    (hcount : D ≤ Fintype.card ι + L) :
    I₀ ⊔ J = pointInitialIdeal x := by
  haveI : FiniteDimensional ℂ (MvPolynomial σ ℂ ⧸ (I₀ ⊔ J)) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.factorₐ ℂ (le_sup_left : I₀ ≤ I₀ ⊔ J)).toLinearMap
      (Ideal.Quotient.factor_surjective le_sup_left)
  apply pointInitialIdeal_eq_of_rank_bound x hx _ hle
  have hmap : J.map (Ideal.Quotient.mkₐ ℂ I₀) = J.map (Ideal.Quotient.mk I₀) := rfl
  have e1 := (DoubleQuot.quotQuotEquivQuotSupₐ ℂ I₀ J).toLinearEquiv.finrank_eq
  rw [hmap] at e1
  have e2 := (Submodule.Quotient.restrictScalarsEquiv ℂ
    (J.map (Ideal.Quotient.mk I₀))).finrank_eq
  have e3 := Submodule.finrank_quotient_add_finrank
    ((J.map (Ideal.Quotient.mk I₀)).restrictScalars ℂ)
  omega

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.pointInitialIdeal_le_comp
#print axioms VOA.DeligneAudit.SL4T.remainderRowMinor_mem_pointInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.mul_remainderRowMinor_mem_pointInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_evaluate_points
#print axioms VOA.DeligneAudit.SL4T.selectedSitePolynomial_dvd_product
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedPoint_characteristic
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedPoint_characteristic
#print axioms VOA.DeligneAudit.SL4T.zeroSitePolynomial_coeff
#print axioms VOA.DeligneAudit.SL4T.zeroSitePolynomial_natDegree_le
#print axioms VOA.DeligneAudit.SL4T.sitePolynomial_coeff
#print axioms VOA.DeligneAudit.SL4T.sitePolynomial_natDegree_le
#print axioms VOA.DeligneAudit.SL4T.selectedZeroFactor
#print axioms VOA.DeligneAudit.SL4T.selectedZeroFactor_dvd
#print axioms VOA.DeligneAudit.SL4T.singlyMarked_deformedMinor_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarked_markedDeformedMinor_zero
#print axioms VOA.DeligneAudit.SL4T.doublyMarked_deformedMinor_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedStratumPoint
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedStratumPoint
#print axioms VOA.DeligneAudit.SL4T.singlyMarked_remainderTopIdeal_le
#print axioms VOA.DeligneAudit.SL4T.singlyMarked_markedRemainderMinor_mem
#print axioms VOA.DeligneAudit.SL4T.doublyMarked_remainderTopIdeal_le
#print axioms VOA.DeligneAudit.SL4T.polynomialSubmoduleTopIdeal_power_eq
#print axioms VOA.DeligneAudit.SL4T.sup_eq_pointInitialIdeal_of_count
