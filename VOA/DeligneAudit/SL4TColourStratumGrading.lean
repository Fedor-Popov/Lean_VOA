import VOA.DeligneAudit.SL4TLineFlagRefinement
import VOA.DeligneAudit.SL4TColourFlagTailQuotient
import VOA.DeligneAudit.SL4TFullFlagGradedCertificate

/-!
# The graded determinantal strata of the Young-invariant truncated flag ring

The coefficient ring is the colour-invariant polynomial algebra modulo the contraction of the
full-flag truncation ideal (elementary relations and coordinate powers). Its strata are the
images of the contracted top-minor ideals of the selected alphabet. This file proves the
properties of this stratification used by the line-flag refinement:

* the remainder minors vanish beyond the alphabet length and decrease in size by Laplace
  expansion along the first row, so the strata descend from the whole ring to zero;
* every stratum is spanned by images of homogeneous invariants in degrees between zero and
  `B * N`, obtained by averaging homogeneous components; above `B * N` every homogeneous
  invariant lies in the coordinate-power ideal;
* the selected power sums are homogeneous of their mode and act on the degree pieces;
* the quotient by each stratum is the contracted stratum quotient, whose dimension is the
  number of attained site colour multiplicities, and the ring is finite-dimensional.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-! ## Remainder minors: vanishing beyond the length and the Laplace step -/

section Minors

variable {A : Type*} [CommRing A]

/-- Below the last row of the remainder matrix every coefficient vanishes. -/
theorem alphabetPowerRemainder_eq_zero_of_length_le (xs : List A) (m l : ℕ)
    (hl : xs.length ≤ l) : alphabetPowerRemainder xs m l = 0 := by
  nontriviality A
  rw [alphabetPowerRemainder]
  apply Polynomial.coeff_eq_zero_of_degree_lt
  calc (Polynomial.X ^ m %ₘ alphabetCharacteristic xs).degree
      < (alphabetCharacteristic xs).degree :=
        Polynomial.degree_modByMonic_lt _ (alphabetCharacteristic_monic xs)
    _ = xs.length := by
        rw [Polynomial.degree_eq_natDegree (alphabetCharacteristic_monic xs).ne_zero,
          alphabetCharacteristic_natDegree]
    _ ≤ l := by exact_mod_cast hl

/-- Top-row minors with more rows than letters vanish. -/
theorem remainderTopIdeal_eq_bot_of_length_lt (xs : List A) (N j : ℕ)
    (hj : xs.length < j) : remainderTopIdeal xs N j = ⊥ := by
  rw [remainderTopIdeal, Ideal.span_eq_bot]
  rintro x ⟨cols, rfl⟩
  apply Matrix.det_eq_zero_of_row_eq_zero (⟨j - 1, by omega⟩ : Fin j)
  intro b
  apply alphabetPowerRemainder_eq_zero_of_length_le
  simp only
  omega

/-- Laplace expansion along the first row: larger top-row minors lie in the smaller ideal. -/
theorem remainderTopIdeal_succ_le (xs : List A) (N j : ℕ) (hj : j + 1 ≤ xs.length) :
    remainderTopIdeal xs N (j + 1) ≤ remainderTopIdeal xs N j := by
  apply Ideal.span_le.mpr
  rintro x ⟨cols, rfl⟩
  rw [SetLike.mem_coe, remainderTopMinor, Matrix.det_succ_row_zero]
  apply Ideal.sum_mem
  intro b _
  apply Ideal.mul_mem_left
  have he : Matrix.det ((Matrix.of fun a c : Fin (j + 1) =>
      alphabetPowerRemainder xs (N + cols c) (xs.length - (j + 1) + a.val)).submatrix
        Fin.succ b.succAbove) = remainderTopMinor xs N j (fun c => cols (b.succAbove c)) := by
    rw [remainderTopMinor]
    congr 1
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ]
    congr 1
    omega
  exact he ▸ remainderTopMinor_mem xs N j _

/-- The top-row ideals descend with the minor size. -/
theorem remainderTopIdeal_antitone_step (xs : List A) (N j : ℕ) :
    remainderTopIdeal xs N (j + 1) ≤ remainderTopIdeal xs N j := by
  by_cases hj : j + 1 ≤ xs.length
  · exact remainderTopIdeal_succ_le xs N j hj
  · rw [remainderTopIdeal_eq_bot_of_length_lt xs N (j + 1) (by omega)]
    exact bot_le

end Minors

/-! ## Homogeneity under permutations of the variables -/

/-- Renaming the variables preserves the ordinary degree. -/
theorem isWeightedHomogeneous_rename_one {σ τ A : Type*} [CommRing A] (f : σ → τ)
    {p : MvPolynomial σ A} {d : ℤ} (hp : p.IsWeightedHomogeneous (fun _ => (1 : ℤ)) d) :
    (rename f p).IsWeightedHomogeneous (fun _ => (1 : ℤ)) d := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro s hs
  rw [rename_monomial]
  apply MvPolynomial.isWeightedHomogeneous_monomial
  rw [← hp (mem_support_iff.mp hs), Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index] <;> simp

/-- Ordinary-degree components of an arbitrary polynomial add up to it. -/
theorem weightedComponent_sum_image_support {σ A : Type*} [CommRing A] (w : σ → ℤ)
    (p : MvPolynomial σ A) :
    ∑ d ∈ p.support.image (Finsupp.weight w), weightedHomogeneousComponent w d p = p := by
  classical
  ext s
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (Finset.mem_image_of_mem _ (mem_support_iff.mpr (Ne.symm hne)))

/-- Ordinary degrees of monomials are nonnegative. -/
theorem weight_one_nonneg {σ : Type*} (s : σ →₀ ℕ) :
    0 ≤ Finsupp.weight (fun _ : σ => (1 : ℤ)) s := by
  rw [Finsupp.weight_apply]
  apply Finset.sum_nonneg
  intro i _
  simp

/-- The full-flag stratum ideal is homogeneous. -/
theorem fullFlagStratumIdeal_component_mem (B N j : ℕ) (Y : Finset (Fin B)) (d : ℤ)
    (p : MvPolynomial (Fin B) ℂ)
    (hp : p ∈ fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Y) N j) :
    weightedHomogeneousComponent (fun _ => (1 : ℤ)) d p ∈
      fullFlagTruncationIdeal B N ⊔ remainderTopIdeal (fullFlagSubalphabet Y) N j := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hp
  rw [map_add]
  apply Ideal.add_mem
  · exact Ideal.mem_sup_left (fullFlagTruncationIdeal_component_mem B N d a ha)
  · apply Ideal.mem_sup_right
    have hxs : ∀ x ∈ fullFlagSubalphabet Y, x.IsWeightedHomogeneous (fun _ => (1 : ℤ)) 1 := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact isWeightedHomogeneous_X ℂ _ i
    exact homogeneous_span_component_mem (fun _ => (1 : ℤ))
      (remainderTopMinor (fullFlagSubalphabet Y) N j)
      (fun cols => remainderMinorDegree N j
        (fun a => (fullFlagSubalphabet Y).length - j + a.val) cols)
      (fun cols => remainderRowMinor_homogeneous _ _ hxs N j _ cols) b hb d

/-- Homogeneous polynomials of large degree lie in the coordinate-power part of the flag. -/
theorem fullFlagTruncationIdeal_of_high_degree (B N : ℕ) (d : ℤ) (hd : ((B * N : ℕ) : ℤ) < d)
    (p : MvPolynomial (Fin B) ℂ) (hp : p.IsWeightedHomogeneous (fun _ => (1 : ℤ)) d) :
    p ∈ fullFlagTruncationIdeal B N := by
  classical
  apply Ideal.mem_sup_right
  have hspan : Ideal.span (Set.range fun i : Fin B => (X i : MvPolynomial (Fin B) ℂ) ^ N) =
      Ideal.span ((fun s => monomial s (1 : ℂ)) '' Set.range fun i => Finsupp.single i N) := by
    congr 1
    ext x
    simp [X_pow_eq_monomial]
  rw [hspan, mem_ideal_span_monomial_image]
  intro s hs
  have hw := hp (mem_support_iff.mp hs)
  have hex : ∃ i, N ≤ s i := by
    by_contra hno
    have hle : ∀ i, s i ≤ N := fun i => by
      by_contra hi
      exact hno ⟨i, by omega⟩
    have hsum : Finsupp.weight (fun _ : Fin B => (1 : ℤ)) s ≤ ((B * N : ℕ) : ℤ) := by
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
      calc (∑ i : Fin B, s i • (1 : ℤ)) ≤ ∑ _i : Fin B, (N : ℤ) := by
            apply Finset.sum_le_sum
            intro i _
            simpa using hle i
        _ = ((B * N : ℕ) : ℤ) := by simp
    omega
  obtain ⟨i, hi⟩ := hex
  refine ⟨Finsupp.single i N, ⟨i, rfl⟩, ?_⟩
  intro l
  by_cases hl : l = i
  · subst l
    simpa using hi
  · simp [Ne.symm hl]

/-! ## Averaging in the colour-invariant polynomial algebra -/

variable {C : Type*} {B : ℕ} (colour : Fin B → C)

/-- The local finite-type instance used for Young-subgroup averaging. -/
local instance colourStratumPermutationFintype : Fintype (positionColourSubgroup colour) :=
  Fintype.ofFinite _

/-- Averaging stays in every submodule stable under the colour-preserving permutations. -/
theorem colourPolynomialAverage_mem_stable (I : Submodule ℂ (MvPolynomial (Fin B) ℂ))
    (hI : ∀ g : positionColourSubgroup colour, ∀ x ∈ I, rename g.val x ∈ I)
    (x : MvPolynomial (Fin B) ℂ) (hx : x ∈ I) : (colourPolynomialAverage colour x).val ∈ I := by
  change finiteActionAverage
    (polynomialPositionAlgebraAction (positionColourSubgroup colour).subtype) x ∈ I
  simp only [finiteActionAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    AlgEquiv.toLinearMap_apply]
  exact I.smul_mem _ (I.sum_mem fun g _ => hI g x hx)

/-- Averaging fixes invariant polynomials. -/
theorem colourPolynomialAverage_fixed (f : ColourPolynomialRing colour) :
    colourPolynomialAverage colour f.val = f := by
  apply Subtype.ext
  exact finiteActionAverage_id _ f.val f.property

/-- Invariant polynomials homogeneous of a given ordinary degree. -/
def colourHomogeneousPiece (d : ℤ) : Submodule ℂ (ColourPolynomialRing colour) :=
  (weightedHomogeneousSubmodule ℂ (fun _ : Fin B => (1 : ℤ)) d).comap
    (ColourPolynomialRing colour).val.toLinearMap

theorem mem_colourHomogeneousPiece (d : ℤ) (f : ColourPolynomialRing colour) :
    f ∈ colourHomogeneousPiece colour d ↔
      f.val.IsWeightedHomogeneous (fun _ => (1 : ℤ)) d := Iff.rfl

/-- Averaging a homogeneous polynomial gives a homogeneous invariant of the same degree. -/
theorem colourPolynomialAverage_homogeneous (d : ℤ) (x : MvPolynomial (Fin B) ℂ)
    (hx : x.IsWeightedHomogeneous (fun _ => (1 : ℤ)) d) :
    colourPolynomialAverage colour x ∈ colourHomogeneousPiece colour d := by
  apply colourPolynomialAverage_mem_stable colour
    (weightedHomogeneousSubmodule ℂ (fun _ : Fin B => (1 : ℤ)) d) _ x hx
  intro g y hy
  exact isWeightedHomogeneous_rename_one g.val hy

/-- Products of homogeneous invariants are homogeneous. -/
theorem colourHomogeneousPiece_mul (d e : ℤ) (a b : ColourPolynomialRing colour)
    (ha : a ∈ colourHomogeneousPiece colour d) (hb : b ∈ colourHomogeneousPiece colour e) :
    a * b ∈ colourHomogeneousPiece colour (d + e) := by
  rw [mem_colourHomogeneousPiece] at ha hb ⊢
  exact ha.mul hb

/-- An invariant lying in a stable homogeneous ideal is a sum of homogeneous invariants of
nonnegative degree lying in the same ideal. -/
theorem colourPolynomial_homogeneous_decomposition (I : Ideal (MvPolynomial (Fin B) ℂ))
    (hstable : ∀ g : positionColourSubgroup colour, ∀ x ∈ I, rename g.val x ∈ I)
    (hhom : ∀ (d : ℤ) p, p ∈ I → weightedHomogeneousComponent (fun _ => (1 : ℤ)) d p ∈ I)
    (f : ColourPolynomialRing colour) (hf : f.val ∈ I) :
    ∃ T : Finset ℤ, (∀ d ∈ T, 0 ≤ d) ∧
      ∑ d ∈ T, colourPolynomialAverage colour
        (weightedHomogeneousComponent (fun _ => (1 : ℤ)) d f.val) = f ∧
      ∀ d, colourPolynomialAverage colour
          (weightedHomogeneousComponent (fun _ => (1 : ℤ)) d f.val) ∈
            colourHomogeneousPiece colour d ∧
        (colourPolynomialAverage colour
          (weightedHomogeneousComponent (fun _ => (1 : ℤ)) d f.val)).val ∈ I := by
  classical
  refine ⟨f.val.support.image (Finsupp.weight fun _ => (1 : ℤ)), ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hd
    exact weight_one_nonneg s
  · rw [← map_sum, weightedComponent_sum_image_support, colourPolynomialAverage_fixed]
  · intro d
    refine ⟨colourPolynomialAverage_homogeneous colour d _
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _), ?_⟩
    apply colourPolynomialAverage_mem_stable colour (I.restrictScalars ℂ) hstable
    exact hhom d _ hf

/-! ## The truncated invariant ring, its strata and its grading -/

section Strata

variable [DecidableEq C]

/-- The truncation relations contracted to colour-invariant polynomials. -/
def colourTruncationIdeal (N : ℕ) : Ideal (ColourPolynomialRing colour) :=
  (fullFlagTruncationIdeal B N).comap (ColourPolynomialRing colour).val.toRingHom

/-- Young-invariant coefficients of the truncated full flag. -/
abbrev ColourTruncatedFlagRing (N : ℕ) :=
  ColourPolynomialRing colour ⧸ colourTruncationIdeal colour N

/-- The contracted determinantal stratum ideal of the selected colours. -/
def colourStratumContraction (selected : Finset C) (N j : ℕ) :
    Ideal (ColourPolynomialRing colour) :=
  (fullFlagTruncationIdeal B N ⊔
    remainderTopIdeal (fullFlagSubalphabet (selectedColourPositions colour selected)) N j).comap
      (ColourPolynomialRing colour).val.toRingHom

/-- The determinantal stratum in the truncated invariant ring. -/
def colourTruncatedStratum (selected : Finset C) (N j : ℕ) :
    Ideal (ColourTruncatedFlagRing colour N) :=
  (colourStratumContraction colour selected N j).map
    (Ideal.Quotient.mk (colourTruncationIdeal colour N))

/-- The image of the homogeneous invariants of a given degree. -/
def colourTruncatedDegree (N : ℕ) (d : ℤ) : Submodule ℂ (ColourTruncatedFlagRing colour N) :=
  (colourHomogeneousPiece colour d).map
    (Ideal.Quotient.mkₐ ℂ (colourTruncationIdeal colour N)).toLinearMap

/-- The power sum of all selected colours, as an invariant polynomial. -/
def selectedColourPowerSum (selected : Finset C) (s : ℕ) : ColourPolynomialRing colour :=
  ∑ c ∈ selected, colourPolynomialPowerSum colour c s

/-- The selected power sum in the truncated invariant ring. -/
def colourTruncatedPowerSum (selected : Finset C) (N s : ℕ) :
    ColourTruncatedFlagRing colour N :=
  Ideal.Quotient.mk _ (selectedColourPowerSum colour selected s)

theorem selectedColourPowerSum_val (selected : Finset C) (s : ℕ) :
    (selectedColourPowerSum colour selected s).val =
      ∑ i ∈ selectedColourPositions colour selected, (X i : MvPolynomial (Fin B) ℂ) ^ s := by
  classical
  rw [selectedColourPowerSum, AddSubmonoidClass.coe_finsetSum]
  change ∑ c ∈ selected, ∑ i ∈ Finset.univ.filter (fun i => colour i = c),
    (X i : MvPolynomial (Fin B) ℂ) ^ s = _
  rw [selectedColourPositions, ← Finset.sum_fiberwise_of_maps_to (g := colour)
    (t := selected) (fun i hi => (Finset.mem_filter.mp hi).2)]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨h ▸ hc, h⟩
    · intro h
      exact h.2
  · intro _ _
    rfl

theorem selectedColourPowerSum_homogeneous (selected : Finset C) (s : ℕ) :
    selectedColourPowerSum colour selected s ∈ colourHomogeneousPiece colour s := by
  rw [mem_colourHomogeneousPiece, selectedColourPowerSum_val]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i _
  simpa using (isWeightedHomogeneous_X ℂ (fun _ : Fin B => (1 : ℤ)) i).pow s

theorem colourTruncationIdeal_le_contraction (selected : Finset C) (N j : ℕ) :
    colourTruncationIdeal colour N ≤ colourStratumContraction colour selected N j :=
  Ideal.comap_mono le_sup_left

/-- An element of a stratum has a representative in the contracted stratum ideal. -/
theorem colourTruncatedStratum_mem_iff (selected : Finset C) (N j : ℕ)
    (f : ColourPolynomialRing colour) :
    Ideal.Quotient.mk _ f ∈ colourTruncatedStratum colour selected N j ↔
      f ∈ colourStratumContraction colour selected N j := by
  rw [colourTruncatedStratum, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · rintro ⟨g, hg, he⟩
    have hd : g - f ∈ colourTruncationIdeal colour N := Ideal.Quotient.eq.mp he
    have hd' := colourTruncationIdeal_le_contraction colour selected N j hd
    have := (colourStratumContraction colour selected N j).sub_mem hg hd'
    simpa using this
  · intro hf
    exact ⟨f, hf, rfl⟩

/-- The selected power sums raise the degree by their mode. -/
theorem colourTruncatedDegree_powerSum_mul (selected : Finset C) (N s : ℕ) (d : ℤ)
    (a : ColourTruncatedFlagRing colour N) (ha : a ∈ colourTruncatedDegree colour N d) :
    colourTruncatedPowerSum colour selected N s * a ∈
      colourTruncatedDegree colour N (d + (s : ℤ)) := by
  obtain ⟨f, hf, rfl⟩ := ha
  refine ⟨selectedColourPowerSum colour selected s * f, ?_, ?_⟩
  · rw [add_comm]
    exact colourHomogeneousPiece_mul colour _ _ _ _
      (selectedColourPowerSum_homogeneous colour selected s) hf
  · simp [colourTruncatedPowerSum]

omit [DecidableEq C] in
/-- Above the bound `B * N` the truncated ring has no homogeneous elements. -/
theorem colourTruncatedDegree_eq_bot (N : ℕ) (d : ℤ) (hd : ((B * N : ℕ) : ℤ) < d) :
    colourTruncatedDegree colour N d = ⊥ := by
  rw [eq_bot_iff]
  rintro a ⟨f, hf, rfl⟩
  rw [Submodule.mem_bot]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact fullFlagTruncationIdeal_of_high_degree B N d hd f.val hf

/-- The stratum ideal of the polynomial ring is stable under the colour-preserving
permutations. -/
theorem fullFlagColourStratumIdeal_stable (k : ℕ) (hk : 2 * k ≤ B) (selected : Finset C)
    (j : ℕ) (g : positionColourSubgroup colour) (x : MvPolynomial (Fin B) ℂ)
    (hx : x ∈ fullFlagTruncationIdeal B (B - k) ⊔
      remainderTopIdeal (fullFlagSubalphabet (selectedColourPositions colour selected))
        (B - k) j) :
    rename g.val x ∈ fullFlagTruncationIdeal B (B - k) ⊔
      remainderTopIdeal (fullFlagSubalphabet (selectedColourPositions colour selected))
        (B - k) j :=
  fullFlagStratumIdeal_algebra_stable B k j _ hk (positionColourSubgroup colour).subtype
    (positionColourSubgroup_preserves_selected colour selected) g x hx

/-- Every stratum is spanned by its homogeneous elements of degree at most `B * N`. -/
theorem colourTruncatedStratum_homogeneous (k : ℕ) (hk : 2 * k ≤ B) (selected : Finset C)
    (j : ℕ) :
    (colourTruncatedStratum colour selected (B - k) j).restrictScalars ℂ ≤
      ⨆ (d : ℕ) (_ : d ≤ B * (B - k)),
        (colourTruncatedStratum colour selected (B - k) j).restrictScalars ℂ ⊓
          colourTruncatedDegree colour (B - k) d := by
  intro a ha
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hf := (colourTruncatedStratum_mem_iff colour selected (B - k) j f).mp ha
  obtain ⟨T, hT0, hsum, hpiece⟩ := colourPolynomial_homogeneous_decomposition colour _
    (fullFlagColourStratumIdeal_stable colour k hk selected j)
    (fun d p hp => fullFlagStratumIdeal_component_mem B (B - k) j _ d p hp) f hf
  rw [← hsum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  obtain ⟨hhom, hmem⟩ := hpiece d
  by_cases hdD : ((B * (B - k) : ℕ) : ℤ) < d
  · have hz : Ideal.Quotient.mk (colourTruncationIdeal colour (B - k))
        (colourPolynomialAverage colour
          (weightedHomogeneousComponent (fun _ => (1 : ℤ)) d f.val)) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact fullFlagTruncationIdeal_of_high_degree B (B - k) d hdD _ hhom
    rw [hz]
    exact Submodule.zero_mem _
  · have hd0 := hT0 d hd
    apply Submodule.mem_iSup_of_mem d.toNat
    apply Submodule.mem_iSup_of_mem (show d.toNat ≤ B * (B - k) by omega)
    refine ⟨(colourTruncatedStratum_mem_iff colour selected (B - k) j _).mpr hmem, ?_⟩
    refine ⟨_, ?_, rfl⟩
    rw [Int.toNat_of_nonneg hd0]
    exact hhom

/-- The first stratum is the whole ring. -/
theorem colourTruncatedStratum_zero (selected : Finset C) (N : ℕ) :
    colourTruncatedStratum colour selected N 0 = ⊤ := by
  rw [colourTruncatedStratum, colourStratumContraction, remainderTopIdeal_zero, sup_top_eq,
    Ideal.comap_top, Ideal.map_top]

/-- Strata with more rows than selected positions vanish. -/
theorem colourTruncatedStratum_eq_bot (selected : Finset C) (N j : ℕ)
    (hj : (selectedColourPositions colour selected).card < j) :
    colourTruncatedStratum colour selected N j = ⊥ := by
  rw [colourTruncatedStratum, colourStratumContraction,
    remainderTopIdeal_eq_bot_of_length_lt _ N j (by
      simpa [fullFlagSubalphabet] using hj), sup_bot_eq]
  exact Ideal.map_quotient_self _

/-- The strata descend. -/
theorem colourTruncatedStratum_succ_le (selected : Finset C) (N j : ℕ) :
    colourTruncatedStratum colour selected N (j + 1) ≤
      colourTruncatedStratum colour selected N j := by
  apply Ideal.map_mono
  apply Ideal.comap_mono
  exact sup_le_sup_left (remainderTopIdeal_antitone_step _ N j) _

/-- Each stratum quotient is the contracted stratum quotient of the invariant polynomials. -/
def colourTruncatedStratumQuotientEquiv (selected : Finset C) (N j : ℕ) :
    (ColourTruncatedFlagRing colour N ⧸ colourTruncatedStratum colour selected N j) ≃ₐ[ℂ]
      (ColourPolynomialRing colour ⧸ colourStratumContraction colour selected N j) := by
  have he : colourTruncatedStratum colour selected N j =
      (colourStratumContraction colour selected N j).map
        (Ideal.Quotient.mkₐ ℂ (colourTruncationIdeal colour N)) := rfl
  rw [he]
  exact DoubleQuot.quotQuotEquivQuotOfLEₐ ℂ
    (colourTruncationIdeal_le_contraction colour selected N j)

/-- The stratum quotients have the attained site colour multiplicity counts as dimensions. -/
theorem colourTruncatedStratum_quotient_finrank (k : ℕ) (hk : 2 * k ≤ B)
    (selected : Finset C) (j : ℕ) :
    FiniteDimensional ℂ (ColourTruncatedFlagRing colour (B - k) ⧸
        colourTruncatedStratum colour selected (B - k) j) ∧
      Module.finrank ℂ (ColourTruncatedFlagRing colour (B - k) ⧸
        colourTruncatedStratum colour selected (B - k) j) =
      Nat.card (Set.range (fun f : FullFlagStratumConfiguration B k j
        (selectedColourPositions colour selected) =>
          configurationColourMultiplicity colour f.val)) := by
  obtain ⟨hfin, hdim⟩ := colourStratum_contracted_finrank B k j hk colour selected
  let e := (colourTruncatedStratumQuotientEquiv colour selected (B - k) j).toLinearEquiv
  letI : FiniteDimensional ℂ
      (ColourPolynomialRing colour ⧸ colourStratumContraction colour selected (B - k) j) := hfin
  exact ⟨Module.Finite.of_injective e.toLinearMap e.injective, e.finrank_eq.trans hdim⟩

omit [DecidableEq C] in
/-- The truncated invariant ring is finite-dimensional. -/
theorem colourTruncatedFlagRing_finite (k : ℕ) (hk : 2 * k ≤ B) :
    FiniteDimensional ℂ (ColourTruncatedFlagRing colour (B - k)) := by
  classical
  let selected : Finset C := ∅
  let j := (selectedColourPositions colour selected).card + 1
  have hfin := (colourTruncatedStratum_quotient_finrank colour k hk selected j).1
  rw [colourTruncatedStratum_eq_bot colour selected (B - k) j (by omega)] at hfin
  exact Module.Finite.equiv
    (AlgEquiv.quotientBot ℂ (ColourTruncatedFlagRing colour (B - k))).toLinearEquiv

end Strata

end

end VOA.DeligneAudit.SL4T
