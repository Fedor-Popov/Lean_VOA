import VOA.Moonshine.MoonshineCNConformalTranslation

/-!
# Complex-frame lattice construction: GradedFields

Structural adaptation of `LatticeGenGradedField` using a complex bilinear
frame. The carrier, formal-distribution conventions and finite-support proofs
are preserved. No positive-definiteness hypothesis is introduced.
-/

set_option maxHeartbeats 1600000
set_option linter.style.longLine false

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct
open Module (End)
open IntegralLattice HeisenbergN LatGen Reconstruction

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

theorem halfNorm_add (L : IntegralLattice) (hEven : L.Even) (α β : L.carrier) :
    halfNorm L (α + β) = halfNorm L α + halfNorm L β + L.form α β := by
  have hexp : L.form (α + β) (α + β) = L.form α α + L.form β β + 2 * L.form α β := by
    simp only [map_add, LinearMap.add_apply]
    rw [form_symm L β α]; ring
  have h2ab := two_halfNorm L hEven (α + β)
  have h2a := two_halfNorm L hEven α
  have h2b := two_halfNorm L hEven β
  omega


theorem creationVariable_mem_gradingWN (α : L.carrier) (m : ℕ) :
    creationVariable F α m ∈ HeisenbergN.gradingWN (rank L) (m + 1) := by
  rw [creationVariable]
  refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ ?_)
  rw [HeisenbergN.mem_gradingWN]
  have := MvPolynomial.isWeightedHomogeneous_X ℂ (HeisenbergN.weightFnN (r := rank L)) (m, a)
  rwa [HeisenbergN.weightFnN_apply] at this


theorem creationCoefficient_mem_gradingWN (α : L.carrier) (N : ℕ) :
    creationCoefficient F α N ∈ HeisenbergN.gradingWN (rank L) N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [creationCoefficient_zero]; exact HeisenbergN.vacuumN_mem_gradingWN (rank L)
    | (M + 1) =>
      rw [creationCoefficient_succ]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
      simp only [Finset.mem_range] at hm
      have hcv : creationVariable F α m ∈ HeisenbergN.gradingWN (rank L) (m + 1) := creationVariable_mem_gradingWN F α m
      have hsc : creationCoefficient F α (M - m) ∈ HeisenbergN.gradingWN (rank L) (M - m) := ih (M - m) (by omega)
      rw [HeisenbergN.mem_gradingWN] at hcv hsc ⊢
      have hmul := hcv.mul hsc
      rwa [show (m + 1) + (M - m) = M + 1 from by omega] at hmul


theorem creationOperator_mem_gradingWN (α : L.carrier) (N : ℕ) {w : ℕ} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingWN (rank L) w) :
    creationOperator F α N p ∈ HeisenbergN.gradingWN (rank L) (N + w) := by
  rw [creationOperator, LinearMap.mulLeft_apply]
  have hc : creationCoefficient F α N ∈ HeisenbergN.gradingWN (rank L) N := creationCoefficient_mem_gradingWN F α N
  rw [HeisenbergN.mem_gradingWN] at hc hp ⊢
  exact hc.mul hp


theorem creationField_mem_gradingZN (α : L.carrier) (t : ℤ) {w : ℕ} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingWN (rank L) w) :
    creationField F α t p ∈ HeisenbergN.gradingZN (rank L) ((w : ℤ) + t) := by
  rw [creationField_apply]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    have h := HeisenbergN.mem_gradingZN_of_gradingWN (creationOperator_mem_gradingWN F α t.toNat hp)
    rwa [show ((t.toNat + w : ℕ) : ℤ) = (w : ℤ) + t from by
      rw [Nat.cast_add, Int.toNat_of_nonneg ht]; ring] at h
  · rw [if_neg ht, LinearMap.zero_apply]; exact Submodule.zero_mem _


theorem annihilationField_mem_gradingZN (α : L.carrier) (t : ℤ) {w : ℕ} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingWN (rank L) w) :
    annihilationField F α t p ∈ HeisenbergN.gradingZN (rank L) ((w : ℤ) + t) := by
  rw [annihilationField_apply]
  by_cases ht : t ≤ 0
  · rw [if_pos ht]
    have := annihilationCoefficient_mem_gradingZN F α (-t).toNat hp
    rwa [show (w : ℤ) - ((-t).toNat : ℤ) = (w : ℤ) + t from by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -t)]; ring] at this
  · rw [if_neg ht, LinearMap.zero_apply]; exact Submodule.zero_mem _


theorem creationField_memZ (α : L.carrier) (t : ℤ) {d : ℤ} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) d) :
    creationField F α t p ∈ HeisenbergN.gradingZN (rank L) (d + t) := by
  by_cases hd : 0 ≤ d
  · rw [HeisenbergN.gradingZN_of_nonneg hd] at hp
    have := creationField_mem_gradingZN F α t hp
    rwa [Int.toNat_of_nonneg hd] at this
  · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
    rw [hp, LinearMap.map_zero]; exact Submodule.zero_mem _


theorem annihilationField_memZ (α : L.carrier) (t : ℤ) {d : ℤ} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) d) :
    annihilationField F α t p ∈ HeisenbergN.gradingZN (rank L) (d + t) := by
  by_cases hd : 0 ≤ d
  · rw [HeisenbergN.gradingZN_of_nonneg hd] at hp
    have := annihilationField_mem_gradingZN F α t hp
    rwa [Int.toNat_of_nonneg hd] at this
  · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
    rw [hp, LinearMap.map_zero]; exact Submodule.zero_mem _


theorem finsumFockN_mem_submodule (L : IntegralLattice) {ι : Type*} (S : Submodule ℂ (FockN (rank L)))
    (g : ι → FockN (rank L)) (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) :
    (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset) (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)


theorem dressingField_memZ (α : L.carrier) (s : ℤ) {d : ℤ} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) d) :
    dressingField F α s p ∈ HeisenbergN.gradingZN (rank L) (d + s) := by
  rw [dressingField, nprod_apply]
  refine finsumFockN_mem_submodule L _ _
    (normalOrdered_diag_support_finite (creationField_isField F α) (annihilationField_isField F α) s p)
    (fun m => ?_)
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, Module.End.mul_apply]
    have h1 := annihilationField_memZ F α (s - m) hp
    have h2 := creationField_memZ F α m h1
    rwa [show d + (s - m) + m = d + s from by ring] at h2
  · rw [if_neg h0, Module.End.mul_apply]
    have h1 := creationField_memZ F α m hp
    have h2 := annihilationField_memZ F α (s - m) h1
    rwa [show d + m + (s - m) = d + s from by ring] at h2


theorem canonicalChargedField_bigrad_mem (hEven : L.Even) (α β : L.carrier) (t w : ℤ) {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) w) :
    canonicalChargedField F α t (mkEα L β p) ∈ gradingLatGen L (halfNorm L α + (w + halfNorm L β) + t) := by
  rw [show mkEα L β p = latStateGen L p β from rfl, canonicalChargedField_tmul]
  refine Submodule.smul_mem _ _ ?_
  have hE : dressingField F α (t - L.form α β) p ∈ HeisenbergN.gradingZN (rank L) (w + (t - L.form α β)) :=
    dressingField_memZ F α (t - L.form α β) hp
  have hle := bigradα_le_gradingLatGen L (w + (t - L.form α β)) (α + β)
    (show latStateGen L (dressingField F α (t - L.form α β) p) (α + β)
        ∈ bigradα L (w + (t - L.form α β), α + β) from ⟨_, hE, rfl⟩)
  rwa [show (w + (t - L.form α β)) + halfNorm L (α + β)
      = halfNorm L α + (w + halfNorm L β) + t from by rw [halfNorm_add L hEven α β]; ring] at hle


def FrameGradedField (L : IntegralLattice) (a : FormalDist (End ℂ (LatModuleGen L))) (D : ℤ) : Prop :=
  ∀ (j q : ℤ) (x : LatModuleGen L), x ∈ gradingLatGen L q → a j x ∈ gradingLatGen L (D + q + j)


theorem FrameGradedField.of_bigrad (L : IntegralLattice) (hEven : L.Even) 
    {a : FormalDist (End ℂ (LatModuleGen L))} {D : ℤ}
    (h : ∀ (j w : ℤ) (β : L.carrier) (p : FockN (rank L)), p ∈ HeisenbergN.gradingZN (rank L) w →
      a j (mkEα L β p) ∈ gradingLatGen L (D + (w + halfNorm L β) + j)) :
    FrameGradedField L a D := by
  intro j q x hx
  refine (?_ : gradingLatGen L q ≤ (gradingLatGen L (D + q + j)).comap (a j)) hx
  rw [latticeWeightGrading_eq_positiveFiber L q]
  refine iSup_le (fun p' => iSup_le (fun hp' => ?_))
  rintro y ⟨z, hz, rfl⟩
  rw [Submodule.mem_comap]
  obtain ⟨hfib, hpos⟩ := hp'
  have hgoal := h j p'.1 p'.2 z hz
  rwa [show D + (p'.1 + halfNorm L p'.2) + j = D + q + j from by rw [← hfib]] at hgoal


theorem canonicalChargedField_gradedField (hEven : L.Even)  (α : L.carrier) :
    FrameGradedField L (canonicalChargedField F α) (halfNorm L α) := by
  refine FrameGradedField.of_bigrad L hEven (fun j w β p hp => ?_)
  have := canonicalChargedField_bigrad_mem F hEven α β j w hp
  rwa [show halfNorm L α + (w + halfNorm L β) + j = halfNorm L α + (w + halfNorm L β) + j from rfl]


theorem frameCurrent_bigrad_mem (a : Fin (rank L)) (j w : ℤ) {δ : L.carrier} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) w) :
    frameCurrent F a j (mkEα L δ p) ∈ gradingLatGen L (1 + (w + halfNorm L δ) + j) := by
  rw [show mkEα L δ p = latStateGen L p δ from rfl, frameCurrent_tmul]
  refine Submodule.add_mem _ ?_ ?_
  · have hα : currentN (rank L) 1 a j p ∈ HeisenbergN.gradingZN (rank L) (w + j + 1) := by
      rw [currentN_apply]
      by_cases hd : 0 ≤ w
      · rw [HeisenbergN.gradingZN_of_nonneg hd] at hp
        have h := HeisenbergN.oscN_mem_gradingZN (rank L) 1 a (-j - 1) hp
        rw [Int.toNat_of_nonneg hd] at h
        rwa [show w - (-j - 1) = w + j + 1 from by ring] at h
      · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
        rw [hp, map_zero]; exact HeisenbergN.zero_mem_gradingZN (rank L) _
    have hle := bigradα_le_gradingLatGen L (w + j + 1) δ
      (show latStateGen L (currentN (rank L) 1 a j p) δ ∈ bigradα L (w + j + 1, δ) from ⟨_, hα, rfl⟩)
    rwa [show (w + j + 1) + halfNorm L δ = 1 + (w + halfNorm L δ) + j from by ring] at hle
  · by_cases hj : j = -1
    · rw [if_pos hj]
      refine Submodule.smul_mem _ _ ?_
      have hle := bigradα_le_gradingLatGen L w δ
        (show latStateGen L p δ ∈ bigradα L (w, δ) from ⟨p, hp, rfl⟩)
      rwa [show w + halfNorm L δ = 1 + (w + halfNorm L δ) + j from by rw [hj]; ring] at hle
    · rw [if_neg hj]; exact Submodule.zero_mem _


theorem frameCurrent_gradedField (hEven : L.Even)  (a : Fin (rank L)) :
    FrameGradedField L (frameCurrent F a) 1 := by
  refine FrameGradedField.of_bigrad L hEven (fun j w β p hp => ?_)
  exact frameCurrent_bigrad_mem F a j w hp


theorem finsum_lattice_submodule (L : IntegralLattice) {ι : Type*} (S : Submodule ℂ (LatModuleGen L))
    (g : ι → LatModuleGen L) (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) :
    (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset) (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)


theorem FrameGradedField.add (L : IntegralLattice) {a b : FormalDist (End ℂ (LatModuleGen L))} {D : ℤ}
    (ha : FrameGradedField L a D) (hb : FrameGradedField L b D) :
    FrameGradedField L (a + b) D := by
  intro j q x hx
  show (a j + b j) x ∈ _
  rw [LinearMap.add_apply]
  exact Submodule.add_mem _ (ha j q x hx) (hb j q x hx)


theorem FrameGradedField.smul' (L : IntegralLattice) {a : FormalDist (End ℂ (LatModuleGen L))} {D : ℤ} (c : ℂ)
    (ha : FrameGradedField L a D) : FrameGradedField L (c • a) D := by
  intro j q x hx
  show (c • a j) x ∈ _
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ c (ha j q x hx)


theorem FrameGradedField.zero (L : IntegralLattice) {D : ℤ} :
    FrameGradedField L (0 : FormalDist (End ℂ (LatModuleGen L))) D := by
  intro j q x hx
  show (0 : End ℂ (LatModuleGen L)) x ∈ _
  rw [LinearMap.zero_apply]; exact Submodule.zero_mem _


theorem FrameGradedField.deriv (L : IntegralLattice) {a : FormalDist (End ℂ (LatModuleGen L))} {D : ℤ}
    (ha : FrameGradedField L a D) : FrameGradedField L (VOA.deriv a) (D + 1) := by
  intro j q x hx
  rw [deriv_apply, ← Int.cast_smul_eq_zsmul ℂ (j + 1), LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  have := ha (j + 1) q x hx
  rwa [show D + q + (j + 1) = D + 1 + q + j from by ring] at this


theorem FrameGradedField.deriv_iterate (L : IntegralLattice) {a : FormalDist (End ℂ (LatModuleGen L))} {D : ℤ}
    (ha : FrameGradedField L a D) (i : ℕ) :
    FrameGradedField L (VOA.deriv^[i] a) (D + i) := by
  induction i with
  | zero => rw [Function.iterate_zero, id]; rwa [Nat.cast_zero, add_zero]
  | succ p ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    have := ih.deriv L
    rwa [show D + (p : ℤ) + 1 = D + ((p : ℤ) + 1) from by ring, ← Nat.cast_succ] at this


theorem frameDerivativeCurrent_gradedField (hEven : L.Even)  (a : Fin (rank L)) (i : ℕ) :
    FrameGradedField L (frameDerivativeCurrent F a i) ((i : ℤ) + 1) := by
  rw [frameDerivativeCurrent]
  have := ((frameCurrent_gradedField F hEven a).deriv_iterate L i).smul' L ((i.factorial : ℂ)⁻¹)
  rwa [show (1 : ℤ) + (i : ℤ) = (i : ℤ) + 1 from by ring] at this


theorem FrameGradedField.nprod (L : IntegralLattice) {a b : FormalDist (End ℂ (LatModuleGen L))}
    (haf : IsField a) (hbf : IsField b) {Da Db : ℤ}
    (ha : FrameGradedField L a Da) (hb : FrameGradedField L b Db) :
    FrameGradedField L (VOA.nprod haf hbf) (Da + Db) := by
  intro s q x hx
  rw [nprod_apply]
  refine finsum_lattice_submodule L _ _
    (normalOrdered_diag_support_finite haf hbf s x) (fun m => ?_)
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, Module.End.mul_apply]
    have hb' := hb (s - m) q x hx
    have ha' := ha m (Db + q + (s - m)) _ hb'
    rwa [show Da + (Db + q + (s - m)) + m = Da + Db + q + s from by ring] at ha'
  · rw [if_neg h0, Module.End.mul_apply]
    have ha' := ha m q x hx
    have hb' := hb (s - m) (Da + q + m) _ ha'
    rwa [show Db + (Da + q + m) + (s - m) = Da + Db + q + s from by ring] at hb'


noncomputable def latticeWordWeight (L : IntegralLattice) : List (ℕ × Fin (rank L)) → L.carrier → ℤ
  | [], α => halfNorm L α
  | (ia :: rest), α => ((ia.1 : ℤ) + 1) + latticeWordWeight L rest α

@[simp] theorem latticeWordWeight_nil (α : L.carrier) : latticeWordWeight L [] α = halfNorm L α := rfl


theorem latticeWordWeight_cons (L : IntegralLattice) (ia : ℕ × Fin (rank L)) (rest : List (ℕ × Fin (rank L))) (α : L.carrier) :
    latticeWordWeight L (ia :: rest) α = ((ia.1 : ℤ) + 1) + latticeWordWeight L rest α := rfl


theorem frameWordField_gradedField (hEven : L.Even)  :
    ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      FrameGradedField L (frameWordField F l α) (latticeWordWeight L l α)
  | [], α => by rw [frameWordField_nil, latticeWordWeight_nil]; exact canonicalChargedField_gradedField F hEven α
  | (ia :: rest), α => by
      rw [frameWordField_cons, latticeWordWeight_cons]
      exact FrameGradedField.nprod L (frameDerivativeCurrent_isField F ia.2 ia.1)
        (frameWordField_isField F rest α) (frameDerivativeCurrent_gradedField F hEven ia.2 ia.1)
        (frameWordField_gradedField hEven rest α)


noncomputable def homogeneousWordSpan (L : IntegralLattice) (q : ℤ) : Submodule ℂ (LatModuleGen L) :=
  Submodule.span ℂ {x | ∃ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
    latticeWordWeight L l α = q ∧ frameWordState L l α = x}


theorem latticeWordWeight_eq_sum (L : IntegralLattice) (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    latticeWordWeight L l α = ((HeisenbergN.wordWeightNN l : ℕ) : ℤ) + halfNorm L α := by
  induction l with
  | nil => rw [latticeWordWeight_nil, HeisenbergN.wordWeightNN]; simp
  | cons ia rest ih =>
      rw [latticeWordWeight_cons, ih]
      simp only [HeisenbergN.wordWeightNN, List.map_cons, List.sum_cons]
      push_cast; ring


theorem latticeWordWeight_monoWordN (L : IntegralLattice) (a : (ℕ × Fin (rank L)) →₀ ℕ) (α : L.carrier) :
    latticeWordWeight L (HeisenbergN.monoWordN a) α
      = ((Finsupp.weight HeisenbergN.weightFnN a : ℕ) : ℤ) + halfNorm L α := by
  rw [latticeWordWeight_eq_sum, HeisenbergN.wordWeightNN_monoWordN_eq_weight]


theorem monomial_tmul_mem_homogeneousWordSpan (L : IntegralLattice) (a : (ℕ × Fin (rank L)) →₀ ℕ) (w : ℕ) (α : L.carrier)
    (ha : Finsupp.weight HeisenbergN.weightFnN a = w) :
    (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eGen L α ∈ homogeneousWordSpan L ((w : ℤ) + halfNorm L α) := by
  have hword : frameWordState L (HeisenbergN.monoWordN a) α
      = (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eGen L α := by
    rw [frameWordState_eq, HeisenbergN.wordStateN_monoWordN]
  rw [← hword]
  refine Submodule.subset_span ⟨HeisenbergN.monoWordN a, α, ?_, rfl⟩
  rw [latticeWordWeight_monoWordN, ha]


theorem mkEα_mem_homogeneousWordSpan (L : IntegralLattice) (w : ℕ) (α : L.carrier) {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingWN (rank L) w) :
    mkEα L α p ∈ homogeneousWordSpan L ((w : ℤ) + halfNorm L α) := by
  classical
  rw [mkEα_apply, ← MvPolynomial.support_sum_monomial_coeff p, TensorProduct.sum_tmul]
  refine Submodule.sum_mem _ (fun a ha => ?_)
  rw [show (MvPolynomial.monomial a (MvPolynomial.coeff a p))
        = (MvPolynomial.coeff a p) • MvPolynomial.monomial a (1 : ℂ) from by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
    ← TensorProduct.smul_tmul' (MvPolynomial.coeff a p) (MvPolynomial.monomial a (1 : ℂ)) (eGen L α)]
  refine Submodule.smul_mem _ _ ?_
  have hwa : Finsupp.weight HeisenbergN.weightFnN a = w := by
    rw [HeisenbergN.mem_gradingWN] at hp
    exact hp (by rw [MvPolynomial.coeff]; exact Finsupp.mem_support_iff.mp ha)
  exact monomial_tmul_mem_homogeneousWordSpan L a w α hwa


theorem gradingLatGen_le_homogeneousWordSpan (L : IntegralLattice) (hEven : L.Even)  (q : ℤ) :
    gradingLatGen L q ≤ homogeneousWordSpan L q := by
  rw [latticeWeightGrading_eq_positiveFiber L q]
  refine iSup_le (fun p' => iSup_le (fun hp' => ?_))
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨hfib, hpos⟩ := hp'
  obtain ⟨w, hw⟩ : ∃ w : ℕ, p'.1 = (w : ℤ) := ⟨p'.1.toNat, by omega⟩
  have hzW : z ∈ HeisenbergN.gradingWN (rank L) w := by
    rw [hw, HeisenbergN.gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at hz; exact hz
  have := mkEα_mem_homogeneousWordSpan L w p'.2 hzW
  rwa [show (w : ℤ) + halfNorm L p'.2 = q from by rw [← hfib, hw]] at this


theorem FrameGradedField.of_HSpan (hEven : L.Even) 
    {a : LatModuleGen L → FormalDist (End ℂ (LatModuleGen L))}
    (hgen : ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      a (frameWordState L l α) = frameWordField F l α)
    (hlin : ∀ (x y : LatModuleGen L), a (x + y) = a x + a y)
    (hsmul : ∀ (c : ℂ) (x : LatModuleGen L), a (c • x) = c • a x)
    (hzero : a 0 = 0)
    (p : ℤ) {u : LatModuleGen L} (hu : u ∈ homogeneousWordSpan L p) :
    FrameGradedField L (a u) p := by
  induction hu using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, α, hl, rfl⟩ := hz
      rw [hgen, ← hl]; exact frameWordField_gradedField F hEven l α
  | zero => rw [hzero]; exact FrameGradedField.zero L
  | add x y _ _ ihx ihy => rw [hlin]; exact FrameGradedField.add L ihx ihy
  | smul c x _ ihx => rw [hsmul]; exact FrameGradedField.smul' L c ihx


theorem frameStateField_gradedField_of_mem (hEven : L.Even)  {p : ℤ} {u : LatModuleGen L}
    (hu : u ∈ gradingLatGen L p) :
    FrameGradedField L (frameStateField F hEven u) p :=
  FrameGradedField.of_HSpan F hEven (frameStateField_word F hEven)
    (fun x y => map_add (frameStateField F hEven) x y)
    (fun c x => map_smul (frameStateField F hEven) c x)
    (map_zero (frameStateField F hEven)) p (gradingLatGen_le_homogeneousWordSpan L hEven p hu)


theorem frameStateField_grading_mode (hEven : L.Even)  {p q : ℤ} (u : LatModuleGen L)
    (hu : u ∈ gradingLatGen L p) (v : LatModuleGen L) (hv : v ∈ gradingLatGen L q) (j : ℤ) :
    mode (frameStateField F hEven u) j v ∈ gradingLatGen L (p + q - j - 1) := by
  rw [mode_apply]
  have := frameStateField_gradedField_of_mem F hEven hu (-j - 1) q v hv
  rwa [show p + q + (-j - 1) = p + q - j - 1 from by ring] at this


end VOA.Moonshine.ConwayNorton
