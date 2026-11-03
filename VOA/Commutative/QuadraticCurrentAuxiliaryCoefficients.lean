/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QuadraticCurrentFunctionalCarrier
import Mathlib.GroupTheory.Perm.Finite

/-!
# Extracting auxiliary coefficients from quadratic current carriers

Separate the auxiliary roots from the current roots. The coefficients in the
auxiliary roots obey the same quadratic current equations. This is a literal
polynomial statement, with no freeness or representation-theoretic assumption.
-/

namespace VOA.QuadraticCurrentAuxiliaryCoefficients

open VOA.CollisionCommonFactors
open VOA.DeligneAuxiliaryCollision
open VOA.QuadraticCurrentFunctionalCarrier

noncomputable section

variable {K σ ρ : Type*} [Field K] [Fintype σ]

/-- Auxiliary roots are polynomial variables; current roots are coefficients. -/
def split (m d : ℕ) :
    MvPolynomial (Particle m d) K ≃ₐ[K]
      MvPolynomial (Fin d) (MvPolynomial (Fin m) K) :=
  (MvPolynomial.renameEquiv K
    (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin m) (Fin d)))).trans
      (MvPolynomial.sumAlgEquiv K (Fin d) (Fin m))

@[simp] theorem split_current_X (m d : ℕ) (i : Fin m) :
    split (K := K) m d (MvPolynomial.X (i.castAdd d)) =
      MvPolynomial.C (MvPolynomial.X i) := by
  simp [split, MvPolynomial.renameEquiv_apply]

@[simp] theorem split_auxiliary_X (m d : ℕ) (i : Fin d) :
    split (K := K) m d (MvPolynomial.X (i.natAdd m)) = MvPolynomial.X i := by
  simp [split, MvPolynomial.renameEquiv_apply]

/-- Apply independently specified maps to the two populations of roots. -/
def particleMap {m d : ℕ} (f : Fin m → Fin m) (h : Fin d → Fin d) :
    Particle m d → Particle m d :=
  finSumFinEquiv ∘ Sum.map f h ∘ finSumFinEquiv.symm

@[simp] theorem particleMap_current {m d : ℕ} (f : Fin m → Fin m)
    (h : Fin d → Fin d) (i : Fin m) :
    particleMap f h (i.castAdd d) = (f i).castAdd d := by
  simp [particleMap]

@[simp] theorem particleMap_auxiliary {m d : ℕ} (f : Fin m → Fin m)
    (h : Fin d → Fin d) (i : Fin d) :
    particleMap f h (i.natAdd m) = (h i).natAdd m := by
  simp [particleMap]

/-- Root substitution separates into substitution of coefficients and of
auxiliary variables. The maps need not be injective, so collisions are included. -/
theorem split_rename {m d : ℕ} (f : Fin m → Fin m) (h : Fin d → Fin d)
    (p : MvPolynomial (Particle m d) K) :
    split m d (MvPolynomial.rename (particleMap f h) p) =
      MvPolynomial.rename h
        (MvPolynomial.map (MvPolynomial.rename f).toRingHom (split m d p)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [split]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i
      · simp [map_mul, hp]
      · simp [map_mul, hp]

/-- The coefficient of one auxiliary monomial, component by component. -/
def auxiliaryCoefficient {m d : ℕ} (a : Fin d →₀ ℕ)
    (p : TensorPolynomial (K := K) (σ := σ) m d) :
    TensorPolynomial (K := K) (σ := σ) m 0 :=
  fun t => MvPolynomial.coeff a (split m d (p t))

/-- Coefficient extraction commutes with every current-root substitution. -/
theorem coefficient_current_rename {m d : ℕ} (a : Fin d →₀ ℕ)
    (f : Fin m → Fin m) (p : MvPolynomial (Particle m d) K) :
    MvPolynomial.coeff a (split m d (MvPolynomial.rename (particleMap f id) p)) =
      MvPolynomial.rename f (MvPolynomial.coeff a (split m d p)) := by
  rw [split_rename]
  simp [MvPolynomial.coeff_map]

/-- A diagonal substitution retaining the original ambient variable set. -/
def diagonalEnd {I : Type*} [DecidableEq I] (i j : I) :
    MvPolynomial I K →ₐ[K] MvPolynomial I K :=
  MvPolynomial.rename (Function.update id i j)

theorem diagonalEnd_eq_rename_collision {I : Type*} [DecidableEq I]
    (i j : I) (hji : j ≠ i) (p : MvPolynomial I K) :
    diagonalEnd i j p = MvPolynomial.rename Subtype.val (collisionMap i j hji p) := by
  simp only [diagonalEnd, collisionMap, MvPolynomial.rename_rename]
  congr 2
  funext x
  by_cases hx : x = i
  · subst x; simp
  · simp [collisionIndex, hx]

theorem diagonalEnd_eq_zero_iff {I : Type*} [DecidableEq I]
    (i j : I) (hji : j ≠ i) (p : MvPolynomial I K) :
    diagonalEnd i j p = 0 ↔ collisionMap i j hji p = 0 := by
  rw [diagonalEnd_eq_rename_collision i j hji]
  rw [← map_zero (MvPolynomial.rename (Subtype.val : {x : I // x ≠ i} → I))]
  exact (MvPolynomial.rename_injective _ Subtype.val_injective).eq_iff

theorem particleMap_update {m d : ℕ} (i j : Fin m) :
    particleMap (Function.update id i j) (id : Fin d → Fin d) =
      Function.update id (i.castAdd d) (j.castAdd d) := by
  funext x
  obtain ⟨x | x, rfl⟩ := finSumFinEquiv.surjective x
  · by_cases hx : x = i
    · subst x; simp
    · simp [hx]
  · have hx : x.natAdd m ≠ i.castAdd d := by
      intro heq
      have hval := congrArg Fin.val heq
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      have := i.isLt
      omega
    simp [Function.update_of_ne hx]

/-- Auxiliary coefficients commute with literal current-current collisions. -/
theorem coefficient_diagonalEnd {m d : ℕ} (a : Fin d →₀ ℕ)
    (i j : Fin m) (p : MvPolynomial (Particle m d) K) :
    MvPolynomial.coeff a (split m d (diagonalEnd (i.castAdd d) (j.castAdd d) p)) =
      diagonalEnd i j (MvPolynomial.coeff a (split m d p)) := by
  simpa only [diagonalEnd, particleMap_update] using
    coefficient_current_rename a (Function.update id i j) p

/-- Contract a pair of tensor slots against a quadratic relation, before
identifying the corresponding current roots. -/
def contraction {m d : ℕ} (q : σ × σ → K)
    (ij : IncreasingPair (Fin m)) (t : Fin m → σ)
    (p : TensorPolynomial (K := K) (σ := σ) m d) :
    MvPolynomial (Particle m d) K :=
  ∑ xy, MvPolynomial.C (q xy) * p (insertPair ij t xy)

theorem diagonalEnd_contraction {m d : ℕ} (q : σ × σ → K)
    (ij : IncreasingPair (Fin m)) (t : Fin m → σ)
    (p : TensorPolynomial (K := K) (σ := σ) m d) :
    diagonalEnd (ij.1.1.castAdd d) (ij.1.2.castAdd d) (contraction q ij t p) =
      MvPolynomial.rename Subtype.val (currentReadback q ij t p) := by
  rw [diagonalEnd_eq_rename_collision _ _
    ((Fin.castAdd_injective m d).ne (ne_of_gt ij.2))]
  simp [contraction, currentReadback, projectedDiagonal]

theorem currentReadback_eq_zero_iff {m d : ℕ} (q : σ × σ → K)
    (ij : IncreasingPair (Fin m)) (t : Fin m → σ)
    (p : TensorPolynomial (K := K) (σ := σ) m d) :
    currentReadback q ij t p = 0 ↔
      diagonalEnd (ij.1.1.castAdd d) (ij.1.2.castAdd d) (contraction q ij t p) = 0 := by
  rw [diagonalEnd_contraction]
  exact (MvPolynomial.rename_eq_zero_iff_of_injective _ Subtype.val_injective).symm

theorem coefficient_contraction {m d : ℕ} (a : Fin d →₀ ℕ)
    (q : σ × σ → K) (ij : IncreasingPair (Fin m)) (t : Fin m → σ)
    (p : TensorPolynomial (K := K) (σ := σ) m d) :
    MvPolynomial.coeff a (split m d (contraction q ij t p)) =
      contraction q ij t (auxiliaryCoefficient a p) := by
  simp [contraction, auxiliaryCoefficient, split, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul]

/-- Every coefficient of an auxiliary monomial obeys precisely the original
current equations. This includes the converse, in all polynomial degrees. -/
theorem currentEquations_iff_coefficients {m d : ℕ} (Q : ρ → σ × σ → K)
    (p : TensorPolynomial (K := K) (σ := σ) m d) :
    CurrentEquations Q p ↔ ∀ a, CurrentEquations Q (auxiliaryCoefficient a p) := by
  constructor
  · intro hp a r ij t
    apply (currentReadback_eq_zero_iff (Q r) ij t _).mpr
    have hr := (currentReadback_eq_zero_iff (Q r) ij t p).mp (hp r ij t)
    have hc := congrArg (fun f => MvPolynomial.coeff a (split m d f)) hr
    simpa only [map_zero, MvPolynomial.coeff_zero, coefficient_diagonalEnd,
      coefficient_contraction] using hc
  · intro hp r ij t
    apply (currentReadback_eq_zero_iff (Q r) ij t p).mpr
    apply (split (K := K) m d).injective
    rw [map_zero]
    apply MvPolynomial.ext
    intro a
    rw [MvPolynomial.coeff_zero, coefficient_diagonalEnd, coefficient_contraction]
    exact (currentReadback_eq_zero_iff (Q r) ij t _).mp (hp a r ij t)

/-- Independently permute the current and auxiliary slots. -/
def particlePermutation {m d : ℕ} (g : Equiv.Perm (Fin m))
    (h : Equiv.Perm (Fin d)) : Equiv.Perm (Particle m d) :=
  finSumFinEquiv.symm.trans ((g.sumCongr h).trans finSumFinEquiv)

@[simp] theorem particlePermutation_coe {m d : ℕ} (g : Equiv.Perm (Fin m))
    (h : Equiv.Perm (Fin d)) :
    ⇑(particlePermutation g h) = particleMap g h := rfl

theorem particlePermutation_extends {m d : ℕ} (g : Equiv.Perm (Fin m))
    (h : Equiv.Perm (Fin d)) :
    ExtendsCurrentPermutation (particlePermutation g h) g := by
  intro i
  simp only [particlePermutation_coe, particleMap_current]

/-- Every allowed particle permutation splits into its two independent
population permutations. -/
theorem exists_particlePermutation_of_extends {m d : ℕ}
    (e : Equiv.Perm (Particle m d)) (g : Equiv.Perm (Fin m))
    (he : ExtendsCurrentPermutation e g) :
    ∃ h : Equiv.Perm (Fin d), e = particlePermutation g h := by
  let E : Equiv.Perm (Fin m ⊕ Fin d) :=
    finSumFinEquiv.trans (e.trans finSumFinEquiv.symm)
  have hE : Set.MapsTo E (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨g i, ?_⟩
    simp [E, he i]
  obtain ⟨⟨g', h⟩, hEq⟩ :=
    Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hE
  have heq : e = particlePermutation g' h := by
    apply Equiv.ext
    intro i
    have hx := congrArg (fun f : Equiv.Perm (Fin m ⊕ Fin d) =>
      finSumFinEquiv (f (finSumFinEquiv.symm i))) hEq
    simpa [E, particlePermutation, Equiv.Perm.sumCongrHom_apply] using hx.symm
  have hg : g' = g := by
    apply Equiv.ext
    intro i
    apply Fin.castAdd_injective m d
    have hi := he i
    rw [heq] at hi
    simpa only [particlePermutation_coe, particleMap_current] using hi
  exact ⟨h, hg ▸ heq⟩

/-- Scalar symmetry in just the auxiliary variables. -/
def AuxiliarySymmetric {m d : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m d) : Prop :=
  ∀ (h : Equiv.Perm (Fin d)) t,
    MvPolynomial.rename (particlePermutation (Equiv.refl (Fin m)) h) (p t) = p t

omit [Fintype σ] in
/-- Simultaneous symmetry of tensor indices and current roots passes to every
auxiliary coefficient. -/
theorem auxiliaryCoefficient_symmetric {m d : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m d) (hp : Symmetric p)
    (a : Fin d →₀ ℕ) : Symmetric (auxiliaryCoefficient a p) := by
  intro e g he t
  have heg : e = g := Equiv.ext (fun i => he i)
  subst e
  have hs := hp (particlePermutation g (Equiv.refl (Fin d))) g
    (particlePermutation_extends g (Equiv.refl _)) t
  have hc := congrArg (fun f => MvPolynomial.coeff a (split m d f)) hs
  simpa only [particlePermutation_coe, Equiv.coe_refl,
    coefficient_current_rename, auxiliaryCoefficient] using hc

/-- Extracting one auxiliary coefficient lands in the literal current-only
carrier. No current-character or fusion hypothesis is used. -/
theorem auxiliaryCoefficient_mem_currentCarrier {m d : ℕ}
    (Q : ρ → σ × σ → K) (p : currentCarrier Q m d) (a : Fin d →₀ ℕ) :
    auxiliaryCoefficient a p.1 ∈ currentCarrier Q m 0 :=
  ⟨auxiliaryCoefficient_symmetric p.1 p.property.1 a,
    (currentEquations_iff_coefficients Q p.1).mp p.property.2 a⟩

omit [Fintype σ] in
/-- The tensor symmetry is equivalent to current symmetry of every auxiliary
coefficient together with scalar symmetry of the auxiliary variables. -/
theorem symmetric_iff_coefficients {m d : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m d) :
    Symmetric p ↔ AuxiliarySymmetric p ∧ ∀ a, Symmetric (auxiliaryCoefficient a p) := by
  constructor
  · intro hp
    refine ⟨?_, auxiliaryCoefficient_symmetric p hp⟩
    intro h t
    simpa using hp (particlePermutation (Equiv.refl _) h) (Equiv.refl _)
      (particlePermutation_extends (Equiv.refl _) h) t
  · rintro ⟨haux, hcoeff⟩ e g he t
    obtain ⟨h, rfl⟩ := exists_particlePermutation_of_extends e g he
    apply (split (K := K) m d).injective
    rw [particlePermutation_coe, split_rename]
    have hcurrent :
        MvPolynomial.map (MvPolynomial.rename g).toRingHom (split m d (p t)) =
          split m d (p (t ∘ g.symm)) := by
      apply MvPolynomial.ext
      intro a
      rw [MvPolynomial.coeff_map]
      exact hcoeff a g g (fun _ => rfl) t
    rw [hcurrent]
    have haux' := congrArg (split (K := K) m d) (haux h (t ∘ g.symm))
    simpa [particlePermutation_coe, split_rename, MvPolynomial.map_id] using haux'

/-- Exact coefficientwise characterization of the carrier with auxiliary
variables. In particular no additional current relations appear after adjoining
the auxiliary symmetric polynomial factor. -/
theorem mem_currentCarrier_iff_coefficients {m d : ℕ}
    (Q : ρ → σ × σ → K) (p : TensorPolynomial (K := K) (σ := σ) m d) :
    p ∈ currentCarrier Q m d ↔ AuxiliarySymmetric p ∧
      ∀ a, auxiliaryCoefficient a p ∈ currentCarrier Q m 0 := by
  change Symmetric p ∧ CurrentEquations Q p ↔ _
  rw [symmetric_iff_coefficients, currentEquations_iff_coefficients]
  constructor
  · rintro ⟨⟨haux, hsym⟩, heq⟩
    exact ⟨haux, fun a => ⟨hsym a, heq a⟩⟩
  · rintro ⟨haux, h⟩
    exact ⟨⟨haux, fun a => (h a).1⟩, fun a => (h a).2⟩

/-- Coefficient extraction as a linear map between literal carriers. -/
def coefficientLinear (Q : ρ → σ × σ → K) (m d : ℕ) (a : Fin d →₀ ℕ) :
    currentCarrier Q m d →ₗ[K] currentCarrier Q m 0 where
  toFun p := ⟨auxiliaryCoefficient a p.1, auxiliaryCoefficient_mem_currentCarrier Q p a⟩
  map_add' p q := by
    apply Subtype.ext
    funext t
    simp [auxiliaryCoefficient, map_add, MvPolynomial.coeff_add]
  map_smul' c p := by
    apply Subtype.ext
    funext t
    simp [auxiliaryCoefficient, map_smul, MvPolynomial.coeff_smul]

omit [Fintype σ] in
/-- All auxiliary coefficients together determine a tensor polynomial. -/
theorem auxiliaryCoefficient_ext {m d : ℕ}
    {p q : TensorPolynomial (K := K) (σ := σ) m d}
    (h : ∀ a, auxiliaryCoefficient a p = auxiliaryCoefficient a q) : p = q := by
  funext t
  apply (split (K := K) m d).injective
  apply MvPolynomial.ext
  intro a
  exact congrFun (h a) t

/-- There are only finitely many nonzero current-valued auxiliary coefficients.
The tensor index set is finite, so the supports of its components have finite union. -/
theorem auxiliaryCoefficient_finiteSupport {m d : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m d) :
    (Function.support (fun a => auxiliaryCoefficient a p)).Finite := by
  classical
  apply (Finset.finite_toSet (Finset.univ.biUnion
    (fun t => (split m d (p t)).support))).subset
  intro a ha
  by_contra h
  apply ha
  funext t
  have ht : a ∉ (split m d (p t)).support := by
    intro ht
    exact h (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ t, ht⟩)
  exact MvPolynomial.notMem_support_iff.mp ht

private theorem coefficientLinear_finiteSupport (Q : ρ → σ × σ → K)
    (m d : ℕ) (p : currentCarrier Q m d) :
    (Function.support (fun a => coefficientLinear Q m d a p)).Finite := by
  apply (auxiliaryCoefficient_finiteSupport p.1).subset
  intro a ha hzero
  apply ha
  exact Subtype.ext hzero

/-- The canonical finite expansion in auxiliary monomials, with coefficients
in the current-only carrier. The image also obeys auxiliary permutation symmetry. -/
def coefficientsLinear (Q : ρ → σ × σ → K) (m d : ℕ) :
    currentCarrier Q m d →ₗ[K] ((Fin d →₀ ℕ) →₀ currentCarrier Q m 0) where
  toFun p := Finsupp.ofSupportFinite (fun a => coefficientLinear Q m d a p)
    (coefficientLinear_finiteSupport Q m d p)
  map_add' p q := by
    apply Finsupp.ext
    intro a
    exact (coefficientLinear Q m d a).map_add p q
  map_smul' c p := by
    apply Finsupp.ext
    intro a
    exact (coefficientLinear Q m d a).map_smul c p

theorem coefficientsLinear_injective (Q : ρ → σ × σ → K) (m d : ℕ) :
    Function.Injective (coefficientsLinear Q m d) := by
  intro p q h
  apply Subtype.ext
  apply auxiliaryCoefficient_ext
  intro a
  exact congrArg Subtype.val (DFunLike.congr_fun h a)

end

end VOA.QuadraticCurrentAuxiliaryCoefficients

section AxiomAudit
#print axioms VOA.QuadraticCurrentAuxiliaryCoefficients.currentEquations_iff_coefficients
#print axioms VOA.QuadraticCurrentAuxiliaryCoefficients.mem_currentCarrier_iff_coefficients
#print axioms VOA.QuadraticCurrentAuxiliaryCoefficients.coefficientsLinear_injective
end AxiomAudit
