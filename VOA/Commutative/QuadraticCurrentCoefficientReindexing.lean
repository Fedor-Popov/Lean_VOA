/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QuadraticJetCoefficientPairing
import VOA.Commutative.QuadraticCurrentGradedCarrier
import VOA.Commutative.ModeParticlePolynomial
import Mathlib.Data.Finsupp.Multiset

/-!
# Colored mode coefficients as tensor-valued current polynomials

A tensor component specifies the color of each labelled particle. Its polynomial
coefficient at a labelled tuple of modes is the value on the corresponding
commutative jet monomial. The construction retains exactly particle number and
derivative degree; simultaneous root/tensor permutation is automatic.
-/

namespace VOA.QuadraticCurrentCoefficientReindexing

open VOA.FiniteJet VOA.ModeParticlePairing
open VOA.ModeParticlePolynomial VOA.QuadraticJetCoefficientPairing
open VOA.QuadraticCurrentFunctionalCarrier VOA.DeligneAuxiliaryCollision
open scoped BigOperators

noncomputable section

variable {K σ ρ : Type*} [Field K]

/-- The commutative jet monomial obtained by forgetting the labels of colored modes. -/
def coloredExponent {N m : ℕ} (t : Fin m → σ) (a : Fin m → Fin (N + 1)) :
    JetVar σ N →₀ ℕ :=
  ∑ i, Finsupp.single ⟨t i, a i⟩ 1

/-- Forgetting labels records exactly one generator per particle. -/
theorem coloredExponent_particleDegree {N m : ℕ}
    (t : Fin m → σ) (a : Fin m → Fin (N + 1)) :
    Finsupp.weight (fun _ : JetVar σ N => 1) (coloredExponent t a) = m := by
  simp [coloredExponent, map_sum, Finsupp.weight_single]

/-- The derivative degree is the sum of all labelled modes. -/
theorem coloredExponent_derivativeDegree {N m : ℕ}
    (t : Fin m → σ) (a : Fin m → Fin (N + 1)) :
    Finsupp.weight (fun v : JetVar σ N => v.order.val) (coloredExponent t a) =
      ∑ i, (a i).val := by
  simp [coloredExponent, map_sum, Finsupp.weight_single]

/-- Root exponents and commutative jet exponents have the same derivative degree. -/
theorem labelledExponent_derivativeDegree {N m : ℕ} (a : Fin m → Fin (N + 1)) :
    Finsupp.weight (fun _ : Fin m => 1) (labelledExponent a) = ∑ i, (a i).val := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp
  · simp

/-- Simultaneous permutations of colors and modes do not change the jet monomial. -/
theorem coloredExponent_relabel {N m : ℕ} (g : Equiv.Perm (Fin m))
    (t : Fin m → σ) (a : Fin m → Fin (N + 1)) :
    coloredExponent (t ∘ g.symm) (relabelModeTuple g a) = coloredExponent t a := by
  exact g.symm.sum_comp (fun i => Finsupp.single (⟨t i, a i⟩ : JetVar σ N) 1)

/-- A concrete tensor polynomial, with no quotient or presumed carrier identification. -/
def tensorPolynomial {N m : ℕ} (F : (JetVar σ N →₀ ℕ) → K) :
    TensorPolynomial (K := K) (σ := σ) m 0 :=
  fun t => ∑ a : Fin m → Fin (N + 1),
    MvPolynomial.monomial (labelledExponent a) (F (coloredExponent t a))

/-- Every labelled coefficient is exactly the prescribed commutative coefficient. -/
theorem coeff_tensorPolynomial {N m : ℕ} (F : (JetVar σ N →₀ ℕ) → K)
    (t : Fin m → σ) (a : Fin m → Fin (N + 1)) :
    MvPolynomial.coeff (labelledExponent a) (tensorPolynomial F t) =
      F (coloredExponent t a) := by
  classical
  rw [tensorPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    rw [if_neg (fun h => hba (labelledExponent_injective h))]
  · simp

/-- The finite jet cutoff gives a literal bound on every labelled exponent. -/
theorem tensorPolynomial_supported {N m : ℕ} (F : (JetVar σ N →₀ ℕ) → K)
    (t : Fin m → σ) : IsSupportedOnJetTuples N m (tensorPolynomial F t) := by
  intro e he
  classical
  rw [tensorPolynomial, MvPolynomial.coeff_sum] at he
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  rw [MvPolynomial.coeff_monomial] at ha
  split at ha
  · rename_i h
    exact ⟨a, h.symm⟩
  · simp at ha

/-- Simultaneous permutation acts on the tensor indices as required by commutativity. -/
theorem tensorPolynomial_rename {N m : ℕ} (F : (JetVar σ N →₀ ℕ) → K)
    (g : Equiv.Perm (Fin m)) (t : Fin m → σ) :
    MvPolynomial.rename g (tensorPolynomial F t) = tensorPolynomial F (t ∘ g.symm) := by
  classical
  rw [tensorPolynomial, map_sum]
  simp_rw [MvPolynomial.rename_monomial, mapDomain_labelledExponent]
  calc
    (∑ a, MvPolynomial.monomial (labelledExponent (relabelModeTuple g a))
        (F (coloredExponent t a))) =
      ∑ a, MvPolynomial.monomial (labelledExponent (relabelModeTuple g a))
        (F (coloredExponent (t ∘ g.symm) (relabelModeTuple g a))) := by
          simp only [coloredExponent_relabel]
    _ = _ := Equiv.sum_comp (relabelModeTuple g)
      (fun a => MvPolynomial.monomial (labelledExponent a)
        (F (coloredExponent (t ∘ g.symm) a)))

/-- The exact symmetry predicate used by the current functional carrier holds. -/
theorem tensorPolynomial_symmetric {N m : ℕ} (F : (JetVar σ N →₀ ℕ) → K) :
    Symmetric (tensorPolynomial (m := m) F) := by
  intro e g heg t
  have he : e = g := by
    apply Equiv.ext
    intro i
    exact heg i
  rw [he]
  exact tensorPolynomial_rename F g t

/-- Coefficient families supported at a fixed particle number and derivative degree. -/
def SupportedBidegree (N m r : ℕ) (F : (JetVar σ N →₀ ℕ) → K) : Prop :=
  ∀ e, F e ≠ 0 →
    Finsupp.weight (fun _ : JetVar σ N => 1) e = m ∧
    Finsupp.weight (fun v : JetVar σ N => v.order.val) e = r

/-- Derivative degree of the coefficient family becomes ordinary polynomial degree. -/
theorem tensorPolynomial_homogeneous {N m r : ℕ} (F : (JetVar σ N →₀ ℕ) → K)
    (hF : SupportedBidegree N m r F) (t : Fin m → σ) :
    (tensorPolynomial F t).IsWeightedHomogeneous (fun _ => 1) r := by
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro a ha
  by_cases h : F (coloredExponent t a) = 0
  · rw [h, MvPolynomial.monomial_zero]
    exact MvPolynomial.isWeightedHomogeneous_zero K _ _
  · apply MvPolynomial.isWeightedHomogeneous_monomial
    rw [labelledExponent_derivativeDegree]
    exact (coloredExponent_derivativeDegree t a).symm.trans (hF _ h).2

/-- Counting a labelled tuple by singleton exponents is its multiset multiplicity function. -/
theorem sum_single_eq_toFinsupp_ofFn {α : Type*} [DecidableEq α] {m : ℕ} (f : Fin m → α) :
    (∑ i, Finsupp.single (f i) 1) = Multiset.toFinsupp (↑(List.ofFn f) : Multiset α) := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ, List.ofFn_succ]
    rw [ih]
    ext x
    simp only [Finsupp.add_apply, Multiset.toFinsupp_apply, Multiset.coe_count,
      Finsupp.single_apply, List.count_cons, beq_iff_eq]
    by_cases hx : f 0 = x <;> simp only [hx, if_true, if_false, add_comm]

/-- Every commutative exponent of particle number `m` admits colored labelled modes.
This supplies the actual spanning statement needed for injectivity. -/
theorem exists_coloredExponent {N m : ℕ} (e : JetVar σ N →₀ ℕ)
    (he : Finsupp.weight (fun _ : JetVar σ N => 1) e = m) :
    ∃ (t : Fin m → σ) (a : Fin m → Fin (N + 1)), coloredExponent t a = e := by
  classical
  have he' : e.sum (fun _ => id) = m := by
    simpa only [Finsupp.weight_apply, smul_eq_mul, mul_one, Function.id_def] using he
  let s : Sym (JetVar σ N) m := (Sym.equivNatSum (JetVar σ N) m).symm ⟨e, he'⟩
  let v := Quotient.out (Sym.symEquivSym' s)
  have hv : Sym.ofVector (List.Vector.ofFn v.get) = s := by
    apply Sym.symEquivSym'.injective
    change Quotient.mk'' (List.Vector.ofFn v.get) = Sym.symEquivSym' s
    rw [show List.Vector.ofFn v.get = v by
      apply List.Vector.ext
      intro i
      simp]
    exact Quotient.out_eq _
  refine ⟨fun i => (v.get i).generator, fun i => (v.get i).order, ?_⟩
  have hv' := congrArg (fun z : Sym (JetVar σ N) m => (Sym.equivNatSum (JetVar σ N) m z).1) hv
  dsimp only at hv'
  have hs : (Sym.equivNatSum (JetVar σ N) m s).1 = e := by
    simp [s]
  rw [hs] at hv'
  change (∑ i, Finsupp.single (v.get i) 1) = e
  rw [sum_single_eq_toFinsupp_ofFn, ← hv']
  ext x
  rw [Sym.coe_equivNatSum_apply_apply]
  change Multiset.count x (↑(List.ofFn v.get) : Multiset (JetVar σ N)) =
    Multiset.count x (↑(List.Vector.toList (List.Vector.ofFn v.get)) : Multiset (JetVar σ N))
  rw [List.Vector.toList_ofFn]

/-- On one fixed particle sector the concrete tensor realization loses no information. -/
theorem tensorPolynomial_injective_on_particleSector {N m : ℕ}
    (F G : (JetVar σ N →₀ ℕ) → K)
    (hF : ∀ e, Finsupp.weight (fun _ : JetVar σ N => 1) e ≠ m → F e = 0)
    (hG : ∀ e, Finsupp.weight (fun _ : JetVar σ N => 1) e ≠ m → G e = 0)
    (h : tensorPolynomial (m := m) F = tensorPolynomial (m := m) G) : F = G := by
  funext e
  by_cases he : Finsupp.weight (fun _ : JetVar σ N => 1) e = m
  · obtain ⟨t, a, rfl⟩ := exists_coloredExponent e he
    have hc := congrArg (MvPolynomial.coeff (labelledExponent a)) (congrFun h t)
    simpa only [coeff_tensorPolynomial] using hc
  · rw [hF e he, hG e he]

/-- Equality of multiplicity functions means that two labelled tuples differ by a
permutation. The proof matches the finite fibers, including repeated entries. -/
theorem exists_perm_of_sum_single_eq {α : Type*} {m : ℕ} (f g : Fin m → α)
    (h : (∑ i, Finsupp.single (f i) 1 : α →₀ ℕ) = ∑ i, Finsupp.single (g i) 1) :
    ∃ e : Equiv.Perm (Fin m), ∀ i, g (e i) = f i := by
  classical
  have hcard (x : α) : Fintype.card {i // f i = x} = Fintype.card {i // g i = x} := by
    have hx := congrArg (fun q : α →₀ ℕ => q x) h
    simpa only [Finsupp.finsetSum_apply, Finsupp.single_apply,
      Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter] using hx
  let e (x : α) := Fintype.equivOfCardEq (hcard x)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

/-- The fibers of the colored exponent map are exactly simultaneous permutation orbits. -/
theorem coloredExponent_eq_iff {N m : ℕ} (t u : Fin m → σ)
    (a b : Fin m → Fin (N + 1)) :
    coloredExponent t a = coloredExponent u b ↔
      ∃ g : Equiv.Perm (Fin m), u = t ∘ g.symm ∧ b = relabelModeTuple g a := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := exists_perm_of_sum_single_eq
      (fun i => (⟨t i, a i⟩ : JetVar σ N)) (fun i => (⟨u i, b i⟩ : JetVar σ N)) h
    refine ⟨g, ?_, ?_⟩
    · funext i
      simpa using congrArg JetVar.generator (hg (g.symm i))
    · funext i
      simpa using congrArg JetVar.order (hg (g.symm i))
  · rintro ⟨g, rfl, rfl⟩
    exact (coloredExponent_relabel g t a).symm

/-- Tensor symmetry makes polynomial coefficient extraction independent of the chosen
labelling of a commutative jet monomial. -/
theorem coefficient_eq_of_coloredExponent_eq {N m : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m 0) (hp : Symmetric p)
    (t u : Fin m → σ) (a b : Fin m → Fin (N + 1))
    (h : coloredExponent t a = coloredExponent u b) :
    MvPolynomial.coeff (labelledExponent a) (p t) =
      MvPolynomial.coeff (labelledExponent b) (p u) := by
  obtain ⟨g, rfl, rfl⟩ := (coloredExponent_eq_iff t u a b).mp h
  have hg := hp g g (by intro i; rfl) t
  rw [← hg, ← mapDomain_labelledExponent]
  exact (MvPolynomial.coeff_rename_mapDomain g g.injective (p t) (labelledExponent a)).symm

/-- Choose a labelling only after verifying that the particle number is correct. -/
def exponentLabelling {N m : ℕ} (e : JetVar σ N →₀ ℕ)
    (he : Finsupp.weight (fun _ : JetVar σ N => 1) e = m) :
    (Fin m → σ) × (Fin m → Fin (N + 1)) :=
  ⟨(exists_coloredExponent e he).choose, (exists_coloredExponent e he).choose_spec.choose⟩

theorem coloredExponent_exponentLabelling {N m : ℕ} (e : JetVar σ N →₀ ℕ)
    (he : Finsupp.weight (fun _ : JetVar σ N => 1) e = m) :
    coloredExponent (exponentLabelling e he).1 (exponentLabelling e he).2 = e :=
  (exists_coloredExponent e he).choose_spec.choose_spec

/-- Read back a tensor polynomial as commutative monomial coefficients, extended by zero
off its particle sector. Symmetry will prove independence of the chosen labelling. -/
def coefficientsOfTensor {N m : ℕ} (p : TensorPolynomial (K := K) (σ := σ) m 0) :
    (JetVar σ N →₀ ℕ) → K :=
  fun e => if he : Finsupp.weight (fun _ : JetVar σ N => 1) e = m then
    MvPolynomial.coeff (labelledExponent (exponentLabelling e he).2)
      (p (exponentLabelling e he).1) else 0

/-- Coefficient readback is independent of labelling, including all repeated modes/colors. -/
theorem coefficientsOfTensor_coloredExponent {N m : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m 0) (hp : Symmetric p)
    (t : Fin m → σ) (a : Fin m → Fin (N + 1)) :
    coefficientsOfTensor p (coloredExponent t a) =
      MvPolynomial.coeff (labelledExponent a) (p t) := by
  rw [coefficientsOfTensor, dif_pos (coloredExponent_particleDegree t a)]
  exact coefficient_eq_of_coloredExponent_eq p hp _ t _ a
    (coloredExponent_exponentLabelling _ _)

/-- Tensor readback has exactly the expected two degrees. -/
theorem coefficientsOfTensor_supportedBidegree {N m r : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m 0)
    (hp : ∀ t, (p t).IsWeightedHomogeneous (fun _ => 1) r) :
    SupportedBidegree N m r (coefficientsOfTensor p) := by
  intro e he
  unfold coefficientsOfTensor at he
  split at he
  · rename_i hm
    refine ⟨hm, ?_⟩
    rw [← coloredExponent_exponentLabelling e hm, coloredExponent_derivativeDegree]
    exact (labelledExponent_derivativeDegree _).symm.trans (hp _ he)
  · exact False.elim (he rfl)

/-- Reconstruct every tensor polynomial supported on the finite mode box from readback. -/
theorem tensorPolynomial_coefficientsOfTensor {N m : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m 0) (hp : Symmetric p)
    (hs : ∀ t, IsSupportedOnJetTuples N m (p t)) :
    tensorPolynomial (coefficientsOfTensor (N := N) p) = p := by
  funext t
  apply MvPolynomial.ext
  intro e
  by_cases he : MvPolynomial.coeff e (p t) = 0
  · rw [he]
    by_contra h
    obtain ⟨a, rfl⟩ := tensorPolynomial_supported (coefficientsOfTensor (N := N) p) t e h
    rw [coeff_tensorPolynomial, coefficientsOfTensor_coloredExponent p hp, he] at h
    exact h rfl
  · obtain ⟨a, rfl⟩ := hs t e he
    rw [coeff_tensorPolynomial, coefficientsOfTensor_coloredExponent p hp]

/-- A homogeneous polynomial of degree at most `N` automatically lies in the finite mode
box. Thus no cutoff condition remains on the stable degree pieces. -/
theorem homogeneous_supportedOnJetTuples {N m r : ℕ} (p : MvPolynomial (Fin m) K)
    (hp : p.IsWeightedHomogeneous (fun _ => 1) r) (hr : r ≤ N) :
    IsSupportedOnJetTuples N m p := by
  intro e he
  have hw := hp he
  have hi (i : Fin m) : e i < N + 1 := by
    have hle := Finsupp.le_weight (fun _ : Fin m => 1) (s := i) one_ne_zero e
    omega
  refine ⟨fun i => ⟨e i, hi i⟩, ?_⟩
  ext i
  simp

/-- The finite coefficient space in one particle/derivative bidegree. -/
def fixedCoefficientSpace (N m r : ℕ) : Submodule K ((JetVar σ N →₀ ℕ) → K) where
  carrier := {F | SupportedBidegree N m r F}
  zero_mem' := by intro e he; exact False.elim (he rfl)
  add_mem' := by
    intro F G hF hG e he
    by_cases hz : F e = 0
    · exact hG e (by simpa [hz] using he)
    · exact hF e hz
  smul_mem' := by
    intro a F hF e he
    apply hF e
    intro hz
    exact he (by simp [hz])

/-- Homogeneous tensor polynomials with simultaneous root/tensor symmetry. -/
def homogeneousSymmetricSpace (m r : ℕ) :
    Submodule K (TensorPolynomial (K := K) (σ := σ) m 0) where
  carrier := {p | Symmetric p ∧ ∀ t, (p t).IsWeightedHomogeneous (fun _ => 1) r}
  zero_mem' := ⟨by intro e g he t; simp, fun _ =>
    MvPolynomial.isWeightedHomogeneous_zero K _ _⟩
  add_mem' := by
    intro p q hp hq
    exact ⟨by intro e g he t; simp only [Pi.add_apply, map_add, hp.1 e g he t, hq.1 e g he t],
      fun t => (hp.2 t).add (hq.2 t)⟩
  smul_mem' := by
    intro a p hp
    refine ⟨?_, fun t => (MvPolynomial.weightedHomogeneousSubmodule K (fun _ => 1) r).smul_mem
      a (hp.2 t)⟩
    intro e g he t
    simpa using congrArg (fun f => a • f) (hp.1 e g he t)

/-- The concrete coefficient reindexing, with both gradings retained. -/
def fixedReindexingMap (N m r : ℕ) :
    fixedCoefficientSpace (K := K) (σ := σ) N m r →ₗ[K]
      homogeneousSymmetricSpace (K := K) (σ := σ) m r where
  toFun F := ⟨tensorPolynomial F.1, tensorPolynomial_symmetric F.1,
    tensorPolynomial_homogeneous F.1 F.2⟩
  map_add' F G := by
    apply Subtype.ext
    funext t
    simp only [tensorPolynomial, Submodule.coe_add, Pi.add_apply,
      map_add, Finset.sum_add_distrib]
  map_smul' a F := by
    apply Subtype.ext
    funext t
    simp only [tensorPolynomial, Submodule.coe_smul, Pi.smul_apply,
      MvPolynomial.smul_monomial, Finset.smul_sum, RingHom.id_apply]

/-- The stable fixed-degree map is bijective, proved by coefficient reconstruction. -/
theorem fixedReindexingMap_bijective (N m r : ℕ) (hr : r ≤ N) :
    Function.Bijective (fixedReindexingMap (K := K) (σ := σ) N m r) := by
  constructor
  · intro F G h
    apply Subtype.ext
    apply tensorPolynomial_injective_on_particleSector F.1 G.1
    · intro e he
      by_contra hn
      exact he (F.2 e hn).1
    · intro e he
      by_contra hn
      exact he (G.2 e hn).1
    · exact congrArg Subtype.val h
  · intro p
    refine ⟨⟨coefficientsOfTensor p.1, coefficientsOfTensor_supportedBidegree p.1 p.2.2⟩, ?_⟩
    apply Subtype.ext
    exact tensorPolynomial_coefficientsOfTensor p.1 p.2.1
      (fun t => homogeneous_supportedOnJetTuples (p.1 t) (p.2.2 t) hr)

/-- The exact fixed-bidegree coefficient/tensor equivalence. It is valid for all quadratic
presentations' ambient spaces, without any Lie-theoretic or characteristic-zero input.
Restricting this equivalence to quadratic convolution/collision kernels is a further step. -/
def fixedReindexingEquiv (N m r : ℕ) (hr : r ≤ N) :
    fixedCoefficientSpace (K := K) (σ := σ) N m r ≃ₗ[K]
      homogeneousSymmetricSpace (K := K) (σ := σ) m r :=
  LinearEquiv.ofBijective (fixedReindexingMap N m r) (fixedReindexingMap_bijective N m r hr)

end

end VOA.QuadraticCurrentCoefficientReindexing

section AxiomAudit
#print axioms VOA.QuadraticCurrentCoefficientReindexing.tensorPolynomial_symmetric
#print axioms VOA.QuadraticCurrentCoefficientReindexing.tensorPolynomial_homogeneous
open VOA.QuadraticCurrentCoefficientReindexing in
#print axioms tensorPolynomial_injective_on_particleSector
#print axioms VOA.QuadraticCurrentCoefficientReindexing.fixedReindexingEquiv
end AxiomAudit
