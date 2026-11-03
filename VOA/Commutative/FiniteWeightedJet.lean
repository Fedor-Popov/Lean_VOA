/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.FiniteJet
import VOA.Commutative.MvPolynomialFiniteHomogeneous
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Fixed-weight stabilization for finite jet polynomial rings

Give the jet variable `x_i^(r)` weight `baseWeight i + r`.  If all base weights are positive,
then a monomial of weight `N` cannot contain a variable of jet order at least `N`.  Consequently,
the order-raising map from order `m` to order `m + 1` is an equivalence on weight `N` whenever
`N <= m`.

For presented jet quotients, this file defines the image of a polynomial weight piece and proves
that the order-raising map is surjective on these images in the stable range.  It deliberately does
not claim injectivity on quotient weight images: new jet relations can create a kernel unless a
separate graded-ideal argument rules this out.
-/

namespace VOA.FiniteJet

open scoped BigOperators

universe uσ uR

section PolynomialWeights

variable {R : Type uR} {σ : Type uσ} [CommSemiring R]

/-- Conformal weight on jet variables: the generator's base weight plus its jet order. -/
def jetWeight (baseWeight : σ → ℕ) (m : ℕ) : JetVar σ m → ℕ :=
  fun v => baseWeight v.generator + v.order

/-- The natural Li/conformal bidegree on a jet variable: derivative order in the first
coordinate and generator weight plus derivative order in the second. -/
def jetLiBidegree (baseWeight : σ → ℕ) (m : ℕ) : JetVar σ m → ℕ × ℕ :=
  fun v => (v.order, baseWeight v.generator + v.order)

/-- The first component of a jet variable’s bidegree records only how many
derivatives it carries; the base generator contributes no Li degree. -/
@[simp] theorem jetLiBidegree_fst (baseWeight : σ → ℕ) (m : ℕ) (v : JetVar σ m) :
    (jetLiBidegree baseWeight m v).1 = v.order := rfl

/-- The second component is exactly the conformal weight: the generator’s
base weight plus the number of derivatives. -/
@[simp] theorem jetLiBidegree_snd (baseWeight : σ → ℕ) (m : ℕ) (v : JetVar σ m) :
    (jetLiBidegree baseWeight m v).2 = jetWeight baseWeight m v := rfl

/-- Allowing one more derivative order does not change the weight of any
variable already present. This makes the inclusion compatible with homogeneous pieces. -/
@[simp]
theorem jetWeight_jetVarSucc (baseWeight : σ → ℕ) (m : ℕ) (v : JetVar σ m) :
    jetWeight baseWeight (m + 1) (jetVarSucc m v) = jetWeight baseWeight m v := by
  rfl

/-- The inclusion into the next jet order keeps both the generator and
derivative index, so distinct old variables remain distinct. -/
theorem jetVarSucc_injective (m : ℕ) : Function.Injective (jetVarSucc (σ := σ) m) := by
  intro v w hvw
  apply JetVar.ext
  · exact congrArg (fun u : JetVar σ (m + 1) => u.generator) hvw
  · apply Fin.ext
    exact congrArg (fun u : JetVar σ (m + 1) => u.order.val) hvw

/-- A variable in order m+1 already existed at order m exactly when its
derivative index is at most m. Only the new top derivative order is excluded. -/
theorem mem_range_jetVarSucc_iff (m : ℕ) (v : JetVar σ (m + 1)) :
    v ∈ Set.range (jetVarSucc (σ := σ) m) ↔ v.order.val ≤ m := by
  constructor
  · rintro ⟨u, rfl⟩
    exact Nat.lt_succ_iff.mp u.order.isLt
  · intro hv
    let u : JetVar σ m := ⟨v.generator, ⟨v.order.val, Nat.lt_succ_iff.mpr hv⟩⟩
    refine ⟨u, ?_⟩
    apply JetVar.ext
    · rfl
    · apply Fin.ext
      rfl

/-- Mapping a monomial's exponent function to the next jet order preserves its weighted degree. -/
theorem weight_mapDomain_jetVarSucc (baseWeight : σ → ℕ) (m : ℕ)
    (d : JetVar σ m →₀ ℕ) :
    Finsupp.weight (jetWeight baseWeight (m + 1))
        (d.mapDomain (jetVarSucc (σ := σ) m)) =
      Finsupp.weight (jetWeight baseWeight m) d := by
  classical
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index]
  · simp only [jetWeight_jetVarSucc]
  · simp
  · simp [Nat.add_mul]

/-- The weight-`N` homogeneous submodule of the order-`m` jet polynomial ring. -/
abbrev JetWeightPiece (R : Type uR) [CommSemiring R] (baseWeight : σ → ℕ) (m N : ℕ) :=
  MvPolynomial.weightedHomogeneousSubmodule R (jetWeight baseWeight m) N

/-- The polynomial submodule of exact Li degree `p` and conformal weight `N`. -/
abbrev JetLiBidegreePiece (R : Type uR) [CommSemiring R]
    (baseWeight : σ → ℕ) (m p N : ℕ) :=
  MvPolynomial.weightedHomogeneousSubmodule R (jetLiBidegree baseWeight m) (p, N)

/-- A polynomial homogeneous for the Li/conformal bidegree is homogeneous of the displayed
conformal weight after forgetting Li degree. -/
theorem isWeightedHomogeneous_jetWeight_of_jetLiBidegree
    (baseWeight : σ → ℕ) (m p N : ℕ) {f : JetPoly R σ m}
    (hf : f.IsWeightedHomogeneous (jetLiBidegree baseWeight m) (p, N)) :
    f.IsWeightedHomogeneous (jetWeight baseWeight m) N := by
  intro d hd
  have hpair := hf hd
  have hsnd := congrArg Prod.snd hpair
  simpa [Finsupp.weight_apply, Finsupp.sum, jetLiBidegree, jetWeight,
    Prod.snd_sum] using hsnd

/-- Forgetting Li degree embeds a jet bidegree piece in its conformal-weight piece. -/
noncomputable def jetLiBidegreePieceToWeightPiece
    (baseWeight : σ → ℕ) (m p N : ℕ) :
    JetLiBidegreePiece R baseWeight m p N →ₗ[R] JetWeightPiece R baseWeight m N where
  toFun f := ⟨f.1,
    isWeightedHomogeneous_jetWeight_of_jetLiBidegree baseWeight m p N f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Forgetting the Li-degree label keeps the underlying polynomial. It
therefore embeds each fixed bidegree piece into its conformal-weight piece
without identifying any distinct elements. -/
theorem jetLiBidegreePieceToWeightPiece_injective
    (baseWeight : σ → ℕ) (m p N : ℕ) :
    Function.Injective
      (jetLiBidegreePieceToWeightPiece (R := R) baseWeight m p N) := by
  intro f g h
  apply Subtype.ext
  exact congrArg
    (fun z : JetWeightPiece R baseWeight m N => z.1) h

/-- Every fixed Li/conformal bidegree in a finite positive-weight jet polynomial ring is
finite-dimensional. -/
theorem finiteDimensional_jetLiBidegreePiece
    {K : Type*} [Field K] [Finite σ]
    (baseWeight : σ → ℕ) (hpositive : ∀ i, 0 < baseWeight i)
    (m p N : ℕ) :
    FiniteDimensional K (JetLiBidegreePiece K baseWeight m p N) := by
  letI : Finite (JetVar σ m) :=
    Finite.of_injective (fun v => (v.generator, v.order)) (by
      intro v w h
      exact JetVar.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  letI : FiniteDimensional K (JetWeightPiece K baseWeight m N) :=
    VOA.MvPolynomialFiniteHomogeneous.finiteDimensional_weightedHomogeneousSubmodule
      (jetWeight baseWeight m) (fun v => by
        simp only [jetWeight]
        have h := hpositive v.generator
        omega) N
  exact FiniteDimensional.of_injective
    (jetLiBidegreePieceToWeightPiece (R := K) baseWeight m p N)
    (jetLiBidegreePieceToWeightPiece_injective (R := K) baseWeight m p N)

/-- Raising jet order preserves weighted homogeneity. -/
theorem jetOrderHom_isWeightedHomogeneous (baseWeight : σ → ℕ) (m N : ℕ)
    {p : JetPoly R σ m} (hp : p.IsWeightedHomogeneous (jetWeight baseWeight m) N) :
    (jetOrderHom (R := R) m p).IsWeightedHomogeneous (jetWeight baseWeight (m + 1)) N := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact MvPolynomial.isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial d r hd =>
      rw [jetOrderHom, MvPolynomial.rename_monomial]
      apply MvPolynomial.isWeightedHomogeneous_monomial
      rw [weight_mapDomain_jetVarSucc]
      exact hd

/-- Killing variables outside the old jet range preserves weighted homogeneity. -/
theorem killCompl_isWeightedHomogeneous (baseWeight : σ → ℕ) (m N : ℕ)
    {p : JetPoly R σ (m + 1)}
    (hp : p.IsWeightedHomogeneous (jetWeight baseWeight (m + 1)) N) :
    (MvPolynomial.killCompl (jetVarSucc_injective (σ := σ) m) p).IsWeightedHomogeneous
      (jetWeight baseWeight m) N := by
  intro d hd
  rw [MvPolynomial.coeff_killCompl] at hd
  have hweight := hp hd
  rwa [weight_mapDomain_jetVarSucc] at hweight

/-- A positive-weight monomial of total weight `N` has zero multiplicity at every jet variable
whose jet order is at least `N`. -/
theorem monomialMultiplicity_eq_zero_of_weight_le_order (baseWeight : σ → ℕ)
    (hpositive : ∀ i, 0 < baseWeight i) (m N : ℕ) (d : JetVar σ m →₀ ℕ)
    (hd : Finsupp.weight (jetWeight baseWeight m) d = N) (v : JetVar σ m)
    (hv : N ≤ v.order.val) : d v = 0 := by
  by_contra hne
  have hle := Finsupp.le_weight_of_ne_zero' (jetWeight baseWeight m) hne
  rw [hd] at hle
  have hpos := hpositive v.generator
  simp only [jetWeight] at hle
  omega

/-- In stable weight, every monomial exponent is supported on the old jet variables. -/
theorem monomialSupport_subset_range_jetVarSucc (baseWeight : σ → ℕ)
    (hpositive : ∀ i, 0 < baseWeight i) (m N : ℕ) (hlarge : N ≤ m)
    (d : JetVar σ (m + 1) →₀ ℕ)
    (hd : Finsupp.weight (jetWeight baseWeight (m + 1)) d = N) :
    ↑d.support ⊆ Set.range (jetVarSucc (σ := σ) m) := by
  intro v hv
  rw [mem_range_jetVarSucc_iff]
  by_contra horder
  have hvbound : v.order.val ≤ m + 1 := Nat.le_of_lt_succ v.order.isLt
  have htop : v.order.val = m + 1 := by omega
  have hzero := monomialMultiplicity_eq_zero_of_weight_le_order baseWeight hpositive
    (m + 1) N d hd v (by omega)
  exact Finsupp.mem_support_iff.mp hv hzero

/-- If every exponent in a polynomial is supported on old variables, killing the complement and
then raising the order recovers the polynomial. -/
theorem jetOrderHom_killCompl_eq_of_support_subset (m : ℕ) (p : JetPoly R σ (m + 1))
    (hsupport : ∀ d ∈ p.support, ↑d.support ⊆ Set.range (jetVarSucc (σ := σ) m)) :
    jetOrderHom (R := R) m
        (MvPolynomial.killCompl (jetVarSucc_injective (σ := σ) m) p) = p := by
  rw [MvPolynomial.as_sum p]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [MvPolynomial.killCompl_monomial_eq_monomial_comapDomain_of_subset
    (jetVarSucc_injective (σ := σ) m) _ (hsupport d hd)]
  rw [jetOrderHom, MvPolynomial.rename_monomial,
    d.mapDomain_comapDomain _ (jetVarSucc_injective (σ := σ) m) (hsupport d hd)]

/-- In the stable range, the complement-killing map is also a right inverse on a positive-weight
homogeneous polynomial. -/
theorem jetOrderHom_killCompl_eq_of_isWeightedHomogeneous (baseWeight : σ → ℕ)
    (hpositive : ∀ i, 0 < baseWeight i) (m N : ℕ) (hlarge : N ≤ m)
    {p : JetPoly R σ (m + 1)}
    (hp : p.IsWeightedHomogeneous (jetWeight baseWeight (m + 1)) N) :
    jetOrderHom (R := R) m
        (MvPolynomial.killCompl (jetVarSucc_injective (σ := σ) m) p) = p := by
  apply jetOrderHom_killCompl_eq_of_support_subset
  intro d hd
  exact monomialSupport_subset_range_jetVarSucc baseWeight hpositive m N hlarge d
    (hp (MvPolynomial.mem_support_iff.mp hd))

/-- The order-raising map restricted to a fixed weight. -/
noncomputable def jetWeightPieceOrderHom (baseWeight : σ → ℕ) (m N : ℕ) :
    JetWeightPiece R baseWeight m N →ₗ[R] JetWeightPiece R baseWeight (m + 1) N where
  toFun p := ⟨jetOrderHom (R := R) m p.1,
    jetOrderHom_isWeightedHomogeneous baseWeight m N p.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul (jetOrderHom (R := R) m).toLinearMap _ _)

/-- Including the old variables into a larger polynomial ring loses no
polynomial information, even before the stable-weight range is reached.
This proves injectivity on each fixed-weight piece of the polynomial ring. -/
theorem jetWeightPieceOrderHom_injective (baseWeight : σ → ℕ) (m N : ℕ) :
    Function.Injective (jetWeightPieceOrderHom (R := R) baseWeight m N) := by
  intro p q hpq
  apply Subtype.ext
  apply MvPolynomial.rename_injective (jetVarSucc (σ := σ) m)
    (jetVarSucc_injective (σ := σ) m)
  exact congrArg Subtype.val hpq

/-- Once `N <= m`, every target weight-`N` polynomial already comes from order `m`. -/
theorem jetWeightPieceOrderHom_surjective (baseWeight : σ → ℕ)
    (hpositive : ∀ i, 0 < baseWeight i) (m N : ℕ) (hlarge : N ≤ m) :
    Function.Surjective (jetWeightPieceOrderHom (R := R) baseWeight m N) := by
  intro p
  let q : JetWeightPiece R baseWeight m N :=
    ⟨MvPolynomial.killCompl (jetVarSucc_injective (σ := σ) m) p.1,
      killCompl_isWeightedHomogeneous baseWeight m N p.2⟩
  refine ⟨q, ?_⟩
  apply Subtype.ext
  exact jetOrderHom_killCompl_eq_of_isWeightedHomogeneous baseWeight hpositive m N hlarge p.2

/-- Fixed positive-weight pieces of successive finite jet polynomial rings stabilize. -/
noncomputable def jetWeightPieceOrderEquiv (baseWeight : σ → ℕ)
    (hpositive : ∀ i, 0 < baseWeight i) (m N : ℕ) (hlarge : N ≤ m) :
    JetWeightPiece R baseWeight m N ≃ₗ[R] JetWeightPiece R baseWeight (m + 1) N :=
  LinearEquiv.ofBijective (jetWeightPieceOrderHom (R := R) baseWeight m N)
    ⟨jetWeightPieceOrderHom_injective baseWeight m N,
      jetWeightPieceOrderHom_surjective baseWeight hpositive m N hlarge⟩

end PolynomialWeights

section PresentedWeightImages

variable {R : Type uR} {σ : Type uσ} [CommRing R]

/-- The image in a presented jet quotient of polynomial representatives homogeneous of weight
`N`.  Without a homogeneous-ideal hypothesis, this is only an image submodule, not a grading. -/
noncomputable def PresentedJetWeightImage (baseWeight : σ → ℕ) (m N : ℕ)
    (I : Ideal (MvPolynomial σ R)) : Submodule R (PresentedJet (R := R) m I) :=
  LinearMap.range ((presentedJetMk (R := R) m I).toLinearMap.comp
    (Submodule.subtype (JetWeightPiece R baseWeight m N)))

/-- The image in a presented jet quotient of representatives of exact Li/conformal
bidegree `(p,N)`. -/
noncomputable def PresentedJetLiBidegreeImage (baseWeight : σ → ℕ) (m p N : ℕ)
    (I : Ideal (MvPolynomial σ R)) : Submodule R (PresentedJet (R := R) m I) :=
  LinearMap.range ((presentedJetMk (R := R) m I).toLinearMap.comp
    (Submodule.subtype (JetLiBidegreePiece R baseWeight m p N)))

/-- Order raising maps a presented weight image into the next presented weight image. -/
noncomputable def presentedJetWeightImageOrderHom (baseWeight : σ → ℕ) (m N : ℕ)
    (I : Ideal (MvPolynomial σ R)) :
    PresentedJetWeightImage (R := R) baseWeight m N I →ₗ[R]
      PresentedJetWeightImage (R := R) baseWeight (m + 1) N I where
  toFun x := by
    refine ⟨presentedJetOrderHom (R := R) m I x.1, ?_⟩
    rcases x.2 with ⟨p, hp⟩
    change presentedJetMk (R := R) m I p.1 = x.1 at hp
    refine ⟨jetWeightPieceOrderHom (R := R) baseWeight m N p, ?_⟩
    change presentedJetMk (R := R) (m + 1) I
      (jetOrderHom (R := R) m p.1) = presentedJetOrderHom (R := R) m I x.1
    rw [← hp]
    rfl
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul (presentedJetOrderHom (R := R) m I).toLinearMap _ _)

/-- Stable polynomial representatives make the quotient transition surjective on weight images.
No injectivity statement is included. -/
theorem presentedJetWeightImageOrderHom_surjective (baseWeight : σ → ℕ)
    (hpositive : ∀ i, 0 < baseWeight i) (m N : ℕ) (hlarge : N ≤ m)
    (I : Ideal (MvPolynomial σ R)) :
    Function.Surjective (presentedJetWeightImageOrderHom (R := R) baseWeight m N I) := by
  intro y
  rcases y.2 with ⟨p, hp⟩
  change presentedJetMk (R := R) (m + 1) I p.1 = y.1 at hp
  obtain ⟨q, hq⟩ := jetWeightPieceOrderHom_surjective (R := R)
    baseWeight hpositive m N hlarge p
  refine ⟨⟨presentedJetMk (R := R) m I q.1, ⟨q, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change presentedJetMk (R := R) (m + 1) I
      (jetOrderHom (R := R) m q.1) = y.1
  rw [show jetOrderHom (R := R) m q.1 = p.1 from congrArg Subtype.val hq, hp]

end PresentedWeightImages

section PresentedBidegreeFinite

variable {K : Type uR} {σ : Type uσ} [Field K] [Finite σ]

/-- A fixed bidegree image in a finite presented jet algebra is finite-dimensional. -/
theorem finiteDimensional_presentedJetLiBidegreeImage
    (baseWeight : σ → ℕ) (hpositive : ∀ i, 0 < baseWeight i)
    (m p N : ℕ) (I : Ideal (MvPolynomial σ K)) :
    FiniteDimensional K (PresentedJetLiBidegreeImage
      (R := K) baseWeight m p N I) := by
  letI : FiniteDimensional K (JetLiBidegreePiece K baseWeight m p N) :=
    finiteDimensional_jetLiBidegreePiece baseWeight hpositive m p N
  exact LinearMap.finiteDimensional_range
    ((presentedJetMk (R := K) m I).toLinearMap.comp
      (Submodule.subtype (JetLiBidegreePiece K baseWeight m p N)))

end PresentedBidegreeFinite

end VOA.FiniteJet
