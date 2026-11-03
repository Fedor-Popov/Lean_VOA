import VOA.Commutative.InfiniteJetDifferential
import VOA.Commutative.PoissonVertexHom

/-!
# Intrinsic uniqueness and generator test for an arc Poisson vertex structure

On the genuine arc presentation, ordinary jet variables are divided translates of
the base variables. Consequently a translation-preserving algebra map preserves all
Poisson vertex products if it preserves the products of the base generators.
This theorem does not assume compatibility on arbitrary arc elements.
-/
namespace VOA.InfiniteJet
open VOA.PoissonVertexAlgebra
noncomputable section
variable {σ B : Type*} [CommRing B] [Algebra ℂ B]

/-- The ordinary jet coordinate in the genuine arc quotient. -/
def generator (I : Ideal (MvPolynomial σ ℂ)) (i : σ) (n : ℕ) : PresentedJet I :=
  presentedJetMk I (MvPolynomial.X (i,n))

/-- Every next ordinary coefficient is the divided translate of its predecessor. -/
theorem generator_succ (I : Ideal (MvPolynomial σ ℂ)) (i : σ) (n : ℕ) :
    generator I i (n+1) = (((n+1 : ℕ) : ℂ)⁻¹) • translation I (generator I i n) := by
  rw [generator, generator, translation_X]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Nat.succ_ne_zero n

variable (I : Ideal (MvPolynomial σ ℂ))
    (P : VOA.PoissonVertexAlgebra (PresentedJet I)) (Q : VOA.PoissonVertexAlgebra B)
    (F : PresentedJet I →ₐ[ℂ] B)

/-- Generator-pair compatibility extends to every pair of ordinary jet coordinates. -/
theorem compatible_generators
    (hP : P.translation = translation I)
    (hT : ∀ x, F (P.translation x) = Q.translation (F x))
    (hbase : ∀ i j, Compatible P Q F (generator I i 0) (generator I j 0))
    (i j : σ) (r s : ℕ) : Compatible P Q F (generator I i r) (generator I j s) := by
  have hright : ∀ s, Compatible P Q F (generator I i 0) (generator I j s) := by
    intro s
    induction s with
    | zero => exact hbase i j
    | succ s ih =>
        rw [generator_succ, ← hP]
        exact compatible_smul_right P Q F (compatible_translate_right P Q F hT ih) _
  induction r with
  | zero => exact hright s
  | succ r ih =>
      rw [generator_succ, ← hP]
      exact compatible_smul_left P Q F (compatible_translate_left P Q F hT ih) _

/-- For a fixed first entry, ordinary polynomial generators suffice in the second entry. -/
theorem compatible_all_right (x : PresentedJet I)
    (hgen : ∀ i n, Compatible P Q F x (generator I i n)) :
    ∀ y, Compatible P Q F x y := by
  intro y
  refine Submodule.Quotient.induction_on _ y (fun p => ?_)
  change Compatible P Q F x (presentedJetMk I p)
  induction p using MvPolynomial.induction_on with
  | C c =>
      change Compatible P Q F x (algebraMap ℂ (PresentedJet I) c)
      exact compatible_const_right P Q F x c
  | add p q hp hq =>
      rw [map_add]
      exact compatible_add_right P Q F hp hq
  | mul_X p v hp =>
      rw [map_mul]
      exact compatible_mul_right P Q F hp (hgen v.1 v.2)

/-- Compatibility on base generators implies compatibility on every arc element. -/
theorem compatible_of_base_generators
    (hP : P.translation = translation I)
    (hT : ∀ x, F (P.translation x) = Q.translation (F x))
    (hbase : ∀ i j, Compatible P Q F (generator I i 0) (generator I j 0)) :
    ∀ x y, Compatible P Q F x y := by
  have hgen : ∀ i r y, Compatible P Q F (generator I i r) y := by
    intro i r
    apply compatible_all_right I P Q F
    exact fun j s => compatible_generators I P Q F hP hT hbase i j r s
  intro x
  apply compatible_all_right I P Q F
  intro i n
  exact compatible_swap P Q F hT (hgen i n x)

/-- The generator test constructs a genuine Poisson vertex homomorphism. -/
def poissonVertexHomOfBaseGenerators
    (hP : P.translation = translation I)
    (hT : ∀ x, F (P.translation x) = Q.translation (F x))
    (hbase : ∀ i j, Compatible P Q F (generator I i 0) (generator I j 0)) : Hom P Q where
  toAlgHom := F
  map_translation := hT
  map_mode n x y := compatible_of_base_generators I P Q F hP hT hbase x y n

/-- An arc Poisson vertex structure is uniquely determined by its translation and
nonnegative products of the original algebra generators. -/
theorem poissonVertexAlgebra_unique
    (Q : VOA.PoissonVertexAlgebra (PresentedJet I))
    (hP : P.translation = translation I) (hQ : Q.translation = translation I)
    (hbase : ∀ i j n, P.mode n (generator I i 0) (generator I j 0) =
      Q.mode n (generator I i 0) (generator I j 0)) : P = Q := by
  have h := compatible_of_base_generators I P Q (AlgHom.id ℂ (PresentedJet I)) hP
    (fun x => by simp only [AlgHom.id_apply, hP, hQ]) hbase
  have hmode : P.mode = Q.mode := by
    funext n
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact h x y n
  have htranslation := hP.trans hQ.symm
  cases P
  cases Q
  cases htranslation
  cases hmode
  rfl

end
end VOA.InfiniteJet
