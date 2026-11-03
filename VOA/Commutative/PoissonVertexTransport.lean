import VOA.Commutative.PoissonVertexHom

/-!
# Transport of a Poisson vertex algebra through an actual algebra equivalence

The supplied translation is retained, with a proved intertwining identity. Every
mode identity is transported through injectivity; no structural law is assumed.
-/
namespace VOA.PoissonVertexAlgebra
open scoped BigOperators
noncomputable section
variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
variable (Q : VOA.PoissonVertexAlgebra B) (e : A ≃ₐ[ℂ] B)
    (T : Derivation ℂ A A) (hT : ∀ x, e (T x) = Q.translation (e x))

/-- Pull back the actual bilinear nonnegative products. -/
def transportedMode (n : ℕ) : A →ₗ[ℂ] A →ₗ[ℂ] A where
  toFun x := e.symm.toLinearMap.comp ((Q.mode n (e x)).comp e.toLinearMap)
  map_add' x y := by ext z; simp
  map_smul' c x := by ext z; simp

@[simp] theorem map_transportedMode (n : ℕ) (x y : A) :
    e (transportedMode Q e n x y) = Q.mode n (e x) (e y) := e.apply_symm_apply _

include hT in
theorem map_translationIterate (j : ℕ) (x : A) :
    e ((T.toLinearMap^j) x) = (Q.translation.toLinearMap^j) (e x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [pow_succ', Module.End.mul_apply]
      change e (T ((T.toLinearMap^j) x)) = Q.translation ((Q.translation.toLinearMap^j) (e x))
      rw [hT,ih]

theorem transportedMode_locality (x y : A) :
    ∃ b : ℕ, ∀ n, b ≤ n → transportedMode Q e n x y = 0 := by
  obtain ⟨b,hb⟩ := Q.locality (e x) (e y)
  exact ⟨b,fun n hn => e.injective (by simpa using hb n hn)⟩

/-- An actual algebra equivalence transports all PVA axioms to the supplied translation. -/
def transport : VOA.PoissonVertexAlgebra A where
  translation := T
  mode := transportedMode Q e
  locality := transportedMode_locality Q e
  translation_left_zero x y := e.injective (by
    simp only [map_transportedMode,hT,Q.translation_left_zero,map_zero])
  translation_left_succ n x y := e.injective (by
    simp only [map_transportedMode,hT,map_smul,Q.translation_left_succ])
  translation_mode n x y := e.injective (by
    simp only [hT,map_transportedMode,map_add,Q.translation_mode])
  leibniz n x y z := e.injective (by
    simp only [map_transportedMode,map_add,map_mul,Q.leibniz])
  skew n x y := by
    apply e.injective
    rw [map_transportedMode,Q.skew]
    have hfin : (Function.support fun j : ℕ => (j.factorial : ℂ)⁻¹ •
        (-1 : ℂ)^(n+j+1) • ((T.toLinearMap^j) (transportedMode Q e (n+j) y x))).Finite := by
      obtain ⟨b,hb⟩ := transportedMode_locality Q e y x
      apply (Set.finite_Iio b).subset
      intro j hj
      by_contra hlt
      change (j.factorial : ℂ)⁻¹ • (-1 : ℂ)^(n+j+1) •
        ((T.toLinearMap^j) (transportedMode Q e (n+j) y x)) ≠ 0 at hj
      apply hj
      rw [hb (n+j) (by change j ∉ Set.Iio b at hlt; simp only [Set.mem_Iio] at hlt; omega),
        map_zero,smul_zero,smul_zero]
    have hm := e.toLinearMap.toAddMonoidHom.map_finsum hfin
    change e (∑ᶠ j : ℕ, _) = _ at hm
    rw [hm]
    apply finsum_congr
    intro j
    change _ = e ((j.factorial : ℂ)⁻¹ • (-1 : ℂ)^(n+j+1) •
      ((T.toLinearMap^j) (transportedMode Q e (n+j) y x)))
    rw [map_smul,map_smul,map_translationIterate Q e T hT,map_transportedMode]
  jacobi m n x y z := e.injective (by
    simp only [map_sub,map_transportedMode,map_sum,map_smul,Q.jacobi])

/-- The transport equivalence is a genuine PVA homomorphism. -/
def transportHom : Hom (transport Q e T hT) Q where
  toAlgHom := e.toAlgHom
  map_translation := hT
  map_mode := map_transportedMode Q e

end
end VOA.PoissonVertexAlgebra
