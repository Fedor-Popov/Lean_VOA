import VOA.Commutative.PoissonVertexHom
import Mathlib.RingTheory.Derivation.MapCoeffs

/-! # Genuine quotients by translation- and mode-stable ideals -/
namespace VOA.PoissonVertexAlgebra
open scoped BigOperators
noncomputable section
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (P : VOA.PoissonVertexAlgebra A) (I : Ideal A)
    (hT : ∀ a ∈ I, P.translation a ∈ I)
    (hL : ∀ n a, a ∈ I → ∀ b, P.mode n a b ∈ I)
    (hR : ∀ n a b, b ∈ I → P.mode n a b ∈ I)

include hR in
private theorem mode_right_ker (n : ℕ) :
    I.restrictScalars ℂ ≤ LinearMap.ker
      ((P.mode n).compr₂ (Ideal.Quotient.mkₐ ℂ I).toLinearMap).flip := by
  intro b hb
  apply LinearMap.ext
  intro a
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hR n a b hb)

include hL in
private theorem mode_left_ker (n : ℕ) :
    I.restrictScalars ℂ ≤ LinearMap.ker
      (((I.restrictScalars ℂ).liftQ
        ((P.mode n).compr₂ (Ideal.Quotient.mkₐ ℂ I).toLinearMap).flip
        (mode_right_ker P I hR n)).flip) := by
  intro a ha
  apply LinearMap.ext
  intro b
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hL n a ha b)

/-- The true bilinear operations descended through a two-sided mode-stable ideal. -/
def quotientMode (n : ℕ) : (A ⧸ I) →ₗ[ℂ] (A ⧸ I) →ₗ[ℂ] (A ⧸ I) :=
  (I.restrictScalars ℂ).liftQ
    (((I.restrictScalars ℂ).liftQ
      ((P.mode n).compr₂ (Ideal.Quotient.mkₐ ℂ I).toLinearMap).flip
      (mode_right_ker P I hR n)).flip)
    (mode_left_ker P I hL hR n)

@[simp] theorem quotientMode_mk (n : ℕ) (a b : A) :
    quotientMode P I hL hR n (Ideal.Quotient.mkₐ ℂ I a) (Ideal.Quotient.mkₐ ℂ I b) =
      Ideal.Quotient.mkₐ ℂ I (P.mode n a b) := rfl

/-- The genuine derivation descended through the stable ideal. -/
def quotientTranslation : Derivation ℂ (A ⧸ I) (A ⧸ I) :=
  Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective ℂ I)
    (d := P.translation) (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      (hT a (Ideal.Quotient.eq_zero_iff_mem.mp ha)))

@[simp] theorem quotientTranslation_mk (a : A) :
    quotientTranslation P I hT (Ideal.Quotient.mkₐ ℂ I a) =
      Ideal.Quotient.mkₐ ℂ I (P.translation a) := by
  exact Derivation.liftOfSurjective_apply (Ideal.Quotient.mkₐ_surjective ℂ I)
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr
      (hT x (Ideal.Quotient.eq_zero_iff_mem.mp hx))) a

theorem quotientTranslation_pow_mk (j : ℕ) (a : A) :
    ((quotientTranslation P I hT).toLinearMap^j) (Ideal.Quotient.mkₐ ℂ I a) =
      Ideal.Quotient.mkₐ ℂ I ((P.translation.toLinearMap^j) a) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [pow_succ',Module.End.mul_apply,ih]
      exact quotientTranslation_mk P I hT _

/-- Every PVA law descends to the actual ideal quotient. -/
def quotient : VOA.PoissonVertexAlgebra (A ⧸ I) where
  translation := quotientTranslation P I hT
  mode := quotientMode P I hL hR
  locality a b := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I a
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I b
    obtain ⟨N,hN⟩ := P.locality a b
    exact ⟨N,fun n hn => by rw [quotientMode_mk,hN n hn,map_zero]⟩
  translation_left_zero a b := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I a
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I b
    simp only [quotientTranslation_mk,quotientMode_mk,P.translation_left_zero,map_zero]
  translation_left_succ n a b := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I a
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I b
    simp only [quotientTranslation_mk,quotientMode_mk,P.translation_left_succ,map_smul]
  translation_mode n a b := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I a
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I b
    simp only [quotientTranslation_mk,quotientMode_mk,P.translation_mode,map_add]
  leibniz n a b c := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I a
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I b
    obtain ⟨c,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I c
    rw [← map_mul,quotientMode_mk,P.leibniz,map_add,map_mul,map_mul,
      quotientMode_mk,quotientMode_mk]
  skew n a b := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I a
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I b
    rw [quotientMode_mk,P.skew]
    have hfin : (Function.support fun j : ℕ => (j.factorial : ℂ)⁻¹ •
        (-1 : ℂ)^(n+j+1) • ((P.translation.toLinearMap^j) (P.mode (n+j) b a))).Finite := by
      obtain ⟨N,hN⟩ := P.locality b a
      apply (Set.finite_Iio N).subset
      intro j hj
      change j < N
      by_contra hlt
      apply hj
      change (j.factorial : ℂ)⁻¹ • (-1 : ℂ)^(n+j+1) •
        ((P.translation.toLinearMap^j) (P.mode (n+j) b a)) = 0
      rw [hN (n+j) (by omega),map_zero,smul_zero,smul_zero]
    have hm := (Ideal.Quotient.mkₐ ℂ I).toLinearMap.toAddMonoidHom.map_finsum hfin
    change Ideal.Quotient.mkₐ ℂ I (∑ᶠ j : ℕ, _) = _ at hm
    rw [hm]
    apply finsum_congr
    intro j
    change Ideal.Quotient.mkₐ ℂ I ((j.factorial : ℂ)⁻¹ • (-1 : ℂ)^(n+j+1) •
      ((P.translation.toLinearMap^j) (P.mode (n+j) b a))) = _
    rw [map_smul,map_smul,quotientMode_mk,quotientTranslation_pow_mk]
  jacobi m n a b c := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I a
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I b
    obtain ⟨c,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I c
    simp only [quotientMode_mk,← map_sub,P.jacobi,map_sum,map_smul]

end
end VOA.PoissonVertexAlgebra
