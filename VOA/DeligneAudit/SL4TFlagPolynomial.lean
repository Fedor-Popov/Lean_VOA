import VOA.DeligneAudit.SL4TSpanningFlag
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Polynomial.Basic

/-! # Polynomial relation transport for spanning Thom flags -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra ℂ R] [Algebra ℂ T]

/-- Lift a relation through a Thom map. Only the two target generator relations are needed. -/
theorem thomFlag_polynomial (ρ : R →ₐ[ℂ] T) (hρ : Function.Surjective ρ)
    (t : R) (I : Ideal R) (A : Ideal R[X]) (q : R[X]) (m s : ℕ)
    (hq : Polynomial.C t * X ^ s * q ∈ I.map Polynomial.C ⊔ A)
    (hm : Polynomial.C t * X ^ (m + s) ∈ I.map Polynomial.C ⊔ A)
    (K : Ideal T) (x : R) (n : ℕ)
    (hx : Polynomial.C (ρ x) * X ^ n ∈ K.map Polynomial.C ⊔
      (Ideal.span {q.map ρ.toRingHom} ⊔ Ideal.span {X ^ m})) :
    Polynomial.C (t * x) * X ^ (n + s) ∈
      (thomFlagIdeal ρ t I K).map Polynomial.C ⊔ A := by
  let J := (thomFlagIdeal ρ t I K).map Polynomial.C ⊔ A
  let L : Ideal R[X] := J.colon {Polynomial.C t * X ^ s}
  let φ : R[X] →+* T[X] := Polynomial.mapRingHom ρ.toRingHom
  have hφ : Function.Surjective φ := Polynomial.map_surjective _ hρ
  have hIJ : I.map Polynomial.C ⊔ A ≤ J :=
    sup_le_sup (Ideal.map_mono (thomFlagIdeal_lower ρ t I K)) le_rfl
  have hc (z : R) (hz : ρ z ∈ K) : Polynomial.C z ∈ L := by
    apply Submodule.mem_colon_singleton.mpr
    change Polynomial.C z * (Polynomial.C t * X ^ s) ∈ J
    have htz : Polynomial.C (t * z) ∈ J :=
      (show (thomFlagIdeal ρ t I K).map Polynomial.C ≤ J from le_sup_left)
        (Ideal.mem_map_of_mem Polynomial.C (thomFlagIdeal_mul ρ t I K hz))
    convert J.mul_mem_right (X ^ s) htz using 1
    rw [map_mul]
    ring
  have hker : RingHom.ker φ ≤ L := by
    rw [Polynomial.ker_mapRingHom]
    apply Ideal.map_le_iff_le_comap.mpr
    intro z hz
    apply hc
    rw [RingHom.mem_ker] at hz
    change ρ z = 0 at hz
    rw [hz]
    exact K.zero_mem
  have hsource : K.map Polynomial.C ⊔
      (Ideal.span {q.map ρ.toRingHom} ⊔ Ideal.span {X ^ m}) ≤ L.map φ := by
    refine sup_le ?_ (sup_le ?_ ?_)
    · apply Ideal.map_le_iff_le_comap.mpr
      intro y hy
      obtain ⟨z, rfl⟩ := hρ y
      exact (Ideal.mem_map_iff_of_surjective φ hφ).mpr
        ⟨Polynomial.C z, hc z hy, by simp [φ]⟩
    · apply Ideal.span_le.mpr
      rintro y rfl
      apply Ideal.mem_map_of_mem φ
      apply Submodule.mem_colon_singleton.mpr
      change q * (Polynomial.C t * X ^ s) ∈ J
      rw [mul_comm]
      exact hIJ hq
    · apply Ideal.span_le.mpr
      rintro y rfl
      apply (Ideal.mem_map_iff_of_surjective φ hφ).mpr
      refine ⟨X ^ m, ?_, by simp [φ]⟩
      apply Submodule.mem_colon_singleton.mpr
      change X ^ m * (Polynomial.C t * X ^ s) ∈ J
      convert hIJ hm using 1
      rw [pow_add]
      ring
  have hmem : Polynomial.C x * X ^ n ∈ (L.map φ).comap φ := by
    change φ (Polynomial.C x * X ^ n) ∈ L.map φ
    simpa [φ] using hsource hx
  rw [Ideal.comap_map_of_surjective φ hφ] at hmem
  have hL : Polynomial.C x * X ^ n ∈ L :=
    (sup_le le_rfl hker) hmem
  have hresult := Submodule.mem_colon_singleton.mp hL
  change (Polynomial.C x * X ^ n) * (Polynomial.C t * X ^ s) ∈ J at hresult
  convert hresult using 1
  rw [map_mul, pow_add]
  ring

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.thomFlag_polynomial
