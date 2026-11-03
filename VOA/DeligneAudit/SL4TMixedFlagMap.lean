import VOA.DeligneAudit.SL4TMixedThomTruncation

/-! # Surjective transport and finite assembly of ideal flags -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra ℂ R] [Algebra ℂ T]

/-- Under a surjection, the image ideal has exactly the image of its underlying vector space. -/
theorem ideal_map_restrictScalars (ρ : R →ₐ[ℂ] T) (hρ : Function.Surjective ρ)
    (I : Ideal R) :
    (I.map ρ.toRingHom).restrictScalars ℂ = (I.restrictScalars ℂ).map ρ.toLinearMap := by
  ext y
  change y ∈ I.map ρ.toRingHom ↔ ∃ x, x ∈ I ∧ ρ x = y
  exact Ideal.mem_map_iff_of_surjective ρ.toRingHom hρ

/-- A one-vector ideal step remains a one-vector step after a surjection. -/
theorem ideal_map_linear_step (ρ : R →ₐ[ℂ] T) (hρ : Function.Surjective ρ)
    (I K : Ideal R) (x : R)
    (h : K.restrictScalars ℂ = I.restrictScalars ℂ ⊔ ℂ ∙ x) :
    (K.map ρ.toRingHom).restrictScalars ℂ =
      (I.map ρ.toRingHom).restrictScalars ℂ ⊔ ℂ ∙ ρ x := by
  rw [ideal_map_restrictScalars ρ hρ K, h, Submodule.map_sup,
    ← ideal_map_restrictScalars ρ hρ I, Submodule.map_span, Set.image_singleton]
  rfl

/-- Mapping coefficients commutes with extending an ideal to the polynomial ring. -/
theorem ideal_map_constant_polynomials (ρ : R →ₐ[ℂ] T) (I : Ideal R) :
    (I.map Polynomial.C).map (Polynomial.mapRingHom ρ.toRingHom) =
      (I.map ρ.toRingHom).map Polynomial.C := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext x : 1
  simp

/-- Spanning flags descend through algebra surjections without requiring injectivity. -/
theorem SpanningChain.map_surjective (ρ : R →ₐ[ℂ] T) (hρ : Function.Surjective ρ)
    {A : Ideal R[X]} {I J : Ideal R} {ns : List ℕ} (h : SpanningChain A I J ns) :
    SpanningChain (A.map (Polynomial.mapRingHom ρ.toRingHom))
      (I.map ρ.toRingHom) (J.map ρ.toRingHom) ns := by
  induction h with
  | nil I => exact .nil _
  | @cons I K J ns x n hs hr ht ih =>
      refine .cons (ρ x) n (ideal_map_linear_step ρ hρ I K x hs) ?_ ih
      have hm := Ideal.mem_map_of_mem (Polynomial.mapRingHom ρ.toRingHom) hr
      rw [Ideal.map_sup, ideal_map_constant_polynomials] at hm
      simpa only [Polynomial.coe_mapRingHom, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X] using hm

/-- A reduced-ring surjection is sufficient to transport a flag through a Thom step. -/
theorem SpanningChain.of_surjective_state (K : Ideal R) (ψ : T →ₐ[ℂ] R ⧸ K)
    (hψ : Function.Surjective ψ) (t : R) (I : Ideal R) (A : Ideal R[X])
    (p : T[X]) (q : R[X]) (m s : ℕ) (hK : ∀ x ∈ K, t * x ∈ I)
    (hpoly : q.map (Ideal.Quotient.mkₐ ℂ K).toRingHom = p.map ψ.toRingHom)
    (hq : Polynomial.C t * X ^ s * q ∈ I.map Polynomial.C ⊔ A)
    (hm : Polynomial.C t * X ^ (m + s) ∈ I.map Polynomial.C ⊔ A)
    {ns : List ℕ}
    (h : SpanningChain (Ideal.span {p} ⊔ Ideal.span {X ^ m}) ⊥ ⊤ ns) :
    SpanningChain A I (I ⊔ Ideal.span {t}) (ns.map (fun n => n + s)) := by
  have ht := h.map_surjective ψ hψ
  simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton,
    Polynomial.coe_mapRingHom, Polynomial.map_pow, Polynomial.map_X,
    Ideal.map_bot, Ideal.map_top] at ht
  rw [← hpoly] at ht
  apply SpanningChain.thom_of_generators (Ideal.Quotient.mkₐ ℂ K)
    (Ideal.Quotient.mkₐ_surjective ℂ K) t I A q m s ?_ hq hm ht
  intro x hx
  exact hK x (Ideal.Quotient.eq_zero_iff_mem.mp hx)

/-- A zero state quotient contributes an empty flag, because its Thom element is already old. -/
theorem SpanningChain.of_zero_state (K I : Ideal R) (A : Ideal R[X]) (t : R)
    (hzero : Subsingleton (R ⧸ K)) (hK : ∀ x ∈ K, t * x ∈ I) :
    SpanningChain A I (I ⊔ Ideal.span {t}) [] := by
  letI := hzero
  have hk : (1 : R) ∈ K := Ideal.Quotient.eq_zero_iff_mem.mp (Subsingleton.elim _ _)
  have ht : t ∈ I := by simpa only [mul_one] using hK 1 hk
  have hle : Ideal.span {t} ≤ I := Ideal.span_le.mpr (by rintro x rfl; exact ht)
  rw [sup_eq_left.mpr hle]
  exact .nil _

/-- Concatenate finitely many consecutive ideal flags in their given order. -/
theorem SpanningChain.join_range (A : Ideal R[X]) (J : ℕ → Ideal R)
    (ns : ℕ → List ℕ) (n : ℕ)
    (h : ∀ i < n, SpanningChain A (J i) (J (i + 1)) (ns i)) :
    SpanningChain A (J 0) (J n) ((List.range n).flatMap ns) := by
  induction n with
  | zero => simpa using SpanningChain.nil (A := A) (J 0)
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append]
      simpa using (ih (fun i hi => h i (by omega))).append (h n (by omega))

/-- Mapping a divided polynomial is determined by the removed zero root. -/
theorem polynomial_map_divX_of_zero_root (ρ : R →ₐ[ℂ] T) (p : R[X]) (q : T[X])
    (h : p.map ρ.toRingHom = X * q) : p.divX.map ρ.toRingHom = q := by
  ext n : 1
  have hc := congrArg (fun f : T[X] => f.coeff (n + 1)) h
  dsimp at hc
  rw [coeff_map, coeff_X_mul] at hc
  simpa only [coeff_map, coeff_divX] using hc

/-- Dividing by a single zero root changes the generator relation only by a constant term. -/
theorem characteristic_divX_mem (p : R[X]) (t : R) (I : Ideal R) (A : Ideal R[X])
    (hp : p ∈ A) (h0 : t * p.coeff 0 ∈ I) :
    Polynomial.C t * X * p.divX ∈ I.map Polynomial.C ⊔ A := by
  let J := I.map Polynomial.C ⊔ A
  have hprod : Polynomial.C t * p ∈ J :=
    J.mul_mem_left _ ((show A ≤ J from le_sup_right) hp)
  have hconst : Polynomial.C (t * p.coeff 0) ∈ J :=
    (show I.map Polynomial.C ≤ J from le_sup_left) (Ideal.mem_map_of_mem Polynomial.C h0)
  have h : Polynomial.C t * X * p.divX =
      Polynomial.C t * p - Polynomial.C (t * p.coeff 0) := by
    have he := X_mul_divX_add p
    rw [map_mul]
    linear_combination Polynomial.C t * he
  rw [h]
  exact J.sub_mem hprod hconst


/-- Transport a state with no removed characteristic root at unchanged cell levels. -/
theorem SpanningChain.of_state_without_root (K : Ideal R) (ψ : T →ₐ[ℂ] R ⧸ K)
    (hψ : Function.Surjective ψ) (t : R) (I : Ideal R) (A : Ideal R[X])
    (p : T[X]) (q : R[X]) (m : ℕ) (hK : ∀ x ∈ K, t * x ∈ I)
    (hpoly : q.map (Ideal.Quotient.mkₐ ℂ K).toRingHom = p.map ψ.toRingHom)
    (hq : q ∈ A) (hm : Polynomial.C t * X ^ m ∈ I.map Polynomial.C ⊔ A)
    {ns : List ℕ}
    (h : SpanningChain (Ideal.span {p} ⊔ Ideal.span {X ^ m}) ⊥ ⊤ ns) :
    SpanningChain A I (I ⊔ Ideal.span {t}) ns := by
  have ht := SpanningChain.of_surjective_state K ψ hψ t I A p q m 0 hK hpoly
    (by simpa using ((show A ≤ I.map Polynomial.C ⊔ A from le_sup_right)
      (A.mul_mem_left (Polynomial.C t) hq))) (by simpa using hm) h
  simpa using ht

/-- Transport a state with one removed root, increasing each cell level by one. -/
theorem SpanningChain.of_state_with_root (K : Ideal R) (ψ : T →ₐ[ℂ] R ⧸ K)
    (hψ : Function.Surjective ψ) (t : R) (I : Ideal R) (A : Ideal R[X])
    (p : T[X]) (q : R[X]) (m : ℕ) (hK : ∀ x ∈ K, t * x ∈ I)
    (hpoly : q.map (Ideal.Quotient.mkₐ ℂ K).toRingHom = X * p.map ψ.toRingHom)
    (hq : q ∈ A) (hm : X ^ (m + 1) ∈ A) {ns : List ℕ}
    (h : SpanningChain (Ideal.span {p} ⊔ Ideal.span {X ^ m}) ⊥ ⊤ ns) :
    SpanningChain A I (I ⊔ Ideal.span {t}) (ns.map (fun n => n + 1)) := by
  have hc := congrArg (fun f : (R ⧸ K)[X] => f.coeff 0) hpoly
  have hzero : Ideal.Quotient.mk K (q.coeff 0) = 0 := by simpa using hc
  have hconst := hK (q.coeff 0) (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  apply SpanningChain.of_surjective_state K ψ hψ t I A p q.divX m 1 hK
    (polynomial_map_divX_of_zero_root _ q _ hpoly) _ _ h
  · simpa only [pow_one] using characteristic_divX_mem q t I A hq hconst
  · exact (show A ≤ I.map Polynomial.C ⊔ A from le_sup_right) (A.mul_mem_left _ hm)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.ideal_map_restrictScalars
#print axioms VOA.DeligneAudit.SL4T.ideal_map_linear_step
#print axioms VOA.DeligneAudit.SL4T.ideal_map_constant_polynomials
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.map_surjective
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.of_surjective_state
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.of_zero_state
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.join_range
#print axioms VOA.DeligneAudit.SL4T.polynomial_map_divX_of_zero_root
#print axioms VOA.DeligneAudit.SL4T.characteristic_divX_mem

#print axioms VOA.DeligneAudit.SL4T.SpanningChain.of_state_without_root
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.of_state_with_root
