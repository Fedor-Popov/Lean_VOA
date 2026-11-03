import VOA.DeligneAudit.D4LevelReductionCommonRootPolynomial

/-! Transport of the two polynomial relations through a coefficient-ideal flag. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open Polynomial
open VOA.DeligneAudit.SL4T

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra ℂ R] [Algebra ℂ T]

/-- Two characteristic relations are lifted simultaneously through a Thom map. -/
theorem commonRoot_polynomialTransport (ρ : R →ₐ[ℂ] T) (hρ : Function.Surjective ρ)
    (t : R) (I : Ideal R) (A : Ideal R[X]) (p q : R[X]) (s : ℕ)
    (hp : Polynomial.C t * X ^ s * p ∈ I.map Polynomial.C ⊔ A)
    (hq : Polynomial.C t * X ^ s * q ∈ I.map Polynomial.C ⊔ A)
    (K : Ideal T) (x : R) (n : ℕ)
    (hx : Polynomial.C (ρ x) * X ^ n ∈ K.map Polynomial.C ⊔
      (commonRootIdeal (p.map ρ.toRingHom) (q.map ρ.toRingHom))) :
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
      (commonRootIdeal (p.map ρ.toRingHom) (q.map ρ.toRingHom)) ≤ L.map φ := by
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
      change p * (Polynomial.C t * X ^ s) ∈ J
      rw [mul_comm]
      exact hIJ hp
    · apply Ideal.span_le.mpr
      rintro y rfl
      apply Ideal.mem_map_of_mem φ
      apply Submodule.mem_colon_singleton.mpr
      change q * (Polynomial.C t * X ^ s) ∈ J
      rw [mul_comm]
      exact hIJ hq
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


/-- A coefficient flag records both the union and common-root exponents of each cell. -/
inductive TwoRelationChain (A B : Ideal R[X]) : Ideal R → Ideal R → List (ℕ × ℕ) → Prop
  | nil (I) : TwoRelationChain A B I I []
  | cons {I K J ns} (x : R) (n d : ℕ)
      (step : K.restrictScalars ℂ = I.restrictScalars ℂ ⊔ ℂ ∙ x)
      (union : Polynomial.C x * X ^ n ∈ I.map Polynomial.C ⊔ A)
      (common : Polynomial.C x * X ^ d ∈ I.map Polynomial.C ⊔ B)
      (tail : TwoRelationChain A B K J ns) : TwoRelationChain A B I J ((n, d) :: ns)

/-- Concatenating ideal flags preserves both polynomial relations. -/
theorem TwoRelationChain.append {A B : Ideal R[X]} {I J K : Ideal R}
    {ns ms : List (ℕ × ℕ)} (h : TwoRelationChain A B I J ns)
    (h' : TwoRelationChain A B J K ms) : TwoRelationChain A B I K (ns ++ ms) := by
  induction h with
  | nil => exact h'
  | cons x n d hs hu hc ht ih => exact .cons x n d hs hu hc (ih h')

/-- Transport preserves the union and common-root cutoffs on the same generators. -/
theorem TwoRelationChain.thom (ρ : R →ₐ[ℂ] T) (hρ : Function.Surjective ρ)
    (t : R) (I : Ideal R) (A B : Ideal R[X]) (A' B' : Ideal T[X]) (s d : ℕ)
    (hunion : ∀ (K : Ideal T) (x : R) (n : ℕ),
      Polynomial.C (ρ x) * X ^ n ∈ K.map Polynomial.C ⊔ A' →
      Polynomial.C (t * x) * X ^ (n + s) ∈
        (thomFlagIdeal ρ t I K).map Polynomial.C ⊔ A)
    (hcommon : ∀ (K : Ideal T) (x : R) (n : ℕ),
      Polynomial.C (ρ x) * X ^ n ∈ K.map Polynomial.C ⊔ B' →
      Polynomial.C (t * x) * X ^ (n + d) ∈
        (thomFlagIdeal ρ t I K).map Polynomial.C ⊔ B)
    {K L : Ideal T} {ns : List (ℕ × ℕ)} (h : TwoRelationChain A' B' K L ns) :
    TwoRelationChain A B (thomFlagIdeal ρ t I K) (thomFlagIdeal ρ t I L)
      (ns.map fun n => (n.1 + s, n.2 + d)) := by
  induction h with
  | nil => exact .nil _
  | @cons K J L ns y n j hs hu hc ht ih =>
      obtain ⟨x, rfl⟩ := hρ y
      exact .cons (t * x) (n + s) (j + d) (thomFlagIdeal_step ρ t I hs)
        (hunion K x n hu) (hcommon K x j hc) ih

/-- Exporting the flag keeps both relations attached to each natural-number index. -/
theorem TwoRelationChain.export {A B : Ideal R[X]} {I J : Ideal R} {ns : List (ℕ × ℕ)}
    (h : TwoRelationChain A B I J ns) :
    ∃ (v : ℕ → R) (F : ℕ → Ideal R), F 0 = I ∧ F ns.length = J ∧
      (∀ i < ns.length,
        (F (i + 1)).restrictScalars ℂ = (F i).restrictScalars ℂ ⊔ ℂ ∙ v i) ∧
      (∀ i < ns.length,
        Polynomial.C (v i) * X ^ (ns.getD i (0, 0)).1 ∈ (F i).map Polynomial.C ⊔ A) ∧
      (∀ i < ns.length,
        Polynomial.C (v i) * X ^ (ns.getD i (0, 0)).2 ∈ (F i).map Polynomial.C ⊔ B) := by
  induction h with
  | nil I => exact ⟨fun _ => 0, fun _ => I, rfl, rfl, by simp, by simp, by simp⟩
  | @cons I K J ns x n d hs hu hc ht ih =>
      obtain ⟨v, F, h0, htop, hstep, hunion, hcommon⟩ := ih
      let w : ℕ → R := fun i => match i with | 0 => x | j + 1 => v j
      let G : ℕ → Ideal R := fun i => match i with | 0 => I | j + 1 => F j
      refine ⟨w, G, rfl, htop, ?_, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => simpa only [G, w, h0] using hs
        | succ i => exact hstep i (by simpa using hi)
      · intro i hi
        cases i with
        | zero => simpa only [G, w, List.getD_cons_zero] using hu
        | succ i => exact hunion i (by simpa using hi)
      · intro i hi
        cases i with
        | zero => simpa only [G, w, List.getD_cons_zero] using hc
        | succ i => exact hcommon i (by simpa using hi)

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.commonRoot_polynomialTransport
#print axioms VOA.DeligneAudit.D4LevelReduction.TwoRelationChain.append
#print axioms VOA.DeligneAudit.D4LevelReduction.TwoRelationChain.thom
#print axioms VOA.DeligneAudit.D4LevelReduction.TwoRelationChain.export
