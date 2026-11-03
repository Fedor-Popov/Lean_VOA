import VOA.DeligneAudit.SL4TPiTheorem

/-! Current-module bounds from coefficient subspaces stable under positive power sums. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial
open VOA.DeligneAudit.CVsl2 (SL2 bal)

variable {R V : Type*} [CommRing R] [Algebra ℂ R]
variable [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V}

/-- Nilpotent multiplication acts trivially on a stable one-dimensional subspace quotient. -/
theorem subspace_cell_nilpotent_mul (I K : Submodule ℂ R) (x p : R)
    (hcell : K = I ⊔ ℂ ∙ x)
    (hI : ∀ a ∈ I, p * a ∈ I) (hK : ∀ a ∈ K, p * a ∈ K)
    (hp : IsNilpotent p) : p * x ∈ I := by
  have hx : x ∈ K := by
    rw [hcell]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hpx := hK x hx
  rw [hcell] at hpx
  obtain ⟨y, hy, z, hz, heq⟩ := Submodule.mem_sup.mp hpx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  let L : Module.End ℂ R :=
    { toFun := fun a => p * a
      map_add' := fun a b => mul_add p a b
      map_smul' := fun c a => mul_smul_comm c p a }
  let T : Module.End ℂ (R ⧸ I) := I.mapQ I L (fun a ha => hI a ha)
  have hT (a : R) : T (I.mkQ a) = I.mkQ (p * a) := rfl
  have hy0 : I.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero I).mpr hy
  have he : T (I.mkQ x) = c • I.mkQ x := by
    rw [hT, ← heq, map_add, map_smul, hy0, zero_add]
  have hpow : ∀ n : ℕ, I.mkQ (p ^ n * x) = c ^ n • I.mkQ x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', mul_assoc, ← hT, ih, map_smul, he, smul_smul, pow_succ]
  obtain ⟨n, hn⟩ := hp
  have hz : c ^ n • I.mkQ x = 0 := by
    rw [← hpow n, hn, zero_mul, map_zero]
  apply (Submodule.Quotient.mk_eq_zero I).mp
  change I.mkQ (p * x) = 0
  rw [← hT, he]
  by_cases hc : c = 0
  · simp [hc]
  · rw [(smul_eq_zero.mp hz).resolve_left (pow_ne_zero n hc), smul_zero]

/-- Polynomial coefficients in a subspace evaluate into the generated current submodule. -/
theorem piCurrentMap_subspace (π : R →ₗ[ℂ] V) (F : ℕ → Module.End ℂ V)
    (I : Submodule ℂ R) (N : Submodule ℂ V)
    (hπ : ∀ a ∈ I, π a ∈ N) (hF : ∀ s, N ≤ N.comap (F s))
    (p : R[X]) (hp : ∀ l, p.coeff l ∈ I) : piCurrentMap F π p ∈ N := by
  change (p.sum fun s a => F s (π a)) ∈ N
  apply Submodule.sum_mem
  intro s _
  exact hF s (hπ _ (hp s))

/-- A correction with coefficients in an earlier subspace gives every later mode relation. -/
theorem piCurrentMap_subspace_cell (π : R →ₗ[ℂ] V) (F : ℕ → Module.End ℂ V)
    (I : Submodule ℂ R) (N : Submodule ℂ V) (P : R[X]) (M : ℕ)
    (hπ : ∀ a ∈ I, π a ∈ N) (hF : ∀ s, N ≤ N.comap (F s))
    (hP : PiCharacteristic F π P) (hM : ∀ s, M ≤ s → ∀ a, F s (π a) = 0)
    (a : R) (n : ℕ) (p : R[X]) (hp : ∀ l, p.coeff l ∈ I)
    (hrel : Polynomial.C a * X ^ n + p ∈ Ideal.span {P} ⊔ Ideal.span {X ^ M})
    (s : ℕ) (hs : n ≤ s) : F s (π a) ∈ N := by
  have hr := (Ideal.span {P} ⊔ Ideal.span {X ^ M}).mul_mem_right (X ^ (s - n)) hrel
  rw [add_mul, mul_assoc, ← pow_add, Nat.add_sub_of_le hs] at hr
  have hz := piCurrentMap_relationIdeal F π P M hP hM hr
  rw [map_add, piCurrentMap_C_mul_X_pow] at hz
  rw [eq_neg_of_add_eq_zero_left hz]
  apply N.neg_mem
  apply piCurrentMap_subspace π F I N hπ hF
  intro l
  rw [coeff_mul_X_pow']
  split_ifs
  · exact hp _
  · exact I.zero_mem

/-- A line-by-line subspace flag is the span of its successive chosen vectors. -/
theorem subspaceFlag_eq_prefix (v : ℕ → R) (I : ℕ → Submodule ℂ R) (n : ℕ)
    (h0 : I 0 = ⊥) (hstep : ∀ i < n, I (i + 1) = I i ⊔ ℂ ∙ v i) :
    ∀ i ≤ n, I i = generatorPrefix v i := by
  intro i
  induction i with
  | zero => intro _; rw [h0, generatorPrefix_zero]
  | succ i ih =>
      intro hi
      rw [hstep i (by omega), ih (by omega), generatorPrefix_succ]

/-- The cell bound for a power-sum-stable flag with relative polynomial levels. -/
theorem pi_subspaceFlag_bound_of_characteristic (hS : SL2 E H F)
    (π : R →ₗ[ℂ] V) (p : ℕ → R) (P : R[X]) (r M n : ℕ)
    (v : ℕ → R) (I : ℕ → Submodule ℂ R) (ν : ℕ → ℕ)
    (h0 : I 0 = ⊥) (htop : I n = ⊤)
    (hstep : ∀ i < n, I (i + 1) = I i ⊔ ℂ ∙ v i)
    (hstable : ∀ i ≤ n, ∀ s, 1 ≤ s → ∀ a ∈ I i, p s * a ∈ I i)
    (hrel : ∀ i < n, ∃ q : R[X], (∀ l, q.coeff l ∈ I i) ∧
      Polynomial.C (v i) * X ^ (ν i) + q ∈ Ideal.span {P} ⊔ Ideal.span {X ^ M})
    (hp : ∀ s, 1 ≤ s → IsNilpotent (p s))
    (hE : ∀ s a, E s (π a) = 0)
    (hH0 : ∀ a, H 0 (π a) = (r : ℂ) • π a)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (p s * a))
    (hF0 : ∀ a, (F 0 ^ (r + 1)) (π a) = 0)
    (hM : ∀ s, M ≤ s → ∀ a, F s (π a) = 0)
    (hP : PiCharacteristic F π P) :
    FiniteDimensional ℂ (currentSpan E H F (Set.range π)) ∧
      Module.finrank ℂ (currentSpan E H F (Set.range π)) ≤
        ∑ i ∈ Finset.range n, ((bal r (ν i)).map (· + 1)).prod := by
  have hprefix := subspaceFlag_eq_prefix v I n h0 hstep
  have himage (i : ℕ) (hi : i ≤ n) (a : R) (ha : a ∈ I i) :
      π a ∈ cellFlag E H F (fun j => π (v j)) i := by
    apply pi_prefix_le_cellFlag π v i
    rw [← hprefix i hi]
    exact ha
  have hspan : generatorPrefix v n = ⊤ := by rw [← hprefix n le_rfl, htop]
  rw [pi_currentSpan_eq_cellFlag π v n hspan]
  apply cellFlag_bound_any hS _ r ν n
  intro i hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hE]
    exact Submodule.zero_mem _
  · rw [hH0, sub_self]
    exact Submodule.zero_mem _
  · intro s hs
    rw [hH s hs]
    exact himage i (by omega) _ (subspace_cell_nilpotent_mul (I i) (I (i + 1))
      (v i) (p s) (hstep i hi) (hstable i (by omega) s hs)
      (hstable (i + 1) (by omega) s hs) (hp s hs))
  · rw [hF0]
    exact Submodule.zero_mem _
  · obtain ⟨q, hq, hqr⟩ := hrel i hi
    exact piCurrentMap_subspace_cell π F (I i) _ P M (himage i (by omega))
      (cellFlag_stable _ i).2.2 hP hM (v i) (ν i) q hq hqr

/-- Garland supplies the characteristic relation for any power-sum-stable subspace flag. -/
theorem pi_subspaceFlag_bound (hS : SL2 E H F)
    (π : R →ₗ[ℂ] V) (p : ℕ → R) (r M n : ℕ)
    (v : ℕ → R) (I : ℕ → Submodule ℂ R) (ν : ℕ → ℕ)
    (h0 : I 0 = ⊥) (htop : I n = ⊤)
    (hstep : ∀ i < n, I (i + 1) = I i ⊔ ℂ ∙ v i)
    (hstable : ∀ i ≤ n, ∀ s, 1 ≤ s → ∀ a ∈ I i, p s * a ∈ I i)
    (hrel : ∀ i < n, ∃ q : R[X], (∀ l, q.coeff l ∈ I i) ∧
      Polynomial.C (v i) * X ^ (ν i) + q ∈
        Ideal.span {descendingPoly (newtonCoeff p) r} ⊔ Ideal.span {X ^ M})
    (hp : ∀ s, 1 ≤ s → IsNilpotent (p s))
    (htail : ∀ j, r < j → newtonCoeff p j = 0)
    (hE : ∀ s a, E s (π a) = 0)
    (hH0 : ∀ a, H 0 (π a) = (r : ℂ) • π a)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (p s * a))
    (hF0 : ∀ a, (F 0 ^ (r + 1)) (π a) = 0)
    (hM : ∀ s, M ≤ s → ∀ a, F s (π a) = 0) :
    FiniteDimensional ℂ (currentSpan E H F (Set.range π)) ∧
      Module.finrank ℂ (currentSpan E H F (Set.range π)) ≤
        ∑ i ∈ Finset.range n, ((bal r (ν i)).map (· + 1)).prod :=
  pi_subspaceFlag_bound_of_characteristic hS π p (descendingPoly (newtonCoeff p) r)
    r M n v I ν h0 htop hstep hstable hrel hp hE hH0 hH hF0 hM
    (piCharacteristic_of_highest hS π p hE hH r hF0 htail)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.subspace_cell_nilpotent_mul
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_subspace
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_subspace_cell
#print axioms VOA.DeligneAudit.SL4T.subspaceFlag_eq_prefix
#print axioms VOA.DeligneAudit.SL4T.pi_subspaceFlag_bound_of_characteristic
#print axioms VOA.DeligneAudit.SL4T.pi_subspaceFlag_bound
