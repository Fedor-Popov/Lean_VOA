import VOA.DeligneAudit.SL4TRootPowerFiltration

/-! # Smaller full-flag presentations of the root-power layers -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- The ring presenting a power layer at the first root of a full flag. -/
abbrev FullFlagPowerLayer (B N i : ℕ) :=
  FullFlagRing (B + 1) N ⧸ rootPowerLayerIdeal (fullFlagRoot (B + 1) N 0) i

/-- The surviving roots in a power layer. -/
def fullFlagPowerLayerRoot (B N i : ℕ) (j : Fin B) : FullFlagPowerLayer B N i :=
  Ideal.Quotient.mk _ (fullFlagRoot (B + 1) N j.succ)

theorem fullFlagPowerLayer_first_zero (B N i : ℕ) :
    Ideal.Quotient.mk (rootPowerLayerIdeal (fullFlagRoot (B + 1) N 0) i)
      (fullFlagRoot (B + 1) N 0) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (root_mem_powerLayerIdeal _ _)

theorem fullFlagPowerLayer_elementary (B N i : ℕ) :
    D4Levi.ksEPoly (List.ofFn (fullFlagPowerLayerRoot B N i)) = 1 := by
  let q := Ideal.Quotient.mk (rootPowerLayerIdeal (fullFlagRoot (B + 1) N 0) i)
  have he := congrArg (Polynomial.map q) (fullFlag_elementaryPolynomial (B + 1) N)
  rw [alphabetElementary_map, List.map_ofFn, Polynomial.map_one] at he
  rw [List.ofFn_succ] at he
  simp only [D4Levi.ksEPoly, List.map_cons, List.prod_cons, Function.comp_apply,
    show q (fullFlagRoot (B + 1) N 0) = 0 from fullFlagPowerLayer_first_zero B N i,
    map_zero, zero_mul, sub_zero, one_mul] at he
  exact he

theorem fullFlagPowerLayerRoot_pow (B N i : ℕ) (j : Fin B) :
    fullFlagPowerLayerRoot B N i j ^ N = 0 := by
  rw [fullFlagPowerLayerRoot, ← map_pow, fullFlagRoot_pow, map_zero]

theorem fullFlagPowerLayer_aeval_surjective (B N i : ℕ) :
    Function.Surjective
      (MvPolynomial.aeval (fullFlagPowerLayerRoot B N i) :
        MvPolynomial (Fin B) ℂ →ₐ[ℂ] FullFlagPowerLayer B N i) := by
  let q := Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (fullFlagRoot (B + 1) N 0) i)
  let p := Ideal.Quotient.mkₐ ℂ (fullFlagTruncationIdeal (B + 1) N)
  let ev : MvPolynomial (Fin B) ℂ →ₐ[ℂ] FullFlagPowerLayer B N i :=
    MvPolynomial.aeval (fullFlagPowerLayerRoot B N i)
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ a
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ a
  change ∃ g, ev g = q (p f)
  induction f using MvPolynomial.induction_on with
  | C c =>
      refine ⟨MvPolynomial.C c, ?_⟩
      change ev (algebraMap ℂ _ c) = q (p (algebraMap ℂ _ c))
      rw [ev.commutes, p.commutes, q.commutes]
  | add f g hf hg =>
      obtain ⟨a, ha⟩ := hf
      obtain ⟨b, hb⟩ := hg
      exact ⟨a + b, by rw [map_add, ha, hb, map_add, map_add]⟩
  | mul_X f j hf =>
      obtain ⟨a, ha⟩ := hf
      refine Fin.cases ?_ (fun j => ?_) j
      · refine ⟨0, ?_⟩
        rw [map_zero, map_mul, map_mul]
        change 0 = q (p f) * Ideal.Quotient.mk _ (fullFlagRoot (B + 1) N 0)
        rw [fullFlagPowerLayer_first_zero, mul_zero]
      · refine ⟨a * MvPolynomial.X j, ?_⟩
        rw [map_mul, ha, map_mul, map_mul]
        dsimp only [ev]
        rw [MvPolynomial.aeval_X]
        rfl

/-- Every power layer is a quotient of the smaller full flag with unchanged cutoff. -/
theorem fullFlagPowerLayer_rank_le (B N i : ℕ) :
    Module.finrank ℂ (FullFlagPowerLayer B N i) ≤ Module.finrank ℂ (FullFlagRing B N) := by
  letI := fullFlag_finite B N
  exact LinearMap.finrank_le_finrank_of_surjective
    (f := (fullFlagLift B N (fullFlagPowerLayerRoot B N i)
      (fullFlagPowerLayer_elementary B N i) (fullFlagPowerLayerRoot_pow B N i)).toLinearMap)
    (fullFlagLift_surjective B N (fullFlagPowerLayerRoot B N i)
      (fullFlagPowerLayer_elementary B N i) (fullFlagPowerLayerRoot_pow B N i)
      (fullFlagPowerLayer_aeval_surjective B N i))

variable {A : Type*} [CommRing A]

/-- A member of the remaining alphabet satisfies the cutoff improvement in a power layer. -/
theorem alphabetRoot_powerLayer_mem (xs : List A) (x z : A) (N k i : ℕ)
    (hxmem : x ∈ xs) (hN : 0 < N) (hlen : xs.length + 1 = N + k)
    (he : D4Levi.ksEPoly (xs ++ [z]) = 1) (hx : x ^ N = 0) (hi : k ≤ i) :
    x ^ (N - 1) ∈ rootPowerLayerIdeal z i := by
  classical
  have hp := List.perm_cons_erase hxmem
  have hpair : D4Levi.ksEPoly ([x, z] ++ xs.erase x) = 1 := by
    have hprod := (hp.map (fun a : A => 1 - Polynomial.C a * Polynomial.X)).prod_eq
    simp only [D4Levi.ksEPoly, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one] at he ⊢
    rw [hprod] at he
    simp only [List.map_cons, List.prod_cons] at he
    convert he using 1
    ring
  apply (rootPowerLayerIdeal_mem z _ i).mpr
  apply fullFlag_boundary_power_layer x z (xs.erase x) N k i hN ?_ hpair hx hi
  have hlen' := hp.length_eq
  simp only [List.length_cons] at hlen'
  omega

theorem fullFlagPowerLayerRoot_lower_pow (B N k i : ℕ) (hN : 0 < N)
    (hlen : B + 1 = N + k) (hi : k ≤ i) (j : Fin B) :
    fullFlagPowerLayerRoot B N i j ^ (N - 1) = 0 := by
  let xs := List.ofFn fun j : Fin B => fullFlagRoot (B + 1) N j.succ
  let z := fullFlagRoot (B + 1) N 0
  have he : D4Levi.ksEPoly (xs ++ [z]) = 1 := by
    have h := fullFlag_elementaryPolynomial (B + 1) N
    rw [List.ofFn_succ] at h
    simp only [D4Levi.ksEPoly, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h ⊢
    rw [mul_comm]
    exact h
  rw [fullFlagPowerLayerRoot, ← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact alphabetRoot_powerLayer_mem xs _ z N k i (List.mem_ofFn.mpr ⟨j, rfl⟩) hN
    (by simpa only [xs, List.length_ofFn] using hlen) he (fullFlagRoot_pow _ _ _) hi

/-- The later power layers are quotients of the smaller flag with cutoff lowered by one. -/
theorem fullFlagPowerLayer_lower_rank_le (B N k i : ℕ) (hN : 0 < N)
    (hlen : B + 1 = N + k) (hi : k ≤ i) :
    Module.finrank ℂ (FullFlagPowerLayer B N i) ≤
      Module.finrank ℂ (FullFlagRing B (N - 1)) := by
  letI := fullFlag_finite B (N - 1)
  exact LinearMap.finrank_le_finrank_of_surjective
    (f := (fullFlagLift B (N - 1) (fullFlagPowerLayerRoot B N i)
      (fullFlagPowerLayer_elementary B N i)
      (fullFlagPowerLayerRoot_lower_pow B N k i hN hlen hi)).toLinearMap)
    (fullFlagLift_surjective B (N - 1) (fullFlagPowerLayerRoot B N i)
      (fullFlagPowerLayer_elementary B N i) (fullFlagPowerLayerRoot_lower_pow B N k i hN hlen hi)
      (fullFlagPowerLayer_aeval_surjective B N i))

/-- The dimension recursion obtained by deleting a full-flag root. -/
theorem fullFlag_finrank_recursion (B N k : ℕ) (hN : 0 < N)
    (hlen : B + 1 = N + k) (hk : k ≤ N) :
    Module.finrank ℂ (FullFlagRing (B + 1) N) ≤
      k * Module.finrank ℂ (FullFlagRing B N) +
        (N - k) * Module.finrank ℂ (FullFlagRing B (N - 1)) := by
  letI := fullFlag_finite (B + 1) N
  rw [rootPowerFiltration_finrank (fullFlagRoot (B + 1) N 0) N (fullFlagRoot_pow _ _ _)]
  calc
    _ ≤ ∑ i ∈ Finset.range N, if i < k then Module.finrank ℂ (FullFlagRing B N)
        else Module.finrank ℂ (FullFlagRing B (N - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with hik
      · exact fullFlagPowerLayer_rank_le B N i
      · exact fullFlagPowerLayer_lower_rank_le B N k i hN hlen (by omega)
    _ = _ := by
      rw [show Finset.range N = Finset.range (k + (N - k)) by congr 1; omega,
        Finset.sum_range_add]
      have hleft : (∑ i ∈ Finset.range k,
          if i < k then Module.finrank ℂ (FullFlagRing B N)
          else Module.finrank ℂ (FullFlagRing B (N - 1))) =
          k * Module.finrank ℂ (FullFlagRing B N) := by
        simp [Finset.sum_ite_of_true (fun i hi => Finset.mem_range.mp hi)]
      rw [hleft]
      simp

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayer_first_zero
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayer_elementary
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayerRoot_pow
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayer_aeval_surjective
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayer_rank_le
#print axioms VOA.DeligneAudit.SL4T.alphabetRoot_powerLayer_mem
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayerRoot_lower_pow
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayer_lower_rank_le
#print axioms VOA.DeligneAudit.SL4T.fullFlag_finrank_recursion
