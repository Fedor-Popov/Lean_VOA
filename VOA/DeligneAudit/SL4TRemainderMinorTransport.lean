import VOA.DeligneAudit.SL4TRemainderStrata

/-! # Transport of top-row minors across a decrease of the cutoff -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A : Type*} [CommRing A]

/-- Determinant linearity transports a spanning relation in one column into an ideal. -/
theorem determinant_updateColumn_mem_of_span {j : ℕ} (M : Matrix (Fin j) (Fin j) A)
    (b : Fin j) (I : Ideal A) (S : Set (Fin j → A))
    (hS : ∀ v ∈ S, (M.updateCol b v).det ∈ I) (v : Fin j → A)
    (hv : v ∈ Submodule.span A S) : (M.updateCol b v).det ∈ I := by
  classical
  induction hv using Submodule.span_induction with
  | mem v hv => exact hS v hv
  | zero =>
      have h := Matrix.det_updateCol_smul M b (0 : A) (0 : Fin j → A)
      simp only [zero_smul, zero_mul] at h
      rw [h]
      exact I.zero_mem
  | add u v hu hv ihu ihv =>
      rw [Matrix.det_updateCol_add]
      exact I.add_mem ihu ihv
  | smul a v hv ih =>
      rw [Matrix.det_updateCol_smul]
      exact I.mul_mem_left a ih

/-- Multiplication by the deleted-root power transports every top minor to the old ideal,
after the next root power has been set to zero. -/
theorem remainderTopMinor_shift_of_nilpotent (ys zs : List A) (z : A) (N k j : ℕ)
    (hN : 0 < N) (hlen : (ys ++ zs).length + 1 = N + k)
    (he : D4Levi.ksEPoly ((ys ++ zs) ++ [z]) = 1) (hz : z ^ (k + 1) = 0)
    (cols : Fin j → ℕ) :
    z ^ k * remainderTopMinor ys (N - 1) j cols ∈ remainderTopIdeal ys N j := by
  classical
  let M : Matrix (Fin j) (Fin j) A := fun a b =>
    alphabetPowerRemainder ys (N - 1 + cols b) (ys.length - j + a.val)
  let v : ℕ → Fin j → A := fun c a =>
    alphabetPowerRemainder ys (N + c) (ys.length - j + a.val)
  by_cases hzero : ∃ b, cols b = 0
  · obtain ⟨b, hb⟩ := hzero
    by_cases hdup : ∃ d, d ≠ b ∧ cols d = 0
    · obtain ⟨d, hdb, hd⟩ := hdup
      have hdet : M.det = 0 := Matrix.det_zero_of_column_eq hdb (by
        intro a
        simp only [M, hd, hb])
      change z ^ k * M.det ∈ _
      rw [hdet, mul_zero]
      exact Ideal.zero_mem _
    · have hother (d : Fin j) (hd : d ≠ b) : 0 < cols d := by
        have hne : cols d ≠ 0 := fun h => hdup ⟨d, hd, h⟩
        omega
      have hspan : z ^ k • (fun a => M a b) ∈ Submodule.span A (Set.range v) := by
        have hcol : z ^ k • (fun a => M a b) =
            -(∑ e ∈ Finset.range k, z ^ e • v (k - 1 - e)) := by
          ext a
          have h := alphabetRemainder_shift_of_nilpotent ys zs z N k 0
            (ys.length - j + a.val) hN hlen he hz
          simp only [Nat.add_zero] at h
          have hs : (∑ e ∈ Finset.range k,
              z ^ e * alphabetPowerRemainder ys (N + k - 1 - e)
                (ys.length - j + a.val)) =
              ∑ e ∈ Finset.range k, z ^ e * v (k - 1 - e) a := by
            apply Finset.sum_congr rfl
            intro e he
            have he' := Finset.mem_range.mp he
            dsimp [v]
            rw [show N + k - 1 - e = N + (k - 1 - e) by omega]
          rw [hs] at h
          simpa only [Pi.smul_apply, Pi.neg_apply, Finset.sum_apply, smul_eq_mul,
            M, hb, Nat.add_zero] using eq_neg_of_add_eq_zero_left h
        rw [hcol]
        apply Submodule.neg_mem
        apply Submodule.sum_mem
        intro e he
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      have hminor : ∀ w ∈ Set.range v,
          (M.updateCol b w).det ∈ remainderTopIdeal ys N j := by
        rintro w ⟨c, rfl⟩
        have hmat : M.updateCol b (v c) =
            (fun a d : Fin j => alphabetPowerRemainder ys
              (N + Function.update (fun d => cols d - 1) b c d)
              (ys.length - j + a.val)) := by
          ext a d
          by_cases hd : d = b
          · subst d
            simp only [Matrix.updateCol_self, Function.update_self, v]
          · rw [Matrix.updateCol_ne hd, Function.update_of_ne hd]
            dsimp [M]
            rw [show N - 1 + cols d = N + (cols d - 1) by have := hother d hd; omega]
        rw [hmat]
        exact remainderTopMinor_mem ys N j _
      have h := determinant_updateColumn_mem_of_span M b (remainderTopIdeal ys N j)
        (Set.range v) hminor _ hspan
      rw [Matrix.det_updateCol_smul, Matrix.updateCol_eq_self] at h
      exact h
  · have hcols (d : Fin j) : 0 < cols d := by
      have hne : cols d ≠ 0 := fun h => hzero ⟨d, h⟩
      omega
    have hminor : remainderTopMinor ys (N - 1) j cols =
        remainderTopMinor ys N j (fun d => cols d - 1) := by
      unfold remainderTopMinor
      congr 1
      ext a d
      rw [show N - 1 + cols d = N + (cols d - 1) by have := hcols d; omega]
    rw [hminor]
    exact Ideal.mul_mem_left _ _ (remainderTopMinor_mem ys N j _)

/-- Every lowered-cutoff top minor enters the old ideal modulo the next deleted-root power. -/
theorem remainderTopMinor_shift_mem (ys zs : List A) (z : A) (N k j : ℕ)
    (hN : 0 < N) (hlen : (ys ++ zs).length + 1 = N + k)
    (he : D4Levi.ksEPoly ((ys ++ zs) ++ [z]) = 1) (cols : Fin j → ℕ) :
    z ^ k * remainderTopMinor ys (N - 1) j cols ∈
      remainderTopIdeal ys N j ⊔ Ideal.span {z ^ (k + 1)} := by
  let I : Ideal A := Ideal.span {z ^ (k + 1)}
  let q := Ideal.Quotient.mk I
  have hq : D4Levi.ksEPoly ((ys.map q ++ zs.map q) ++ [q z]) = 1 := by
    have h := congrArg (Polynomial.map q) he
    simpa only [alphabetElementary_map, List.map_append, List.map_cons,
      List.map_nil, Polynomial.map_one] using h
  have hz : q z ^ (k + 1) = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have h := remainderTopMinor_shift_of_nilpotent (ys.map q) (zs.map q) (q z) N k j hN
    (by simpa only [List.length_append, List.length_map] using hlen) hq hz cols
  rw [← remainderTopIdeal_map q ys N j] at h
  have hm : z ^ k * remainderTopMinor ys (N - 1) j cols ∈
      ((remainderTopIdeal ys N j).map q).comap q := by
    simpa only [Ideal.mem_comap, map_mul, map_pow, remainderTopMinor_map] using h
  rw [Ideal.comap_map_of_surjective q (Ideal.Quotient.mk_surjective)] at hm
  change z ^ k * remainderTopMinor ys (N - 1) j cols ∈
    remainderTopIdeal ys N j ⊔ RingHom.ker (Ideal.Quotient.mk I) at hm
  rw [Ideal.mk_ker] at hm
  exact hm

/-- The whole lowered-cutoff stratum ideal is killed in the corresponding power layer. -/
theorem remainderTopIdeal_shift_le (ys zs : List A) (z : A) (N k j : ℕ)
    (hN : 0 < N) (hlen : (ys ++ zs).length + 1 = N + k)
    (he : D4Levi.ksEPoly ((ys ++ zs) ++ [z]) = 1) :
    remainderTopIdeal ys (N - 1) j ≤
      (remainderTopIdeal ys N j ⊔ Ideal.span {z ^ (k + 1)}).colon {z ^ k} := by
  apply Ideal.span_le.mpr
  rintro x ⟨cols, rfl⟩
  apply Submodule.mem_colon_singleton.mpr
  change remainderTopMinor ys (N - 1) j cols * z ^ k ∈ _
  rw [mul_comm]
  exact remainderTopMinor_shift_mem ys zs z N k j hN hlen he cols

/-- The stratum cutoff improvement persists in every later root-power layer. -/
theorem remainderTopIdeal_later_layer (ys zs : List A) (z : A) (N k j i : ℕ)
    (hN : 0 < N) (hlen : (ys ++ zs).length + 1 = N + k)
    (he : D4Levi.ksEPoly ((ys ++ zs) ++ [z]) = 1) (hi : k ≤ i)
    (x : A) (hx : x ∈ remainderTopIdeal ys (N - 1) j) :
    z ^ i * x ∈ remainderTopIdeal ys N j ⊔ Ideal.span {z ^ (i + 1)} := by
  have h := Submodule.mem_colon_singleton.mp
    (remainderTopIdeal_shift_le ys zs z N k j hN hlen he hx)
  change x * z ^ k ∈ remainderTopIdeal ys N j ⊔ Ideal.span {z ^ (k + 1)} at h
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  apply Submodule.mem_sup.mpr
  refine ⟨z ^ (i - k) * a, Ideal.mul_mem_left _ _ ha,
    z ^ (i + 1) * c, Ideal.mem_span_singleton.mpr ⟨c, rfl⟩, ?_⟩
  have ht := congrArg (fun t => z ^ (i - k) * t) hab
  dsimp only at ht
  rw [hc, mul_add, ← mul_assoc, ← pow_add,
    show i - k + (k + 1) = i + 1 by omega] at ht
  convert ht using 1
  rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel hi, mul_comm]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.determinant_updateColumn_mem_of_span
#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor_shift_of_nilpotent
#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor_shift_mem
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_shift_le
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_later_layer
