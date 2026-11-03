import VOA.DeligneAudit.SL4TAdjointSiteFlatRelation

/-!
# The flat top relation at one adjoint site, for every number of compound letters

Letters: `x = f₁ (6)`, `y (7)`, `z (8)`, `g = f₂ (9)`, `q (10)`, `F = f₃ (11)`, all of mode zero
unless a mode is written; `[q, x] = z`, and `z` commutes with `x` and `q`. Put `u = g^B v`, so that
`q u` is the corner vector, and let `K₃` be the flat kernel space.

* **Moving `q` past `x`** (`lastPairPow_firstPow_mem_flatKernelSpace`): for all `d, e`,
  `q^e x^d u - [d]_e z^e x^(d-e) u ∈ K₃`, with `[d]_e` the descending factorial. Since `ad q` acts
  on the commuting letters `x, z` as `z ∂_x`, `q x^m u = x^m (q u) + m z x^(m-1) u`; the first term
  lies in `K₃`, and induction on `e` gives the claim.
* **The expanded top word is in the kernel space** (`flatNewton_expandedTopWord_mem`): with
  `f = d + 1 - e`, `D_f (q^e x^d u) ∈ K₃`, because `D_f` commutes with `z^e` and kills
  `x^(d-e) u` (fewer than `f` shifted letters `x`).
* **The flat top relation** (`flatTopRelation_of_compound`): for `h ≥ 1`, `d ≤ B` and
  `e ≤ d + 1`, `F(h) D_f (g^(B-d) q^e y^d v) ∈ M_{>(0,d,0)}`. Expand `x^d g^B v` (the expansion
  identity with no compound letter: its only correction is the marked word
  `g^(B-d+1) y^(d-1) x v`), multiply by `q^e`, apply `F(h) D_f`; `F(h)` kills `K₃`, and the marked
  word lies in the higher first Levi closure, which `q`, `D_f` and `F(h)` preserve.

On the universal module `M(B, h)` this proves the former residual for every `h`
(`adjointSiteFlatTopRelation_holds`; for `h = 0` the generator vanishes when `B ≥ 1`), hence the
flat level relation (`zeroAdjointFlatRelation_all`) and Law B at one adjoint site from the
stratum count alone (`adjointSiteLawB_of_stratumCount`).
-/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

noncomputable section

section Generic

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- `q x = x q + z`. -/
theorem lastPair_first_comm (u : V) :
    ρ.op 10 0 (ρ.op 6 0 u) = ρ.op 6 0 (ρ.op 10 0 u) + ρ.op 8 0 u := by
  have hxq : ρ.op 6 0 (ρ.op 10 0 u) = ρ.op 10 0 (ρ.op 6 0 u) - ρ.op 8 0 u := by
    rw [op_comm_of_single_bracket ρ bracket_first_lastPair 0 0 u]
    simp [sub_eq_add_neg]
  rw [hxq]
  abel

/-- `q x^m u = x^m (q u) + m z x^(m-1) u`. -/
theorem lastPair_firstPow (m : ℕ) (u : V) :
    ρ.op 10 0 ((ρ.op 6 0 ^ m) u) =
      (ρ.op 6 0 ^ m) (ρ.op 10 0 u) + (m : ℂ) • ρ.op 8 0 ((ρ.op 6 0 ^ (m - 1)) u) := by
  rcases m with _ | m
  · simp
  · have hzx : ∀ v, ρ.op 8 0 (ρ.op 6 0 v) = ρ.op 6 0 (ρ.op 8 0 v) :=
      fun v => (op_comm_of_zero_bracket ρ bracket_first_highest 0 0 v).symm
    have h := endomorphism_derivation_pow (ρ.op 10 0) (ρ.op 6 0) (ρ.op 8 0)
      (lastPair_first_comm ρ) hzx m u
    rw [h, Nat.add_sub_cancel, endomorphism_commute_pow (ρ.op 8 0) (ρ.op 6 0) hzx m u]

/-- Every power of a parabolic colour preserves the flat kernel space. -/
theorem flatKernelSpace_parabolicPow (B : ℕ) (c : Fin 15) (hc : flatParabolicColour c) (n : ℕ)
    (v : V) (hv : v ∈ flatKernelSpace ρ w B) : (ρ.op c 0 ^ n) v ∈ flatKernelSpace ρ w B := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact flatKernelSpace_parabolic ρ w B c hc ih

/-- **Moving `q` past `x`.** `q^e x^d g^B v - [d]_e z^e x^(d-e) g^B v ∈ K₃`. -/
theorem lastPairPow_firstPow_mem_flatKernelSpace (B e : ℕ) : ∀ d : ℕ,
    (ρ.op 10 0 ^ e) ((ρ.op 6 0 ^ d) ((ρ.op 9 0 ^ B) w)) -
        (d.descFactorial e : ℂ) • (ρ.op 8 0 ^ e) ((ρ.op 6 0 ^ (d - e)) ((ρ.op 9 0 ^ B) w)) ∈
      flatKernelSpace ρ w B := by
  set u := (ρ.op 9 0 ^ B) w with hu
  induction e with
  | zero =>
    intro d
    simp
  | succ e ih =>
    intro d
    set k := (ρ.op 10 0 ^ e) ((ρ.op 6 0 ^ d) u) -
      (d.descFactorial e : ℂ) • (ρ.op 8 0 ^ e) ((ρ.op 6 0 ^ (d - e)) u) with hk
    have hkK : k ∈ flatKernelSpace ρ w B := ih d
    have hsplit : (ρ.op 10 0 ^ e) ((ρ.op 6 0 ^ d) u) =
        (d.descFactorial e : ℂ) • (ρ.op 8 0 ^ e) ((ρ.op 6 0 ^ (d - e)) u) + k := by
      rw [hk]
      abel
    have hqz : ρ.op 10 0 ((ρ.op 8 0 ^ e) ((ρ.op 6 0 ^ (d - e)) u)) =
        (ρ.op 8 0 ^ e) (ρ.op 10 0 ((ρ.op 6 0 ^ (d - e)) u)) :=
      op_pow_comm_of_zero_bracket ρ bracket_lastPair_highest 0 0 e _
    have hcorner : (ρ.op 6 0 ^ (d - e)) (ρ.op 10 0 u) ∈ flatKernelSpace ρ w B := by
      have h := firstPow_flatCorner_mem ρ w B (d - e)
      rwa [flatCornerVector] at h
    have hstep : (ρ.op 10 0 ^ (e + 1)) ((ρ.op 6 0 ^ d) u) -
        (d.descFactorial (e + 1) : ℂ) • (ρ.op 8 0 ^ (e + 1)) ((ρ.op 6 0 ^ (d - (e + 1))) u) =
        (d.descFactorial e : ℂ) • (ρ.op 8 0 ^ e) ((ρ.op 6 0 ^ (d - e)) (ρ.op 10 0 u)) +
          ρ.op 10 0 k := by
      have hq1 : (ρ.op 10 0 ^ (e + 1)) ((ρ.op 6 0 ^ d) u) =
          ρ.op 10 0 ((ρ.op 10 0 ^ e) ((ρ.op 6 0 ^ d) u)) := by
        rw [pow_succ', Module.End.mul_apply]
      have hz1 : (ρ.op 8 0 ^ (e + 1)) ((ρ.op 6 0 ^ (d - (e + 1))) u) =
          (ρ.op 8 0 ^ e) (ρ.op 8 0 ((ρ.op 6 0 ^ (d - e - 1)) u)) := by
        rw [pow_succ, Module.End.mul_apply, show d - (e + 1) = d - e - 1 by omega]
      have hdf : (d.descFactorial (e + 1) : ℂ) =
          ((d - e : ℕ) : ℂ) * (d.descFactorial e : ℂ) := by
        rw [Nat.descFactorial_succ]
        push_cast
        ring
      rw [hq1, hsplit, map_add, map_smul, hqz, lastPair_firstPow, map_add, map_smul, hz1, hdf]
      module
    rw [hstep]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (flatKernelSpace_parabolicPow ρ w B 8 (by simp [flatParabolicColour])
        e _ hcorner))
      (flatKernelSpace_parabolic ρ w B 10 (by simp [flatParabolicColour]) hkK)

variable (B h : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (hg : ρ.op 9 h w = 0)
variable (hh : 1 ≤ h) (ht : ∀ i s u, h + 1 ≤ s → ρ.op i s u = 0)

include hW in
/-- **The expanded top word is in the kernel space.** For `e ≤ d + 1`, `f = d + 1 - e`,
`D_f (q^e x^d g^B v) ∈ K₃`. -/
theorem flatNewton_expandedTopWord_mem (d e : ℕ) (he : e ≤ d + 1) :
    newtonEnd (flatShiftCurrent ρ) (d + 1 - e)
        ((ρ.op 10 0 ^ e) ((ρ.op 6 0 ^ d) ((ρ.op 9 0 ^ B) w))) ∈ flatKernelSpace ρ w B := by
  set u := (ρ.op 9 0 ^ B) w with hu
  set D := newtonEnd (flatShiftCurrent ρ) (d + 1 - e) with hD
  have hk := lastPairPow_firstPow_mem_flatKernelSpace ρ w B e d
  rw [← hu] at hk
  have hDK := newtonEnd_le_comap _ _ (fun s hs => flatKernelSpace_flatShift ρ w B s hs)
    (d + 1 - e) hk
  rw [Submodule.mem_comap, map_sub, map_smul] at hDK
  by_cases hed : e ≤ d
  · have hcomm := newtonEnd_commute (flatShiftCurrent ρ) (ρ.op 8 0 ^ e)
      (fun s _ => LinearMap.ext fun v => (flatShiftCurrent_highestPow ρ s e v).symm)
      (d + 1 - e)
    have hc' : D ((ρ.op 8 0 ^ e) ((ρ.op 6 0 ^ (d - e)) u)) =
        (ρ.op 8 0 ^ e) (D ((ρ.op 6 0 ^ (d - e)) u)) := by
      simpa only [Module.End.mul_apply] using
        (LinearMap.congr_fun hcomm.eq ((ρ.op 6 0 ^ (d - e)) u)).symm
    have hx : D ((ρ.op 6 0 ^ (d - e)) u) = 0 :=
      newtonEnd_shift_pow_eq_zero (flatShiftCurrent ρ) (fun n => ρ.op 6 n)
        (fun s _ n => LinearMap.ext fun v => by
          simp only [LinearMap.sub_apply, Module.End.mul_apply]
          rw [flatShiftCurrent_first]
          abel)
        u (fun s hs => by
          rw [hu, flatShiftCurrent_middlePow, flatShiftCurrent_source_zero ρ w 1 B 1 hW s hs,
            map_zero]) (d - e) (d + 1 - e) (by omega)
    rw [hc', hx, map_zero, smul_zero, sub_zero] at hDK
    exact hDK
  · have hz : d.descFactorial e = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hz, Nat.cast_zero, zero_smul, sub_zero] at hDK
    exact hDK

/-- With no compound letter, every marked word lies in the higher first Levi closure. -/
theorem flatMarkedSpan_zero_le (B d : ℕ) :
    flatMarkedSpan ρ w B 0 d ≤ higherRadicalCountClosure ρ w ![0, d, 0] := by
  rw [flatMarkedSpan, Submodule.span_le]
  rintro u ⟨a, b, hab, hae, rfl⟩
  have hm := flatMarkedWord_mem_higherRadical ρ w B 0 a b (by omega)
  rwa [hab] at hm

/-- With no compound letter there are no leak words. -/
theorem flatLeakSpan_zero_eq_bot (B d : ℕ) : flatLeakSpan ρ w B 0 d = ⊥ := by
  rw [flatLeakSpan, Submodule.span_eq_bot]
  rintro u ⟨a, b, _, ha1, ha0, _⟩
  omega

include hW hg hh ht in
/-- **The flat top relation.** For `h ≥ 1`, `d ≤ B` and `e ≤ d + 1`, with `f = d + 1 - e`,
`F(h) D_f (g^(B-d) q^e y^d v) ∈ M_{>(0,d,0)}`. -/
theorem flatTopRelation_of_compound (d e : ℕ) (hd : d ≤ B) (he : e ≤ d + 1) :
    ρ.op 11 h (newtonEnd (flatShiftCurrent ρ) (d + 1 - e) (flatNormalWord ρ (B - d) e d 0 w)) ∈
      higherRadicalCountClosure ρ w ![0, d, 0] := by
  set D := newtonEnd (flatShiftCurrent ρ) (d + 1 - e) with hD
  set M := higherRadicalCountClosure ρ w ![0, d, 0] with hM
  set Q := ρ.op 10 0 ^ e with hQ
  have hx2 : ρ.op 6 0 (ρ.op 6 0 w) = 0 := lowering_square_of_label_one ρ w _ hW 0 rfl
  have hexp := flat_expansion ρ w B 0 hx2 d
  rw [flatLeakSpan_zero_eq_bot, bot_sup_eq] at hexp
  set m := (ρ.op 6 0 ^ d) (flatLeakWord ρ w B 0 0 0) -
    ((-1 : ℂ) ^ d * (B.descFactorial d : ℂ)) • flatLeakWord ρ w B 0 0 d with hm
  have hmM : m ∈ M := flatMarkedSpan_zero_le ρ w B d hexp
  have hQm : Q m ∈ M := higherRadicalCountClosure_leviPow ρ w _ 5 0 e hmM
  have hDQm : ρ.op 11 h (D (Q m)) ∈ M :=
    a3LeviClosure_inv ρ _ 4 h (higherRadicalCountClosure_flatNewton ρ w B hW _ _ hQm)
  -- the two words after multiplying by `q^e`
  have hstart : flatLeakWord ρ w B 0 0 0 = (ρ.op 9 0 ^ B) w := by
    simp [flatLeakWord, flatNormalWord]
  have htop : Q (flatLeakWord ρ w B 0 0 d) = flatNormalWord ρ (B - d) e d 0 w := by
    simp only [hQ, flatLeakWord, flatNormalWord, Nat.sub_self, pow_zero, Module.End.one_apply]
    have hcq : Commute (ρ.op 10 0) (ρ.op 9 0) :=
      LinearMap.ext fun v => op_comm_of_zero_bracket ρ bracket_lastPair_middle_zero 0 0 v
    exact LinearMap.congr_fun (hcq.pow_pow e (B - d)).eq _
  have hK : D (Q ((ρ.op 6 0 ^ d) (flatLeakWord ρ w B 0 0 0))) ∈ flatKernelSpace ρ w B := by
    rw [hstart]
    exact flatNewton_expandedTopWord_mem ρ w B hW d e he
  have hF0 := flatKernelSpace_lastLowering_zero ρ w B h hW hg hh ht _ hK
  have hc : ((-1 : ℂ) ^ d * (B.descFactorial d : ℂ)) ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
  have hL : ((-1 : ℂ) ^ d * (B.descFactorial d : ℂ)) • flatLeakWord ρ w B 0 0 d =
      (ρ.op 6 0 ^ d) (flatLeakWord ρ w B 0 0 0) - m := by
    rw [hm]
    abel
  have heq : ((-1 : ℂ) ^ d * (B.descFactorial d : ℂ)) •
      ρ.op 11 h (D (flatNormalWord ρ (B - d) e d 0 w)) =
      ρ.op 11 h (D (Q ((ρ.op 6 0 ^ d) (flatLeakWord ρ w B 0 0 0)))) - ρ.op 11 h (D (Q m)) := by
    rw [← htop, ← map_smul, ← map_smul, ← map_smul, hL, map_sub, map_sub, map_sub]
  have hmem : ((-1 : ℂ) ^ d * (B.descFactorial d : ℂ)) •
      ρ.op 11 h (D (flatNormalWord ρ (B - d) e d 0 w)) ∈ M := by
    rw [heq, hF0, zero_sub]
    exact Submodule.neg_mem _ hDQm
  have hfin := M.smul_mem ((-1 : ℂ) ^ d * (B.descFactorial d : ℂ))⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hfin


end Generic

/-! ### The universal module -/

/-- `[η, g] = h₂`. -/
theorem bracket_middleRaising_middle (e : Fin 15) :
    bracketInt 3 9 e = if e = 13 then 1 else 0 := by
  fin_cases e <;> decide

/-- Without truncation room (`h = 0`) the generator of `M(B, 0)` vanishes when `B ≥ 1`: then
`B v = [η, g] v = 0`. -/
theorem adjointSiteGenerator_eq_zero_of_noRoom (B : ℕ) (hB : 1 ≤ B) :
    adjointSiteGenerator B 0 = 0 := by
  have hrel := adjointSite_relations B 0
  have hg : (adjointSiteRep B 0).op 9 0 (adjointSiteGenerator B 0) = 0 := hrel.2.2
  have hη : (adjointSiteRep B 0).op 3 0 (adjointSiteGenerator B 0) = 0 :=
    hrel.1.raising 3 (by decide) 0
  have hh2 : (adjointSiteRep B 0).op 13 0 (adjointSiteGenerator B 0) =
      (B : ℂ) • adjointSiteGenerator B 0 := hrel.1.cartan_zero 1
  have hc := op_comm_of_single_bracket (adjointSiteRep B 0) bracket_middleRaising_middle 0 0
    (adjointSiteGenerator B 0)
  rw [hg, map_zero, hη, map_zero, zero_add, Nat.add_zero, hh2, Int.cast_one, one_smul] at hc
  have hB' : (B : ℂ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  exact (smul_eq_zero.mp hc.symm).resolve_left hB'

/-- **The flat top relation on `M(B, h)`, for every `h`.** -/
theorem adjointSiteFlatTopRelation_holds (B h : ℕ) : AdjointSiteFlatTopRelation B h := by
  intro d e hd he2 hed
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · rw [adjointSiteGenerator_eq_zero_of_noRoom B (by omega), flatNormalWord_zero, map_zero,
      map_zero]
    exact Submodule.zero_mem _
  · exact flatTopRelation_of_compound (adjointSiteRep B h) (adjointSiteGenerator B h) B h
      (adjointSite_localWeyl B h) (adjointSite_relations B h).2.2 hh
      (fun i s v hs => adjointSiteModule_current_zero B h i s hs v) d e hd (by omega)

set_option synthInstance.maxHeartbeats 100000 in
-- The second Levi multiplicity is built over nested tensor-product coefficient algebras.
/-- **The flat level relation at one adjoint site**, for all `1 ≤ k` and `2k ≤ B`. -/
theorem zeroAdjointFlatRelation_all (B k : ℕ) (hk : 1 ≤ k) (hkB : 2 * k ≤ B) :
    ZeroAdjointFlatRelation B k :=
  zeroAdjointFlatRelation_of_topRelation B k hkB hk (adjointSiteFlatTopRelation_holds B (B - k))

/-- **Law B at one adjoint site from the stratum count alone.** -/
theorem adjointSiteLawB_of_stratumCount (B k : ℕ) (hk : 1 ≤ k) (hkB : 2 * k ≤ B)
    (hS : OneAdjointStratumCount B k) : AdjointSiteLawB B k :=
  adjointSiteLawB_of_stratumCount_and_flatTop B k hk hkB hS
    (adjointSiteFlatTopRelation_holds B (B - k))

end

end VOA.DeligneAudit.SL4T
