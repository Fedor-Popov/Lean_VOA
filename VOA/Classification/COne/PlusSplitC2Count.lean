import VOA.Classification.COne.PlusSplitC2Charged
import VOA.Classification.COne.PlusSplitC2Neutral
import VOA.Classification.COne.PlusSplitZhuMixed

/-! The sharp C₂ spanning count for m ≥ 5. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusC2Sharp
open PlusC2 PlusUnitary PlusZhuMixed VOA.TripletNilp VOA.LatGen VOA.LatGen.Triplet
  HeisenbergN VOA.Moonshine VOA.IntegralLattice

section Algebra
variable {R : Type*} [CommRing R] [Algebra ℂ R]

def neutralList (m : ℕ) (o w : R) : Fin (m + 1) ⊕ Fin 3 → R
  | .inl i => o ^ i.val
  | .inr i => o ^ i.val * w

theorem neutral_monomial_mem (m : ℕ) (o w : R) (ρ σ τ : ℂ)
    (h8 : w ^ 2 = ρ • (o ^ 2 * w) + σ • o ^ 4)
    (h10 : o ^ 3 * w = τ • o ^ 5) (hn : o ^ (m + 1) = 0) (a b : ℕ) :
    o ^ a * w ^ b ∈ Submodule.span ℂ (Set.range (neutralList m o w)) := by
  let S := Submodule.span ℂ (Set.range (neutralList m o w))
  have ho (a : ℕ) : o ^ a ∈ S := by
    by_cases ha : a < m + 1
    · exact Submodule.subset_span ⟨.inl ⟨a, ha⟩, rfl⟩
    · rw [show a = (m + 1) + (a - (m + 1)) by omega, pow_add, hn, zero_mul]
      exact S.zero_mem
  have how (a : ℕ) : o ^ a * w ∈ S := by
    by_cases ha : a < 3
    · exact Submodule.subset_span ⟨.inr ⟨a, ha⟩, rfl⟩
    · obtain ⟨c, rfl⟩ : ∃ c, a = c + 3 := ⟨a - 3, by omega⟩
      rw [pow_add, mul_assoc, h10, mul_smul_comm, ← pow_add]
      exact S.smul_mem _ (ho _)
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rcases b with _ | _ | b
    · simpa using ho a
    · simpa using how a
    · have heq : o ^ a * w ^ (b + 2) =
          ρ • (o ^ (a + 2) * w ^ (b + 1)) + σ • (o ^ (a + 4) * w ^ b) := by
        rw [pow_add w b 2, h8]
        simp only [mul_add, mul_smul_comm]
        ring_nf
      rw [heq]
      exact S.add_mem (S.smul_mem _ (ih (b + 1) (by omega) (a + 2)))
        (S.smul_mem _ (ih b (by omega) (a + 4)))
end Algebra

variable (m : ℕ) (hm : 1 ≤ m)

def o : A₂ (V2mPlus m hm) := mk₂ _ (V2mPlus m hm).conformalVector
def w : A₂ (V2mPlus m hm) := mk₂ _ (WP m hm)
def e : A₂ (V2mPlus m hm) := mk₂ _ (y0 m hm)

def neutralSpan : Submodule ℂ (A₂ (V2mPlus m hm)) :=
  Submodule.span ℂ (Set.range (neutralList m (o m hm) (w m hm)))

def chargedList (i : Fin 3) : A₂ (V2mPlus m hm) := o m hm ^ i.val * e m hm

def chargedSpan : Submodule ℂ (A₂ (V2mPlus m hm)) :=
  Submodule.span ℂ (Set.range (chargedList m hm))

theorem neutral_monomial (hm5 : 5 ≤ m) (a b : ℕ) :
    o m hm ^ a * w m hm ^ b ∈ neutralSpan m hm := by
  obtain ⟨ρ, σ, h8⟩ := rel8M_holds m hm
  obtain ⟨τ, h10⟩ := rel10M_holds m hm
  have h8' := congrArg (poissonIncl m hm) h8
  have h10' := congrArg (poissonIncl m hm) h10
  simp only [map_pow, map_add, map_smul, map_mul, poissonIncl_mk₂] at h8' h10'
  exact neutral_monomial_mem m (o m hm) (w m hm) ρ σ τ h8' h10'
    (omega_pow_eq_zero m hm hm5) a b

theorem neutral_mem (hm5 : 5 ≤ m) (v : (m1Sub m hm).carrier) :
    mk₂ (V2mPlus m hm) (incl m hm v) ∈ neutralSpan m hm := by
  let T := (neutralSpan m hm).comap ((mk₂ (V2mPlus m hm)).comp (incl m hm))
  suffices h : (⊤ : Submodule ℂ (m1Sub m hm).carrier) ≤ T from h Submodule.mem_top
  rw [← span_homog_eq_top (M1P m hm), Submodule.span_le]
  rintro x ⟨d, hx⟩
  have h := neutral_class_mem_monSpan m hm x hx
  change poissonIncl m hm (mk₂ (M1P m hm) x) ∈ neutralSpan m hm
  refine Submodule.span_induction
    (p := fun y _ => poissonIncl m hm y ∈ neutralSpan m hm) ?_ ?_ ?_ ?_ h
  · intro x hx
    obtain ⟨a, b, -, rfl⟩ := hx
    simp only [map_mul, map_pow, poissonIncl_mk₂]
    exact neutral_monomial m hm hm5 a b
  · simp only [map_zero, Submodule.zero_mem]
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem sec0_mem_neutralSpan (hm5 : 5 ≤ m) (q : FockN (rank (latP m))) :
    mk₂ (V2mPlus m hm) (PP m hm (latStateGen (latP m) q 0)) ∈ neutralSpan m hm := by
  let q' := (1 / 2 : ℂ) • (q + sigmaN _ q)
  have hσ : sigmaN (rank (latP m)) q' = q' := by
    dsimp [q']; rw [map_smul, map_add, sigmaN_sigmaN, add_comm]
  let v : (m1Sub m hm).carrier :=
    ⟨latStateGen (latP m) q' 0, (mem_m1Carrier_iff m hm _).mpr ⟨_, hσ, rfl⟩⟩
  have he : PP m hm (latStateGen (latP m) q 0) = incl m hm v := by
    apply Subtype.ext
    rw [PP_coe, incl_coe, thetaLat_latStateGen, neg_zero,
      ← latStateGen_add_boson, ← latStateGen_csmul]
  rw [he]
  exact neutral_mem m hm hm5 v

theorem omega_power_E_mem (hm2 : 2 ≤ m) (a : ℕ) :
    o m hm ^ a * e m hm ∈ chargedSpan m hm := by
  by_cases ha : a < 3
  · exact Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 3 := ⟨a - 3, by omega⟩
    rw [pow_add, mul_assoc, show o m hm ^ 3 * e m hm = 0 from
      PlusC2Charged.omega_cubed_E m hm hm2, mul_zero]
    exact Submodule.zero_mem _

theorem W_mul_E (hm2 : 2 ≤ m) :
    w m hm * e m hm =
      (-(scalarC (cα m) dC)⁻¹ * scalarC (cα m) aC) • (o m hm ^ 2 * e m hm) := by
  have hd : scalarC (cα m) dC ≠ 0 := by
    have he : scalarC (cα m) dC = ((4 * m - 1 : ℂ) * (4 * m - 9)) := by
      norm_num [scalarC, dC]
      have h : cα m ^ 2 = 2 * (m : ℂ) := by rw [pow_two, cα_sq m hm]
      calc
        _ = 4 * (cα m ^ 2) ^ 2 + -20 * cα m ^ 2 + 9 := by ring
        _ = _ := by rw [h]; ring
    rw [he]
    exact PlusZhuNormalForms.mixed_denominator_ne_zero m hm2
  have h := congrArg (fun x : A₂ (V2mPlus m hm) => (scalarC (cα m) dC)⁻¹ • x)
    (PlusC2Charged.W_E_relation m hm)
  dsimp only at h
  rw [smul_add, smul_smul, inv_mul_cancel₀ hd, one_smul, smul_zero] at h
  apply eq_neg_of_add_eq_zero_left at h
  simpa only [smul_smul, neg_smul, neg_mul] using h

theorem E_mul_neutral_mem (hm2 : 2 ≤ m) {x : A₂ (V2mPlus m hm)}
    (hx : x ∈ neutralSpan m hm) : e m hm * x ∈ chargedSpan m hm := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rcases i with i | i
    · simpa [neutralList, mul_comm] using omega_power_E_mem m hm hm2 i.val
    · change e m hm * (o m hm ^ i.val * w m hm) ∈ _
      rw [show e m hm * (o m hm ^ i.val * w m hm) =
        o m hm ^ i.val * (w m hm * e m hm) by ring, W_mul_E m hm hm2,
        mul_smul_comm, ← mul_assoc, ← pow_add]
      exact Submodule.smul_mem _ _ (omega_power_E_mem m hm hm2 _)
  | zero => simp only [mul_zero, Submodule.zero_mem]
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-- The two surviving sectors lie in the proposed neutral and charged spans. -/
theorem c2_span_eq_top (hm5 : 5 ≤ m) : neutralSpan m hm ⊔ chargedSpan m hm = ⊤ := by
  let S := neutralSpan m hm ⊔ chargedSpan m hm
  let T := S.comap (mk₂ (V2mPlus m hm))
  have hO : O₂ (V2mPlus m hm) ≤ T := by
    intro x hx
    change mk₂ _ x ∈ S
    rw [(mk₂_eq_zero_iff _).mpr hx]
    exact S.zero_mem
  have h0 : sectorP m hm 0 ≤ T := by
    rw [sectorP, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    exact Submodule.mem_sup_left (sec0_mem_neutralSpan m hm hm5 q)
  have hE : eTimesM1Plus m hm ≤ T := by
    rw [eTimesM1Plus, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    change mk₂ _ ((V2mPlus m hm).smul (EP m hm) (-1) _) ∈ S
    rw [mk₂_smul_neg_one, EP_eq_y0, map_smul, smul_mul_assoc]
    exact Submodule.mem_sup_right (Submodule.smul_mem _ _
      (E_mul_neutral_mem m hm (by omega) (sec0_mem_neutralSpan m hm hm5 q)))
  have h1 : sectorP m hm (1 : ℤ) ≤ T := by
    rw [sectorP, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    exact (sup_le hO hE) (sectorOneViaE_holds m hm (by omega) q)
  apply top_unique
  intro x _
  obtain ⟨v, rfl⟩ := (O₂ (V2mPlus m hm)).mkQ_surjective x
  exact (sup_le hO (sup_le h0 h1)) (sector_reduction m hm v)

/-- m+1 omega powers, three W columns, and three E columns. -/
def spanningList : (Fin (m + 1) ⊕ Fin 3) ⊕ Fin 3 → A₂ (V2mPlus m hm) :=
  Sum.elim (neutralList m (o m hm) (w m hm)) (chargedList m hm)

theorem spanningList_span (hm5 : 5 ≤ m) :
    Submodule.span ℂ (Set.range (spanningList m hm)) = ⊤ := by
  have hr : Set.range (spanningList m hm) =
      Set.range (neutralList m (o m hm) (w m hm)) ∪ Set.range (chargedList m hm) := by
    ext x
    constructor
    · rintro ⟨i | i, rfl⟩
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨.inl i, rfl⟩
      · exact ⟨.inr i, rfl⟩
  rw [hr, Submodule.span_union]
  exact c2_span_eq_top m hm hm5

/-- The sharp C₂ upper bound, for every m ≥ 5. -/
theorem finrank_c2_le (hm5 : 5 ≤ m) :
    Module.finrank ℂ (A₂ (V2mPlus m hm)) ≤ m + 7 := by
  have h := finrank_range_le_card (R := ℂ) (spanningList m hm)
  change Module.finrank ℂ (Submodule.span ℂ (Set.range (spanningList m hm))) ≤ _ at h
  rw [spanningList_span m hm hm5, finrank_top] at h
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_assoc] using h

/-- The sharp Zhu upper bound follows without a Schur-to-Zhu identity. -/
theorem finrank_zhu_le (hm5 : 5 ≤ m) :
    Module.finrank ℂ (VOA.A (V2mPlus m hm)) ≤ m + 7 :=
  (V2mPlus_finrank_zhu_le_finrank_c2Quotient m hm).trans (finrank_c2_le m hm hm5)

end VOA.Classification.COne.PlusC2Sharp
