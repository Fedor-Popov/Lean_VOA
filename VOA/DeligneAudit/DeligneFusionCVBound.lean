import VOA.DeligneAudit.DeligneFusionCVsl2
import VOA.DeligneAudit.DeligneFusionCVPart

/-!
# The Chari–Venkatesh upper bound for `sl₂[t]` (general partitions)

For a partition `ξ` (weakly decreasing, positive parts) and a highest-weight vector `y` of an `sl₂[t]`-module
satisfying CV's relations `Q(r,s) y = 0` whenever `s + r ≥ 1 + rk + Σ_{j>k} ξ_j` (`CVRel`), the `F`-span of `y`
is finite-dimensional of dimension `≤ ∏ⱼ (ξⱼ + 1)` (`cv_bound`).

Proof (CV §6): induction on `(|ξ|, ℓ(ξ), ξ_ℓ)`.  With `y' = F_{ℓ−1}^{ξ_ℓ} y` and `K = F-span(y')`:
`y mod K` satisfies the relations of `ξ⁺` (`arith_plus`, `Q_div`), `y'` satisfies those of `ξ⁻`
(`shift_iter`, `Q_div`, `Q_top`), and `∏(ξ+1) = ∏(ξ⁺+1) + ∏(ξ⁻+1)`.
-/

namespace VOA.DeligneAudit.CVsl2

open VOA.DeligneAudit.CVPart

universe u

/-- The `sl₂[t]` relations. -/
structure SL2 {V : Type u} [AddCommGroup V] [Module ℂ V] (E H F : ℕ → Module.End ℂ V) : Prop where
  hEF : ∀ s k, E s * F k - F k * E s = H (s + k)
  hHF : ∀ p k, H p * F k - F k * H p = (-2 : ℂ) • F (p + k)
  hHE : ∀ p q, H p * E q - E q * H p = (2 : ℂ) • E (p + q)
  hFF : ∀ i j, F i * F j = F j * F i
  hEE : ∀ i j, E i * E j = E j * E i

/-- CV's relations for the partition `ξ`. -/
def CVRel {V : Type u} [AddCommGroup V] [Module ℂ V] (F : ℕ → Module.End ℂ V) (ξ : List ℕ) (y : V) :
    Prop :=
  ∀ r s k, 1 ≤ r → 1 + r * k + T k ξ ≤ s + r → Q F r s y = 0

/-- The statement for one partition. -/
def CVGoal (ξ : List ℕ) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (E H F : ℕ → Module.End ℂ V), SL2 E H F →
    ∀ y : V, (∀ s, E s y = 0) → (∀ p, 1 ≤ p → H p y = 0) → (∃ c : ℂ, H 0 y = c • y) →
      CVRel F ξ y → FiniteDimensional ℂ (Fspan F y) ∧
        Module.finrank ℂ (Fspan F y) ≤ (ξ.map (· + 1)).prod

section Generic

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem Q_one (F : ℕ → Module.End ℂ V) (s : ℕ) : Q F 1 s = F s := by
  simp [Q, Garland.Fs]

theorem Fspan_zero (F : ℕ → Module.End ℂ V) : Fspan F (0 : V) = ⊥ := by
  rw [Fspan, Submodule.span_eq_bot]
  rintro _ ⟨l, rfl⟩
  induction l with
  | nil => rfl
  | cons k l ih => simp only [ECalc.Fw, Module.End.mul_apply] at ih ⊢; rw [ih, map_zero]

/-- Quotients of `sl₂[t]`-modules by stable subspaces. -/
theorem SL2_quot {E H F : ℕ → Module.End ℂ V} (h : SL2 E H F) (K : Submodule ℂ V)
    (hE : ∀ s, K ≤ K.comap (E s)) (hH : ∀ p, K ≤ K.comap (H p)) (hF : ∀ k, K ≤ K.comap (F k)) :
    SL2 (fun s => K.mapQ K (E s) (hE s)) (fun p => K.mapQ K (H p) (hH p))
      (fun k => K.mapQ K (F k) (hF k)) := by
  have qext : ∀ (A B : Module.End ℂ (V ⧸ K)), (∀ v, A (K.mkQ v) = B (K.mkQ v)) → A = B := by
    intro A B hAB; ext v; exact hAB v
  refine ⟨fun s k => ?_, fun p k => ?_, fun p q => ?_, fun i j => ?_, fun i j => ?_⟩ <;>
    refine qext _ _ fun v => ?_ <;>
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul] <;> congr 1
  · have := congrArg (fun T => T v) (h.hEF s k); simpa [Module.End.mul_apply] using this
  · have := congrArg (fun T => T v) (h.hHF p k); simpa [Module.End.mul_apply] using this
  · have := congrArg (fun T => T v) (h.hHE p q); simpa [Module.End.mul_apply] using this
  · have := congrArg (fun T => T v) (h.hFF i j); simpa [Module.End.mul_apply] using this
  · have := congrArg (fun T => T v) (h.hEE i j); simpa [Module.End.mul_apply] using this

/-- Rank–nullity inequality for a submodule. -/
theorem finrank_le_map_add_inf' {W : Type u} [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W)
    (P : Submodule ℂ V) [FiniteDimensional ℂ P] :
    Module.finrank ℂ P ≤ Module.finrank ℂ (P.map f) +
      Module.finrank ℂ (P ⊓ LinearMap.ker f : Submodule ℂ V) := by
  have h := (f.domRestrict P).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have e : Module.finrank ℂ ((LinearMap.ker f).comap P.subtype) =
      Module.finrank ℂ (P ⊓ LinearMap.ker f : Submodule ℂ V) := by
    rw [← Submodule.map_comap_subtype]
    exact (Submodule.equivMapOfInjective P.subtype P.injective_subtype _).finrank_eq
  omega

end Generic

/-! ## Base cases -/

theorem cv_nil : CVGoal.{u} [] := by
  intro V _ _ E H F hS y hE hH _ hR
  have hF : ∀ s, F s y = 0 := fun s => by
    have := hR 1 s 0 le_rfl (by simp [T]); rwa [Q_one] at this
  have hle : Fspan F y ≤ ℂ ∙ y := by
    rw [Fspan, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    induction l with
    | nil => exact Submodule.mem_span_singleton_self y
    | cons k l ih =>
        change ECalc.Fw F l y ∈ ℂ ∙ y at ih
        obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp ih
        change F k (ECalc.Fw F l y) ∈ ℂ ∙ y
        rw [← ht, map_smul, hF k, smul_zero]; exact Submodule.zero_mem _
  haveI : FiniteDimensional ℂ (Fspan F y) := Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, ?_⟩
  calc Module.finrank ℂ (Fspan F y) ≤ Module.finrank ℂ (ℂ ∙ y) := Submodule.finrank_mono hle
    _ ≤ 1 := by simpa using finrank_span_le_card ({y} : Set V)
    _ = _ := by simp

theorem cv_single (a : ℕ) : CVGoal.{u} [a] := by
  intro V _ _ E H F hS y hE hH _ hR
  have hF : ∀ s, 1 ≤ s → F s y = 0 := fun s hs => by
    have := hR 1 s 1 le_rfl (by simp [T]; omega); rwa [Q_one] at this
  have hF0 : (F 0 ^ (a + 1)) y = 0 := by
    have := hR (a + 1) 0 0 (by omega) (by simp [T]; omega); rwa [Q_s_zero] at this
  set S := Submodule.span ℂ (Set.range fun i : Fin (a + 1) => (F 0 ^ (i : ℕ)) y)
  have hS0 : ∀ k, S ≤ S.comap (F k) := by
    intro k
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [← Module.End.mul_apply, ← pow_succ']
      by_cases hi : (i : ℕ) + 1 ≤ a
      · exact Submodule.subset_span ⟨⟨i + 1, by omega⟩, rfl⟩
      · rw [show (i : ℕ) + 1 = a + 1 by omega, hF0]; exact Submodule.zero_mem _
    · rw [F_F0pow hS.hFF, hF k hk, map_zero]; exact Submodule.zero_mem _
  have hle : Fspan F y ≤ S := by
    rw [Fspan, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    induction l with
    | nil => exact Submodule.subset_span ⟨⟨0, by omega⟩, by simp [ECalc.Fw]⟩
    | cons k l ih => exact hS0 k ih
  haveI : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (Fspan F y) := Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, ?_⟩
  calc Module.finrank ℂ (Fspan F y) ≤ Module.finrank ℂ S := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (a + 1)) := finrank_range_le_card _
    _ = _ := by simp

/-! ## The inductive step -/

theorem hw_pow_Fb {V : Type u} [AddCommGroup V] [Module ℂ V] {E H F : ℕ → Module.End ℂ V}
    (hS : SL2 E H F) {L1 : ℕ} (hL1 : 1 ≤ L1) {y : V} (hE : ∀ s, E s y = 0)
    (hH : ∀ p, 1 ≤ p → H p y = 0) (hF : ∀ q, L1 + 1 ≤ q → F q y = 0) {c0 : ℂ} (hH0 : H 0 y = c0 • y) :
    ∀ n, (∀ s, E s ((F L1 ^ n) y) = 0) ∧ (∀ p, 1 ≤ p → H p ((F L1 ^ n) y) = 0) ∧
      (∀ q, L1 + 1 ≤ q → F q ((F L1 ^ n) y) = 0) ∧ ∃ c : ℂ, H 0 ((F L1 ^ n) y) = c • (F L1 ^ n) y
  | 0 => ⟨by simpa using hE, by simpa using hH, by simpa using hF, c0, by simpa using hH0⟩
  | n + 1 => by
      obtain ⟨h1, h2, h3, c, h4⟩ := hw_pow_Fb hS hL1 hE hH hF hH0 n
      obtain ⟨g1, g2, g3⟩ := hw_Fb hS.hEF hS.hHF hS.hFF hL1 h1 h2 h3
      rw [pow_succ', Module.End.mul_apply]
      exact ⟨g1, g2, g3, c - 2, H0_Fb hS.hHF h4⟩

theorem cv_step (μ : List ℕ) (c a b : ℕ) (hb : 1 ≤ b) (hab : b ≤ a)
    (IHp : CVGoal.{u} (Pp μ c a b)) (IHm : CVGoal.{u} (Pm μ c a b)) : CVGoal.{u} (P μ c a b) := by
  intro V _ _ E H F hS y hE hH hH0 hR
  obtain ⟨c0, hH0⟩ := hH0
  set L1 := μ.length + c + 1 with hL1def
  have hFhigh : ∀ q, L1 + 1 ≤ q → F q y = 0 := by
    intro q hq
    have := hR 1 q (μ.length + c + 2) le_rfl (by rw [T_P_high μ c a b _ le_rfl]; omega)
    rwa [Q_one] at this
  obtain ⟨hE', hH', hF', c1, hH0'⟩ := hw_pow_Fb hS (by omega) hE hH hFhigh hH0 b
  set y' := (F L1 ^ b) y with hy'
  obtain ⟨hKE, hKH⟩ := Fspan_stable hS.hEF hS.hHF hE' hH' hH0'
  set K := Fspan F y' with hK
  have hKF : ∀ k, K ≤ K.comap (F k) := fun k => Fspan_F y' k
  have hS' := SL2_quot hS K hKE hKH hKF
  have hL : ∀ q, μ.length + c + 2 ≤ q → F q y = 0 := fun q hq => hFhigh q (by omega)
  have hL' : ∀ q, μ.length + c + 2 ≤ q → F q y' = 0 := fun q hq => hF' q (by omega)
  have e1 : μ.length + c + 2 - 1 = L1 := by omega
  have e2 : μ.length + c + 2 - 2 = μ.length + c := by omega
  -- `y mod K` satisfies the relations of `ξ⁺`
  have hRp : CVRel (fun k => K.mapQ K (F k) (hKF k)) (Pp μ c a b) (K.mkQ y) := by
    intro r s k hr h
    rw [← map_Q K.mkQ (fun k w => rfl) r s y, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rcases arith_plus μ c a b hb hab hr h with ⟨k', hk'⟩ | hdiv
    · rw [hR r s k' hr hk']; exact Submodule.zero_mem _
    · have := Q_div hS.hFF hL r b s (by rw [e2]; exact hdiv)
      rwa [e1] at this
  -- `y'` satisfies the relations of `ξ⁻`
  have htop : (F L1 ^ (b + 1)) y = 0 := by
    have := Q_top hS.hFF hL (b + 1)
    rw [e1] at this
    rw [← this]
    refine hR (b + 1) _ L1 (by omega) ?_
    rw [hL1def, show μ.length + c + 1 = μ.length + (c + 1) by ring, T_P_mid μ c a b (c + 1) le_rfl]
    simp; ring_nf; omega
  have hRm : CVRel F (Pm μ c a b) y' := by
    intro r s k hr h
    by_cases hk : k ≤ μ.length + c
    · have hT := (T_minus μ c a hab k).1 hk
      have hX := shift_iter hS.hEF hS.hHF hS.hHE hS.hFF hS.hEE k (T k (P μ c a b)) L1 (by omega) b y
        hE hH hFhigh (fun r s hr h => X_zero_of_Q hS.hEF hS.hHF hS.hFF hE hH hr (hR r s k hr h))
        r s hr (by omega)
      exact Q_zero_of_X hS.hEF hS.hHF hS.hFF hE' hH' hr hX
    · have hT := (T_minus μ c a hab k).2 (by omega)
      have hrk : r * (μ.length + c + 1) ≤ r * k := Nat.mul_le_mul_left r (by omega)
      have hmem := Q_div hS.hFF hL' r 1 s (by rw [e2]; nlinarith)
      rw [e1, pow_one, hy', ← Module.End.mul_apply, ← pow_succ', htop, Fspan_zero] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
  -- the two halves
  obtain ⟨fdp, bp⟩ := IHp (V ⧸ K) (fun s => K.mapQ K (E s) (hKE s)) (fun p => K.mapQ K (H p) (hKH p))
    (fun k => K.mapQ K (F k) (hKF k)) hS' (K.mkQ y)
    (fun s => by simp [hE s]) (fun p hp => by simp [hH p hp])
    ⟨c0, by simp [hH0]⟩ hRp
  obtain ⟨fdm, bm⟩ := IHm V E H F hS y' hE' hH' ⟨c1, hH0'⟩ hRm
  have hmap : (Fspan F y).map K.mkQ = Fspan (fun k => K.mapQ K (F k) (hKF k)) (K.mkQ y) :=
    map_Fspan K.mkQ (fun k w => rfl) y
  have hinf : Fspan F y ⊓ LinearMap.ker K.mkQ ≤ K := by rw [Submodule.ker_mkQ]; exact inf_le_right
  haveI : FiniteDimensional ℂ (Fspan F y) := by
    apply Module.Finite.iff_fg.mpr
    refine Submodule.fg_of_fg_map_of_fg_inf_ker K.mkQ ?_ ?_
    · rw [hmap]; exact Module.Finite.iff_fg.mp fdp
    · haveI := fdm
      exact Module.Finite.iff_fg.mp (Submodule.finiteDimensional_of_le hinf)
  refine ⟨inferInstance, ?_⟩
  have h1 := finrank_le_map_add_inf' K.mkQ (Fspan F y)
  rw [hmap] at h1
  have h2 : Module.finrank ℂ (Fspan F y ⊓ LinearMap.ker K.mkQ : Submodule ℂ V) ≤ Module.finrank ℂ K := by
    haveI := fdm; exact Submodule.finrank_mono hinf
  have bm' : Module.finrank ℂ K ≤ ((Pm μ c a b).map (· + 1)).prod := bm
  rw [prod_split μ c a b hb hab]
  omega

/-! ## The bound -/

theorem cv_main : ∀ (n ℓ e : ℕ) (ξ : List ℕ), ξ.sum = n → ξ.length = ℓ → T (ℓ - 1) ξ = e →
    ξ.Pairwise (· ≥ ·) → (∀ x ∈ ξ, 1 ≤ x) → CVGoal.{u} ξ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ihl =>
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ihe =>
  intro ξ hn hl he hs hp
  rcases ξ with _ | ⟨x, _ | ⟨y, t⟩⟩
  · exact cv_nil
  · exact cv_single x
  · obtain ⟨μ, c, a, b, hξ, hμ, hab⟩ := shape_exists (x :: y :: t) hs (by simp)
    rw [hξ] at hs hp hn hl he ⊢
    obtain ⟨hμp, ha, hb⟩ := P_pos μ c a b hp
    have hμs := P_sorted_parts μ c a b hs
    refine cv_step μ c a b hb hab ?_ ?_
    · have hps := Pp_sorted μ c a b hμs hμ hab
      have hpp := Pp_pos μ c a b hμp ha hb
      have hsum := sum_Pp μ c a b hb
      rcases Pp_measure μ c a b hb with hlt | ⟨heq, hlt⟩
      · exact ihl _ (by rw [← hl]; exact hlt) _ _ (by rw [hsum, hn]) rfl rfl hps hpp
      · rw [heq, hl, he] at hlt
        exact ihe _ hlt _ (by rw [hsum, hn]) (by rw [heq, hl]) rfl hps hpp
    · have hms := Pm_sorted μ c a b hμs hμ
      have hmp := Pm_pos μ c a b hμp ha hab
      have hsum := sum_Pm μ c a b hab
      exact ihn _ (by omega) _ _ _ rfl rfl rfl hms hmp

/-- **The Chari–Venkatesh upper bound for `sl₂[t]`**: for every partition `ξ`, a highest-weight vector
satisfying CV's relations generates (under the `F`-modes) a space of dimension `≤ ∏ⱼ (ξⱼ + 1)`. -/
theorem cv_bound (ξ : List ℕ) (hs : ξ.Pairwise (· ≥ ·)) (hp : ∀ x ∈ ξ, 1 ≤ x) : CVGoal.{u} ξ :=
  cv_main _ _ _ ξ rfl rfl rfl hs hp

end VOA.DeligneAudit.CVsl2

section AxiomAudit
#print axioms VOA.DeligneAudit.CVsl2.cv_bound
end AxiomAudit
