import VOA.Huang.DLNSmallAverage

/-!
# The averaging criterion, relative to a central subgroup

Variant of `layer_eq_one_of_averaging` in which the conjugation average of the layer is only
required to lie in a subgroup `C₀` whose lifts are all central. Used for the two-adic layer,
where the `C₃`-average of the layer is the central scalar `1 + 2^a`, not `1`.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

/-- **Averaging criterion, relative version.** As `layer_eq_one_of_averaging`, but the average
is only required to land in a subgroup `C₀ ≤ G` all of whose lifts are central. -/
theorem layer_eq_one_of_averaging_rel {G S E : Type} [Group G] [Group S] [Group E]
    (π : E →* G) (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    (N : Subgroup G) [N.Normal] (ρ : G →* S) (hρ : Function.Surjective ρ)
    (hNρ : N ≤ ρ.ker)
    (hcent : ∀ e m : E, ρ (π e) = 1 → π m ∈ N → Commute e m)
    (Q : Finset S) (hQ : ∀ s : S, ∀ q ∈ Q, s⁻¹ * q * s ∈ Q)
    (p : ℕ) (hNexp : ∀ n ∈ N, n ^ p = 1) (hcop : Nat.Coprime Q.card p)
    (C₀ : Subgroup G) (hC₀ : ∀ e : E, π e ∈ C₀ → e ∈ Subgroup.center E)
    (havg : ∀ g : S → G, (∀ q ∈ Q, ρ (g q) = q) → ∀ n ∈ N,
      (Q.toList.map (fun q => g q * n * (g q)⁻¹)).prod ∈ C₀) :
    ∀ x ∈ ⁅(⊤ : Subgroup E), N.comap π⁆, π x = 1 → x = 1 := by
  classical
  set M : Subgroup E := N.comap π with hM
  haveI hMn : M.Normal := by rw [hM]; infer_instance
  have hMcomm : ∀ a b : E, a ∈ M → b ∈ M → Commute a b := by
    intro a b ha hb
    exact hcent a b (hNρ ha) hb
  letI instM : CommGroup M :=
    { (inferInstance : Group M) with
      mul_comm := fun a b => Subtype.ext (hMcomm a b a.2 b.2) }
  have hkerM : ∀ z : E, π z = 1 → z ∈ M := by
    intro z hz
    change π z ∈ N
    rw [hz]; exact N.one_mem
  -- Chosen lifts.
  let g : S → G := fun q => Function.surjInv hρ q
  have hg : ∀ q, ρ (g q) = q := fun q => Function.surjInv_eq hρ q
  let σ : S → E := fun q => Function.surjInv hs (g q)
  have hσ : ∀ q, π (σ q) = g q := fun q => Function.surjInv_eq hs (g q)
  let c : E → M →* M := fun e => (MulAut.conjNormal e).toMonoidHom
  have hc_apply : ∀ e (m : M), ((c e m : M) : E) = e * m * e⁻¹ := by
    intro e m; exact MulAut.conjNormal_apply e m
  -- The averaging operator.
  let A : M →* M :=
    { toFun := fun m => ∏ q ∈ Q, c (σ q) m
      map_one' := by simp
      map_mul' := by intro a b; simp [Finset.prod_mul_distrib] }
  have hA_apply : ∀ m, A m = ∏ q ∈ Q, c (σ q) m := fun m => rfl
  -- The averaging operator lands in `π⁻¹ C₀`.
  have hA_ker : ∀ m : M, π (A m : E) ∈ C₀ := by
    intro m
    rw [hA_apply, ← Finset.prod_map_toList]
    have hsub : ((((Q.toList.map fun q => c (σ q) m).prod : M)) : E) =
        (Q.toList.map fun q => σ q * (m : E) * (σ q)⁻¹).prod := by
      rw [← M.coe_subtype, map_list_prod, List.map_map]
      congr 1
    rw [hsub, map_list_prod, List.map_map]
    have hm : π (m : E) ∈ N := m.2
    have := havg g (fun q _ => hg q) (π m) hm
    convert this using 2
    apply List.map_congr_left
    intro q _
    simp [hσ]
  have hA_center : ∀ m : M, (A m : E) ∈ Subgroup.center E := fun m => hC₀ _ (hA_ker m)
  -- Conjugation invariance.
  have hA_conj : ∀ (e : E) (m : M), A (c e m) = A m := by
    intro e m
    set s : S := ρ (π e) with hs_def
    have hterm : ∀ q, c (σ q) (c e m) = c e (c (σ (s⁻¹ * q * s)) m) := by
      intro q
      set q' := s⁻¹ * q * s
      set y : E := (σ q')⁻¹ * e⁻¹ * σ q * e with hy
      have hyρ : ρ (π y) = 1 := by
        simp only [hy, map_mul, map_inv, hσ, hg, q', ← hs_def]
        group
      have hym : Commute y (m : E) := hcent y m hyρ m.2
      have heq : σ q * e = e * σ q' * y := by simp only [hy]; group
      apply Subtype.ext
      simp only [hc_apply]
      calc σ q * (e * (m : E) * e⁻¹) * (σ q)⁻¹ = (σ q * e) * (m : E) * (σ q * e)⁻¹ := by group
        _ = (e * σ q' * y) * (m : E) * (e * σ q' * y)⁻¹ := by rw [heq]
        _ = e * σ q' * (y * (m : E) * y⁻¹) * (σ q')⁻¹ * e⁻¹ := by group
        _ = e * (σ q' * (m : E) * (σ q')⁻¹) * e⁻¹ := by
          rw [hym.eq, mul_inv_cancel_right]; group
    rw [hA_apply, hA_apply]
    simp_rw [hterm]
    rw [← map_prod]
    have hre : ∏ q ∈ Q, c (σ (s⁻¹ * q * s)) m = ∏ q ∈ Q, c (σ q) m := by
      apply Finset.prod_nbij' (fun q => s⁻¹ * q * s) (fun q => s * q * s⁻¹)
      · intro q hq; exact hQ s q hq
      · intro q hq; simpa using hQ s⁻¹ q hq
      · intro q _; group
      · intro q _; group
      · intro q _; rfl
    rw [hre, ← hA_apply]
    apply Subtype.ext
    rw [hc_apply, Subgroup.mem_center_iff.mp (hA_center m) e, mul_inv_cancel_right]
  -- Commutators are killed by `A` and have exponent dividing `p`.
  have hgen : ∀ x ∈ ⁅(⊤ : Subgroup E), M⁆, ∃ hx : x ∈ M, A ⟨x, hx⟩ = 1 ∧ x ^ p = 1 := by
    intro x hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨e, -, m, hm, rfl⟩ := hy
      have hmem : ⁅e, m⁆ ∈ M := by
        rw [commutatorElement_def]
        exact M.mul_mem (hMn.conj_mem m hm e) (M.inv_mem hm)
      refine ⟨hmem, ?_, ?_⟩
      · have : (⟨⁅e, m⁆, hmem⟩ : M) = c e ⟨m, hm⟩ * (⟨m, hm⟩ : M)⁻¹ := by
          apply Subtype.ext
          simp [hc_apply, commutatorElement_def]
        rw [this, map_mul, map_inv, hA_conj, mul_inv_cancel]
      · apply commutator_pow_eq_one_of_commute e m p
        · exact hMcomm _ _ (hMn.conj_mem m hm e) hm
        · apply hc
          rw [MonoidHom.mem_ker, map_pow]
          exact hNexp _ hm
    | one => exact ⟨M.one_mem, A.map_one, one_pow p⟩
    | mul y z _ _ hy hz =>
      obtain ⟨hy1, hy2, hy3⟩ := hy
      obtain ⟨hz1, hz2, hz3⟩ := hz
      refine ⟨M.mul_mem hy1 hz1, ?_, ?_⟩
      · have : (⟨y * z, M.mul_mem hy1 hz1⟩ : M) = ⟨y, hy1⟩ * ⟨z, hz1⟩ := rfl
        rw [this, map_mul, hy2, hz2, one_mul]
      · rw [(hMcomm y z hy1 hz1).mul_pow, hy3, hz3, one_mul]
    | inv y _ hy =>
      obtain ⟨hy1, hy2, hy3⟩ := hy
      refine ⟨M.inv_mem hy1, ?_, ?_⟩
      · have : (⟨y⁻¹, M.inv_mem hy1⟩ : M) = (⟨y, hy1⟩ : M)⁻¹ := rfl
        rw [this, map_inv, hy2, inv_one]
      · rw [inv_pow, hy3, inv_one]
  intro x hx hπx
  obtain ⟨hxM, hAx, hxp⟩ := hgen x hx
  have hxc : x ∈ Subgroup.center E := hc hπx
  have hAx' : A ⟨x, hxM⟩ = ⟨x, hxM⟩ ^ Q.card := by
    rw [hA_apply, ← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro q _
    apply Subtype.ext
    rw [hc_apply, Subgroup.mem_center_iff.mp hxc (σ q), mul_inv_cancel_right]
  have hcard : x ^ Q.card = 1 := by
    have := congrArg Subtype.val (hAx'.symm.trans hAx)
    simpa using this
  have := (pow_gcd_eq_one (a := x)).mpr ⟨hcard, hxp⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

end VOA.Huang.DLNSchur
