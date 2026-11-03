/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.SchurWeylDLMProofDensity
import VOA.Core.BorcherdsIdentity
import VOA.Core.SimpleImage

/-!
# Dong–Li–Mason Schur–Weyl duality, part 2: every irreducible representation occurs

For a simple VOA `W` and a finite `G ≤ Aut W`:

* `sum_smul_smul_eq_zero` — **annihilator stability (locality)**: if `Σᵢ (yᵢ)₍ₙ₎ wᵢ = 0` for every
  `n`, then also `Σᵢ (yᵢ)₍ₙ₎ a₍ₚ₎ wᵢ = 0` (module Jacobi identity with `ℓ` beyond the truncation of
  `a` at the `yᵢ`, then downward induction on `p`); `sum_smul_modeAlgebra_eq_zero` — the same for
  every element of the mode algebra;
* `aut_sum_eq_zero_imp` — **Dedekind's lemma for a simple VOA**: distinct automorphisms are
  linearly independent in `End ℂ 𝒱` (via the annihilator stability, Jacobson density and the
  creation property `y₍₋₁₎𝟙 = y`);
* `multSpace_ne_bot` — **every nonzero finite-dimensional representation occurs**:
  `Hom_G(E, 𝒱) ≠ 0` (the group algebra acts faithfully).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.SchurWeyl

open VOA Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- A `ℤ`-indexed `finsum` supported in `[0, L]` is a `range` sum. -/
theorem finsum_eq_sum_range {X : Type*} [AddCommMonoid X] (f : ℤ → X) (L : ℕ)
    (hneg : ∀ j : ℤ, j < 0 → f j = 0) (hbig : ∀ j : ℤ, (L : ℤ) < j → f j = 0) :
    ∑ᶠ j, f j = ∑ k ∈ Finset.range (L + 1), f k := by
  classical
  rw [finsum_eq_sum_of_support_subset f (s := (Finset.range (L + 1)).image (fun k : ℕ => (k : ℤ)))]
  · rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]
  · intro j hj
    rw [Function.mem_support] at hj
    have h0 : 0 ≤ j := by
      by_contra h
      exact hj (hneg j (by omega))
    have h1 : j ≤ L := by
      by_contra h
      exact hj (hbig j (by omega))
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
    exact ⟨j.toNat, by omega, by omega⟩

theorem cbz_natCast_eq_zero {L : ℕ} {j : ℤ} (h : (L : ℤ) < j) : cbz (L : ℤ) j = 0 := by
  rw [cbz, if_pos (by omega)]
  exact VertexOperatorAlgebra.gBinom_natCast_eq_zero (by omega)

theorem negOnePow_ne_zero (n : ℤ) : negOnePow n ≠ 0 := by
  unfold negOnePow
  split_ifs <;> norm_num

theorem smul_sum_right {ι : Type*} (T : Finset ι) (a : 𝒱) (p : ℤ) (z : ι → 𝒱) :
    ∑ i ∈ T, W.smul a p (z i) = W.smul a p (∑ i ∈ T, z i) :=
  (map_sum (mode (W.Y a) p) z T).symm

/-- **Annihilator stability (locality).**  If `Σᵢ (yᵢ)₍ₙ₎ wᵢ = 0` for every `n`, then
`Σᵢ (yᵢ)₍ₙ₎ a₍ₚ₎ wᵢ = 0` for every `a`, `p`, `n`. -/
theorem sum_smul_smul_eq_zero {ι : Type*} (T : Finset ι) (y w : ι → 𝒱)
    (h : ∀ n : ℤ, ∑ i ∈ T, W.smul (y i) n (w i) = 0) (a : 𝒱) (p n : ℤ) :
    ∑ i ∈ T, W.smul (y i) n (W.smul a p (w i)) = 0 := by
  classical
  choose Ry hRy using fun i => W.regularity a (y i)
  choose Rw hRw using fun i => W.regularity a (w i)
  set L : ℕ := ∑ i ∈ T, (Ry i).toNat with hLdef
  set P : ℤ := ∑ i ∈ T, |Rw i| with hPdef
  have hL : ∀ i ∈ T, ∀ j : ℤ, (L : ℤ) ≤ j → W.smul a j (y i) = 0 := by
    intro i hi j hj
    refine hRy i j ?_
    have : (Ry i).toNat ≤ L := Finset.single_le_sum (f := fun i => (Ry i).toNat)
      (fun _ _ => Nat.zero_le _) hi
    omega
  have hP : ∀ i ∈ T, ∀ q : ℤ, P ≤ q → W.smul a q (w i) = 0 := by
    intro i hi q hq
    refine hRw i q ?_
    have : |Rw i| ≤ P := Finset.single_le_sum (f := fun i => |Rw i|)
      (fun i _ => abs_nonneg (Rw i)) hi
    have := le_abs_self (Rw i)
    omega
  set F : ℤ → ℤ → 𝒱 := fun p q => ∑ i ∈ T, W.smul (y i) q (W.smul a p (w i)) with hFdef
  -- the recurrence from the Jacobi identity
  have hrec : ∀ m n : ℤ, ∑ k ∈ Finset.range (L + 1),
      (negOnePow k * cbz L k) • F (m + k) (L + n - k) = 0 := by
    intro m n
    have hJ : ∀ i ∈ T, ∑ k ∈ Finset.range (L + 1), (negOnePow k * cbz L k) •
        (W.smul a (L + m - k) (W.smul (y i) (n + k) (w i))
          - negOnePow L • W.smul (y i) (L + n - k) (W.smul a (m + k) (w i))) = 0 := by
      intro i hi
      have hj := W.jacobi a (y i) (w i) L m n
      rw [finsum_eq_sum_range _ L (fun j hj => by rw [cbz_apply_neg _ hj]; simp)
        (fun j hj => by rw [cbz_natCast_eq_zero hj]; simp)] at hj
      rw [hj]
      rw [finsum_congr (g := fun _ => (0 : 𝒱)), finsum_zero]
      intro j
      by_cases hj0 : j < 0
      · rw [cbz_apply_neg _ hj0, zero_smul]
      · rw [hL i hi (L + j) (by omega), PreVertexAlgebra.smul_zero_left, smul_zero]
    have hsum := Finset.sum_eq_zero hJ
    rw [Finset.sum_comm] at hsum
    have hterm : ∀ k ∈ Finset.range (L + 1), (∑ i ∈ T, (negOnePow k * cbz L k) •
        (W.smul a (L + m - k) (W.smul (y i) (n + k) (w i))
          - negOnePow L • W.smul (y i) (L + n - k) (W.smul a (m + k) (w i))))
        = -negOnePow L • ((negOnePow k * cbz L k) • F (m + k) (L + n - k)) := by
      intro k _
      rw [← Finset.smul_sum, Finset.sum_sub_distrib, smul_sum_right, h (n + k),
        PreVertexAlgebra.smul_zero_right, zero_sub, ← Finset.smul_sum, smul_neg, neg_smul,
        smul_comm]
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum] at hsum
    exact (smul_eq_zero.mp hsum).resolve_left (neg_ne_zero.mpr (negOnePow_ne_zero _))
  -- downward induction on the mode of `a`
  have hbase : ∀ m : ℤ, P ≤ m → ∀ q, F m q = 0 := by
    intro m hm q
    apply Finset.sum_eq_zero
    intro i hi
    rw [hP i hi m hm, PreVertexAlgebra.smul_zero_right]
  have hF : ∀ d : ℕ, ∀ m : ℤ, P - m ≤ d → ∀ q, F m q = 0 := by
    intro d
    induction d with
    | zero => intro m hm q; exact hbase m (by omega) q
    | succ d ih =>
      intro m hm q
      by_cases hmP : P ≤ m
      · exact hbase m hmP q
      have hr := hrec m (q - L)
      rw [Finset.sum_eq_single 0] at hr
      · simpa [negOnePow] using hr
      · intro k _ hk0
        rw [ih (m + k) (by omega), smul_zero]
      · intro h0
        exact absurd (Finset.mem_range.mpr (Nat.succ_pos L)) h0
  exact hF (P - p).toNat p (by omega) n

/-- Annihilator stability for every element of the mode algebra. -/
theorem sum_smul_modeAlgebra_eq_zero {ι : Type*} (T : Finset ι) (y : ι → 𝒱) {f : Module.End ℂ 𝒱}
    (hf : f ∈ modeAlgebra W) : ∀ w : ι → 𝒱, (∀ n : ℤ, ∑ i ∈ T, W.smul (y i) n (w i) = 0) →
      ∀ n : ℤ, ∑ i ∈ T, W.smul (y i) n (f (w i)) = 0 := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨a, p, rfl⟩ := hf
    intro w hw n
    exact sum_smul_smul_eq_zero T y w hw a p n
  | algebraMap c =>
    intro w hw n
    simp only [Module.algebraMap_end_apply, PreVertexAlgebra.smul_smul_right]
    rw [← Finset.smul_sum, hw n, smul_zero]
  | add f g _ _ hf hg =>
    intro w hw n
    simp only [LinearMap.add_apply, PreVertexAlgebra.smul_add_right, Finset.sum_add_distrib,
      hf w hw n, hg w hw n, add_zero]
  | mul f g _ _ hf hg =>
    intro w hw n
    exact hf (fun i => g (w i)) (hg w hw) n

/-- **Dedekind's lemma for a simple VOA**: distinct automorphisms are linearly independent as
operators on `𝒱`. -/
theorem aut_sum_eq_zero_imp (hW : W.IsSimple) (G : Subgroup (Aut W)) :
    ∀ (S : Finset G) (c : G → ℂ), (∀ v : 𝒱, ∑ g ∈ S, c g • (g : Aut W) v = 0) →
      ∀ g ∈ S, c g = 0 := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => intro c _ g hg; simp at hg
  | insert k T hk ih =>
    intro c hrel
    -- Step 1: `Σ_{g∈T} (c_g (gu - ku))₍ₙ₎ (gv) = 0`.
    have h1 : ∀ (u v : 𝒱) (n : ℤ),
        ∑ g ∈ T, W.smul (c g • ((g : Aut W) u - (k : Aut W) u)) n ((g : Aut W) v) = 0 := by
      intro u v n
      have hA := hrel (W.smul u n v)
      simp only [Aut.map_smul] at hA
      have hB : W.smul ((k : Aut W) u) n (∑ g ∈ insert k T, c g • (g : Aut W) v) = 0 := by
        rw [hrel v, PreVertexAlgebra.smul_zero_right]
      rw [← smul_sum_right] at hB
      have hexp : ∀ g : G, W.smul (c g • ((g : Aut W) u - (k : Aut W) u)) n ((g : Aut W) v)
          = c g • W.smul ((g : Aut W) u) n ((g : Aut W) v)
            - W.smul ((k : Aut W) u) n (c g • (g : Aut W) v) := by
        intro g
        rw [← smulLeft_apply, map_smul, map_sub, smulLeft_apply, smulLeft_apply,
          PreVertexAlgebra.smul_smul_right, smul_sub]
      have hD : ∑ g ∈ insert k T,
          W.smul (c g • ((g : Aut W) u - (k : Aut W) u)) n ((g : Aut W) v) = 0 := by
        simp only [hexp, Finset.sum_sub_distrib, hA, hB, sub_zero]
      rw [Finset.sum_insert hk, sub_self, smul_zero, PreVertexAlgebra.smul_zero_left, zero_add] at hD
      exact hD
    -- Step 2: the induction hypothesis on `T`.
    have h2 : ∀ (u : 𝒱) (μ : Module.Dual ℂ 𝒱), ∀ g ∈ T,
        c g * μ ((g : Aut W) u - (k : Aut W) u) = 0 := by
      intro u μ
      apply ih (fun g => c g * μ ((g : Aut W) u - (k : Aut W) u))
      intro v
      rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
      intro l
      obtain ⟨f, hf, hfF⟩ := exists_modeAlgebra_eq hW (LinearMap.smulRight l W.vacuum)
        (T.image fun g : G => (g : Aut W) v)
      have hs := sum_smul_modeAlgebra_eq_zero T (fun g => c g • ((g : Aut W) u - (k : Aut W) u))
        hf (fun g => (g : Aut W) v) (h1 u v) (-1)
      have hval : ∀ g ∈ T, W.smul (c g • ((g : Aut W) u - (k : Aut W) u)) (-1) (f ((g : Aut W) v))
          = l ((g : Aut W) v) • (c g • ((g : Aut W) u - (k : Aut W) u)) := by
        intro g hg
        rw [hfF _ (Finset.mem_image_of_mem _ hg), LinearMap.smulRight_apply,
          PreVertexAlgebra.smul_smul_right, PreVertexAlgebra.smul_def, (W.creation _).1]
      rw [Finset.sum_congr rfl hval] at hs
      have hμ := congrArg μ hs
      rw [map_sum, map_zero] at hμ
      rw [map_sum]
      simp only [map_smul, smul_eq_mul] at hμ ⊢
      rw [← hμ]
      refine Finset.sum_congr rfl fun g _ => ?_
      ring
    -- Step 3: the coefficients on `T` vanish (`G` acts faithfully).
    have h3 : ∀ g ∈ T, c g = 0 := by
      intro g hg
      by_contra hc
      apply hk
      have hgk : g = k := by
        apply Subtype.ext
        apply Aut.ext
        apply LinearEquiv.ext
        intro u
        rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
        intro μ
        exact (mul_eq_zero.mp (h2 u μ g hg)).resolve_left hc
      rw [← hgk]
      exact hg
    -- Step 4: the remaining coefficient, at the vacuum.
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hgT
    · have hv := hrel W.vacuum
      rw [Finset.sum_insert hk, Finset.sum_eq_zero (fun g hg => by rw [h3 g hg, zero_smul]),
        add_zero] at hv
      have hkv : (g : Aut W) W.vacuum = W.vacuum := (g : Aut W).map_vacuum
      rw [hkv] at hv
      exact (smul_eq_zero.mp hv).resolve_right hW.vacuum_ne_zero
    · exact h3 g hgT

/-- An irreducible representation is on a nontrivial space. -/
theorem nontrivial_of_isIrreducible {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
    {σ : Representation ℂ G E} (hσ : σ.IsIrreducible) : Nontrivial E := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  haveI := hσ
  apply (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  exact Subsingleton.elim _ _

/-- A `G`-stable subspace of an irreducible representation is `⊥` or `⊤`. -/
theorem stable_eq_bot_or_top {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
    {σ : Representation ℂ G E} (hσ : σ.IsIrreducible) (N : Submodule ℂ E)
    (hN : ∀ (g : G) (x : E), x ∈ N → σ g x ∈ N) : N = ⊥ ∨ N = ⊤ := by
  rcases hσ.eq_bot_or_eq_top ⟨N, fun g x hx => hN g x hx⟩ with h | h
  · left; exact congrArg Subrepresentation.toSubmodule h
  · right; exact congrArg Subrepresentation.toSubmodule h

/-- **Every nonzero representation occurs in a simple VOA** (clause "occurs" of DLM):
`Hom_G(E, 𝒱) ≠ 0` for every finite `G ≤ Aut W` and every nontrivial `E`. -/
theorem multSpace_ne_bot (hW : W.IsSimple) (G : Subgroup (Aut W)) [Finite G] {E : Type*}
    [AddCommGroup E] [Module ℂ E] (σ : Representation ℂ G E) [Nontrivial E] :
    multSpace G σ ≠ ⊥ := by
  classical
  haveI := Fintype.ofFinite G
  obtain ⟨e₀, he₀⟩ := exists_ne (0 : E)
  obtain ⟨μ, hμ⟩ : ∃ μ : Module.Dual ℂ E, μ e₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact he₀ ((Module.forall_dual_apply_eq_zero_iff ℂ e₀).mp h)
  obtain ⟨v, hv⟩ : ∃ v : 𝒱, ∑ g : G, μ (σ g⁻¹ e₀) • (g : Aut W) v ≠ 0 := by
    by_contra h
    push Not at h
    have h1 := aut_sum_eq_zero_imp hW G Finset.univ (fun g => μ (σ g⁻¹ e₀)) h 1
      (Finset.mem_univ _)
    simp only [inv_one, map_one, Module.End.one_apply] at h1
    exact hμ h1
  let φ : E →ₗ[ℂ] 𝒱 := ∑ g : G, (μ ∘ₗ σ g⁻¹).smulRight ((g : Aut W) v)
  have hφ : φ ∈ multSpace G σ := by
    intro h e
    simp only [φ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply]
    rw [← Aut.coe_toLinearEquiv, map_sum]
    simp only [map_smul]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulLeft, mul_inv_rev, map_mul, Module.End.mul_apply,
      Representation.inv_self_apply, Subgroup.coe_mul, Aut.mul_apply]
  intro hbot
  have h0 : φ = 0 := by
    rw [hbot] at hφ
    exact (Submodule.mem_bot ℂ).mp hφ
  apply hv
  have := congrArg (fun ψ : E →ₗ[ℂ] 𝒱 => ψ e₀) h0
  simpa [φ] using this

end VOA.Huang.SchurWeyl
