/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.ZhuGenGround

/-!
# Modes of the quadratic Heisenberg states on charged Fock states  (Moonshine step M8g, R-gen)

For the quadratic state `u = h_a(-i-1)h_b(-j-1)𝟙 = X(i,a)X(j,b) ⊗ e^0 ∈ V_Λ` and a charged Fock
state `p ⊗ e^γ`, the mode `u₍ₙ₎` preserves the charge and acts on the Fock factor by the finite
normal-ordered sum

  `quadF γ a i b j s p = ∑ᶠ m, :g_a^i(m) g_b^j(s-m): p`,  `s = -n-1`,

where `g_a^i(m) = cf i m • h_a(-(m+i)-1)` is the `m`-th coefficient of `(i!)⁻¹∂^i α_a(z)` and
`h_a(k)` is the oscillator plus the momentum `⟨e_a,γ⟩` at `k = 0` (`smul_quad`).  This is read
off directly from the reconstruction (`YfullGen_word`, `nprod`): no Borcherds identity is used.

Consequences used by the spanning arguments of `FockSpanCharged` / `FockSpanFock`:

* `quadF_lead` — the `(-1)`-mode acts on a state of total degree `≤ d` as multiplication by
  `X(i,a)X(j,b)` modulo total degree `≤ d+1` (same weight).  The nonzero non-leading summands
  each contain one creation and one annihilation/zero mode; the "creation × creation" summands
  other than `m = 0` carry a vanishing coefficient `cf` (`cf_eq_zero`).
* `quadF_X_mul` — for weight-one legs (`i = j = 0`) and `s ≥ -1`, the commutator with a creation
  operator is `[(h_ah_b)_s, X(t,c)] = (t+1)(δ_{cb}X(t+s+2,a) + δ_{ca}X(t+s+2,b))`.
* `quadF_D_one`, `quadF_lead_one` — values on the charged vacuum `e^γ`:
  `(h_ah_b)₍₀₎e^γ = γ_b h_a(-1)e^γ + γ_a h_b(-1)e^γ` and
  `(h_a(-1)h_c(-j-1))₍₋₁₎e^γ = X(0,a)X(j,c) + (-1)^j γ_c X(j+1,a) + (j+1)γ_a X(j+1,c)`.

## Main results
* `hOp`, `cf`, `gOp`, `qTerm`, `quadF`, `quadL`, `Fdw`.
* `smul_quad`, `quadF_lead`, `quadF_X_mul`, `quadF_D_one`, `quadF_lead_one`.

## Status
`sorry`-free; no project axiom (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.FockSpan

open VOA VOA.Moonshine VOA.Moonshine.SigmaExist VOA.Moonshine.ZhuGen LatGen IntegralLattice
  HeisenbergN MvPolynomial
open Submodule

/-- The Fock space of the Leech lattice VOA. -/
abbrev Fk : Type := FockN (rank leech)

/-! ## §1  The boson modes on a fixed charge sector -/

/-- The mode `h_a(k)` on the charge-`γ` sector: oscillator plus momentum `⟨e_a, γ⟩` at `k = 0`. -/
noncomputable def hOp (γ : leech.carrier) (a : Fin (rank leech)) (k : ℤ) : Module.End ℂ Fk :=
  oscN (rank leech) 1 a k + if k = 0 then chargeCoord leech γ a • LinearMap.id else 0

theorem alphaLatGen_latStateGen (a : Fin (rank leech)) (j : ℤ) (p : Fk) (γ : leech.carrier) :
    alphaLatGen leech a j (latStateGen leech p γ) = latStateGen leech (hOp γ a (-j - 1) p) γ := by
  rw [alphaLatGen_apply, LinearMap.add_apply]
  have h1 : LinearMap.rTensor (leech.carrier →₀ ℂ) (currentN (rank leech) 1 a j)
      (latStateGen leech p γ) = latStateGen leech (oscN (rank leech) 1 a (-j - 1) p) γ := by
    simp only [latStateGen, LinearMap.rTensor_tmul, currentN_apply]
  rw [h1, hOp, LinearMap.add_apply, latStateGen_add_boson]
  by_cases hj : j = -1
  · subst hj
    rw [if_pos rfl, if_pos (by norm_num), zGradeOpGen_latStateGen, LinearMap.smul_apply,
      LinearMap.id_apply, latStateGen_smul]
  · rw [if_neg hj, if_neg (by omega), LinearMap.zero_apply, LinearMap.zero_apply]
    simp [latStateGen]

/-- The scalar of the `j`-th coefficient of `(i!)⁻¹ ∂^i α(z)`. -/
noncomputable def cf (i : ℕ) (j : ℤ) : ℂ :=
  ((i.factorial : ℂ))⁻¹ * (((∏ m ∈ Finset.range i, (j + 1 + (m : ℤ))) : ℤ) : ℂ)

/-- The `j`-th coefficient of `Y(h_a(-i-1)𝟙, z)` on the charge-`γ` sector. -/
noncomputable def gOp (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) (j : ℤ) :
    Module.End ℂ Fk :=
  cf i j • hOp γ a (-(j + i) - 1)

theorem genFieldLatGen_latStateGen (a : Fin (rank leech)) (i : ℕ) (j : ℤ) (p : Fk)
    (γ : leech.carrier) :
    genFieldLatGen leech a i j (latStateGen leech p γ)
      = latStateGen leech (gOp γ a i j p) γ := by
  change ((i.factorial : ℂ)⁻¹ • ((VOA.deriv^[i] (alphaLatGen leech a)) j)) _ = _
  rw [VertexOperatorAlgebra.deriv_pow_apply, ← Int.cast_smul_eq_zsmul ℂ]
  simp only [LinearMap.smul_apply]
  rw [alphaLatGen_latStateGen, gOp, LinearMap.smul_apply, latStateGen_smul, smul_smul]
  rfl

/-! ## §2  The quadratic state `h_a(-i-1)h_b(-j-1)𝟙` and its modes -/

theorem latStateGen_quad (i j : ℕ) (a b : Fin (rank leech)) :
    latStateGen leech (X (i, a) * X (j, b) : Fk) 0 = wordStateLatGen leech [(i, a), (j, b)] 0 := by
  rw [wordStateLatGen_eq]
  simp [latStateGen]

theorem leechVOA_Y_quad (i j : ℕ) (a b : Fin (rank leech)) :
    leechVOA.Y (latStateGen leech (X (i, a) * X (j, b) : Fk) 0)
      = nprod (genFieldLatGen_isField leech a i) (YwordLatGen_isField leech [(j, b)] 0) := by
  rw [latStateGen_quad]
  exact (YfullGen_word leech leech_even leech_posDef _ 0).trans (YwordLatGen_cons leech _ _ _)

/-- The neutral length-one word field is the boson generator field (cf. `LatticeBackgroundChargeA`). -/
theorem YwordLatGen_single (i : ℕ) (a : Fin (rank leech)) :
    YwordLatGen leech [(i, a)] 0 = genFieldLatGen leech a i := by
  have h0 : YwordLatGen leech ([] : List (ℕ × Fin (rank leech))) (0 : leech.carrier)
      = (idField : FormalDist (Module.End ℂ (LatModuleGen leech))) := by
    rw [YwordLatGen_nil]
    funext t
    refine LinearMap.ext fun y => ?_
    rw [Yeαvec_zero_apply, idField_apply]
    split_ifs with ht
    · rw [LinearMap.id_apply]
    · rw [LinearMap.zero_apply]
  rw [YwordLatGen_cons]
  have := nprod_idField (genFieldLatGen_isField leech a i)
  convert this using 2

/-- The `m`-th normal-ordered summand of the `s`-th coefficient, on the Fock factor. -/
noncomputable def qTerm (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) (b : Fin (rank leech))
    (j : ℕ) (s m : ℤ) (p : Fk) : Fk :=
  if 0 ≤ m then gOp γ a i m (gOp γ b j (s - m) p) else gOp γ b j (s - m) (gOp γ a i m p)

theorem normalOrdered_quad (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ)
    (b : Fin (rank leech)) (j : ℕ) (s m : ℤ) (p : Fk) :
    normalOrdered (genFieldLatGen leech a i) (YwordLatGen leech [(j, b)] 0) m (s - m)
        (latStateGen leech p γ)
      = latStateGen leech (qTerm γ a i b j s m p) γ := by
  rw [normalOrdered_apply, YwordLatGen_single, qTerm]
  split_ifs <;> simp only [Module.End.mul_apply, genFieldLatGen_latStateGen]

/-- Extraction of the Fock factor of the charge-`γ` sector. -/
noncomputable def piG (γ : leech.carrier) : LatModuleGen leech →ₗ[ℂ] Fk :=
  (TensorProduct.rid ℂ Fk).toLinearMap ∘ₗ LinearMap.lTensor Fk (Finsupp.lapply γ)

theorem piG_latStateGen (γ : leech.carrier) (p : Fk) : piG γ (latStateGen leech p γ) = p := by
  simp [piG, latStateGen, eGen]

theorem latStateGen_inj {γ : leech.carrier} {p q : Fk}
    (h : latStateGen leech p γ = latStateGen leech q γ) : p = q := by
  rw [← piG_latStateGen γ p, h, piG_latStateGen]

theorem latStateGen_eq_zero_iff {γ : leech.carrier} {p : Fk} :
    latStateGen leech p γ = 0 ↔ p = 0 := by
  constructor
  · intro h
    apply latStateGen_inj (γ := γ)
    rw [h]; simp [latStateGen]
  · rintro rfl; simp [latStateGen]

theorem qTerm_support_finite (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ)
    (b : Fin (rank leech)) (j : ℕ) (s : ℤ) (p : Fk) :
    (Function.support fun m => qTerm γ a i b j s m p).Finite := by
  refine (normalOrdered_diag_support_finite (genFieldLatGen_isField leech a i)
    (YwordLatGen_isField leech [(j, b)] 0) s (latStateGen leech p γ)).subset ?_
  intro m hm
  simp only [Function.mem_support, ne_eq] at hm ⊢
  rw [normalOrdered_quad]
  exact fun h => hm (latStateGen_eq_zero_iff.mp h)

/-- The `s`-th coefficient of `Y(h_a(-i-1)h_b(-j-1)𝟙)` on the Fock factor of the charge-`γ`
sector, as a finite normal-ordered sum. -/
noncomputable def quadF (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) (b : Fin (rank leech))
    (j : ℕ) (s : ℤ) (p : Fk) : Fk :=
  ∑ᶠ m, qTerm γ a i b j s m p

/-- The latStateGen map in the boson slot, as a linear map. -/
noncomputable def latL (γ : leech.carrier) : Fk →ₗ[ℂ] LatModuleGen leech :=
  (TensorProduct.mk ℂ Fk (leech.carrier →₀ ℂ)).flip (eGen leech γ)

theorem latL_apply (γ : leech.carrier) (p : Fk) : latL γ p = latStateGen leech p γ := rfl

/-- **The mode formula**: `(h_a(-i-1)h_b(-j-1)𝟙)₍ₙ₎(p ⊗ e^γ) = quadF(-n-1)(p) ⊗ e^γ`. -/
theorem smul_quad (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) (b : Fin (rank leech))
    (j : ℕ) (n : ℤ) (p : Fk) :
    leechVOA.smul (latStateGen leech (X (i, a) * X (j, b) : Fk) 0) n (latStateGen leech p γ)
      = latStateGen leech (quadF γ a i b j (-n - 1) p) γ := by
  rw [PreVertexAlgebra.smul_eq_coeff, leechVOA_Y_quad, nprod_apply]
  simp only [normalOrdered_quad]
  rw [quadF, ← latL_apply, map_finsum (latL γ) (qTerm_support_finite γ a i b j _ p)]
  rfl

theorem quadF_add (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) (b : Fin (rank leech))
    (j : ℕ) (s : ℤ) (p q : Fk) :
    quadF γ a i b j s (p + q) = quadF γ a i b j s p + quadF γ a i b j s q := by
  apply latStateGen_inj (γ := γ)
  have h := smul_quad γ a i b j (-s - 1) (p + q)
  rw [latStateGen_add_boson, PreVertexAlgebra.smul_add_right, smul_quad, smul_quad,
    show -(-s - 1) - 1 = s by ring, ← latStateGen_add_boson] at h
  exact h.symm

theorem quadF_smul (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) (b : Fin (rank leech))
    (j : ℕ) (s : ℤ) (c : ℂ) (p : Fk) :
    quadF γ a i b j s (c • p) = c • quadF γ a i b j s p := by
  apply latStateGen_inj (γ := γ)
  have h := smul_quad γ a i b j (-s - 1) (c • p)
  rw [latStateGen_smul, PreVertexAlgebra.smul_smul_right, smul_quad,
    show -(-s - 1) - 1 = s by ring, ← latStateGen_smul] at h
  exact h.symm

/-- `quadF` as a linear map. -/
noncomputable def quadL (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) (b : Fin (rank leech))
    (j : ℕ) (s : ℤ) : Fk →ₗ[ℂ] Fk where
  toFun := quadF γ a i b j s
  map_add' := quadF_add γ a i b j s
  map_smul' := quadF_smul γ a i b j s

/-! ## §3  Weight and degree bookkeeping -/

theorem totalDegree_pderiv_le (v : ℕ × Fin (rank leech)) (p : Fk) :
    (pderiv v p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [pderiv_monomial]
  refine (totalDegree_monomial_le _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  have h := Finsupp.degree_mono (σ := ℕ × Fin (rank leech)) (R := ℕ)
    (tsub_le_self : s - Finsupp.single v 1 ≤ s)
  simpa [Finsupp.degree, Finsupp.sum] using h

/-- Fock states of total degree `≤ d` and weight `w`. -/
noncomputable def Fdw (d : ℕ) (w : ℤ) : Submodule ℂ Fk :=
  restrictTotalDegree (ℕ × Fin (rank leech)) ℂ d ⊓ gradingZN (rank leech) w

theorem mem_Fdw {d : ℕ} {w : ℤ} {p : Fk} :
    p ∈ Fdw d w ↔ p.totalDegree ≤ d ∧ p ∈ gradingZN (rank leech) w := by
  rw [Fdw, mem_inf, mem_restrictTotalDegree]

theorem Fdw_mono {d d' : ℕ} (h : d ≤ d') (w : ℤ) : Fdw d w ≤ Fdw d' w := by
  intro p hp
  rw [mem_Fdw] at hp ⊢
  exact ⟨hp.1.trans h, hp.2⟩

theorem hOp_neg (γ : leech.carrier) (a : Fin (rank leech)) {k : ℤ} (hk : k < 0) (p : Fk) :
    hOp γ a k p = X ((-k - 1).toNat, a) * p := by
  rw [hOp, LinearMap.add_apply, oscN_apply_neg _ _ _ hk, if_neg (by omega), LinearMap.zero_apply,
    add_zero]

theorem hOp_pos (γ : leech.carrier) (a : Fin (rank leech)) {k : ℤ} (hk : 0 < k) (p : Fk) :
    hOp γ a k p = (k : ℂ) • pderiv ((k - 1).toNat, a) p := by
  rw [hOp, LinearMap.add_apply, oscN_apply_pos _ _ _ hk, if_neg (by omega), LinearMap.zero_apply,
    add_zero, one_smul]

theorem hOp_zero (γ : leech.carrier) (a : Fin (rank leech)) (p : Fk) :
    hOp γ a 0 p = chargeCoord leech γ a • p := by
  rw [hOp, LinearMap.add_apply, oscN_zero, if_pos rfl]
  simp

theorem hOp_mem_gradingZN (γ : leech.carrier) (a : Fin (rank leech)) (k : ℤ) {w : ℤ} {p : Fk}
    (hp : p ∈ gradingZN (rank leech) w) : hOp γ a k p ∈ gradingZN (rank leech) (w - k) := by
  rcases lt_or_ge w 0 with hw | hw
  · rw [gradingZN_of_neg hw, mem_bot] at hp
    subst hp
    rw [map_zero]
    exact zero_mem _
  · have hp' := hp
    rw [gradingZN_of_nonneg hw] at hp'
    have h1 := oscN_mem_gradingZN (rank leech) 1 a k hp'
    rw [Int.toNat_of_nonneg hw] at h1
    rw [hOp, LinearMap.add_apply]
    refine add_mem h1 ?_
    split_ifs with hk
    · subst hk
      rw [sub_zero, LinearMap.smul_apply, LinearMap.id_apply]
      exact smul_mem _ _ hp
    · exact zero_mem _

theorem hOp_deg_nonneg (γ : leech.carrier) (a : Fin (rank leech)) {k : ℤ} (hk : 0 ≤ k) (p : Fk) :
    (hOp γ a k p).totalDegree ≤ p.totalDegree := by
  rcases hk.lt_or_eq with hk | hk
  · rw [hOp_pos γ a hk]
    exact (totalDegree_smul_le _ _).trans (totalDegree_pderiv_le _ _)
  · subst hk
    rw [hOp_zero]
    exact totalDegree_smul_le _ _

theorem X_mul_deg (v : ℕ × Fin (rank leech)) (p : Fk) :
    (X v * p : Fk).totalDegree ≤ p.totalDegree + 1 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X]
  omega

theorem hOp_mem_Fdw_nonneg (γ : leech.carrier) (a : Fin (rank leech)) {k : ℤ} (hk : 0 ≤ k)
    {d : ℕ} {w : ℤ} {p : Fk} (hp : p ∈ Fdw d w) : hOp γ a k p ∈ Fdw d (w - k) := by
  rw [mem_Fdw] at hp ⊢
  exact ⟨(hOp_deg_nonneg γ a hk p).trans hp.1, hOp_mem_gradingZN γ a k hp.2⟩

theorem hOp_mem_Fdw_neg (γ : leech.carrier) (a : Fin (rank leech)) {k : ℤ} (hk : k < 0)
    {d : ℕ} {w : ℤ} {p : Fk} (hp : p ∈ Fdw d w) : hOp γ a k p ∈ Fdw (d + 1) (w - k) := by
  rw [mem_Fdw] at hp ⊢
  refine ⟨?_, hOp_mem_gradingZN γ a k hp.2⟩
  rw [hOp_neg γ a hk]
  exact (X_mul_deg _ _).trans (by omega)

/-! ## §4  The coefficients `cf` -/

theorem cf_zero_left (m : ℤ) : cf 0 m = 1 := by
  simp [cf]

theorem cf_zero_right (i : ℕ) : cf i 0 = 1 := by
  have h : ∏ m ∈ Finset.range i, ((0 : ℤ) + 1 + (m : ℤ))
      = ((∏ m ∈ Finset.range i, (m + 1) : ℕ) : ℤ) := by
    push_cast
    exact Finset.prod_congr rfl fun m _ => by ring
  rw [Finset.prod_range_add_one_eq_factorial] at h
  rw [cf, h]
  push_cast
  exact inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i)

theorem cf_eq_zero {i : ℕ} {m : ℤ} (h1 : -(i : ℤ) ≤ m) (h2 : m ≤ -1) : cf i m = 0 := by
  rw [cf, Finset.prod_eq_zero (i := (-m - 1).toNat) (Finset.mem_range.mpr (by omega))
    (by omega)]
  simp

theorem cf_one (j : ℕ) : cf j 1 = (j : ℂ) + 1 := by
  have h : ∏ m ∈ Finset.range j, ((1 : ℤ) + 1 + (m : ℤ))
      = (((j + 1).factorial : ℕ) : ℤ) := by
    rw [← Finset.prod_range_add_one_eq_factorial, Finset.prod_range_succ']
    push_cast
    rw [mul_one]
    exact Finset.prod_congr rfl fun m _ => by ring
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [cf, h, Nat.factorial_succ]
  push_cast
  field_simp

theorem cf_neg_succ (j : ℕ) : cf j (-((j : ℤ) + 1)) = (-1 : ℂ) ^ j := by
  have h : ∏ m ∈ Finset.range j, (-((j : ℤ) + 1) + 1 + (m : ℤ))
      = (-1) ^ j * ((j.factorial : ℕ) : ℤ) := by
    rw [← Finset.prod_range_reflect, ← Finset.prod_range_add_one_eq_factorial]
    push_cast
    rw [show ((-1 : ℤ)) ^ j = ∏ _m ∈ Finset.range j, (-1 : ℤ) by simp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [cf, h]
  push_cast
  field_simp

/-! ## §5  The leading term of the `(-1)`-mode -/

theorem gOp_mem_Fdw_nonneg (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) {m : ℤ}
    (hm : 0 ≤ -(m + i) - 1) {d : ℕ} {w : ℤ} {p : Fk} (hp : p ∈ Fdw d w) :
    gOp γ a i m p ∈ Fdw d (w + (m + i) + 1) := by
  rw [gOp, LinearMap.smul_apply]
  refine smul_mem _ _ ?_
  have h := hOp_mem_Fdw_nonneg γ a hm hp
  rwa [show w - (-(m + (i : ℤ)) - 1) = w + (m + i) + 1 by ring] at h

theorem gOp_mem_Fdw_neg (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) {m : ℤ}
    (hm : -(m + i) - 1 < 0) {d : ℕ} {w : ℤ} {p : Fk} (hp : p ∈ Fdw d w) :
    gOp γ a i m p ∈ Fdw (d + 1) (w + (m + i) + 1) := by
  rw [gOp, LinearMap.smul_apply]
  refine smul_mem _ _ ?_
  have h := hOp_mem_Fdw_neg γ a hm hp
  rwa [show w - (-(m + (i : ℤ)) - 1) = w + (m + i) + 1 by ring] at h

theorem gOp_eq_zero (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) {m : ℤ}
    (h1 : -(i : ℤ) ≤ m) (h2 : m ≤ -1) (p : Fk) : gOp γ a i m p = 0 := by
  rw [gOp, LinearMap.smul_apply, cf_eq_zero h1 h2, zero_smul]

theorem qTerm_mem_Fdw (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) (b : Fin (rank leech))
    (j : ℕ) {m : ℤ} (hm : m ≠ 0) {d : ℕ} {w : ℤ} {p : Fk} (hp : p ∈ Fdw d w) :
    qTerm γ a i b j 0 m p ∈ Fdw (d + 1) (w + i + j + 2) := by
  rw [qTerm]
  split_ifs with h0
  · have hm' : 0 < m := lt_of_le_of_ne h0 (Ne.symm hm)
    by_cases hmj : m ≤ j
    · rw [gOp_eq_zero γ b j (by omega) (by omega), map_zero]
      exact zero_mem _
    · have h1 := gOp_mem_Fdw_nonneg γ b j (m := 0 - m) (by omega) hp
      have h2 := gOp_mem_Fdw_neg γ a i (m := m) (by omega) h1
      convert h2 using 2
      ring
  · by_cases hmi : -(i : ℤ) ≤ m
    · rw [gOp_eq_zero γ a i hmi (by omega), map_zero]
      exact zero_mem _
    · have h1 := gOp_mem_Fdw_nonneg γ a i (m := m) (by omega) hp
      have h2 := gOp_mem_Fdw_neg γ b j (m := 0 - m) (by omega) h1
      convert h2 using 2
      ring

theorem qTerm_zero (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) (b : Fin (rank leech))
    (j : ℕ) (p : Fk) : qTerm γ a i b j 0 0 p = X (i, a) * X (j, b) * p := by
  rw [qTerm, if_pos le_rfl, sub_zero, gOp, gOp, LinearMap.smul_apply, LinearMap.smul_apply,
    cf_zero_right, cf_zero_right, one_smul, one_smul, hOp_neg _ _ (by omega),
    hOp_neg _ _ (by omega), mul_assoc]
  congr 3 <;> simp

/-- **Leading term**: `(h_a(-i-1)h_b(-j-1)𝟙)₍₋₁₎` acts on a Fock state of degree `≤ d` as
multiplication by `X(i,a)X(j,b)`, up to degree `≤ d + 1`. -/
theorem quadF_lead (γ : leech.carrier) (a : Fin (rank leech)) (i : ℕ) (b : Fin (rank leech))
    (j : ℕ) {d : ℕ} {w : ℤ} {p : Fk} (hp : p ∈ Fdw d w) :
    quadF γ a i b j 0 p - X (i, a) * X (j, b) * p ∈ Fdw (d + 1) (w + i + j + 2) := by
  classical
  have hfin := qTerm_support_finite γ a i b j 0 p
  set S : Finset ℤ := insert (0 : ℤ) hfin.toFinset with hS
  have hsub : Function.support (fun m => qTerm γ a i b j 0 m p) ⊆ (S : Set ℤ) := by
    intro m hm
    rw [hS, Finset.coe_insert, Set.Finite.coe_toFinset]
    exact Set.mem_insert_of_mem _ hm
  rw [quadF, finsum_eq_sum_of_support_subset _ hsub,
    ← Finset.add_sum_erase S _ (Finset.mem_insert_self 0 _), qTerm_zero, add_sub_cancel_left]
  exact sum_mem fun m hm => qTerm_mem_Fdw γ a i b j (Finset.ne_of_mem_erase hm) hp

/-! ## §6  Weight-one legs: commutators with creation operators -/

theorem gOp_zero_index (γ : leech.carrier) (a : Fin (rank leech)) (m : ℤ) :
    gOp γ a 0 m = hOp γ a (-m - 1) := by
  rw [gOp, cf_zero_left, one_smul]
  congr 1
  push_cast
  ring

/-- `[h_b(k), X v] = k·δ`: the commutator of a boson mode with a creation operator. -/
theorem hOp_X_mul (γ : leech.carrier) (b : Fin (rank leech)) (k : ℤ) (v : ℕ × Fin (rank leech))
    (p : Fk) :
    hOp γ b k (X v * p) = X v * hOp γ b k p
      + (if 0 < k ∧ v = ((k - 1).toNat, b) then (k : ℂ) • p else 0) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [hOp_neg γ b hk, hOp_neg γ b hk, if_neg (by omega), add_zero]
    ring
  · subst hk
    rw [hOp_zero, hOp_zero, if_neg (by omega), add_zero, mul_smul_comm]
  · rw [hOp_pos γ b hk, hOp_pos γ b hk, pderiv_mul, pderiv_X, smul_add, mul_smul_comm]
    by_cases hv : v = ((k - 1).toNat, b)
    · subst hv
      rw [if_pos ⟨hk, rfl⟩, Pi.single_eq_same, one_mul, add_comm]
    · rw [if_neg (fun h => hv h.2), Pi.single_eq_of_ne hv, zero_mul, smul_zero, zero_add,
        add_zero]

/-- The commutator correction of `qTerm` (weight-one legs) with `X(t,c)`. -/
noncomputable def corr (a b : Fin (rank leech)) (s : ℤ) (t : ℕ) (c : Fin (rank leech)) (m : ℤ)
    (p : Fk) : Fk :=
  if 0 ≤ m then (if c = b ∧ m = t + s + 2 then ((t : ℂ) + 1) • (X (m.toNat, a) * p) else 0)
  else (if c = a ∧ m = -(t : ℤ) - 2 then ((t : ℂ) + 1) • (X ((s - m).toNat, b) * p) else 0)

theorem qTerm_X_mul (γ : leech.carrier) (a b : Fin (rank leech)) {s : ℤ} (hs : -1 ≤ s) (m : ℤ)
    (t : ℕ) (c : Fin (rank leech)) (p : Fk) :
    qTerm γ a 0 b 0 s m (X (t, c) * p) = X (t, c) * qTerm γ a 0 b 0 s m p + corr a b s t c m p := by
  simp only [qTerm, gOp_zero_index, corr]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, if_pos h0, if_pos h0, hOp_X_mul γ b, map_add]
    simp only [hOp_neg γ a (show -m - 1 < 0 by omega)]
    have hidx : (-(-m - 1) - 1).toNat = m.toNat := by omega
    rw [hidx]
    by_cases h1 : c = b ∧ m = t + s + 2
    · obtain ⟨rfl, hm⟩ := h1
      rw [if_pos ⟨by omega, by simp only [Prod.mk.injEq, and_true]; omega⟩,
        if_pos ⟨rfl, hm⟩]
      rw [show ((-(s - m) - 1 : ℤ) : ℂ) = (t : ℂ) + 1 by rw [hm]; push_cast; ring]
      rw [mul_smul_comm]
      ring
    · rw [if_neg h1, if_neg ?_]
      · ring
      · rintro ⟨hk, hv⟩
        simp only [Prod.mk.injEq] at hv
        exact h1 ⟨hv.2, by omega⟩
  · rw [if_neg h0, if_neg h0, if_neg h0, hOp_X_mul γ a, map_add]
    simp only [hOp_neg γ b (show -(s - m) - 1 < 0 by omega)]
    have hidx : (-(-(s - m) - 1) - 1).toNat = (s - m).toNat := by omega
    rw [hidx]
    by_cases h2 : c = a ∧ m = -(t : ℤ) - 2
    · obtain ⟨rfl, hm⟩ := h2
      rw [if_pos ⟨by omega, by simp only [Prod.mk.injEq, and_true]; omega⟩,
        if_pos ⟨rfl, hm⟩]
      rw [show ((-m - 1 : ℤ) : ℂ) = (t : ℂ) + 1 by rw [hm]; push_cast; ring]
      rw [mul_smul_comm]
      ring
    · rw [if_neg h2, if_neg ?_]
      · ring
      · rintro ⟨hk, hv⟩
        simp only [Prod.mk.injEq] at hv
        exact h2 ⟨hv.2, by omega⟩

theorem finsum_two {f : ℤ → Fk} {m₁ m₂ : ℤ} (hne : m₁ ≠ m₂)
    (h : ∀ m, m ≠ m₁ → m ≠ m₂ → f m = 0) : ∑ᶠ m, f m = f m₁ + f m₂ := by
  classical
  have hsub : Function.support f ⊆ (({m₁, m₂} : Finset ℤ) : Set ℤ) := by
    intro m hm
    by_contra hc
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hc
    exact hm (h m hc.1 hc.2)
  rw [finsum_eq_sum_of_support_subset f hsub, Finset.sum_pair hne]

theorem finsum_three {f : ℤ → Fk} {m₁ m₂ m₃ : ℤ} (h12 : m₁ ≠ m₂) (h13 : m₁ ≠ m₃) (h23 : m₂ ≠ m₃)
    (h : ∀ m, m ≠ m₁ → m ≠ m₂ → m ≠ m₃ → f m = 0) : ∑ᶠ m, f m = f m₁ + f m₂ + f m₃ := by
  classical
  have hsub : Function.support f ⊆ (({m₁, m₂, m₃} : Finset ℤ) : Set ℤ) := by
    intro m hm
    by_contra hc
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hc
    exact hm (h m hc.1 hc.2.1 hc.2.2)
  rw [finsum_eq_sum_of_support_subset f hsub, Finset.sum_insert (by simp [h12, h13]),
    Finset.sum_pair h23, add_assoc]

theorem corr_support (a b : Fin (rank leech)) (s : ℤ) (t : ℕ) (c : Fin (rank leech))
    (p : Fk) : ∀ m, m ≠ (t : ℤ) + s + 2 → m ≠ -(t : ℤ) - 2 → corr a b s t c m p = 0 := by
  intro m h1 h2
  simp only [corr]
  split_ifs with h0 h3 h4 <;> first | rfl | omega

/-- **Commutator with a creation operator** (weight-one legs, `s ≥ -1`):
`[(h_ah_b)_{s}, X(t,c)] = (t+1)(δ_{cb} X(t+s+2,a) + δ_{ca} X(t+s+2,b))`. -/
theorem quadF_X_mul (γ : leech.carrier) (a b : Fin (rank leech)) {s : ℤ} (hs : -1 ≤ s) (t : ℕ)
    (c : Fin (rank leech)) (p : Fk) :
    quadF γ a 0 b 0 s (X (t, c) * p) = X (t, c) * quadF γ a 0 b 0 s p
      + (if c = b then ((t : ℂ) + 1) • (X (((t : ℤ) + s + 2).toNat, a) * p) else 0)
      + (if c = a then ((t : ℂ) + 1) • (X (((t : ℤ) + s + 2).toNat, b) * p) else 0) := by
  have hfin := qTerm_support_finite γ a 0 b 0 s p
  have hcfin : (Function.support fun m => corr a b s t c m p).Finite := by
    refine (Set.toFinite ({(t : ℤ) + s + 2, -(t : ℤ) - 2} : Set ℤ)).subset ?_
    intro m hm
    by_contra hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
    exact hm (corr_support a b s t c p m hc.1 hc.2)
  have hXfin : (Function.support fun m => X (t, c) * qTerm γ a 0 b 0 s m p).Finite :=
    hfin.subset (Function.support_mul_subset_right _ _)
  rw [quadF, quadF, finsum_congr (fun m => qTerm_X_mul γ a b hs m t c p),
    finsum_add_distrib hXfin hcfin, mul_finsum' _ _ hfin,
    finsum_two (by omega) (corr_support a b s t c p)]
  have e1 : corr a b s t c ((t : ℤ) + s + 2) p
      = if c = b then ((t : ℂ) + 1) • (X (((t : ℤ) + s + 2).toNat, a) * p) else 0 := by
    simp only [corr]
    rw [if_pos (by omega)]
    by_cases h : c = b <;> simp [h]
  have e2 : corr a b s t c (-(t : ℤ) - 2) p
      = if c = a then ((t : ℂ) + 1) • (X (((t : ℤ) + s + 2).toNat, b) * p) else 0 := by
    simp only [corr]
    rw [if_neg (by omega)]
    by_cases h : c = a <;> simp [h, show s - (-(t : ℤ) - 2) = (t : ℤ) + s + 2 by ring]
  rw [e1, e2]
  abel

/-! ## §7  Values on the charged vacuum -/

theorem hOp_one_pos (γ : leech.carrier) (a : Fin (rank leech)) {k : ℤ} (hk : 0 < k) :
    hOp γ a k (1 : Fk) = 0 := by
  rw [hOp_pos γ a hk, Derivation.map_one_eq_zero, smul_zero]

theorem hOp_one_zero (γ : leech.carrier) (a : Fin (rank leech)) :
    hOp γ a 0 (1 : Fk) = chargeCoord leech γ a • (1 : Fk) := hOp_zero γ a 1

/-- `(h_a(-1)h_b(-1)𝟙)₍₀₎ e^γ = (γ_b h_a(-1) + γ_a h_b(-1)) e^γ`. -/
theorem quadF_D_one (γ : leech.carrier) (a b : Fin (rank leech)) :
    quadF γ a 0 b 0 (-1) 1
      = chargeCoord leech γ b • (X (0, a) : Fk) + chargeCoord leech γ a • (X (0, b) : Fk) := by
  rw [quadF, finsum_two (m₁ := 0) (m₂ := -1) (by norm_num) ?_]
  · simp only [qTerm, gOp_zero_index]
    rw [if_pos le_rfl, if_neg (by norm_num)]
    norm_num
    rw [hOp_zero, hOp_zero, hOp_neg γ a (by norm_num), hOp_neg γ b (by norm_num),
      mul_smul_comm, mul_smul_comm, mul_one, mul_one]
    rfl
  · intro m h1 h2
    simp only [qTerm, gOp_zero_index]
    split_ifs with h0
    · rw [show -(-1 - m) - 1 = m by ring, hOp_one_pos γ b (by omega), map_zero]
    · rw [hOp_one_pos γ a (by omega), map_zero]

/-- `(h_a(-1)h_c(-j-1)𝟙)₍₋₁₎ e^γ = (X(0,a)X(j,c) + (-1)^j γ_c X(j+1,a) + (j+1) γ_a X(j+1,c)) e^γ`. -/
theorem quadF_lead_one (γ : leech.carrier) (a c : Fin (rank leech)) (j : ℕ) :
    quadF γ a 0 c j 0 1
      = X (0, a) * X (j, c) + ((-1 : ℂ) ^ j * chargeCoord leech γ c) • (X (j + 1, a) : Fk)
        + (((j : ℂ) + 1) * chargeCoord leech γ a) • (X (j + 1, c) : Fk) := by
  rw [quadF, finsum_three (m₁ := 0) (m₂ := (j : ℤ) + 1) (m₃ := -1) (by omega) (by omega)
    (by omega) ?_]
  · rw [qTerm_zero, mul_one]
    congr 1
    · congr 1
      simp only [qTerm, gOp_zero_index]
      rw [if_pos (by omega), gOp, LinearMap.smul_apply,
        show -((0 - ((j : ℤ) + 1)) + j) - 1 = 0 by ring, hOp_one_zero,
        show (0 : ℤ) - ((j : ℤ) + 1) = -((j : ℤ) + 1) by ring, cf_neg_succ,
        hOp_neg γ a (by omega), smul_smul, mul_smul_comm, mul_one]
      simp only [show (-(-((j : ℤ) + 1) - 1) - 1).toNat = j + 1 by omega]
    · simp only [qTerm, gOp_zero_index]
      rw [if_neg (by norm_num), show -(-1 : ℤ) - 1 = 0 by ring, hOp_one_zero, gOp,
        show (0 : ℤ) - -1 = 1 by ring, LinearMap.smul_apply, cf_one, map_smul,
        hOp_neg γ c (by omega), smul_smul, mul_one, mul_comm]
      simp only [show (-(-(1 + (j : ℤ)) - 1) - 1).toNat = j + 1 by omega]
  · intro m h1 h2 h3
    simp only [qTerm, gOp_zero_index]
    split_ifs with h0
    · by_cases hmj : m ≤ j
      · rw [gOp_eq_zero γ c j (by omega) (by omega), map_zero]
      · rw [gOp, LinearMap.smul_apply, hOp_one_pos γ c (by omega), smul_zero, map_zero]
    · rw [hOp_one_pos γ a (by omega), map_zero]

end VOA.Moonshine.FockSpan
