/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusC2Eval

/-!
# `M(1)⁺`: certificate infrastructure and the two relations

Notation of `PlusC2M1Ring.lean`.  Elements of `M1P` are described by raw polynomials
(`PlusC2Eval.lean`); products are computed by `polyAct`, and identities between the resulting
polynomials are checked by `decide +kernel` (kernel reduction only; no `native_decide`, no
extra axioms).

## Main results

* `M1P_smul_poly` — `u₍ₙ₎v` of two polynomial states is the polynomial `polyAct Q (−n−1) w P`.
* `mem_of_lc` — a polynomial identity `y = Σ cᵢ xᵢ` with `xᵢ` in a submodule puts `y` in it.
* `rel8M_holds : Rel8M m hm` — `W̄² = (132/7)·ω̄²W̄` in `A₂(M(1)⁺)`.
* `rel10M_holds : Rel10M m hm` — `ω̄³W̄ = 0` in `A₂(M(1)⁺)`.

(With the quadratic generator `W⁴` instead of Dong–Nagatomo's `J = W⁴ + (const)·L(−2)²𝟙` the
constants of Yamskulna's Cor. 5.10 / 5.14(3) become `ρ = 132/7, σ = 0` and `τ = 0`.  The
certificates were found by exact rational linear algebra, `scratchpad/q2c/cert2.py`.)
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN VOA.Moonshine LatMod
  MvPolynomial VOA.TripletNilp VOA.SparseRational PlusC2Eval

namespace PlusC2

variable (m : ℕ) (hm : 1 ≤ m)

/-! ## §1  Polynomial states of `M1P` -/

/-- The raw polynomials of `𝟙`, `ω = ½x₀²` and `W⁴ = 4x₀x₂ − 3x₁²`. -/
def vacR : RawPoly ℕ := [(1, [])]
def omR : RawPoly ℕ := [(1 / 2, [0, 0])]
def WR : RawPoly ℕ := [(4, [0, 2]), (-3, [1, 1])]

/-- `y` has polynomial `P`. -/
def HasPoly (y : (m1Sub m hm).carrier) (P : RawPoly ℕ) : Prop :=
  (y : LatModuleGen (latP m)) = latStateGen (latP m) (evR (a0 m) P) 0

theorem hasPoly_vacuum : HasPoly m hm (M1P m hm).vacuum vacR := by
  change latStateGen (latP m) (vacuumN _) 0 = _
  congr 1
  simp [vacR, evalRaw, evalWord, vacuumN]

theorem hasPoly_omega : HasPoly m hm (ωM m hm) omR := by
  rw [HasPoly, omegaLatGen_eq, wordStateLatGen_eq]
  change _ = (evR (a0 m) omR) ⊗ₜ[ℂ] eGen (latP m) 0
  rw [TensorProduct.smul_tmul']
  congr 1
  simp [omR, evalRaw, evalWord, MvPolynomial.smul_eq_C_mul]

theorem hasPoly_W : HasPoly m hm (WM m hm) WR := by
  change latStateGen (latP m) (W4poly m) 0 = _
  congr 1
  simp only [WR, evalRaw, evalWord, W4poly, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
  rw [algebraMap_rat_mul, algebraMap_rat_mul]
  push_cast
  module

/-- **Products of polynomial states.** -/
theorem M1P_smul_poly {u v : (m1Sub m hm).carrier} {Q P : RawPoly ℕ} (hu : HasPoly m hm u Q)
    (hv : HasPoly m hm v P) (w : ℕ) (hw : ∀ t ∈ P, wWt t.2 = w) (n : ℤ) :
    HasPoly m hm ((M1P m hm).smul u n v) (polyAct Q (-n - 1) w P) := by
  rw [HasPoly, M1P_smul_coe, hu, hv, V2m_smul_evR m hm Q P n w hw]

theorem hasPoly_normR {y : (m1Sub m hm).carrier} {P : RawPoly ℕ} (h : HasPoly m hm y P) :
    HasPoly m hm y (normR P) := by
  rw [HasPoly, h, evR_normR]

theorem hasPoly_of_normR_eq {y : (m1Sub m hm).carrier} {P P' : RawPoly ℕ} (h : HasPoly m hm y P)
    (he : normR P = normR P') : HasPoly m hm y P' := by
  rw [HasPoly, h, ← evR_normR _ P, he, evR_normR]

/-- `σ(x_{i₁}⋯x_{i_k}) = (−1)^k x_{i₁}⋯x_{i_k}`. -/
theorem sigma_evalWord : ∀ w : List ℕ,
    sigmaN (rank (latP m)) (evalWord (xv (a0 m)) w) = ((-1 : ℂ) ^ w.length) • evalWord (xv (a0 m)) w
  | [] => by simp [evalWord, sigmaN_one]
  | i :: w => by
    rw [evalWord_cons, sigmaN_mul, sigmaN_X, sigma_evalWord w, List.length_cons, pow_succ,
      mul_neg_one, neg_smul, neg_mul, mul_smul_comm]

/-- The state `x_{i₁}⋯x_{i_k}𝟙` for an even-length word. -/
noncomputable def mkW (b : List ℕ) (hb : Even b.length) : (m1Sub m hm).carrier :=
  ⟨latStateGen (latP m) (evR (a0 m) [(1, b)]) 0, (mem_m1Carrier_iff m hm _).mpr ⟨_, by
    simp only [evalRaw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      map_one, one_mul]
    rw [sigma_evalWord, Even.neg_one_pow hb, one_smul], rfl⟩⟩

theorem hasPoly_mkW (b : List ℕ) (hb : Even b.length) : HasPoly m hm (mkW m hm b hb) [(1, b)] := rfl

/-! ## §2  Linear combinations -/

/-- `Σ cᵢ Pᵢ`. -/
def lc : List (ℚ × RawPoly ℕ) → RawPoly ℕ
  | [] => []
  | (c, B) :: rest => scaleR c B ++ lc rest

/-- **A polynomial identity `y = Σ cᵢ xᵢ` with every `xᵢ ∈ S` puts `y` in `S`.** -/
theorem mem_of_lc (S : Submodule ℂ (m1Sub m hm).carrier) :
    ∀ (L : List (ℚ × RawPoly ℕ)), (∀ t ∈ L, ∃ x ∈ S, HasPoly m hm x t.2) →
      ∃ z ∈ S, HasPoly m hm z (lc L)
  | [], _ => ⟨0, Submodule.zero_mem _, by
      rw [HasPoly, lc, evR_nil]; simp [latStateGen]⟩
  | (c, B) :: rest, h => by
    obtain ⟨x, hxS, hx⟩ := h (c, B) List.mem_cons_self
    obtain ⟨z, hzS, hz⟩ := mem_of_lc S rest fun t ht => h t (List.mem_cons_of_mem _ ht)
    refine ⟨((c : ℚ) : ℂ) • x + z, Submodule.add_mem _ (Submodule.smul_mem _ _ hxS) hzS, ?_⟩
    rw [HasPoly, lc, evR_append, evR_scaleR, latStateGen_add_boson, latStateGen_csmul,
      Submodule.coe_add, Submodule.coe_smul, hx, hz]

theorem mem_of_cert (S : Submodule ℂ (m1Sub m hm).carrier) {y : (m1Sub m hm).carrier}
    {A : RawPoly ℕ} (hy : HasPoly m hm y A) (L : List (ℚ × RawPoly ℕ))
    (hL : ∀ t ∈ L, ∃ x ∈ S, HasPoly m hm x t.2) (h : normR A = normR (lc L)) : y ∈ S := by
  obtain ⟨z, hzS, hz⟩ := mem_of_lc m hm S L hL
  have : y = z := by
    apply Subtype.ext
    rw [hy, hz, ← evR_normR _ A, h, evR_normR]
  rw [this]; exact hzS

/-! ## §3  `O₂` generators -/

theorem T_mem_O₂ (b : List ℕ) (hb : Even b.length) :
    ∃ x ∈ O₂ (M1P m hm), HasPoly m hm x (polyAct [(1, b)] 1 0 vacR) := by
  refine ⟨(M1P m hm).smul (mkW m hm b hb) (-2) (M1P m hm).vacuum,
    smul_le_neg_two_mem_O₂ _ _ _ le_rfl, ?_⟩
  have := M1P_smul_poly m hm (hasPoly_mkW m hm b hb) (hasPoly_vacuum m hm) 0 (by decide) (-2)
  simpa using this

theorem L3_mem_O₂ (b : List ℕ) (hb : Even b.length) :
    ∃ x ∈ O₂ (M1P m hm), HasPoly m hm x (polyAct omR 1 (wWt b) [(1, b)]) := by
  refine ⟨(M1P m hm).smul (ωM m hm) (-2) (mkW m hm b hb),
    smul_le_neg_two_mem_O₂ _ _ _ le_rfl, ?_⟩
  have := M1P_smul_poly m hm (hasPoly_omega m hm) (hasPoly_mkW m hm b hb) (wWt b) (by simp) (-2)
  simpa using this

/-- The `O₂` certificate format: `Σ cᵢ T(bᵢ) + Σ dⱼ L(−3)(b'ⱼ)`. -/
def o2cert (Tl Ll : List (ℚ × List ℕ)) : List (ℚ × RawPoly ℕ) :=
  Tl.map (fun t => (t.1, polyAct [(1, t.2)] 1 0 vacR)) ++
    Ll.map (fun t => (t.1, polyAct omR 1 (wWt t.2) [(1, t.2)]))

theorem o2cert_mem (Tl Ll : List (ℚ × List ℕ)) (hT : ∀ t ∈ Tl, Even t.2.length)
    (hL : ∀ t ∈ Ll, Even t.2.length) :
    ∀ t ∈ o2cert Tl Ll, ∃ x ∈ O₂ (M1P m hm), HasPoly m hm x t.2 := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    exact T_mem_O₂ m hm s.2 (hT s hs)
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    exact L3_mem_O₂ m hm s.2 (hL s hs)

/-! ## §4  The weight-8 relation -/

/-- The polynomial of `L(−2)^k`-type iterates: `ω₍₋₁₎` applied `k` times to `P` of weight `w`. -/
def omIter : ℕ → ℕ → RawPoly ℕ → RawPoly ℕ
  | 0, _, P => P
  | k + 1, w, P => normR (polyAct omR 0 (w + 2 * k) (omIter k w P))

def rel8T : List (ℚ × List ℕ) :=
  [(-267/7, [0, 5]), (-249, [1, 4]), (-251/14, [2, 3]), (-1221/14, [0, 0, 0, 3]),
   (-472/7, [0, 0, 1, 2]), (9, [0, 1, 1, 1]), (-66/7, [0, 0, 0, 0, 0, 1])]

def rel8L : List (ℚ × List ℕ) :=
  [(7089/14, [0, 3]), (794/7, [1, 2]), (429/7, [0, 0, 0, 1])]

/-- The certificate of the weight-8 relation: `W₍₋₁₎W − (132/7)·ω₍₋₁₎ω₍₋₁₎W ∈ O₂`. -/
theorem rel8_cert :
    normR (polyAct WR 0 4 WR ++ scaleR (-132/7) (omIter 2 4 WR)) =
      normR (lc (o2cert rel8T rel8L)) := by
  decide +kernel

/-- `ω₍₋₁₎^k` applied to a polynomial state. -/
theorem hasPoly_omIter {y : (m1Sub m hm).carrier} {P : RawPoly ℕ} (w : ℕ) (hy : HasPoly m hm y P) :
    ∀ k : ℕ, (∀ j < k, ∀ t ∈ omIter j w P, wWt t.2 = w + 2 * j) →
      HasPoly m hm ((fun x => (M1P m hm).smul (ωM m hm) (-1) x)^[k] y) (omIter k w P)
  | 0, _ => hy
  | k + 1, hk => by
    rw [Function.iterate_succ_apply', omIter]
    refine hasPoly_normR m hm ?_
    have := M1P_smul_poly m hm (hasPoly_omega m hm)
      (hasPoly_omIter w hy k fun j hj => hk j (by omega)) (w + 2 * k) (hk k (by omega)) (-1)
    simpa using this

theorem mk₂_omIter (y : (m1Sub m hm).carrier) (k : ℕ) :
    mk₂ (M1P m hm) ((fun x => (M1P m hm).smul (ωM m hm) (-1) x)^[k] y) =
      (mk₂ (M1P m hm) (ωM m hm)) ^ k * mk₂ (M1P m hm) y := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', mk₂_smul_neg_one, ih, pow_succ]; ring

/-- **The weight-8 relation**: `W̄² = (132/7)·ω̄²W̄` in `A₂(M(1)⁺)`. -/
theorem rel8M_holds : Rel8M m hm := by
  set Wv := WM m hm
  set y := (M1P m hm).smul Wv (-1) Wv -
    (((132 / 7 : ℚ) : ℂ) • ((fun x => (M1P m hm).smul (ωM m hm) (-1) x)^[2] Wv)) with hy
  have hpoly : HasPoly m hm y (polyAct WR 0 4 WR ++ scaleR (-132/7) (omIter 2 4 WR)) := by
    have h1 := M1P_smul_poly m hm (hasPoly_W m hm) (hasPoly_W m hm) 4 (by decide) (-1)
    have h2 := hasPoly_omIter m hm 4 (hasPoly_W m hm) 2 (by decide +kernel)
    rw [HasPoly, hy, Submodule.coe_sub, Submodule.coe_smul, h1, h2, evR_append, evR_scaleR,
      latStateGen_add_boson, latStateGen_csmul]
    push_cast
    module
  have hO : y ∈ O₂ (M1P m hm) :=
    mem_of_cert m hm _ hpoly _ (o2cert_mem m hm rel8T rel8L (by decide) (by decide)) rel8_cert
  refine ⟨132 / 7, 0, ?_⟩
  have h0 := (mk₂_eq_zero_iff (M1P m hm)).mpr hO
  rw [hy, map_sub, map_smul, mk₂_smul_neg_one, mk₂_omIter, sub_eq_zero] at h0
  rw [pow_two, h0, zero_smul, add_zero]
  norm_num
  rfl

def rel10T : List (ℚ × List ℕ) :=
  [(-9351/256, [0, 7]), (22607/128, [1, 6]), (3075/128, [2, 5]), (815/24, [0, 0, 0, 5]),
   (5915/128, [3, 4]), (2365/128, [0, 0, 1, 4]), (263/16, [0, 0, 2, 3]),
   (6577/1024, [0, 1, 1, 3]), (53/16, [0, 0, 0, 0, 0, 3]), (1969/128, [0, 1, 2, 2]),
   (-7541/1536, [1, 1, 1, 2]), (9/2, [0, 0, 0, 0, 1, 2]), (1/4, [0, 0, 0, 0, 0, 0, 0, 1])]

def rel10L : List (ℚ × List ℕ) :=
  [(-25441/128, [0, 5]), (-2459/64, [1, 4]), (-16741/128, [2, 3]), (-455/16, [0, 0, 0, 3]),
   (-45/2, [0, 0, 1, 2]), (-17/8, [0, 0, 0, 0, 0, 1])]

/-- The certificate of the weight-10 relation:
`ω₍₋₁₎³W − (945/2048)·W₍₋₃₎W ∈ O₂` (Virasoro part). -/
theorem rel10_cert :
    normR (omIter 3 4 WR ++ scaleR (-945/2048) (polyAct WR 2 4 WR)) =
      normR (lc (o2cert rel10T rel10L)) := by
  decide +kernel

/-- **The weight-10 relation**: `ω̄³W̄ = 0` in `A₂(M(1)⁺)`. -/
theorem rel10M_holds : Rel10M m hm := by
  set Wv := WM m hm
  set z := (M1P m hm).smul Wv (-3) Wv with hz
  set y := (fun x => (M1P m hm).smul (ωM m hm) (-1) x)^[3] Wv - (((945 / 2048 : ℚ) : ℂ) • z) with hy
  have hpoly : HasPoly m hm y (omIter 3 4 WR ++ scaleR (-945/2048) (polyAct WR 2 4 WR)) := by
    have h1 := M1P_smul_poly m hm (hasPoly_W m hm) (hasPoly_W m hm) 4 (by decide) (-3)
    have h2 := hasPoly_omIter m hm 4 (hasPoly_W m hm) 3 (by decide +kernel)
    rw [HasPoly, hy, Submodule.coe_sub, Submodule.coe_smul, h2, hz, h1, evR_append, evR_scaleR,
      latStateGen_add_boson, latStateGen_csmul]
    norm_num
    rw [sub_eq_add_neg, ← neg_smul]
  have hO : y ∈ O₂ (M1P m hm) :=
    mem_of_cert m hm _ hpoly _ (o2cert_mem m hm rel10T rel10L (by decide) (by decide)) rel10_cert
  have hzO : z ∈ O₂ (M1P m hm) := smul_le_neg_two_mem_O₂ _ _ _ (by norm_num)
  have hsum : (fun x => (M1P m hm).smul (ωM m hm) (-1) x)^[3] Wv ∈ O₂ (M1P m hm) := by
    have := Submodule.add_mem _ hO (Submodule.smul_mem _ (((945 / 2048 : ℚ) : ℂ)) hzO)
    rwa [hy, sub_add_cancel] at this
  refine ⟨0, ?_⟩
  have h0 := (mk₂_eq_zero_iff (M1P m hm)).mpr hsum
  rw [mk₂_omIter] at h0
  rw [h0, zero_smul]

end PlusC2

end VOA.Classification.COne
