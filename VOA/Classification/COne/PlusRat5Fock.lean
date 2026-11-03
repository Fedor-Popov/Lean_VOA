import VOA.Classification.COne.PlusRat4Fourteen

/-! # Fock spectra of `o(H⁴)`, `o(H⁶)` on the lattice modules `V_{L+λ_j}`

Abe (Math. Z. 249 (2005), Prop. 4.3): on a Fock module, `o(H^{2r})` acts on
`h(-n₁)…h(-n_k)e^γ` by `Σ nᵢ^{2r-1}`.  Here:

* `shiftWeakModule_current`: on the shifted module the field of the current `h(-1)𝟙` is the
  shifted current `α'(z) = α(z) + λ z⁻¹` (`alphaShift`);
* the commutators `[o(H⁴), h₍ₙ₎] = -n³ h₍ₙ₎`, `[o(H⁶), h₍ₙ₎] = -n⁵ h₍ₙ₎`;
* `o(H⁴) e^γ = o(H⁶) e^γ = 0` on every charge sector;
* Fock monomials are joint eigenvectors with eigenvalues `Σ (i+1)³ eᵢ`, `Σ (i+1)⁵ eᵢ`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section

namespace VOA.Classification.COne.LatMod
open VOA VOA.IntegralLattice VOA.LatGen HeisenbergN
open Module (End)

section Current

variable (K N : IntegralLattice.{0}) (ι : K.carrier →ₗ[ℤ] N.carrier) (δ : N.carrier)
  (hKe : K.Even) (hK : K.PosDef) (hNe : N.Even) (hN : N.PosDef)
  (hι : ∀ α β, N.form (ι α) (ι β) = K.form α β)

/-- The current state `h_a(-1)𝟙`. -/
def curState (a : Fin (rank K)) : LatModuleGen K :=
  LinearMap.rTensor (K.carrier →₀ ℂ) (currentN (rank K) 1 a ((0 : ℕ) : ℤ)) (latVacuumGen K)

include hKe hK hNe hN hι in
/-- The module field of the current is the shifted current. -/
theorem shiftWeakModule_current (a : Fin (rank K)) (t : ℤ) (x : LatModuleGen K) :
    (shiftWeakModule K N ι δ hKe hK hNe hN hι).YM (curState K a) t x =
      alphaShift K N ι δ a t x := by
  apply shiftEmb_injective K N ι δ hK hN hι
  rw [shiftWeakModule_intertw, curState]
  change YfullGen N hNe hN _ t _ = _
  rw [YN_latMorph_current K N ι hK hNe hN hι a]
  have h1 : YfullGen N hNe hN (latMorph K N ι (latVacuumGen K)) = idField := by
    have hv := (latMorph_isVOAHom K N ι hK hN hι hKe hNe).map_vacuum
    change latMorph K N ι (latVacuumGen K) = latVacuumGen N at hv
    rw [hv]
    have := (latticeVOAGen N hNe hN).vacuum_Y
    change YfullGen N hNe hN (latVacuumGen N) = 1 at this
    rw [this]
    funext j
    rw [idField_apply]
    rfl
  rw [nprod_congr_right _ (YfullGen_isField N hNe hN _) idField_isField h1,
    nprod_idField_right]
  have h := shiftEmb_alphaShift K N ι δ hK hN hι a t x
  rw [one_smul] at h
  exact h.symm

end Current

end VOA.Classification.COne.LatMod

namespace VOA.Classification.COne.PlusRat5
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusRat3

/-! ## §1  Certificates (any `m`) -/

/-- The current `h(-1)𝟙` as a raw polynomial. -/
def hR : RawPoly ℕ := [(1, [0])]

theorem certH4h_3 : normR (polyActW H4R (-3 - 1) hR) = normR (scaleR 1 (LmPow 0 hR)) := by decide +kernel
theorem certH4h_2 : normR (polyActW H4R (-2 - 1) hR) = normR (scaleR (7/3) (LmPow 1 hR)) := by decide +kernel
theorem certH4h_1 : normR (polyActW H4R (-1 - 1) hR) = normR (scaleR 2 (LmPow 2 hR)) := by decide +kernel
theorem certH4h_0 : normR (polyActW H4R (-0 - 1) hR) = normR (scaleR 1 (LmPow 3 hR)) := by decide +kernel
theorem certH6h_5 : normR (polyActW H6R (-5 - 1) hR) = normR (scaleR 1 (LmPow 0 hR)) := by decide +kernel
theorem certH6h_4 : normR (polyActW H6R (-4 - 1) hR) = normR (scaleR (31/5) (LmPow 1 hR)) := by decide +kernel
theorem certH6h_3 : normR (polyActW H6R (-3 - 1) hR) = normR (scaleR 9 (LmPow 2 hR)) := by decide +kernel
theorem certH6h_2 : normR (polyActW H6R (-2 - 1) hR) = normR (scaleR (13/2) (LmPow 3 hR)) := by decide +kernel
theorem certH6h_1 : normR (polyActW H6R (-1 - 1) hR) = normR (scaleR 3 (LmPow 4 hR)) := by decide +kernel
theorem certH6h_0 : normR (polyActW H6R (-0 - 1) hR) = normR (scaleR 1 (LmPow 5 hR)) := by decide +kernel

/-- `H⁴ = (h₍₋₃₎h − h₍₋₂₎L(-1)h)/3`. -/
theorem certH4quad : normR H4R = normR (scaleR (1/3) (polyActW hR (-(-3) - 1) hR) ++
    scaleR (-1/3) (polyActW hR (-(-2) - 1) (LmPow 1 hR))) := by decide +kernel

/-- `H⁶ = h₍₋₅₎h/5 − 13 h₍₋₄₎L(-1)h/10 + 11 h₍₋₃₎L(-1)²h/20`. -/
theorem certH6quad : normR H6R = normR (scaleR (1/5) (polyActW hR (-(-5) - 1) hR) ++
    scaleR (-13/10) (polyActW hR (-(-4) - 1) (LmPow 1 hR)) ++
    scaleR (11/20) (polyActW hR (-(-3) - 1) (LmPow 2 hR))) := by decide +kernel

/-! ## §2  States of `V_{2m}` -/

variable (m : ℕ) (hm : 1 ≤ m)

theorem ls_hR : ls m hR = curState (latP m) (a0 m) := by
  rw [ls, curState, hR, evR_cons, evR_nil, add_zero, evalWord_cons, evalWord_nil, latVacuumGen,
    latStateGen, latStateGen, LinearMap.rTensor_tmul, currentN_apply,
    oscN_apply_neg _ _ _ (by norm_num), vacuumN]
  norm_num

theorem ls_scaleR (q : ℚ) (P : RawPoly ℕ) : ls m (scaleR q P) = ((q : ℂ)) • ls m P := by
  rw [ls, ls, evR_scaleR, latStateGen_csmul]

theorem ls_append (P Q : RawPoly ℕ) : ls m (P ++ Q) = ls m P + ls m Q := by
  rw [ls, ls, ls, evR_append, latStateGen_add_boson]

theorem V2m_smul_ls (Q P : RawPoly ℕ) (n : ℤ) :
    (V2m m hm).smul (ls m Q) n (ls m P) = ls m (polyActW Q (-n - 1) P) :=
  V2m_smul_evR_W m hm Q n P

theorem ls_LmPow (P : RawPoly ℕ) : ∀ k : ℕ, ls m (LmPow k P) = ((V2m m hm).L (-1))^[k] (ls m P)
  | 0 => rfl
  | k + 1 => by
    rw [LmPow, Function.iterate_succ_apply', ← ls_LmPow P k, LmR, ls_normR,
      VertexOperatorAlgebra.L_def, omega_V2m m hm]
    change _ = (V2m m hm).smul (ls m omR) (-1 + 1) _
    rw [V2m_smul_ls m hm]
    norm_num

theorem H4_h (j : ℕ) (c : ℚ) (k : ℕ)
    (hc : normR (polyActW H4R (-(j : ℤ) - 1) hR) = normR (scaleR c (LmPow k hR))) :
    (V2m m hm).smul (ls m H4R) j (ls m hR) = (c : ℂ) • ((V2m m hm).L (-1))^[k] (ls m hR) := by
  rw [V2m_smul_ls, ← ls_normR, hc, ls_normR, ls_scaleR, ls_LmPow]

theorem H6_h (j : ℕ) (c : ℚ) (k : ℕ)
    (hc : normR (polyActW H6R (-(j : ℤ) - 1) hR) = normR (scaleR c (LmPow k hR))) :
    (V2m m hm).smul (ls m H6R) j (ls m hR) = (c : ℂ) • ((V2m m hm).L (-1))^[k] (ls m hR) := by
  rw [V2m_smul_ls, ← ls_normR, hc, ls_normR, ls_scaleR, ls_LmPow]

/-! ## §3  The current on the lattice module `V_{L+λ_j}` -/

section Module
variable (j : ℤ)

/-- The shifted momentum of the sector `γ` of `V_{L+λ_j}`. -/
abbrev mu (γ : (latP m).carrier) : ℂ :=
  chargeCoord (latP m) γ (a0 m) + lamShift (latP m) (glueLat m j) (glueIota m j) (glueDelta m j) (a0 m)

/-- The `V_{2m}`-module `V_{L+λ_j}`. -/
abbrev LA : WeakModule (V2m m hm) (LatModuleGen (latP m)) := (latticeModule m hm j).toWeakModule

theorem lat_h_mode (n : ℤ) (p : FockN (rank (latP m))) (γ : (latP m).carrier) :
    mode ((LA m hm j).YM (ls m hR)) n (latStateGen (latP m) p γ) =
      latStateGen (latP m) (oscN (rank (latP m)) 1 (a0 m) n p +
        (if n = 0 then mu m j γ • p else 0)) γ := by
  rw [ls_hR, mode_apply]
  change (shiftWeakModule (latP m) (glueLat m j) (glueIota m j) (glueDelta m j) (latP_even m)
    (latP_posDef m hm) (glueLat_even m j) (glueLat_posDef m hm j) (glueIota_isometry m j)).YM
      (curState (latP m) (a0 m)) (-n - 1) _ = _
  rw [shiftWeakModule_current, alphaShift_latStateGen, show -(-n - 1) - 1 = n by ring]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg (by omega), if_neg hn]

end Module

section Generic
variable (B : WeakModule (V2m m hm) (LatModuleGen (latP m))) (μ : (latP m).carrier → ℂ)
  (hB : ∀ (n : ℤ) (p : FockN (rank (latP m))) (γ : (latP m).carrier),
    mode (B.YM (ls m hR)) n (latStateGen (latP m) p γ) =
      latStateGen (latP m) (oscN (rank (latP m)) 1 (a0 m) n p + (if n = 0 then μ γ • p else 0)) γ)

theorem modeT (k : ℕ) (c : ℂ) (q : ℤ) (y : LatModuleGen (latP m)) :
    mode (B.YM (c • ((V2m m hm).L (-1))^[k] (ls m hR))) q y =
      (c * fallC q k) • mode (B.YM (ls m hR)) (q - k) y := by
  rw [map_smul, mode_smul, LinearMap.smul_apply, Tpow_mode, smul_smul]

/-- `[o(H⁴), h₍ₙ₎] = -n³ h₍ₙ₎`. -/
theorem oH4_h_comm (n : ℤ) (y : LatModuleGen (latP m)) :
    mode (B.YM (ls m H4R)) 3 (mode (B.YM (ls m hR)) n y) =
      mode (B.YM (ls m hR)) n (mode (B.YM (ls m H4R)) 3 y) +
        (-(n : ℂ) ^ 3) • mode (B.YM (ls m hR)) n y := by
  have hc := zero_mode_comm B 3 (ls m H4R) (ls m hR) n y
  rw [show ((3 : ℕ) : ℤ) = 3 from rfl] at hc
  rw [hc]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H4_h m hm 0 1 3 certH4h_0, H4_h m hm 1 2 2 certH4h_1, H4_h m hm 2 (7/3) 1 certH4h_2,
    H4_h m hm 3 1 0 certH4h_3]
  simp only [modeT]
  simp only [Nat.cast_ofNat, Nat.cast_one, CharP.cast_eq_zero]
  rw [show (3 : ℤ) + n - 0 - 3 = n by ring, show (3 : ℤ) + n - 1 - 2 = n by ring,
    show (3 : ℤ) + n - 2 - 1 = n by ring, show (3 : ℤ) + n - 3 - 0 = n by ring]
  simp only [fallC, show Nat.choose 3 0 = 1 from rfl, show Nat.choose 3 1 = 3 from rfl,
    show Nat.choose 3 2 = 3 from rfl, show Nat.choose 3 3 = 1 from rfl]
  push_cast
  module


/-- `[o(H⁶), h₍ₙ₎] = -n⁵ h₍ₙ₎`. -/
theorem oH6_h_comm (n : ℤ) (y : LatModuleGen (latP m)) :
    mode (B.YM (ls m H6R)) 5 (mode (B.YM (ls m hR)) n y) =
      mode (B.YM (ls m hR)) n (mode (B.YM (ls m H6R)) 5 y) +
        (-(n : ℂ) ^ 5) • mode (B.YM (ls m hR)) n y := by
  have hc := zero_mode_comm B 5 (ls m H6R) (ls m hR) n y
  rw [show ((5 : ℕ) : ℤ) = 5 from rfl] at hc
  rw [hc]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [H6_h m hm 0 1 5 certH6h_0, H6_h m hm 1 3 4 certH6h_1, H6_h m hm 2 (13/2) 3 certH6h_2,
    H6_h m hm 3 9 2 certH6h_3, H6_h m hm 4 (31/5) 1 certH6h_4, H6_h m hm 5 1 0 certH6h_5]
  simp only [modeT]
  simp only [Nat.cast_ofNat, Nat.cast_one, CharP.cast_eq_zero]
  rw [show (5 : ℤ) + n - 0 - 5 = n by ring, show (5 : ℤ) + n - 1 - 4 = n by ring,
    show (5 : ℤ) + n - 2 - 3 = n by ring, show (5 : ℤ) + n - 3 - 2 = n by ring,
    show (5 : ℤ) + n - 4 - 1 = n by ring, show (5 : ℤ) + n - 5 - 0 = n by ring]
  simp only [fallC, show Nat.choose 5 0 = 1 from rfl, show Nat.choose 5 1 = 5 from rfl,
    show Nat.choose 5 2 = 10 from rfl, show Nat.choose 5 3 = 10 from rfl,
    show Nat.choose 5 4 = 5 from rfl, show Nat.choose 5 5 = 1 from rfl]
  push_cast
  module


include hB in
theorem h_vac_pos (k : ℤ) (hk : 0 < k) (γ : (latP m).carrier) :
    mode (B.YM (ls m hR)) k (latStateGen (latP m) 1 γ) = 0 := by
  rw [hB, if_neg hk.ne', add_zero, oscN_apply_pos _ _ _ hk, pderiv_one, smul_zero,
    smul_zero]
  simp [latStateGen]

include hB in
theorem h_vac_zero (p : FockN (rank (latP m))) (γ : (latP m).carrier) :
    mode (B.YM (ls m hR)) 0 (latStateGen (latP m) p γ) =
      μ γ • latStateGen (latP m) p γ := by
  rw [hB, if_pos rfl, oscN_zero, LinearMap.zero_apply, zero_add, latStateGen_csmul]

include hB in
/-- The zero mode of `h₍₋ₐ₋₁₎L(-1)^b h` on a charged vacuum. -/
theorem quad_vac (a b : ℕ) (γ : (latP m).carrier) :
    mode (B.YM ((V2m m hm).smul (ls m hR) (-((a : ℤ) + 1))
        (((V2m m hm).L (-1))^[b] (ls m hR)))) ((a : ℤ) + b + 1) (latStateGen (latP m) 1 γ) =
      (-(negOnePow (-((a : ℤ) + 1))) * fallC (b : ℤ) b * μ γ ^ 2) •
        latStateGen (latP m) 1 γ := by
  set x := latStateGen (latP m) 1 γ
  set A := B
  rw [module_iterate0 A (ls m hR) _ x (-((a : ℤ) + 1)) ((a : ℤ) + b + 1)]
  rw [finsum_eq_single _ 0]
  · rw [cbz_zero, show negOnePow 0 = 1 by simp [negOnePow], one_mul, one_smul, Tpow_mode,
      Tpow_mode, add_zero, show (a : ℤ) + b + 1 - b = a + 1 by ring,
      h_vac_pos m hm B μ hB _ (by omega), smul_zero, map_zero, zero_sub, h_vac_zero m hm B μ hB, map_smul,
      show -((a : ℤ) + 1) + ((a : ℤ) + b + 1) - 0 - b = 0 by ring, h_vac_zero m hm B μ hB, smul_smul,
      smul_smul, smul_smul, ← neg_smul]
    congr 1
    ring_nf
  · intro i hi
    by_cases hneg : i < 0
    · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
    · have hpos : 0 < i := by omega
      rw [Tpow_mode, h_vac_pos m hm B μ hB _ (by omega), smul_zero, map_zero, zero_sub,
        h_vac_pos m hm B μ hB _ hpos, map_zero, smul_zero, neg_zero, smul_zero]

theorem ls_quad (a : ℤ) (b : ℕ) :
    ls m (polyActW hR (-a - 1) (LmPow b hR)) =
      (V2m m hm).smul (ls m hR) a (((V2m m hm).L (-1))^[b] (ls m hR)) := by
  rw [← V2m_smul_ls, ls_LmPow]

theorem ls_quad0 (a : ℤ) :
    ls m (polyActW hR (-a - 1) hR) =
      (V2m m hm).smul (ls m hR) a (((V2m m hm).L (-1))^[0] (ls m hR)) := by
  rw [← V2m_smul_ls]; rfl

theorem mode_ls_add (P Q : RawPoly ℕ) (n : ℤ) (y : LatModuleGen (latP m)) :
    mode (B.YM (ls m (P ++ Q))) n y =
      mode (B.YM (ls m P)) n y + mode (B.YM (ls m Q)) n y := by
  rw [ls_append, map_add, mode_add, LinearMap.add_apply]

theorem mode_ls_scale (q : ℚ) (P : RawPoly ℕ) (n : ℤ) (y : LatModuleGen (latP m)) :
    mode (B.YM (ls m (scaleR q P))) n y = (q : ℂ) • mode (B.YM (ls m P)) n y := by
  rw [ls_scaleR, map_smul, mode_smul, LinearMap.smul_apply]

include hB in
/-- `o(H⁴) e^γ = 0`. -/
theorem oH4_vac (γ : (latP m).carrier) :
    mode (B.YM (ls m H4R)) 3 (latStateGen (latP m) 1 γ) = 0 := by
  rw [← ls_normR, certH4quad, ls_normR, mode_ls_add m hm B, mode_ls_scale m hm B, mode_ls_scale m hm B,
    ls_quad0 m hm, ls_quad m hm]
  have h1 := quad_vac m hm B μ hB 2 0 γ
  have h2 := quad_vac m hm B μ hB 1 1 γ
  push_cast at h1 h2
  norm_num only at h1 h2 ⊢
  rw [h1, h2, smul_smul, smul_smul, ← add_smul]
  simp only [fallC]
  norm_num [negOnePow, Int.even_iff]

include hB in
/-- `o(H⁶) e^γ = 0`. -/
theorem oH6_vac (γ : (latP m).carrier) :
    mode (B.YM (ls m H6R)) 5 (latStateGen (latP m) 1 γ) = 0 := by
  rw [← ls_normR, certH6quad, ls_normR, mode_ls_add m hm B, mode_ls_add m hm B, mode_ls_scale m hm B, mode_ls_scale m hm B,
    mode_ls_scale m hm B, ls_quad0 m hm, ls_quad m hm, ls_quad m hm]
  have h1 := quad_vac m hm B μ hB 4 0 γ
  have h2 := quad_vac m hm B μ hB 3 1 γ
  have h3 := quad_vac m hm B μ hB 2 2 γ
  push_cast at h1 h2 h3
  norm_num only at h1 h2 h3 ⊢
  rw [h1, h2, h3, smul_smul, smul_smul, smul_smul, ← add_smul, ← add_smul]
  simp only [fallC]
  norm_num [negOnePow, Int.even_iff]
  left; ring


/-- The derivation `Σ (i+1)^e X_i ∂_i` of the Fock space. -/
def DD (e : ℕ) : Derivation ℂ (FockN (rank (latP m))) (FockN (rank (latP m))) :=
  MvPolynomial.mkDerivation ℂ (fun v => (((v.1 + 1 : ℕ) : ℂ) ^ e) • X v)

theorem a0_eq (a : Fin (rank (latP m))) : a = a0 m := by
  apply Fin.ext
  change (a : ℕ) = 0
  have h1 := a.isLt
  have h2 : (latP m).rank = 1 := rank_latP m
  omega

include hB in
theorem h_create (i : ℕ) (p : FockN (rank (latP m))) (γ : (latP m).carrier) :
    mode (B.YM (ls m hR)) (-((i : ℤ) + 1)) (latStateGen (latP m) p γ) =
      latStateGen (latP m) (X (i, a0 m) * p) γ := by
  rw [hB, if_neg (by omega), add_zero, oscN_apply_neg _ _ _ (by omega),
    show (-(-((i : ℤ) + 1)) - 1).toNat = i by omega]

include hB in
/-- `o(H⁴)` acts on `p ⊗ e^γ` through the cubic Euler derivation. -/
theorem oH4_lat (p : FockN (rank (latP m))) (γ : (latP m).carrier) :
    mode (B.YM (ls m H4R)) 3 (latStateGen (latP m) p γ) =
      latStateGen (latP m) (DD m 3 p) γ := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.C_eq_smul_one, latStateGen_csmul, map_smul, oH4_vac m hm B μ hB, smul_zero,
      Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]
    simp [latStateGen]
  | add p q hp hq =>
    rw [latStateGen_add_boson, map_add, hp, hq, map_add, latStateGen_add_boson]
  | mul_X p v hp =>
    obtain ⟨i, a⟩ := v
    rw [a0_eq m a, mul_comm, ← h_create m hm B μ hB, oH4_h_comm m hm B, hp, h_create m hm B μ hB, h_create m hm B μ hB,
      Derivation.leibniz, DD, MvPolynomial.mkDerivation_X, ← DD]
    rw [← latStateGen_csmul, ← latStateGen_add_boson]
    congr 1
    simp only [smul_eq_mul]
    rw [mul_smul_comm, mul_comm p (X _)]
    congr 2
    push_cast
    ring

include hB in
/-- `o(H⁶)` acts on `p ⊗ e^γ` through the quintic Euler derivation. -/
theorem oH6_lat (p : FockN (rank (latP m))) (γ : (latP m).carrier) :
    mode (B.YM (ls m H6R)) 5 (latStateGen (latP m) p γ) =
      latStateGen (latP m) (DD m 5 p) γ := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.C_eq_smul_one, latStateGen_csmul, map_smul, oH6_vac m hm B μ hB, smul_zero,
      Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]
    simp [latStateGen]
  | add p q hp hq =>
    rw [latStateGen_add_boson, map_add, hp, hq, map_add, latStateGen_add_boson]
  | mul_X p v hp =>
    obtain ⟨i, a⟩ := v
    rw [a0_eq m a, mul_comm, ← h_create m hm B μ hB, oH6_h_comm m hm B, hp, h_create m hm B μ hB, h_create m hm B μ hB,
      Derivation.leibniz, DD, MvPolynomial.mkDerivation_X, ← DD]
    rw [← latStateGen_csmul, ← latStateGen_add_boson]
    congr 1
    simp only [smul_eq_mul]
    rw [mul_smul_comm, mul_comm p (X _)]
    congr 2
    push_cast
    ring

theorem DD_X (e : ℕ) (v : ℕ × Fin (rank (latP m))) :
    DD m e (X v) = (((v.1 + 1 : ℕ) : ℂ) ^ e) • X v :=
  MvPolynomial.mkDerivation_X _ _ _

/-- The weight `Σ sᵥ (v+1)^e` of a monomial. -/
abbrev wtE (e : ℕ) : ((ℕ × Fin (rank (latP m))) →₀ ℕ) →+ ℕ :=
  Finsupp.weight (fun v : ℕ × Fin (rank (latP m)) => (v.1 + 1) ^ e)

theorem DD_monomial (e : ℕ) (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) :
    DD m e (MvPolynomial.monomial s (1 : ℂ)) = ((wtE m e s : ℕ) : ℂ) • MvPolynomial.monomial s 1 := by
  induction s using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, Nat.cast_zero, zero_smul, show (MvPolynomial.monomial 0 (1 : ℂ)) = 1 from rfl,
      Derivation.map_one_eq_zero]
  | add f g hf hg =>
    have hm : (MvPolynomial.monomial (f + g) (1 : ℂ)) =
        MvPolynomial.monomial f 1 * MvPolynomial.monomial g 1 := by
      rw [MvPolynomial.monomial_mul, one_mul]
    rw [hm, Derivation.leibniz, hf, hg, map_add, Nat.cast_add, smul_eq_mul, smul_eq_mul,
      mul_smul_comm, mul_smul_comm, add_smul, mul_comm (MvPolynomial.monomial g 1), add_comm]
  | single a b =>
    rw [← MvPolynomial.X_pow_eq_monomial, Derivation.leibniz_pow, DD_X, Finsupp.weight_single]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have hx : (X a : FockN (rank (latP m))) ^ b = X a ^ (b - 1) * X a := by
        rw [← pow_succ, Nat.sub_add_cancel hb]
      rw [hx]
      simp only [smul_eq_mul, nsmul_eq_mul, MvPolynomial.smul_eq_C_mul, Nat.cast_mul,
        Nat.cast_pow, map_mul, map_pow, map_natCast]
      ring

theorem wtE_ge (e : ℕ) (he : 1 ≤ e) (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) :
    Finsupp.weight HeisenbergN.weightFnN s ≤ wtE m e s := by
  induction s using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add]; omega
  | single a b =>
    rw [Finsupp.weight_single, Finsupp.weight_single, smul_eq_mul, smul_eq_mul,
      HeisenbergN.weightFnN_apply]
    exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) _)

include hB in
theorem oH4_mono (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) (γ : (latP m).carrier) :
    mode (B.YM (ls m H4R)) 3 (latStateGen (latP m) (MvPolynomial.monomial s 1) γ) =
      ((wtE m 3 s : ℕ) : ℂ) • latStateGen (latP m) (MvPolynomial.monomial s 1) γ := by
  rw [oH4_lat m hm B μ hB, DD_monomial, latStateGen_csmul]

include hB in
theorem oH6_mono (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) (γ : (latP m).carrier) :
    mode (B.YM (ls m H6R)) 5 (latStateGen (latP m) (MvPolynomial.monomial s 1) γ) =
      ((wtE m 5 s : ℕ) : ℂ) • latStateGen (latP m) (MvPolynomial.monomial s 1) γ := by
  rw [oH6_lat m hm B μ hB, DD_monomial, latStateGen_csmul]

end Generic

section Adjoint

/-- The current on `V_{2m}` itself (the adjoint module): unshifted momentum. -/
theorem adj_h_mode (n : ℤ) (p : FockN (rank (latP m))) (γ : (latP m).carrier) :
    mode ((adjointWeakModule (V2m m hm)).YM (ls m hR)) n (latStateGen (latP m) p γ) =
      latStateGen (latP m) (oscN (rank (latP m)) 1 (a0 m) n p +
        (if n = 0 then chargeCoord (latP m) γ (a0 m) • p else 0)) γ := by
  rw [ls_hR, mode_apply, curState]
  change YfullGen (latP m) (latP_even m) (latP_posDef m hm) _ (-n - 1) _ = _
  rw [YfullGen_rTensor_current]
  have h1 : YfullGen (latP m) (latP_even m) (latP_posDef m hm) (latVacuumGen (latP m)) = idField := by
    have := (latticeVOAGen (latP m) (latP_even m) (latP_posDef m hm)).vacuum_Y
    change YfullGen (latP m) (latP_even m) (latP_posDef m hm) (latVacuumGen (latP m)) = 1 at this
    rw [this]
    funext j
    rw [idField_apply]
    rfl
  rw [nprod_congr_right _ (YfullGen_isField _ _ _ _) idField_isField h1, nprod_idField_right,
    genFieldLatGen_zero, alphaLatGen_latStateGen, show -(-n - 1) - 1 = n by ring]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg (by omega), if_neg hn]

end Adjoint

section Spec
variable (j : ℤ)

/-- Every weight space of `V_{L+λ_j}` is spanned by monomial states of its fiber. -/
theorem lat_weight_mem_span (w : ℂ) {v : LatModuleGen (latP m)}
    (hv : v ∈ (latticeModule m hm j).weight w) :
    v ∈ Submodule.span ℂ {u | ∃ (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) (γ : (latP m).carrier),
      ((Finsupp.weight HeisenbergN.weightFnN s : ℕ) : ℤ) = ((Finsupp.weight HeisenbergN.weightFnN s : ℕ) : ℤ) ∧
      (((Finsupp.weight HeisenbergN.weightFnN s : ℕ) : ℤ), γ) ∈
        shiftFiber (latP m) (glueLat m j) (glueIota m j) (glueDelta m j) w ∧
      u = latStateGen (latP m) (MvPolynomial.monomial s 1) γ} := by
  change v ∈ shiftWeightSpace (latP m) (glueLat m j) (glueIota m j) (glueDelta m j) w at hv
  refine (iSup₂_le (fun p hp => ?_) : shiftWeightSpace (latP m) (glueLat m j) (glueIota m j)
    (glueDelta m j) w ≤ _) hv
  obtain ⟨N, γ⟩ := p
  have hN : 0 ≤ N := hp.1
  change Submodule.map (mkEα (latP m) γ) (HeisenbergN.gradingZN (rank (latP m)) N) ≤ _
  rw [gradingZN_of_nonneg hN]
  rintro _ ⟨q, hq, rfl⟩
  have hq' : q.IsWeightedHomogeneous HeisenbergN.weightFnN N.toNat := hq
  rw [MvPolynomial.as_sum q, map_sum]
  refine Submodule.sum_mem _ (fun d hd => ?_)
  have hdw : Finsupp.weight HeisenbergN.weightFnN d = N.toNat :=
    hq' (MvPolynomial.mem_support_iff.mp hd)
  rw [show MvPolynomial.monomial d (MvPolynomial.coeff d q) =
      MvPolynomial.coeff d q • MvPolynomial.monomial d (1 : ℂ) by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨d, γ, rfl, ?_, rfl⟩
  rw [hdw, Int.toNat_of_nonneg hN]
  exact hp

end Spec

end VOA.Classification.COne.PlusRat5
