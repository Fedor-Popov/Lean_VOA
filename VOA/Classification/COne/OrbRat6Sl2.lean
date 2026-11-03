import VOA.Classification.COne.OrbRat6Lift

/-! # The `sl₂` structure of the module `V_{ℤβ+β/2}`

* `mode_comm`: the zero-mode commutator `[u₍₀₎, v₍ₙ₎] = (u₍₀₎v)₍ₙ₎` on the module (transported
  from the lattice VOA `V_N`).
* `Ep, Fm, Hm`: the module zero modes of `e^β, e^{−β}, β(−1)𝟙`, with `[E,F] = ε H`,
  `[H,F] = −2F` and `H = 2n+1` on the charge-`n` sector (`Hm_latStateGen`).
* Sectors `Sd n d = Fock_d ⊗ e^{n}` (`bigradα`) and how the charged modes move them
  (`charge_Sd`); rank-one Fock spans in degrees `0, 1, 2`.
* The weight spaces of the module as sums of sectors (`weight_le`).
* Abstract `sl₂` lemmas (`H_Fpow`, `E_Fpow`).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat6

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod Complex
  MvPolynomial

/-! ## §1 The zero-mode commutator -/

theorem mode_comm (u v : Sp) (n : ℤ) (x : Sp) :
    mode (Mo.YM u) 0 (mode (Mo.YM v) n x) - mode (Mo.YM v) n (mode (Mo.YM u) 0 x) =
      mode (Mo.YM (V1.smul u 0 v)) n x := by
  apply Psi_inj
  rw [map_sub, Psi_mode, Psi_mode, Psi_mode, Psi_mode, Psi_mode, Phi_hom.map_smul,
    VertexOperatorAlgebra.zeroMode_leibniz]
  abel

/-! ## §2 The operators -/

/-- `E = (e^β)₍₀₎`. -/
abbrev Ep : Module.End ℂ Sp := Dpm (a1 1)
/-- `F = (e^{−β})₍₀₎`. -/
abbrev Fm : Module.End ℂ Sp := Dpm (-a1 1)
/-- `H = (β(−1)𝟙)₍₀₎`. -/
abbrev Hm : Module.End ℂ Sp := mode (Mo.YM (hSt (latP 1) (a1 1))) 0

theorem smul_e_f :
    V1.smul (latChargeGen (latP 1) (a1 1)) 0 (latChargeGen (latP 1) (-a1 1)) =
      eps1 • hSt (latP 1) (a1 1) := by
  have h := Qscr_latChargeGen_neg (latP 1) latP1_root
  rw [← zeroMode_latChargeGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)] at h
  exact h

theorem smul_h_charge (k : ℤ) :
    V1.smul (hSt (latP 1) (a1 1)) 0 (latChargeGen (latP 1) k) =
      ((2 * k : ℤ) : ℂ) • latChargeGen (latP 1) k := by
  rw [show latChargeGen (latP 1) k = latStateGen (latP 1) (vacuumN _) k from rfl,
    smul_hSt_zero_latStateGen, latP_form]
  congr 2

theorem comm_EF (x : Sp) : Ep (Fm x) - Fm (Ep x) = eps1 • Hm x := by
  rw [mode_comm, smul_e_f, map_smul]
  rfl

theorem comm_HF (x : Sp) : Hm (Fm x) - Fm (Hm x) = (-2 : ℂ) • Fm x := by
  rw [mode_comm, smul_h_charge, map_smul]
  change ((2 * (-1 : ℤ) : ℤ) : ℂ) • Fm x = _
  norm_num [a1]

theorem comm_HE (x : Sp) : Hm (Ep x) - Ep (Hm x) = (2 : ℂ) • Ep x := by
  rw [mode_comm, smul_h_charge, map_smul]
  change ((2 * (1 : ℤ) : ℤ) : ℂ) • Ep x = _
  norm_num [a1]

theorem Phi_hSt : Phi (hSt (latP 1) (a1 1)) = hSt (glueLat 1 1) (glueIota 1 1 (a1 1)) := by
  rw [hSt, latMorph_latStateGen, latCob_zero, one_smul,
    fockMap_vSchur (latP 1) (glueLat 1 1) (glueIota 1 1) (latP_posDef 1 le_rfl), map_zero]
  rfl

/-- `H = 2n+1` on the charge-`n` sector (the state `p ⊗ e^{n}` stands for `e^{(n+½)β}`). -/
theorem Hm_latStateGen (p : FockN (rank (latP 1))) (n : ℤ) :
    Hm (latStateGen (latP 1) p n) = ((2 * n + 1 : ℤ) : ℂ) • latStateGen (latP 1) p n := by
  apply Psi_inj
  rw [Psi_mode, Phi_hSt, shiftEmb_latStateGen, smul_hSt_zero_latStateGen, map_smul,
    shiftEmb_latStateGen]
  congr 2
  rw [map_add, glueIota_isometry, glueIota_delta, latP_form]
  simp [a1]

/-! ## §3 Sectors -/

/-- The bigraded piece `Fock_d ⊗ e^{n}`. -/
abbrev Sd (n d : ℤ) : Submodule ℂ Sp := bigradα (latP 1) (d, n)

theorem latStateGen_mem_Sd {n d : ℤ} {p : FockN (rank (latP 1))}
    (hp : p ∈ gradingZN (rank (latP 1)) d) : latStateGen (latP 1) p n ∈ Sd n d :=
  ⟨p, hp, rfl⟩

theorem Sd_neg {n d : ℤ} (hd : d < 0) : Sd n d = ⊥ := bigradα_eq_bot_of_neg _ _ hd

theorem charge_latStateGen (k m n : ℤ) (p : FockN (rank (latP 1))) :
    mode (Mo.YM (latChargeGen (latP 1) k)) m (latStateGen (latP 1) p n) =
      (latCob (latP 1) (glueLat 1 1) (glueIota 1 1) k *
          latticeCocycle (glueLat 1 1) (glueIota 1 1 k) (glueIota 1 1 n + glueDelta 1 1)) •
        latStateGen (latP 1) (EEVec (latP 1) k (-m - 1 - 2 * k * n - k) p) (k + n) := by
  have h := latticeModule_latChargeGen 1 le_rfl 1 k n (-m - 1) p
  rw [show (-m - 1 - 2 * ((1 : ℕ) : ℤ) * k * n - 1 * k) = -m - 1 - 2 * k * n - k by
    push_cast; ring] at h
  exact h

/-- A charged mode moves sectors: `(e^{k})₍ₘ₎ : Sd n d → Sd (k+n) (d − m − 1 − 2kn − k)`. -/
theorem charge_Sd (k m : ℤ) {n d : ℤ} {x : Sp} (hx : x ∈ Sd n d) :
    mode (Mo.YM (latChargeGen (latP 1) k)) m x ∈ Sd (k + n) (d + (-m - 1 - 2 * k * n - k)) := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [mkEα_apply]
  change mode (Mo.YM (latChargeGen (latP 1) k)) m (latStateGen (latP 1) p n) ∈ _
  rw [charge_latStateGen]
  exact Submodule.smul_mem _ _ (latStateGen_mem_Sd (EEVec_memZ (latP 1) k _ hp))

theorem Ep_Sd {n d : ℤ} {x : Sp} (hx : x ∈ Sd n d) : Ep x ∈ Sd (n + 1) (d - 2 * n - 2) := by
  have h := charge_Sd (a1 1) 0 hx
  convert h using 2
  · simp only [a1]; omega
  · simp only [a1]; omega

theorem Fm_Sd {n d : ℤ} {x : Sp} (hx : x ∈ Sd n d) : Fm x ∈ Sd (n - 1) (d + 2 * n) := by
  have h := charge_Sd (-a1 1) 0 hx
  convert h using 2
  · simp only [a1]; omega
  · simp only [a1]; omega

theorem Hm_Sd {n d : ℤ} {x : Sp} (hx : x ∈ Sd n d) : Hm x = ((2 * n + 1 : ℤ) : ℂ) • x := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact Hm_latStateGen p n

/-! ## §4 Rank-one Fock spans -/

/-- The oscillator `h(-k-1)`. -/
abbrev xo (k : ℕ) : FockN (rank (latP 1)) := X ((k : ℕ), a0 1)

theorem fin_eq_a0' (a : Fin (rank (latP 1))) : a = a0 1 := by
  apply Fin.ext
  have h1 := a.isLt
  have h2 : rank (latP 1) = 1 := rank_latP 1
  simp only [a0]
  omega

theorem mem_of_monomials' {w : ℕ} {S : Submodule ℂ (FockN (rank (latP 1)))}
    (hS : ∀ d : (ℕ × Fin (rank (latP 1))) →₀ ℕ, Finsupp.weight weightFnN d = w →
      (monomial d (1 : ℂ) : FockN (rank (latP 1))) ∈ S)
    {p : FockN (rank (latP 1))} (hp : p ∈ gradingWN (rank (latP 1)) w) : p ∈ S := by
  classical
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight weightFnN d = w := hp (MvPolynomial.mem_support_iff.mp hd)
  rw [show monomial d (coeff d p) = coeff d p • (monomial d (1 : ℂ) : FockN (rank (latP 1))) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (hS d hw)

theorem fock_zero {p : FockN (rank (latP 1))} (hp : p ∈ gradingZN (rank (latP 1)) 0) :
    p ∈ ℂ ∙ (1 : FockN (rank (latP 1))) := by
  rw [gradingZN_of_nonneg le_rfl] at hp
  apply mem_of_monomials' _ hp
  intro d hd
  rw [VOA.LatGen.weight_eq_zero_iff _ d hd, monomial_zero', C_1]
  exact Submodule.mem_span_singleton_self _

theorem fock_one {p : FockN (rank (latP 1))} (hp : p ∈ gradingZN (rank (latP 1)) 1) :
    p ∈ ℂ ∙ xo 0 := by
  rw [gradingZN_of_nonneg (by norm_num)] at hp
  apply mem_of_monomials' _ hp
  intro d hd
  obtain ⟨a, rfl⟩ := VOA.LatGen.weight_eq_one _ d hd
  rw [fin_eq_a0' a]
  exact Submodule.mem_span_singleton_self _

theorem fock_two {p : FockN (rank (latP 1))} (hp : p ∈ gradingZN (rank (latP 1)) 2) :
    p ∈ Submodule.span ℂ {xo 0 * xo 0, xo 1} := by
  rw [gradingZN_of_nonneg (by norm_num)] at hp
  apply mem_of_monomials' _ hp
  intro d hd
  rcases VOA.LatGen.weight_eq_two _ d hd with ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · rw [fin_eq_a0' a]
    exact Submodule.subset_span (Or.inr rfl)
  · rw [fin_eq_a0' a, fin_eq_a0' b]
    rw [show (monomial (Finsupp.single ((0 : ℕ), a0 1) 1 + Finsupp.single (0, a0 1) 1) (1 : ℂ) :
        FockN (rank (latP 1))) = xo 0 * xo 0 by
      change _ = monomial _ (1 : ℂ) * monomial _ (1 : ℂ)
      rw [monomial_mul, mul_one]]
    exact Submodule.subset_span (by simp)

/-- The charge-`n` sector map. -/
def secMap (n : ℤ) : FockN (rank (latP 1)) →ₗ[ℂ] Sp where
  toFun p := latStateGen (latP 1) p n
  map_add' := fun _ _ => latStateGen_add_boson _ _ _ _
  map_smul' := fun _ _ => latStateGen_csmul _ _ _ _

theorem Sd_eq_map (n d : ℤ) : Sd n d = (gradingZN (rank (latP 1)) d).map (secMap n) := rfl

theorem Sd_zero (n : ℤ) : Sd n 0 ≤ ℂ ∙ latStateGen (latP 1) 1 n := by
  rw [Sd_eq_map]
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (fock_zero hp)
  exact Submodule.mem_span_singleton.mpr ⟨c, (map_smul (secMap n) c 1).symm⟩

theorem Sd_one (n : ℤ) : Sd n 1 ≤ ℂ ∙ latStateGen (latP 1) (xo 0) n := by
  rw [Sd_eq_map]
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (fock_one hp)
  exact Submodule.mem_span_singleton.mpr ⟨c, (map_smul (secMap n) c _).symm⟩

theorem Sd_two (n : ℤ) :
    Sd n 2 ≤ Submodule.span ℂ {latStateGen (latP 1) (xo 0 * xo 0) n,
      latStateGen (latP 1) (xo 1) n} := by
  rw [Sd_eq_map]
  rintro _ ⟨p, hp, rfl⟩
  have h := Submodule.mem_map_of_mem (f := secMap n) (fock_two hp)
  rw [Submodule.map_span, Set.image_pair] at h
  exact h

/-! ## §5 Weight spaces -/

theorem weight_le {h : ℂ} {S : Submodule ℂ Sp}
    (hS : ∀ w n : ℤ, 0 ≤ w →
      ((((w : ℝ) + ((2 * n + 1 : ℤ) : ℝ) ^ 2 / 4 : ℝ)) : ℂ) = h → Sd n w ≤ S) :
    Mo.weight h ≤ S := by
  change shiftWeightSpace (latP 1) (glueLat 1 1) (glueIota 1 1) (glueDelta 1 1) h ≤ S
  refine iSup_le fun p => iSup_le fun hp => ?_
  obtain ⟨hp0, hpw⟩ := hp
  rw [shiftWeight_rankOne 1 le_rfl 1] at hpw
  apply hS p.1 p.2 hp0
  rw [← hpw]
  congr 2
  · have : ((p.1.toNat : ℕ) : ℝ) = (p.1 : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hp0
    rw [this]
  · push_cast; ring

theorem eq_of_weight {w n : ℤ} {r : ℚ}
    (h : ((((w : ℝ) + ((2 * n + 1 : ℤ) : ℝ) ^ 2 / 4 : ℝ)) : ℂ) = (r : ℂ)) :
    (4 * w + (2 * n + 1) ^ 2 : ℚ) = 4 * r := by
  have h1 : (((w : ℝ) + ((2 * n + 1 : ℤ) : ℝ) ^ 2 / 4 : ℝ)) = (r : ℝ) := by
    apply Complex.ofReal_injective
    rw [h]
    simp
  have h2 : ((4 * w + (2 * n + 1) ^ 2 : ℚ) : ℝ) = ((4 * r : ℚ) : ℝ) := by
    push_cast at h1 ⊢
    linarith
  exact_mod_cast h2

/-- Membership in a weight space through the sectors. -/
theorem mem_weight {w n : ℤ} (hw : 0 ≤ w) {x : Sp} (hx : x ∈ Sd n w) :
    x ∈ Mo.weight ((((w : ℝ) + ((2 * n + 1 : ℤ) : ℝ) ^ 2 / 4 : ℝ)) : ℂ) := by
  have h := bigradα_le_shiftWeightSpace (latP 1) (glueLat 1 1) (glueIota 1 1) (glueDelta 1 1)
    (p := (w, n)) hw hx
  rw [shiftWeight_rankOne 1 le_rfl 1] at h
  have : ((w.toNat : ℕ) : ℝ) = (w : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hw
  convert h using 3
  dsimp only
  rw [this]
  push_cast
  ring

/-! ## §6 Abstract `sl₂` -/

section Sl2

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E F H : Module.End ℂ M} {ε : ℂ}

theorem H_Fpow (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x) {v : M} {l : ℂ}
    (hv : H v = l • v) (k : ℕ) : H ((F ^ k) v) = (l - 2 * k) • (F ^ k) v := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := hHF ((F ^ k) v)
    rw [sub_eq_iff_eq_add] at h
    rw [h, ih, map_smul, ← add_smul]
    congr 1
    push_cast; ring

theorem E_Fpow (hEF : ∀ x, E (F x) - F (E x) = ε • H x)
    (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x) {v : M} {l : ℂ}
    (hE : E v = 0) (hv : H v = l • v) (k : ℕ) :
    E ((F ^ (k + 1)) v) = (ε * (k + 1) * (l - k)) • (F ^ k) v := by
  induction k with
  | zero =>
    have h := hEF v
    rw [hE, map_zero, sub_zero] at h
    simp [h, hv, smul_smul]
  | succ k ih =>
    have h := hEF ((F ^ (k + 1)) v)
    rw [sub_eq_iff_eq_add] at h
    rw [show (F ^ (k + 1 + 1)) v = F ((F ^ (k + 1)) v) by rw [pow_succ', Module.End.mul_apply],
      h, H_Fpow hHF hv, ih, map_smul, smul_smul,
      show F ((F ^ k) v) = (F ^ (k + 1)) v by rw [pow_succ', Module.End.mul_apply], ← add_smul]
    congr 1
    push_cast; ring

end Sl2

end VOA.Classification.COne.OrbRat6
