import VOA.DeligneAudit.D4FusionToroidalD4
import VOA.DeligneAudit.D4FusionKernelTheta

/-!
# Garland elements of the `f_θ`-string in the universal module (★a, lift level)

For a sector `S` with a `KernelTable` and `ThetaNilG`, and a vector `w` with
`Sat … (ravSpec S k d)`, the Garland elements
`G_{r,s} w := [z^s] f_θ(z)^r w`, `f_θ(z) = ∑_i (f_θ ⊗ t^i) z^i`, vanish for all
`r ≥ 1` and `2k + 1 ≤ r + s`: this is the project's `Garland.garland` (the `P(u) = 1`
Chari–Pressley identity) fed with the `θ`-string relations, exactly as `theta_garlandG`
feeds `garland_two`.  For `D₄` and `U_m = UModG D4sector.f (ravFam D4sector m 0)` the
bound is `s ≥ 2m − r + 1`, the sharp Chari–Pressley range of the toroidal
presentation.

`garlandVec F r s w` is the same element written as the explicit nested sum over
compositions (`∑_{i₁+⋯+i_r = s} F i₁ ⋯ F i_r w`); the `f_θ ⊗ t^i` commute among
themselves (`ftheta_commG`), so the ordering is immaterial.
-/

namespace VOA.DeligneAudit.UnivG

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector

noncomputable section

section Vec

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (F : ℕ → Module.End ℂ V)

/-- `[z^M] F(z)^k w` as a nested sum over compositions. -/
def garlandVec : ℕ → ℕ → V → V
  | 0, M, w => if M = 0 then w else 0
  | k + 1, M, w => ∑ p ∈ Finset.antidiagonal M, F p.1 (garlandVec k p.2 w)

theorem garlandVec_eq_coeff : ∀ (k M : ℕ) (w : V),
    garlandVec F k M w = (coeff M (Garland.Fs F ^ k)) w
  | 0, M, w => by
      simp only [garlandVec, pow_zero, coeff_one]
      split_ifs <;> simp
  | k + 1, M, w => by
      rw [pow_succ', coeff_mul, LinearMap.coe_sum, Finset.sum_apply]
      simp only [garlandVec, Garland.Fs, coeff_mk, Module.End.mul_apply,
        garlandVec_eq_coeff k]

theorem garlandVec_one (M : ℕ) (w : V) : garlandVec F 1 M w = F M w := by
  simp only [garlandVec]
  rw [Finset.sum_eq_single (M, 0)]
  · simp
  · rintro ⟨a, b⟩ hp hne
    rw [Finset.mem_antidiagonal] at hp
    have hb : b ≠ 0 := by
      intro hb
      apply hne
      ext <;> simp [hb] at hp ⊢
      omega
    simp [hb]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

theorem garlandVec_two (M : ℕ) (w : V) :
    garlandVec F 2 M w = ∑ p ∈ Finset.antidiagonal M, F p.1 (F p.2 w) := by
  change ∑ p ∈ Finset.antidiagonal M, F p.1 (garlandVec F 1 p.2 w) = _
  simp only [garlandVec_one]

end Vec

section Generic

variable {S : DeligneSectorData} (T : KernelTable S) {V : Type} [AddCommGroup V]
  [Module ℂ V] {ρ : CurrentModule S.f V}

include T in
/-- The `f_θ ⊗ t^i` commute among themselves (root vectors of one root). -/
theorem ftheta_commG (r s : ℕ) (v : V) :
    ρ.op S.c₀ r (ρ.op S.c₀ s v) = ρ.op S.c₀ s (ρ.op S.c₀ r v) :=
  comm_c0 T (Or.inl T.c0_fusion) r s v

variable {w : V} {k d : ℕ}

include T in
/-- **Sharp Garland vanishing on the `θ`-string**: with `ravSpec S k d` and `ThetaNilG`,
`[z^s] f_θ(z)^r w = 0` for `r ≥ 1`, `2k + 1 ≤ r + s`. -/
theorem theta_garland_allG (hN : ThetaNilG S) (h : Sat S.f ρ w (ravSpec S k d))
    (r s : ℕ) (hr : 1 ≤ r) (hs : 2 * k + 1 ≤ r + s) :
    (coeff s (Garland.Fs (fun i => ρ.op S.c₀ i) ^ r)) w = 0 := by
  have hFF : ∀ j k, ρ.op S.c₀ j * ρ.op S.c₀ k = ρ.op S.c₀ k * ρ.op S.c₀ j := by
    intro j k
    rw [← sub_eq_zero, op_comm_endG]
    simp [T.lowComm S.c₀ (Or.inl T.c0_fusion)]
  refine Garland.garland (E1 := T.sθ • ρ.op T.eθ 1)
    (H := fun m => T.sθ • ∑ c, S.f T.eθ S.c₀ c • ρ.op c m) (F := fun s => ρ.op S.c₀ s)
    ?_ ?_ hFF ?_ ?_ r hr (hN k V ρ w (fun e he => rs_raising h he 0)
      (fun c hc => rs_cartan_zero h hc) (fun c hc => rs_cartanN_zero h hc)
      (fun i hi => rs_lowering h hi)) s hs
  · intro k
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, op_comm_endG, add_comm 1 k]
  · intro m k
    have hterm : ∀ c, S.f T.eθ S.c₀ c •
        (ρ.op c (m + 1) * ρ.op S.c₀ k - ρ.op S.c₀ k * ρ.op c (m + 1))
        = (S.f T.eθ S.c₀ c * -T.τ c) • ρ.op S.c₀ (m + 1 + k) := by
      intro c
      by_cases hf : S.f T.eθ S.c₀ c = 0
      · simp [hf]
      have hc := T.eθ_cartan c hf
      rw [op_comm_endG, Finset.sum_eq_single S.c₀
        (fun d _ hd => by rw [T.cartTau c hc d, if_neg hd, zero_smul]) (by simp),
        T.cartTau c hc, if_pos rfl, smul_smul]
    have hexp : (T.sθ • ∑ c, S.f T.eθ S.c₀ c • ρ.op c (m + 1)) * ρ.op S.c₀ k -
        ρ.op S.c₀ k * (T.sθ • ∑ c, S.f T.eθ S.c₀ c • ρ.op c (m + 1)) =
        T.sθ • ∑ c, S.f T.eθ S.c₀ c •
          (ρ.op c (m + 1) * ρ.op S.c₀ k - ρ.op S.c₀ k * ρ.op c (m + 1)) := by
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, smul_sub]
    rw [hexp, Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_smul, smul_smul]
    congr 1
    have := T.eθ_theta
    simp only [mul_neg, Finset.sum_neg_distrib, mul_neg]
    linear_combination -this
  · change T.sθ • ρ.op T.eθ 1 w = 0
    rw [rs_raising h T.eθ_raising 1, smul_zero]
  · intro m
    change (T.sθ • ∑ c, S.f T.eθ S.c₀ c • ρ.op c (m + 1)) w = 0
    rw [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_zero, smul_zero]
    intro c _
    by_cases hf : S.f T.eθ S.c₀ c = 0
    · simp [hf]
    · rcases T.eθ_cartan c hf with hc | hc
      · rw [LinearMap.smul_apply, rs_cartan_pos h hc (m + 1) (by omega), smul_zero]
      · rw [LinearMap.smul_apply, rs_cartanN_pos h hc (m + 1) (by omega), smul_zero]

include T in
/-- The same, as the explicit nested sum over compositions. -/
theorem theta_garlandVec_zeroG (hN : ThetaNilG S) (h : Sat S.f ρ w (ravSpec S k d))
    (r s : ℕ) (hr : 1 ≤ r) (hs : 2 * k + 1 ≤ r + s) :
    garlandVec (fun i => ρ.op S.c₀ i) r s w = 0 := by
  rw [garlandVec_eq_coeff]
  exact theta_garland_allG T hN h r s hr hs

end Generic

/-! ## The `D₄` universal module `U_m = UModG D4sector.f (ravFam D4sector m 0)` -/

section D4

open VOA.DeligneAudit.DeligneSector.D4

/-- The current `f_θ ⊗ t^i` on `U_m`. -/
def d4Ftheta (m : ℕ) (i : ℕ) :
    Module.End ℂ (UModG D4sector.f (ravFam D4sector m 0)) :=
  (univRepG D4sector.f (ravFam D4sector m 0)).op D4sector.c₀ i

/-- The generator `v = wUG` of `U_m`. -/
def d4Gen (m : ℕ) : UModG D4sector.f (ravFam D4sector m 0) :=
  wUG D4sector.f (ravFam D4sector m 0)

theorem d4Ftheta_comm (m r s : ℕ) (v : UModG D4sector.f (ravFam D4sector m 0)) :
    d4Ftheta m r (d4Ftheta m s v) = d4Ftheta m s (d4Ftheta m r v) :=
  ftheta_commG d4KernelTable r s v

/-- **Sharp Garland vanishing in `U_m`**: `G_{r,s} v = 0` whenever `r ≥ 1` and
`2m + 1 ≤ r + s`, i.e. `s ≥ 2m − r + 1` (the probe's bound). -/
theorem d4_garland_univ (m r s : ℕ) (hr : 1 ≤ r) (hs : 2 * m + 1 ≤ r + s) :
    garlandVec (d4Ftheta m) r s (d4Gen m) = 0 := by
  have h : Sat D4sector.f (univRepG D4sector.f (ravFam D4sector m 0))
      (wUG D4sector.f (ravFam D4sector m 0)) (ravSpec D4sector (m + 0) (2 * m + 0)) :=
    univG_sat D4sector.f (ravFam D4sector m 0)
  exact theta_garlandVec_zeroG d4KernelTable d4_thetaNil h r s hr (by omega)

/-- The quadratic case: `∑_{a+b=s} (f_θ⊗t^a)(f_θ⊗t^b) v = 0` for `s ≥ 2m − 1`. -/
theorem d4_garland_two (m s : ℕ) (hs : 2 * m + 1 ≤ s + 2) :
    ∑ p ∈ Finset.antidiagonal s, d4Ftheta m p.1 (d4Ftheta m p.2 (d4Gen m)) = 0 := by
  rw [← garlandVec_two]
  exact d4_garland_univ m 2 s (by norm_num) (by omega)

/-- The sharp lower bound, as a named proposition about `U_m`: the Garland element with
`r + s = 2m` is **not** asserted to vanish (the probe reports it nonzero in the fusion
model). -/
def GarlandSharpBelow (m : ℕ) : Prop :=
  ∀ r s, 1 ≤ r → r + s = 2 * m → garlandVec (d4Ftheta m) r s (d4Gen m) ≠ 0

end D4

end

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.garlandVec_eq_coeff
#print axioms VOA.DeligneAudit.UnivG.ftheta_commG
#print axioms VOA.DeligneAudit.UnivG.theta_garland_allG
#print axioms VOA.DeligneAudit.UnivG.theta_garlandVec_zeroG
#print axioms VOA.DeligneAudit.UnivG.d4Ftheta_comm
#print axioms VOA.DeligneAudit.UnivG.d4_garland_univ
#print axioms VOA.DeligneAudit.UnivG.d4_garland_two
end AxiomAudit
