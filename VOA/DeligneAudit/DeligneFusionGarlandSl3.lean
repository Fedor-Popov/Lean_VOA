import VOA.DeligneAudit.DeligneFusionGarland

/-!
# `RavinderKernelTrunc` from the `θ`-Garland identity

For `w` with the relations of `M_{a,b}` (`n = a + b`, `c = 2a + b`):

* `f_θ^{2n+1} w = 0` (`ftheta_pow`), from the Heisenberg lemma for `⟨f₁, f₂, f_θ⟩`;
* `∑_{i+j=s} f_θ(i) f_θ(j) w = 0` for `s ≥ 2n-1` (`theta_garland`), from `garland_two` for the
  `θ`-triple `(e_θ ⊗ t, h₁ + h₂, f_θ)`;
* the three truncations: at `s = 2c-3` only `f_θ(c-2) f_θ(c-1) w` survives (twice); applying `e₂`
  (resp. `e₁`) at `s = (n-1)+(c-1)` only `f₁(n-1) f_θ(c-1) w` (resp. `f₂`) survives.
-/

namespace VOA.DeligneAudit.SectorWeyl

open VOA.AffineSl3 VOA.DeligneAudit.Garland

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule (bracketTable) V}

theorem op_comm_end (a b : Fin 8) (r s : ℕ) :
    ρ.op a r * ρ.op b s - ρ.op b s * ρ.op a r = ∑ e, bracketTable a b e • ρ.op e (r + s) := by
  ext x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  exact ρ.comm a b r s x

theorem op5_comm (i j : ℕ) (v : V) : ρ.op 5 i (ρ.op 5 j v) = ρ.op 5 j (ρ.op 5 i v) := by
  rw [comm_apply 5 5]; simp [Fin.sum_univ_eight, bracketTable]

theorem op3_op5 (i j : ℕ) (v : V) : ρ.op 3 i (ρ.op 5 j v) = ρ.op 5 j (ρ.op 3 i v) := by
  rw [comm_apply 3 5]; simp [Fin.sum_univ_eight, bracketTable]

theorem op4_op5 (i j : ℕ) (v : V) : ρ.op 4 i (ρ.op 5 j v) = ρ.op 5 j (ρ.op 4 i v) := by
  rw [comm_apply 4 5]; simp [Fin.sum_univ_eight, bracketTable]

variable {w : V} {a b : ℕ}

/-- `f_θ^{2(a+b)+1} w = 0`. -/
theorem ftheta_pow (h : MabRel ρ w a b) : ((ρ.op 5 0) ^ (2 * (a + b) + 1)) w = 0 := by
  have hXY : ρ.op 3 0 * ρ.op 4 0 - ρ.op 4 0 * ρ.op 3 0 = -ρ.op 5 0 := by
    rw [op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]
  have hXZ : ρ.op 3 0 * -ρ.op 5 0 = -ρ.op 5 0 * ρ.op 3 0 := by
    rw [mul_neg, neg_mul, neg_inj, ← sub_eq_zero, op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable]
  have hYZ : ρ.op 4 0 * -ρ.op 5 0 = -ρ.op 5 0 * ρ.op 4 0 := by
    rw [mul_neg, neg_mul, neg_inj, ← sub_eq_zero, op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable]
  have hX : ((ρ.op 3 0) ^ (a + b + 1)) w = 0 := by rw [Module.End.pow_apply]; exact h.lowering_f1
  have hY : ((ρ.op 4 0) ^ (a + b + 1)) w = 0 := by rw [Module.End.pow_apply]; exact h.lowering_f2
  have := heis_nilpotent hXY hYZ hXZ hX hY
  rw [neg_pow, Odd.neg_one_pow (by exact ⟨a + b, rfl⟩), neg_one_mul, LinearMap.neg_apply,
    neg_eq_zero] at this
  exact this

/-- **The `θ`-Garland identity**: `∑_{i+j=s} f_θ(i) f_θ(j) w = 0` for `s + 1 ≥ 2(a+b)`. -/
theorem theta_garland (h : MabRel ρ w a b) (s : ℕ) (hs : 2 * (a + b) ≤ s + 1) :
    ∑ x ∈ Finset.antidiagonal s, ρ.op 5 x.1 (ρ.op 5 x.2 w) = 0 := by
  refine garland_two (E1 := ρ.op 2 1) (H := fun m => ρ.op 6 m + ρ.op 7 m) (F := fun k => ρ.op 5 k)
    ?_ ?_ ?_ ?_ ?_ (ftheta_pow h) s (by omega)
  · intro k
    rw [op_comm_end]; simp [Fin.sum_univ_eight, bracketTable, add_comm 1 k]
  · intro m k
    rw [add_mul, mul_add, add_sub_add_comm, op_comm_end, op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable]
    rw [← two_smul ℂ, smul_neg]
  · intro j k
    ext v; exact op5_comm j k v
  · exact h.raising 2 (by decide) 1
  · intro m
    rw [LinearMap.add_apply, h.cartan_pos 6 (by decide) (m + 1) (by omega),
      h.cartan_pos 7 (by decide) (m + 1) (by omega), add_zero]

theorem two_eq_zero {x : V} (hx : x + x = 0) : x = 0 := by
  rw [← two_smul ℂ, smul_eq_zero] at hx
  exact hx.resolve_left two_ne_zero

/-- The `θ`-truncation of the kernel vector. -/
theorem kernel_trunc_theta (h : MabRel ρ w a b) (ha : 1 ≤ a) :
    ρ.op 5 (2 * (a - 1) + b) (ρ.op 5 (2 * a + b - 1) w) = 0 := by
  have hG := theta_garland h (2 * (2 * a + b) - 3) (by omega)
  rw [Finset.sum_eq_add_of_mem (2 * a + b - 2, 2 * a + b - 1) (2 * a + b - 1, 2 * a + b - 2)
    (Finset.mem_antidiagonal.mpr (by simp; omega)) (Finset.mem_antidiagonal.mpr (by simp; omega))
    (by simp; omega) ?_, op5_comm (2 * a + b - 1)] at hG
  · rw [show 2 * (a - 1) + b = 2 * a + b - 2 by omega]
    exact two_eq_zero hG
  · rintro ⟨i, j⟩ hx ⟨h1, h2⟩
    rw [Finset.mem_antidiagonal] at hx
    simp only [ne_eq, Prod.mk.injEq] at h1 h2 hx
    by_cases hj : 2 * a + b ≤ j
    · rw [mab_ftheta_trunc h j hj, map_zero]
    · rw [op5_comm, mab_ftheta_trunc h i (by omega), map_zero]

/-- Extraction for the `f_i`-truncations. -/
theorem kernel_trunc_aux (h : MabRel ρ w a b) (ha : 1 ≤ a) (G : ℕ → V →ₗ[ℂ] V)
    (hGc : ∀ i j v, G i (ρ.op 5 j v) = ρ.op 5 j (G i v)) (hGw : ∀ i, a + b ≤ i → G i w = 0)
    (hsum : ∑ x ∈ Finset.antidiagonal ((a + b - 1) + (2 * a + b - 1)),
      (G x.1 (ρ.op 5 x.2 w) + ρ.op 5 x.1 (G x.2 w)) = 0) :
    G (a - 1 + b) (ρ.op 5 (2 * a + b - 1) w) = 0 := by
  simp only [← hGc] at hsum
  rw [Finset.sum_add_distrib,
    ← Finset.Nat.sum_antidiagonal_swap (f := fun x : ℕ × ℕ => G x.2 (ρ.op 5 x.1 w))] at hsum
  simp only [Prod.fst_swap, Prod.snd_swap] at hsum
  have hS := two_eq_zero hsum
  rw [Finset.sum_eq_single (a + b - 1, 2 * a + b - 1)] at hS
  · rw [show a - 1 + b = a + b - 1 by omega]; exact hS
  · rintro ⟨i, j⟩ hx hne
    rw [Finset.mem_antidiagonal] at hx
    simp only [ne_eq, Prod.mk.injEq] at hne hx
    by_cases hj : 2 * a + b ≤ j
    · rw [mab_ftheta_trunc h j hj, map_zero]
    · rw [hGc, hGw i (by omega), map_zero]
  · intro hn; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) hn

theorem kernel_trunc_f1 (h : MabRel ρ w a b) (ha : 1 ≤ a) :
    ρ.op 3 (a - 1 + b) (ρ.op 5 (2 * a + b - 1) w) = 0 := by
  refine kernel_trunc_aux h ha (fun i => ρ.op 3 i) (fun i j v => op3_op5 i j v)
    (fun i hi => mab_f1_trunc h i hi) ?_
  have hG := congrArg (ρ.op 1 0) (theta_garland h ((a + b - 1) + (2 * a + b - 1)) (by omega))
  rw [map_sum, map_zero] at hG
  rw [← hG]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [comm_apply 1 5 0 x.1, comm_apply 1 5 0 x.2, h.raising 1 (by decide)]
  simp [Fin.sum_univ_eight, bracketTable, add_comm]

theorem kernel_trunc_f2 (h : MabRel ρ w a b) (ha : 1 ≤ a) :
    ρ.op 4 (a - 1 + b) (ρ.op 5 (2 * a + b - 1) w) = 0 := by
  refine kernel_trunc_aux h ha (fun i => ρ.op 4 i) (fun i j v => op4_op5 i j v)
    (fun i hi => mab_f2_trunc h i hi) ?_
  have hG := congrArg (ρ.op 0 0) (theta_garland h ((a + b - 1) + (2 * a + b - 1)) (by omega))
  rw [map_sum, map_zero] at hG
  rw [← neg_eq_zero, ← hG, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [comm_apply 0 5 0 x.1, comm_apply 0 5 0 x.2, h.raising 0 (by decide)]
  simp [Fin.sum_univ_eight, bracketTable]

/-- **`RavinderKernelTrunc` is a theorem** (Garland identity with `P(u) = 1`). -/
theorem ravinderKernelTrunc : RavinderKernelTrunc := by
  intro a b V _ _ ρ w ha h
  exact ⟨kernel_trunc_f1 h ha, kernel_trunc_f2 h ha, kernel_trunc_theta h ha⟩

/-- **`RavinderKernelRel` (F4′) is a theorem.** -/
theorem ravinderKernelRel : RavinderKernelRel := ravinderKernelRel_of_trunc ravinderKernelTrunc

end VOA.DeligneAudit.SectorWeyl

section AxiomAudit
#print axioms VOA.DeligneAudit.Garland.heis_nilpotent
#print axioms VOA.DeligneAudit.Garland.garland
#print axioms VOA.DeligneAudit.Garland.garland_two
#print axioms VOA.DeligneAudit.SectorWeyl.theta_garland
#print axioms VOA.DeligneAudit.SectorWeyl.ravinderKernelTrunc
#print axioms VOA.DeligneAudit.SectorWeyl.ravinderKernelRel
end AxiomAudit
