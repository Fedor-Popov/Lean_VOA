import VOA.DeligneAudit.SL4TAdjointSiteLevelOneRelations

/-!
# The second Levi relation at one adjoint site

Inside the first Levi quotient `Q = V / M_{>D}` at the key `D = (1, n + 1, 1)`, the colours of the
rank-two Levi are `g = f₂` (Levi colour 3), `F = f₃` (Levi colour 4) and `q = f₂₃` (Levi colour 5),
with `[F, g] = q` and `[q, g] = 0`.

**Proposition J** (`adjointSite_highModeCompound_mem_higherSecondLevi`). If `v` satisfies the local
Weyl relations of weight `(1, B, 1)` and `f₂(h) v = 0` with `h ≥ 1`, then for every `E ≥ 0`

    u(n + 1, E) = q(h) g^E x y^(n+1) z v ∈ W_{>(D, (E, 1))}.

The proof applies `F(h)` to the word `g^(E+1) x y^(n+1) z v`, which has the higher second key
`(E + 1, 0)` at the same total count, so that it lies in the `F`-stable subspace `W_{>(D,(E,1))}`.
The commutator gives `(E + 1) q(h) g^E` applied to the top word plus `g^(E+1) F(h)` applied to it;
the last term is `(n + 1) g^(E+1) x y^n z z(h) v`, which vanishes in `Q` by Lemma E.
-/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

noncomputable section

section Levi

variable {W : Type} [AddCommGroup W] [Module ℂ W]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable W)

/-- `[F(r), g(s)] = q(r + s)` in the rank-two Levi. -/
theorem leviLast_middle_comm (r s : ℕ) (X : W) :
    Q.op 4 r (Q.op 3 s X) = Q.op 3 s (Q.op 4 r X) + Q.op 5 (r + s) X := by
  have h : Q.op 4 r (Q.op 3 s X) - Q.op 3 s (Q.op 4 r X) = Q.op 5 (r + s) X := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 4 3 r s X
  exact sub_eq_iff_eq_add'.mp h

/-- `[q(r), g(s)] = 0` in the rank-two Levi. -/
theorem leviCompound_middle_comm (r s : ℕ) (X : W) :
    Q.op 5 r (Q.op 3 s X) = Q.op 3 s (Q.op 5 r X) := by
  have h : Q.op 5 r (Q.op 3 s X) - Q.op 3 s (Q.op 5 r X) = 0 := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 5 3 r s X
  exact sub_eq_zero.mp h

/-- `q(r)` commutes with every power of `g(0)`. -/
theorem leviCompound_middlePower_comm (r m : ℕ) (X : W) :
    Q.op 5 r ((Q.op 3 0 ^ m) X) = (Q.op 3 0 ^ m) (Q.op 5 r X) := by
  have hc : Commute (Q.op 5 r) (Q.op 3 0) :=
    LinearMap.ext fun v => leviCompound_middle_comm Q r 0 v
  exact congrArg (fun T : Module.End ℂ W => T X) (hc.pow_right m).eq

/-- `F(r) g^(m+1) = g^(m+1) F(r) + (m + 1) g^m q(r)`. -/
theorem leviLast_middlePower_comm (r m : ℕ) (X : W) :
    Q.op 4 r ((Q.op 3 0 ^ (m + 1)) X) =
      (Q.op 3 0 ^ (m + 1)) (Q.op 4 r X) + ((m + 1 : ℕ) : ℂ) • (Q.op 3 0 ^ m) (Q.op 5 r X) := by
  induction m with
  | zero =>
    simpa only [zero_add, pow_one, pow_zero, Nat.cast_one, one_smul, Module.End.one_apply,
      add_zero] using leviLast_middle_comm Q r 0 X
  | succ m ih =>
    have hg : ∀ k (v : W), Q.op 3 0 ((Q.op 3 0 ^ k) v) = (Q.op 3 0 ^ (k + 1)) v := by
      intro k v
      rw [pow_succ', Module.End.mul_apply]
    rw [← hg (m + 1) X, ← hg (m + 1) (Q.op 4 r X), leviLast_middle_comm, ih, map_add,
      map_smul, add_zero, leviCompound_middlePower_comm, hg m, hg (m + 1)]
    push_cast
    module

end Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- `[z, z] = 0`. -/
theorem bracket_highest_highest (e : Fin 15) : bracketInt 8 8 e = 0 := by
  fin_cases e <;> decide

/-- The zero-mode top word at the key `(1, n, 1)` lies in the first Levi multiplicity image. -/
theorem adjointSite_topWord_mem_image (B : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (n : ℕ) : ∃ φ, radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![1, n, 1] φ =
      (higherRadicalCountClosure ρ w ![1, n, 1]).mkQ
        (ρ.op 6 0 ((ρ.op 7 0 ^ n) (ρ.op 8 0 w))) := by
  obtain ⟨φ, hφ⟩ := radicalGrassmannianEvaluation_surjective ρ w 1 B 1 hW ![1, n, 1]
    ⟨_, ⟨_, adjointSite_topWord_mem_layer ρ w n 0, rfl⟩⟩
  refine ⟨φ, ?_⟩
  change (radicalGrassmannianEvaluation ρ w 1 B 1 hW ![1, n, 1] φ).val = _
  rw [hφ]

/-- The top word is killed by `F(h)` in the first Levi quotient, by Lemma E. -/
theorem adjointSite_topWord_lastLowering_zero (B h : ℕ)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (hh : 0 < h) (hg : ρ.op 9 h w = 0) (n : ℕ) :
    (radicalCountQuotCurrent ρ w ![1, n + 1, 1]).op 4 h
      ((higherRadicalCountClosure ρ w ![1, n + 1, 1]).mkQ
        (ρ.op 6 0 ((ρ.op 7 0 ^ (n + 1)) (ρ.op 8 0 w)))) = 0 := by
  have hE := adjointSite_lowerKey_mem ρ w B h hW hh hg n
  have hFw : ρ.op 11 h w = 0 :=
    simple_mode_zero ρ w (weightABC 1 B 1) hW 2 h (by change 1 ≤ h; omega)
  change (higherRadicalCountClosure ρ w ![1, n + 1, 1]).mkQ
    (ρ.op 11 h (ρ.op 6 0 ((ρ.op 7 0 ^ (n + 1)) (ρ.op 8 0 w)))) = 0
  rw [op_comm_of_zero_bracket ρ bracket_last_first, last_compoundPower_comm,
    op_comm_of_zero_bracket ρ bracket_last_highest, hFw, map_zero, map_zero, zero_add,
    op_comm_of_zero_bracket ρ bracket_highest_highest h 0, map_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hE

set_option synthInstance.maxHeartbeats 100000 in
-- The second Levi closure is built over nested tensor-product coefficient algebras.
/-- **Proposition J.** The vector `q(h) g^E x y^(n+1) z v` lies in the higher second Levi
subspace `W_{>((1, n+1, 1), (E, 1))}`. -/
theorem adjointSite_highModeCompound_mem_higherSecondLevi (B h : ℕ)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (hh : 0 < h) (hg : ρ.op 9 h w = 0)
    (n E : ℕ) :
    (radicalCountQuotCurrent ρ w ![1, n + 1, 1]).op 5 h
      (((radicalCountQuotCurrent ρ w ![1, n + 1, 1]).op 3 0 ^ E)
        ((higherRadicalCountClosure ρ w ![1, n + 1, 1]).mkQ
          (ρ.op 6 0 ((ρ.op 7 0 ^ (n + 1)) (ρ.op 8 0 w))))) ∈
      higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w ![1, n + 1, 1])
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![1, n + 1, 1]) E 1 := by
  obtain ⟨φ, hφ⟩ := adjointSite_topWord_mem_image ρ w B hW (n + 1)
  have hz0 := adjointSite_topWord_lastLowering_zero ρ w B h hW hh hg n
  set Q := radicalCountQuotCurrent ρ w ![1, n + 1, 1] with hQ
  set β := radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![1, n + 1, 1] with hβ
  rw [← hφ] at hz0 ⊢
  have hlayer : (Q.op 3 0 ^ (E + 1)) (β φ) ∈ secondLeviCountLayer Q β (E + 1) 0 := by
    unfold secondLeviCountLayer
    apply Submodule.mem_iSup_of_mem φ
    have hw := A3Sector.a2CountSpan_first_word Q (β φ) (List.replicate (E + 1) 0) 0 0
      (A3Sector.a2CountSpan_zero Q (β φ))
    simpa [List.map_replicate, List.prod_replicate] using hw
  have hmem : (Q.op 3 0 ^ (E + 1)) (β φ) ∈ ⨆ u : ℕ, ⨆ v : ℕ,
      ⨆ (_ : u + v = E + 1 ∧ E < u), secondLeviCountLayer Q β u v :=
    Submodule.mem_iSup_of_mem (E + 1) (Submodule.mem_iSup_of_mem 0
      (Submodule.mem_iSup_of_mem (⟨by omega, by omega⟩ : E + 1 + 0 = E + 1 ∧ E < E + 1)
        hlayer))
  have hhigh : (Q.op 3 0 ^ (E + 1)) (β φ) ∈ higherSecondLeviCountClosure Q β E 1 :=
    A3Sector.a2LeviClosure_contains Q _ hmem
  have hF : Q.op 4 h ((Q.op 3 0 ^ (E + 1)) (β φ)) ∈ higherSecondLeviCountClosure Q β E 1 :=
    A3Sector.a2LeviClosure_inv Q _ 4 h (by simp [A3Sector.a2Levi]) hhigh
  rw [leviLast_middlePower_comm, hz0, map_zero, zero_add] at hF
  rw [leviCompound_middlePower_comm]
  have hne : ((E + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero E
  have hs := (higherSecondLeviCountClosure Q β E 1).smul_mem ((E + 1 : ℕ) : ℂ)⁻¹ hF
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at hs

end

end VOA.DeligneAudit.SL4T
