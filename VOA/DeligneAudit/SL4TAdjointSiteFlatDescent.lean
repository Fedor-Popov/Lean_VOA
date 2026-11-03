import VOA.DeligneAudit.SL4TAdjointSiteFlatExpansion

/-!
# Descent in the first second-level count

The key input is the inclusion `η(0) W_{>(d,(E,e))} ⊆ W_{>(d,(E-1,e))}`.

Everything here is stated for an arbitrary `sl₃[t]` current module `Q` (the first Levi quotient
in the application) and an arbitrary linear map `β` from a commutative algebra (the first Levi
multiplicity evaluation), under the hypotheses that every `β φ` is killed by the three raising
currents `η = E₁₂`, `E₁₃`, `e₃ = E₂₃` (sl₃ colours `0`, `2`, `1`) and that the two Cartan
currents preserve the image of `β`. Write `S(u, v)` for the second Levi count layer
(`secondLeviCountLayer`: words with `u` letters `g` and `v` letters `q`) and `N(E, e)` for the
higher second Levi closure (`higherSecondLeviCountClosure`).

* `secondLeviCountLayer_le_of_step`: an induction principle over the words of the count layers.
* **Lemma M(i)** (`higherSecondLeviCountClosure_raising_le`): `η(0) N(E + 1, e) ⊆ N(E, e)`. On a
  count layer, `η` turns a `g` into a Cartan current and a `q` into `-F`, so
  `η S(u, v) ⊆ S(u - 1, v) + F S(u, v - 1)`; similarly `E₁₃ S(u, v) ⊆ S(u - 1, v) + S(u, v - 1)`.
  The preimage of `N(E, e)` under all modes of `η` and `E₁₃` is stable under the final `gl₂`.
* **Lemma 6.4** (`raising_topWord`): if `η β₁ = 0` and `h₂(0) β₁ = p β₁`, then
  `η(0) g^(E+1) q^e β₁ = (E + 1)(p - E) g^E q^e β₁ - e F(0) g^(E+1) q^(e-1) β₁`.
* **The descent** (`secondLevi_topWord_descent`): an operator `T` commuting with `η(0)` and
  preserving every `N(E, e)` satisfies `T(g^E q^e β₁) ∈ N(E, e)` for every `E ≤ p` as soon as this
  holds at the top `E = p`.
-/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector VOA.DeligneAudit.LeviTypeA

noncomputable section

/-! ### Commutators in the rank-two Levi -/

section Levi

variable {W : Type} [AddCommGroup W] [Module ℂ W]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable W)

/-- `[η(r), g(s)] = h₂(r + s)`. -/
theorem leviRaising_middle_comm (r s : ℕ) (x : W) :
    Q.op 0 r (Q.op 3 s x) = Q.op 3 s (Q.op 0 r x) + Q.op 6 (r + s) x := by
  have h : Q.op 0 r (Q.op 3 s x) - Q.op 3 s (Q.op 0 r x) = Q.op 6 (r + s) x := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 0 3 r s x
  exact sub_eq_iff_eq_add'.mp h

/-- `[η(r), q(s)] = -F(r + s)`. -/
theorem leviRaising_compound_comm (r s : ℕ) (x : W) :
    Q.op 0 r (Q.op 5 s x) = Q.op 5 s (Q.op 0 r x) - Q.op 4 (r + s) x := by
  have h : Q.op 0 r (Q.op 5 s x) - Q.op 5 s (Q.op 0 r x) = -Q.op 4 (r + s) x := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 0 5 r s x
  rw [sub_eq_iff_eq_add'.mp h, sub_eq_add_neg]

/-- `[E₁₃(r), g(s)] = -e₃(r + s)`. -/
theorem leviOuterRaising_middle_comm (r s : ℕ) (x : W) :
    Q.op 2 r (Q.op 3 s x) = Q.op 3 s (Q.op 2 r x) - Q.op 1 (r + s) x := by
  have h : Q.op 2 r (Q.op 3 s x) - Q.op 3 s (Q.op 2 r x) = -Q.op 1 (r + s) x := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 2 3 r s x
  rw [sub_eq_iff_eq_add'.mp h, sub_eq_add_neg]

/-- `[E₁₃(r), q(s)] = h₂(r + s) + h₃(r + s)`. -/
theorem leviOuterRaising_compound_comm (r s : ℕ) (x : W) :
    Q.op 2 r (Q.op 5 s x) = Q.op 5 s (Q.op 2 r x) + (Q.op 6 (r + s) x + Q.op 7 (r + s) x) := by
  have h : Q.op 2 r (Q.op 5 s x) - Q.op 5 s (Q.op 2 r x) =
      Q.op 6 (r + s) x + Q.op 7 (r + s) x := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 2 5 r s x
  exact sub_eq_iff_eq_add'.mp h

/-- `[e₃(r), g(s)] = 0`. -/
theorem leviLastRaising_middle_comm (r s : ℕ) (x : W) :
    Q.op 1 r (Q.op 3 s x) = Q.op 3 s (Q.op 1 r x) := by
  have h : Q.op 1 r (Q.op 3 s x) - Q.op 3 s (Q.op 1 r x) = 0 := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 1 3 r s x
  exact sub_eq_zero.mp h

/-- `[e₃(r), q(s)] = g(r + s)`. -/
theorem leviLastRaising_compound_comm (r s : ℕ) (x : W) :
    Q.op 1 r (Q.op 5 s x) = Q.op 5 s (Q.op 1 r x) + Q.op 3 (r + s) x := by
  have h : Q.op 1 r (Q.op 5 s x) - Q.op 5 s (Q.op 1 r x) = Q.op 3 (r + s) x := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 1 5 r s x
  exact sub_eq_iff_eq_add'.mp h

/-- `[g(s), F(t)] = -q(s + t)`. -/
theorem leviMiddle_last_comm (s t : ℕ) (x : W) :
    Q.op 3 s (Q.op 4 t x) = Q.op 4 t (Q.op 3 s x) - Q.op 5 (s + t) x := by
  have h : Q.op 3 s (Q.op 4 t x) - Q.op 4 t (Q.op 3 s x) = -Q.op 5 (s + t) x := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 3 4 s t x
  rw [sub_eq_iff_eq_add'.mp h, sub_eq_add_neg]

/-- `[q(s), F(t)] = 0`. -/
theorem leviCompound_last_comm (s t : ℕ) (x : W) :
    Q.op 5 s (Q.op 4 t x) = Q.op 4 t (Q.op 5 s x) := by
  have h : Q.op 5 s (Q.op 4 t x) - Q.op 4 t (Q.op 5 s x) = 0 := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 5 4 s t x
  exact sub_eq_zero.mp h

/-- `[F(r), η(s)] = 0`. -/
theorem leviLast_raising_comm (r s : ℕ) (x : W) :
    Q.op 4 r (Q.op 0 s x) = Q.op 0 s (Q.op 4 r x) := by
  have h : Q.op 4 r (Q.op 0 s x) - Q.op 0 s (Q.op 4 r x) = 0 := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 4 0 r s x
  exact sub_eq_zero.mp h

/-- `[h₂(0), g(0)] = -2 g(0)` on powers: `h₂ g^n = g^n h₂ - 2n g^n`. -/
theorem leviMiddleCartan_middlePow (n : ℕ) (x : W) :
    Q.op 6 0 ((Q.op 3 0 ^ n) x) =
      (Q.op 3 0 ^ n) (Q.op 6 0 x) - ((2 * n : ℕ) : ℂ) • (Q.op 3 0 ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc := (leviCartan_secondLowering_comm Q 0 0 ((Q.op 3 0 ^ n) x)).1
    rw [pow_succ', Module.End.mul_apply, hc, ih, map_sub, map_smul, zero_add,
      Module.End.mul_apply]
    push_cast
    module

/-- **The `sl₂` relation of `η` and `g`.** `η g^(n+1) = g^(n+1) η + (n+1) g^n h₂ - (n+1) n g^n`. -/
theorem leviRaising_middlePow (n : ℕ) (x : W) :
    Q.op 0 0 ((Q.op 3 0 ^ (n + 1)) x) =
      (Q.op 3 0 ^ (n + 1)) (Q.op 0 0 x) + ((n + 1 : ℕ) : ℂ) • (Q.op 3 0 ^ n) (Q.op 6 0 x) -
        (((n + 1) * n : ℕ) : ℂ) • (Q.op 3 0 ^ n) x := by
  induction n with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_one, one_smul,
      mul_zero, Nat.cast_zero, zero_smul, sub_zero]
    exact leviRaising_middle_comm Q 0 0 x
  | succ n ih =>
    rw [pow_succ' (Q.op 3 0) (n + 1), Module.End.mul_apply, leviRaising_middle_comm, ih,
      zero_add, leviMiddleCartan_middlePow, map_sub, map_add, map_smul, map_smul]
    simp only [pow_succ', Module.End.mul_apply]
    push_cast
    module

end Levi

/-! ### Count layers -/

section Layers

variable {R W : Type} [CommRing R] [Algebra ℂ R] [AddCommGroup W] [Module ℂ W]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable W) (β : R →ₗ[ℂ] W)

/-- **Induction over count-layer words.** A family of subspaces containing every `β φ` at the
count `(0, 0)` and propagated by `g` and `q` (on vectors of the matching count layer) contains
every count layer. -/
theorem secondLeviCountLayer_le_of_step (P : ℕ → ℕ → Submodule ℂ W)
    (hbase : ∀ φ, β φ ∈ P 0 0)
    (hg : ∀ u v s x, x ∈ secondLeviCountLayer Q β u v → x ∈ P u v → Q.op 3 s x ∈ P (u + 1) v)
    (hq : ∀ u v s x, x ∈ secondLeviCountLayer Q β u v → x ∈ P u v → Q.op 5 s x ∈ P u (v + 1))
    (u v : ℕ) : secondLeviCountLayer Q β u v ≤ P u v := by
  have hword : ∀ (φ : R) (l : List (Fin 2 × ℕ)),
      radicalWord (a2RadicalOp Q) l • β φ ∈ secondLeviCountLayer Q β
          (l.countP (fun x => x.1 = 0)) (l.countP (fun x => x.1 = 1)) ∧
        radicalWord (a2RadicalOp Q) l • β φ ∈
          P (l.countP (fun x => x.1 = 0)) (l.countP (fun x => x.1 = 1)) := by
    intro φ l
    induction l with
    | nil =>
      simp only [radicalWord, List.map_nil, List.prod_nil, one_smul, List.countP_nil]
      exact ⟨Submodule.mem_iSup_of_mem φ (a2CountSpan_zero Q (β φ)), hbase φ⟩
    | cons x l ih =>
      obtain ⟨i, s⟩ := x
      have hrw : radicalWord (a2RadicalOp Q) ((i, s) :: l) • β φ =
          a2RadicalOp Q i s (radicalWord (a2RadicalOp Q) l • β φ) := rfl
      rw [hrw]
      by_cases hi : i = 0
      · subst hi
        have h₀ : (((0 : Fin 2), s) :: l).countP (fun x => x.1 = 0) =
            l.countP (fun x => x.1 = 0) + 1 := by simp
        have h₁ : (((0 : Fin 2), s) :: l).countP (fun x => x.1 = 1) =
            l.countP (fun x => x.1 = 1) := by simp
        have ha : a2RadicalOp Q 0 s = Q.op 3 s := by simp [a2RadicalOp]
        rw [h₀, h₁, ha]
        exact ⟨secondLeviCountLayer_middle Q β _ _ s ih.1, hg _ _ s _ ih.1 ih.2⟩
      · obtain rfl : i = 1 := by fin_cases i <;> simp_all
        have h₀ : (((1 : Fin 2), s) :: l).countP (fun x => x.1 = 0) =
            l.countP (fun x => x.1 = 0) := by simp
        have h₁ : (((1 : Fin 2), s) :: l).countP (fun x => x.1 = 1) =
            l.countP (fun x => x.1 = 1) + 1 := by simp
        have ha : a2RadicalOp Q 1 s = Q.op 5 s := by simp [a2RadicalOp]
        rw [h₀, h₁, ha]
        exact ⟨secondLeviCountLayer_compound Q β _ _ s ih.1, hq _ _ s _ ih.1 ih.2⟩
  apply iSup_le
  intro φ
  apply iSup_le
  intro deg
  rw [a2KeyLayer, Submodule.span_le]
  rintro z ⟨l, h₁, h₂, -, -, rfl⟩
  have hm := (hword φ l).2
  rw [h₁, h₂] at hm
  exact hm

/-- Every zero-mode word `g^a q^b β φ` lies in the count layer `(a, b)`. -/
theorem zeroModeSecondWord_mem (φ : R) (a b : ℕ) :
    (Q.op 3 0 ^ a) ((Q.op 5 0 ^ b) (β φ)) ∈ secondLeviCountLayer Q β a b := by
  have hq : ∀ b, (Q.op 5 0 ^ b) (β φ) ∈ secondLeviCountLayer Q β 0 b := by
    intro b
    induction b with
    | zero => exact Submodule.mem_iSup_of_mem φ (a2CountSpan_zero Q (β φ))
    | succ b ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact secondLeviCountLayer_compound Q β _ _ 0 ih
  induction a with
  | zero => simpa using hq b
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact secondLeviCountLayer_middle Q β _ _ 0 ih

/-- The two Cartan currents preserve every count layer, if they preserve the image of `β`. -/
theorem secondLeviCountLayer_cartan (c : Fin 8) (hc : c = 6 ∨ c = 7)
    (hβ : ∀ t φ, ∃ φ', Q.op c t (β φ) = β φ') (t u v : ℕ) :
    secondLeviCountLayer Q β u v ≤ (secondLeviCountLayer Q β u v).comap (Q.op c t) := by
  have hle := secondLeviCountLayer_le_of_step Q β
    (fun u v => ⨅ t, (secondLeviCountLayer Q β u v).comap (Q.op c t))
    (fun φ => by
      rw [Submodule.mem_iInf]
      intro t
      obtain ⟨φ', hφ'⟩ := hβ t φ
      rw [Submodule.mem_comap, hφ']
      exact Submodule.mem_iSup_of_mem φ' (a2CountSpan_zero Q (β φ')))
    (fun u v s x hx hP => by
      simp only [Submodule.mem_iInf, Submodule.mem_comap] at hP ⊢
      intro t
      obtain ⟨h₆, h₇, -, -⟩ := leviCartan_secondLowering_comm Q t s x
      rcases hc with rfl | rfl
      · rw [h₆]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _
          (secondLeviCountLayer_middle Q β _ _ _ hx))
          (secondLeviCountLayer_middle Q β _ _ _ (hP t))
      · rw [h₇]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _
          (secondLeviCountLayer_middle Q β _ _ _ hx))
          (secondLeviCountLayer_middle Q β _ _ _ (hP t)))
    (fun u v s x hx hP => by
      simp only [Submodule.mem_iInf, Submodule.mem_comap] at hP ⊢
      intro t
      obtain ⟨-, -, h₆, h₇⟩ := leviCartan_secondLowering_comm Q t s x
      rcases hc with rfl | rfl
      · rw [h₆]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _
          (secondLeviCountLayer_compound Q β _ _ _ hx))
          (secondLeviCountLayer_compound Q β _ _ _ (hP t))
      · rw [h₇]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _
          (secondLeviCountLayer_compound Q β _ _ _ hx))
          (secondLeviCountLayer_compound Q β _ _ _ (hP t)))
    u v
  intro x hx
  exact Submodule.mem_iInf _ |>.mp (hle hx) t

/-- The last raising current `e₃` sends `S(u, v)` into `S(u + 1, v - 1)`, and kills `S(u, 0)`. -/
theorem secondLeviCountLayer_lastRaising (he : ∀ r φ, Q.op 1 r (β φ) = 0) (r u v : ℕ) :
    secondLeviCountLayer Q β u v ≤
      (if v = 0 then ⊥ else secondLeviCountLayer Q β (u + 1) (v - 1)).comap (Q.op 1 r) := by
  have hle := secondLeviCountLayer_le_of_step Q β
    (fun u v => ⨅ r, (if v = 0 then ⊥ else
      secondLeviCountLayer Q β (u + 1) (v - 1)).comap (Q.op 1 r))
    (fun φ => by
      rw [Submodule.mem_iInf]
      intro r
      rw [Submodule.mem_comap, he]
      exact Submodule.zero_mem _)
    (fun u v s x _ hP => by
      simp only [Submodule.mem_iInf, Submodule.mem_comap] at hP ⊢
      intro r
      have h := hP r
      rw [leviLastRaising_middle_comm]
      by_cases hv : v = 0
      · rw [if_pos hv, Submodule.mem_bot] at h
        rw [h, map_zero]
        exact Submodule.zero_mem _
      · rw [if_neg hv] at h ⊢
        exact secondLeviCountLayer_middle Q β _ _ _ h)
    (fun u v s x hx hP => by
      simp only [Submodule.mem_iInf, Submodule.mem_comap] at hP ⊢
      intro r
      have h := hP r
      rw [leviLastRaising_compound_comm, if_neg (Nat.add_one_ne_zero v), Nat.add_sub_cancel]
      have hg' : Q.op 3 (r + s) x ∈ secondLeviCountLayer Q β (u + 1) v :=
        secondLeviCountLayer_middle Q β _ _ _ hx
      refine Submodule.add_mem _ ?_ hg'
      by_cases hv : v = 0
      · rw [if_pos hv, Submodule.mem_bot] at h
        rw [h, map_zero]
        exact Submodule.zero_mem _
      · rw [if_neg hv] at h
        have h' := secondLeviCountLayer_compound Q β _ _ s h
        rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hv)] at h')
    u v
  intro x hx
  exact Submodule.mem_iInf _ |>.mp (hle hx) r

/-- The images of a count layer under all modes of the last lowering current `F`. -/
def secondLeviLastImage (u v : ℕ) : Submodule ℂ W :=
  ⨆ t : ℕ, (secondLeviCountLayer Q β u v).map (Q.op 4 t)

theorem secondLeviLastImage_mem (u v t : ℕ) {y : W} (hy : y ∈ secondLeviCountLayer Q β u v) :
    Q.op 4 t y ∈ secondLeviLastImage Q β u v :=
  Submodule.mem_iSup_of_mem t (Submodule.mem_map_of_mem hy)

/-- `g(s) F S(u, v) ⊆ F S(u + 1, v) + S(u, v + 1)`. -/
theorem secondLeviLastImage_middle (u v s : ℕ) :
    secondLeviLastImage Q β u v ≤ (secondLeviLastImage Q β (u + 1) v ⊔
      secondLeviCountLayer Q β u (v + 1)).comap (Q.op 3 s) := by
  apply iSup_le
  intro t
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  rw [Submodule.mem_comap, Submodule.mem_comap, leviMiddle_last_comm]
  exact Submodule.sub_mem _
    (Submodule.mem_sup_left (secondLeviLastImage_mem Q β _ _ t
      (secondLeviCountLayer_middle Q β _ _ s hy)))
    (Submodule.mem_sup_right (secondLeviCountLayer_compound Q β _ _ _ hy))

/-- `q(s) F S(u, v) ⊆ F S(u, v + 1)`. -/
theorem secondLeviLastImage_compound (u v s : ℕ) :
    secondLeviLastImage Q β u v ≤ (secondLeviLastImage Q β u (v + 1)).comap (Q.op 5 s) := by
  apply iSup_le
  intro t
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  rw [Submodule.mem_comap, Submodule.mem_comap, leviCompound_last_comm]
  exact secondLeviLastImage_mem Q β _ _ t (secondLeviCountLayer_compound Q β _ _ s hy)

/-- The target of `η` on the count layer `(u, v)`: `S(u - 1, v) + F S(u, v - 1)`. -/
def secondLeviRaisingTarget (u v : ℕ) : Submodule ℂ W :=
  (if u = 0 then ⊥ else secondLeviCountLayer Q β (u - 1) v) ⊔
    (if v = 0 then ⊥ else secondLeviLastImage Q β u (v - 1))

/-- The target of `E₁₃` on the count layer `(u, v)`: `S(u - 1, v) + S(u, v - 1)`. -/
def secondLeviOuterRaisingTarget (u v : ℕ) : Submodule ℂ W :=
  (if u = 0 then ⊥ else secondLeviCountLayer Q β (u - 1) v) ⊔
    (if v = 0 then ⊥ else secondLeviCountLayer Q β u (v - 1))

/-- `g(s)` maps the `η`-target of `(u, v)` into that of `(u + 1, v)`. -/
theorem secondLeviRaisingTarget_middle (u v s : ℕ) :
    secondLeviRaisingTarget Q β u v ≤
      (secondLeviRaisingTarget Q β (u + 1) v).comap (Q.op 3 s) := by
  apply sup_le
  · by_cases hu : u = 0
    · rw [if_pos hu]
      exact bot_le
    · rw [if_neg hu]
      intro y hy
      rw [Submodule.mem_comap, secondLeviRaisingTarget, if_neg (Nat.add_one_ne_zero u),
        Nat.add_sub_cancel]
      apply Submodule.mem_sup_left
      have h := secondLeviCountLayer_middle Q β _ _ s hy
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hu)] at h
  · by_cases hv : v = 0
    · rw [if_pos hv]
      exact bot_le
    · rw [if_neg hv]
      intro y hy
      have h := secondLeviLastImage_middle Q β u (v - 1) s hy
      rw [Submodule.mem_comap, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hv)] at h
      rw [Submodule.mem_comap, secondLeviRaisingTarget, if_neg (Nat.add_one_ne_zero u),
        Nat.add_sub_cancel, if_neg hv]
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
      rw [← hab]
      exact Submodule.add_mem _ (Submodule.mem_sup_right ha) (Submodule.mem_sup_left hb)

/-- `q(s)` maps the `η`-target of `(u, v)` into that of `(u, v + 1)`. -/
theorem secondLeviRaisingTarget_compound (u v s : ℕ) :
    secondLeviRaisingTarget Q β u v ≤
      (secondLeviRaisingTarget Q β u (v + 1)).comap (Q.op 5 s) := by
  apply sup_le
  · by_cases hu : u = 0
    · rw [if_pos hu]
      exact bot_le
    · rw [if_neg hu]
      intro y hy
      rw [Submodule.mem_comap, secondLeviRaisingTarget, if_neg hu]
      exact Submodule.mem_sup_left (secondLeviCountLayer_compound Q β _ _ s hy)
  · by_cases hv : v = 0
    · rw [if_pos hv]
      exact bot_le
    · rw [if_neg hv]
      intro y hy
      rw [Submodule.mem_comap, secondLeviRaisingTarget, if_neg (Nat.add_one_ne_zero v),
        Nat.add_sub_cancel]
      apply Submodule.mem_sup_right
      have h := secondLeviLastImage_compound Q β u (v - 1) s hy
      rwa [Submodule.mem_comap, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hv)] at h

/-- `g(s)` maps the `E₁₃`-target of `(u, v)` into that of `(u + 1, v)`. -/
theorem secondLeviOuterRaisingTarget_middle (u v s : ℕ) :
    secondLeviOuterRaisingTarget Q β u v ≤
      (secondLeviOuterRaisingTarget Q β (u + 1) v).comap (Q.op 3 s) := by
  apply sup_le
  · by_cases hu : u = 0
    · rw [if_pos hu]
      exact bot_le
    · rw [if_neg hu]
      intro y hy
      rw [Submodule.mem_comap, secondLeviOuterRaisingTarget, if_neg (Nat.add_one_ne_zero u),
        Nat.add_sub_cancel]
      apply Submodule.mem_sup_left
      have h := secondLeviCountLayer_middle Q β _ _ s hy
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hu)] at h
  · by_cases hv : v = 0
    · rw [if_pos hv]
      exact bot_le
    · rw [if_neg hv]
      intro y hy
      rw [Submodule.mem_comap, secondLeviOuterRaisingTarget, if_neg hv]
      exact Submodule.mem_sup_right (secondLeviCountLayer_middle Q β _ _ s hy)

/-- `q(s)` maps the `E₁₃`-target of `(u, v)` into that of `(u, v + 1)`. -/
theorem secondLeviOuterRaisingTarget_compound (u v s : ℕ) :
    secondLeviOuterRaisingTarget Q β u v ≤
      (secondLeviOuterRaisingTarget Q β u (v + 1)).comap (Q.op 5 s) := by
  apply sup_le
  · by_cases hu : u = 0
    · rw [if_pos hu]
      exact bot_le
    · rw [if_neg hu]
      intro y hy
      rw [Submodule.mem_comap, secondLeviOuterRaisingTarget, if_neg hu]
      exact Submodule.mem_sup_left (secondLeviCountLayer_compound Q β _ _ s hy)
  · by_cases hv : v = 0
    · rw [if_pos hv]
      exact bot_le
    · rw [if_neg hv]
      intro y hy
      rw [Submodule.mem_comap, secondLeviOuterRaisingTarget, if_neg (Nat.add_one_ne_zero v),
        Nat.add_sub_cancel]
      apply Submodule.mem_sup_right
      have h := secondLeviCountLayer_compound Q β _ _ s hy
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hv)] at h

variable (hη : ∀ r φ, Q.op 0 r (β φ) = 0) (hη₂ : ∀ r φ, Q.op 2 r (β φ) = 0)
variable (he : ∀ r φ, Q.op 1 r (β φ) = 0)
variable (h₆ : ∀ t φ, ∃ φ', Q.op 6 t (β φ) = β φ') (h₇ : ∀ t φ, ∃ φ', Q.op 7 t (β φ) = β φ')

include hη h₆ in
/-- `η(r) S(u, v) ⊆ S(u - 1, v) + F S(u, v - 1)`. -/
theorem secondLeviCountLayer_raising_target (r u v : ℕ) :
    secondLeviCountLayer Q β u v ≤
      (secondLeviRaisingTarget Q β u v).comap (Q.op 0 r) := by
  have hle := secondLeviCountLayer_le_of_step Q β
    (fun u v => ⨅ r, (secondLeviRaisingTarget Q β u v).comap (Q.op 0 r))
    (fun φ => by
      rw [Submodule.mem_iInf]
      intro r
      rw [Submodule.mem_comap, hη]
      exact Submodule.zero_mem _)
    (fun u v s x hx hP => by
      simp only [Submodule.mem_iInf, Submodule.mem_comap] at hP ⊢
      intro r
      rw [leviRaising_middle_comm]
      have h1 : Q.op 3 s (Q.op 0 r x) ∈ secondLeviRaisingTarget Q β (u + 1) v :=
        secondLeviRaisingTarget_middle Q β u v s (hP r)
      refine Submodule.add_mem _ h1 ?_
      rw [secondLeviRaisingTarget, if_neg (Nat.add_one_ne_zero u), Nat.add_sub_cancel]
      exact Submodule.mem_sup_left
        (secondLeviCountLayer_cartan Q β 6 (Or.inl rfl) h₆ (r + s) u v hx))
    (fun u v s x hx hP => by
      simp only [Submodule.mem_iInf, Submodule.mem_comap] at hP ⊢
      intro r
      rw [leviRaising_compound_comm]
      have h1 : Q.op 5 s (Q.op 0 r x) ∈ secondLeviRaisingTarget Q β u (v + 1) :=
        secondLeviRaisingTarget_compound Q β u v s (hP r)
      refine Submodule.sub_mem _ h1 ?_
      rw [secondLeviRaisingTarget, if_neg (Nat.add_one_ne_zero v), Nat.add_sub_cancel]
      exact Submodule.mem_sup_right (secondLeviLastImage_mem Q β u v _ hx))
    u v
  intro x hx
  exact Submodule.mem_iInf _ |>.mp (hle hx) r

include hη₂ he h₆ h₇ in
/-- `E₁₃(r) S(u, v) ⊆ S(u - 1, v) + S(u, v - 1)`. -/
theorem secondLeviCountLayer_outerRaising_target (r u v : ℕ) :
    secondLeviCountLayer Q β u v ≤
      (secondLeviOuterRaisingTarget Q β u v).comap (Q.op 2 r) := by
  have hle := secondLeviCountLayer_le_of_step Q β
    (fun u v => ⨅ r, (secondLeviOuterRaisingTarget Q β u v).comap (Q.op 2 r))
    (fun φ => by
      rw [Submodule.mem_iInf]
      intro r
      rw [Submodule.mem_comap, hη₂]
      exact Submodule.zero_mem _)
    (fun u v s x hx hP => by
      simp only [Submodule.mem_iInf, Submodule.mem_comap] at hP ⊢
      intro r
      rw [leviOuterRaising_middle_comm]
      have h1 : Q.op 3 s (Q.op 2 r x) ∈ secondLeviOuterRaisingTarget Q β (u + 1) v :=
        secondLeviOuterRaisingTarget_middle Q β u v s (hP r)
      refine Submodule.sub_mem _ h1 ?_
      have h := secondLeviCountLayer_lastRaising Q β he (r + s) u v hx
      rw [Submodule.mem_comap] at h
      rw [secondLeviOuterRaisingTarget]
      apply Submodule.mem_sup_right
      by_cases hv : v = 0
      · rw [if_pos hv, Submodule.mem_bot] at h
        rw [h]
        exact Submodule.zero_mem _
      · rw [if_neg hv] at h ⊢
        exact h)
    (fun u v s x hx hP => by
      simp only [Submodule.mem_iInf, Submodule.mem_comap] at hP ⊢
      intro r
      rw [leviOuterRaising_compound_comm]
      have h1 : Q.op 5 s (Q.op 2 r x) ∈ secondLeviOuterRaisingTarget Q β u (v + 1) :=
        secondLeviOuterRaisingTarget_compound Q β u v s (hP r)
      refine Submodule.add_mem _ h1 ?_
      rw [secondLeviOuterRaisingTarget, if_neg (Nat.add_one_ne_zero v), Nat.add_sub_cancel]
      exact Submodule.mem_sup_right (Submodule.add_mem _
        (secondLeviCountLayer_cartan Q β 6 (Or.inl rfl) h₆ (r + s) u v hx)
        (secondLeviCountLayer_cartan Q β 7 (Or.inr rfl) h₇ (r + s) u v hx)))
    u v
  intro x hx
  exact Submodule.mem_iInf _ |>.mp (hle hx) r

/-- The vectors sent into a fixed subspace by every mode of `η` and of `E₁₃`. -/
def secondRaisingPreimage (C : Submodule ℂ W) : Submodule ℂ W :=
  ⨅ r : ℕ, C.comap (Q.op 0 r) ⊓ C.comap (Q.op 2 r)

/-- The final `gl₂` preserves the preimage of a `gl₂`-stable subspace under `η` and `E₁₃`. -/
theorem secondRaisingPreimage_finalLevi (C : Submodule ℂ W)
    (hC : ∀ a r, a2Levi a → C ≤ C.comap (Q.op a r)) (a : Fin 8) (t : ℕ) (ha : a2Levi a) :
    secondRaisingPreimage Q C ≤ (secondRaisingPreimage Q C).comap (Q.op a t) := by
  intro x hx
  simp only [secondRaisingPreimage, Submodule.mem_iInf, Submodule.mem_inf,
    Submodule.mem_comap] at hx ⊢
  have key (c : Fin 8) (hc : c = 0 ∨ c = 2) (r : ℕ) : Q.op c r (Q.op a t x) ∈ C := by
    have hcomm := Q.comm c a r t x
    rw [sub_eq_iff_eq_add] at hcomm
    rw [hcomm]
    apply C.add_mem
    · apply Submodule.sum_mem
      intro e _
      by_cases he : e = 0 ∨ e = 2
      · rcases he with rfl | rfl
        · exact C.smul_mem _ (hx (r + t)).1
        · exact C.smul_mem _ (hx (r + t)).2
      · rw [a2_positive_levi_bracket c a e (by rcases hc with rfl | rfl <;> simp [a2Positive])
          ha (by simpa [a2Positive] using he), zero_smul]
        exact C.zero_mem
    · rcases hc with rfl | rfl
      · exact hC a t ha (hx r).1
      · exact hC a t ha (hx r).2
  exact fun r => ⟨key 0 (Or.inl rfl) r, key 2 (Or.inr rfl) r⟩

include hη hη₂ he h₆ h₇ in
/-- **Lemma M(i).** `η(0)` sends `N(E + 1, e)` into `N(E, e)`. -/
theorem higherSecondLeviCountClosure_raising_le (E e : ℕ) :
    higherSecondLeviCountClosure Q β (E + 1) e ≤
      (higherSecondLeviCountClosure Q β E e).comap (Q.op 0 0) := by
  set C := higherSecondLeviCountClosure Q β E e with hC
  have hCinv : ∀ a r, a2Levi a → C ≤ C.comap (Q.op a r) :=
    fun a r ha => a2LeviClosure_inv Q _ a r ha
  have hle : higherSecondLeviCountClosure Q β (E + 1) e ≤ secondRaisingPreimage Q C := by
    apply a2LeviClosure_le_of_inv
    · apply iSup_le
      intro u
      apply iSup_le
      intro v
      apply iSup_le
      intro huv x hx
      simp only [secondRaisingPreimage, Submodule.mem_iInf, Submodule.mem_inf,
        Submodule.mem_comap]
      intro r
      have hu0 : u ≠ 0 := by omega
      constructor
      · have h := secondLeviCountLayer_raising_target Q β hη h₆ r u v hx
        rw [Submodule.mem_comap, secondLeviRaisingTarget, if_neg hu0] at h
        have hT : secondLeviCountLayer Q β (u - 1) v ⊔
            (if v = 0 then ⊥ else secondLeviLastImage Q β u (v - 1)) ≤ C := by
          apply sup_le
          · exact secondLeviCountLayer_le_higher Q β E e (u - 1) v (by omega) (by omega)
          · by_cases hv : v = 0
            · rw [if_pos hv]
              exact bot_le
            · rw [if_neg hv]
              apply iSup_le
              intro t
              rw [Submodule.map_le_iff_le_comap]
              exact (secondLeviCountLayer_le_higher Q β E e u (v - 1) (by omega)
                (by omega)).trans (hCinv 4 t (by simp [a2Levi]))
        exact hT h
      · have h := secondLeviCountLayer_outerRaising_target Q β hη₂ he h₆ h₇ r u v hx
        rw [Submodule.mem_comap, secondLeviOuterRaisingTarget, if_neg hu0] at h
        have hT : secondLeviCountLayer Q β (u - 1) v ⊔
            (if v = 0 then ⊥ else secondLeviCountLayer Q β u (v - 1)) ≤ C := by
          apply sup_le
          · exact secondLeviCountLayer_le_higher Q β E e (u - 1) v (by omega) (by omega)
          · by_cases hv : v = 0
            · rw [if_pos hv]
              exact bot_le
            · rw [if_neg hv]
              exact secondLeviCountLayer_le_higher Q β E e u (v - 1) (by omega) (by omega)
        exact hT h
    · intro a r ha
      exact secondRaisingPreimage_finalLevi Q C hCinv a r ha
  intro x hx
  have h := hle hx
  simp only [secondRaisingPreimage, Submodule.mem_iInf, Submodule.mem_inf,
    Submodule.mem_comap] at h
  exact (h 0).1

end Layers

/-! ### Lemma 6.4 and the descent -/

section Descent

variable {W : Type} [AddCommGroup W] [Module ℂ W]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable W)

/-- `η q^e β₁ = -e F q^(e-1) β₁` when `η` kills `β₁`. -/
theorem leviRaising_compoundPow (β₁ : W) (hη : Q.op 0 0 β₁ = 0) (e : ℕ) :
    Q.op 0 0 ((Q.op 5 0 ^ e) β₁) = -((e : ℂ) • Q.op 4 0 ((Q.op 5 0 ^ (e - 1)) β₁)) := by
  have hq := endomorphism_antiderivation_pow (Q.op 0 0) (Q.op 5 0) (Q.op 4 0)
    (fun u => by simpa using leviRaising_compound_comm Q 0 0 u)
    (fun u => (leviCompound_last_comm Q 0 0 u).symm) e β₁
  rw [hq, hη, map_zero, zero_sub, endomorphism_commute_pow (Q.op 4 0) (Q.op 5 0)
    (fun u => (leviCompound_last_comm Q 0 0 u).symm)]

/-- `h₂(0) q^e β₁ = (p - e) q^e β₁` when `h₂(0) β₁ = p β₁`. -/
theorem leviMiddleCartan_compoundPow (β₁ : W) (p : ℂ) (hw : Q.op 6 0 β₁ = p • β₁) (e : ℕ) :
    Q.op 6 0 ((Q.op 5 0 ^ e) β₁) = (p - e) • (Q.op 5 0 ^ e) β₁ := by
  induction e with
  | zero => simpa using hw
  | succ e ih =>
    have hc := (leviCartan_secondLowering_comm Q 0 0 ((Q.op 5 0 ^ e) β₁)).2.2.1
    rw [pow_succ', Module.End.mul_apply, hc, ih, map_smul, zero_add]
    push_cast
    module

/-- **Lemma 6.4.** If `η` kills `β₁` and `h₂(0) β₁ = p β₁`, then
`η(0) g^(E+1) q^e β₁ = (E + 1)(p - E) g^E q^e β₁ - e F(0) g^(E+1) q^(e-1) β₁`. -/
theorem raising_topWord (β₁ : W) (p : ℂ) (hη : Q.op 0 0 β₁ = 0) (hw : Q.op 6 0 β₁ = p • β₁)
    (E e : ℕ) :
    Q.op 0 0 ((Q.op 3 0 ^ (E + 1)) ((Q.op 5 0 ^ e) β₁)) =
      (((E + 1 : ℕ) : ℂ) * (p - E)) • (Q.op 3 0 ^ E) ((Q.op 5 0 ^ e) β₁) -
        (e : ℂ) • Q.op 4 0 ((Q.op 3 0 ^ (E + 1)) ((Q.op 5 0 ^ (e - 1)) β₁)) := by
  rw [leviRaising_middlePow, leviRaising_compoundPow Q β₁ hη,
    leviMiddleCartan_compoundPow Q β₁ p hw, map_neg, map_smul, map_smul]
  have hF := leviLast_middlePower_comm Q 0 E ((Q.op 5 0 ^ (e - 1)) β₁)
  have hgF : (Q.op 3 0 ^ (E + 1)) (Q.op 4 0 ((Q.op 5 0 ^ (e - 1)) β₁)) =
      Q.op 4 0 ((Q.op 3 0 ^ (E + 1)) ((Q.op 5 0 ^ (e - 1)) β₁)) -
        ((E + 1 : ℕ) : ℂ) • (Q.op 3 0 ^ E) (Q.op 5 0 ((Q.op 5 0 ^ (e - 1)) β₁)) := by
    rw [hF]
    abel
  rw [hgF]
  rcases e with _ | e
  · simp only [Nat.cast_zero, zero_smul, sub_zero, neg_zero, smul_sub]
    push_cast
    module
  · have hq : Q.op 5 0 ((Q.op 5 0 ^ (e + 1 - 1)) β₁) = (Q.op 5 0 ^ (e + 1)) β₁ := by
      rw [Nat.add_sub_cancel, pow_succ', Module.End.mul_apply]
    rw [hq]
    push_cast
    module

/-- **The descent in the first second-level count.** Let `T` commute with `η(0)` and preserve
every `N(E, e)`. If `T(g^p q^e β φ₀) ∈ N(p, e)`, then `T(g^E q^e β φ₀) ∈ N(E, e)` for all
`E ≤ p`. -/
theorem secondLevi_topWord_descent {R : Type} [CommRing R] [Algebra ℂ R] (β : R →ₗ[ℂ] W)
    (hη : ∀ r φ, Q.op 0 r (β φ) = 0) (hη₂ : ∀ r φ, Q.op 2 r (β φ) = 0)
    (he : ∀ r φ, Q.op 1 r (β φ) = 0)
    (h₆ : ∀ t φ, ∃ φ', Q.op 6 t (β φ) = β φ') (h₇ : ∀ t φ, ∃ φ', Q.op 7 t (β φ) = β φ')
    (φ₀ : R) (p : ℕ) (hw : Q.op 6 0 (β φ₀) = (p : ℂ) • β φ₀) (e : ℕ) (T : Module.End ℂ W)
    (hT : ∀ E, higherSecondLeviCountClosure Q β E e ≤
      (higherSecondLeviCountClosure Q β E e).comap T)
    (hTη : Commute T (Q.op 0 0))
    (htop : T ((Q.op 3 0 ^ p) ((Q.op 5 0 ^ e) (β φ₀))) ∈ higherSecondLeviCountClosure Q β p e) :
    ∀ E, E ≤ p → T ((Q.op 3 0 ^ E) ((Q.op 5 0 ^ e) (β φ₀))) ∈
      higherSecondLeviCountClosure Q β E e := by
  suffices h : ∀ k, k ≤ p → T ((Q.op 3 0 ^ (p - k)) ((Q.op 5 0 ^ e) (β φ₀))) ∈
      higherSecondLeviCountClosure Q β (p - k) e by
    intro E hE
    have := h (p - E) (by omega)
    rwa [Nat.sub_sub_self hE] at this
  intro k
  induction k with
  | zero => intro _; simpa using htop
  | succ k ih =>
    intro hk
    set E := p - (k + 1) with hE
    have hE1 : p - k = E + 1 := by omega
    have hprev := ih (by omega)
    rw [hE1] at hprev
    have hη0 := higherSecondLeviCountClosure_raising_le Q β hη hη₂ he h₆ h₇ E e hprev
    rw [Submodule.mem_comap, ← Module.End.mul_apply, ← hTη.eq, Module.End.mul_apply,
      raising_topWord Q (β φ₀) p (hη 0 φ₀) hw E e, map_sub, map_smul, map_smul] at hη0
    have hFmem : T (Q.op 4 0 ((Q.op 3 0 ^ (E + 1)) ((Q.op 5 0 ^ (e - 1)) (β φ₀)))) ∈
        higherSecondLeviCountClosure Q β E e ∨ e = 0 := by
      rcases Nat.eq_zero_or_pos e with he0 | hepos
      · exact Or.inr he0
      · left
        have hY : Q.op 4 0 ((Q.op 3 0 ^ (E + 1)) ((Q.op 5 0 ^ (e - 1)) (β φ₀))) ∈
            higherSecondLeviCountClosure Q β E e :=
          a2LeviClosure_inv Q _ 4 0 (by simp [a2Levi])
            (secondLeviCountLayer_le_higher Q β E e (E + 1) (e - 1) (by omega) (by omega)
              (zeroModeSecondWord_mem Q β φ₀ _ _))
        exact hT E hY
    have hsecond : (e : ℂ) • T (Q.op 4 0 ((Q.op 3 0 ^ (E + 1)) ((Q.op 5 0 ^ (e - 1)) (β φ₀)))) ∈
        higherSecondLeviCountClosure Q β E e := by
      rcases hFmem with h | h
      · exact Submodule.smul_mem _ _ h
      · rw [h, Nat.cast_zero, zero_smul]
        exact Submodule.zero_mem _
    have hfirst := Submodule.add_mem _ hη0 hsecond
    rw [sub_add_cancel] at hfirst
    have hc : (((E + 1 : ℕ) : ℂ) * ((p : ℂ) - E)) ≠ 0 := by
      apply mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero E)
      rw [sub_ne_zero]
      exact_mod_cast (show p ≠ E by omega)
    have hfin := Submodule.smul_mem _ (((E + 1 : ℕ) : ℂ) * ((p : ℂ) - E))⁻¹ hfirst
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hfin

end Descent

end

end VOA.DeligneAudit.SL4T
