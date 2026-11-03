import VOA.DeligneAudit.D4LeviKSMixedActiveList

/-! The maximal-active Rx and Ry target generators lie in the PAIR kernel. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rxMixedSeed_evaluation_list
    (ρ : CurrentModule D4sector.f V) (w : V) (a b c s : ℕ) :
    xyzEvaluation ρ w (pairSourceShape a b c) (rxMixedSeed a b c s) =
      ((yOp ρ 0) ^ b)
        (xyzEvaluation ρ w
          (List.replicate c (5 : Fin 6) ++
            List.replicate (a + b) (1 : Fin 6)).get
          (hsymm (Fin (List.replicate c (5 : Fin 6) ++
            List.replicate (a + b) (1 : Fin 6)).length) ℂ s)) := by
  rw [rxMixedSeed_evaluation]
  have he := xyzEvaluation_rename_bijection ρ w
    (fun t : Fin c ⊕ (Fin b ⊕ Fin a) =>
      match t with
      | Sum.inl _ => (5 : Fin 6)
      | Sum.inr _ => 1)
    (rxActiveIndex a b c) (hsymm (Fin (c + (a + b))) ℂ s)
  rw [rename_hsymm] at he
  have hs := congrArg
    (fun shape : Fin (c + (a + b)) → Fin 6 =>
      xyzEvaluation ρ w shape (hsymm (Fin (c + (a + b))) ℂ s))
    (rxActiveIndex_shape a b c)
  have he' := he.trans hs
  apply congrArg (((yOp ρ 0) ^ b) ·)
  have hget :
      (fun i : Fin (c + (a + b)) =>
        (List.replicate c (5 : Fin 6) ++
          List.replicate (a + b) (1 : Fin 6))[i.val]'(by
            simpa using i.isLt)) =
      (fun i : Fin (c + (a + b)) =>
        (List.replicate c (5 : Fin 6) ++
          List.replicate (a + b) (1 : Fin 6)).get
            ⟨i.val, by simpa using i.isLt⟩) := by
    funext i
    rfl
  rw [hget] at he'
  let cs := List.replicate c (5 : Fin 6) ++
    List.replicate (a + b) (1 : Fin 6)
  let eLen : Fin (c + (a + b)) ≃ Fin cs.length :=
    finCongr (by simp [cs])
  have hshape :
      (fun i : Fin (c + (a + b)) => cs.get
        ⟨i.val, by simpa [cs] using i.isLt⟩) = cs.get ∘ eLen := by
    funext i
    rfl
  rw [show (fun i : Fin (c + (a + b)) =>
      (List.replicate c (5 : Fin 6) ++
        List.replicate (a + b) (1 : Fin 6)).get
          ⟨i.val, by simpa using i.isLt⟩) = cs.get ∘ eLen from hshape] at he'
  have hr := xyzEvaluation_rename_bijection ρ w cs.get eLen
    (hsymm (Fin (c + (a + b))) ℂ s)
  rw [rename_hsymm] at hr
  exact he'.trans hr.symm

theorem ryMixedSeed_evaluation_list
    (ρ : CurrentModule D4sector.f V) (w : V) (a b c s : ℕ) :
    xyzEvaluation ρ w (pairSourceShape a b c) (ryMixedSeed a b c s) =
      ((xOp ρ 0) ^ (a + b))
        (xyzEvaluation ρ w
          (List.replicate c (5 : Fin 6) ++
            List.replicate b (4 : Fin 6)).get
          (hsymm (Fin (List.replicate c (5 : Fin 6) ++
            List.replicate b (4 : Fin 6)).length) ℂ s)) := by
  rw [ryMixedSeed_evaluation]
  have he := xyzEvaluation_rename_bijection ρ w
    (fun t : Fin c ⊕ Fin b =>
      match t with
      | Sum.inl _ => (5 : Fin 6)
      | Sum.inr _ => 4)
    (ryActiveIndex b c) (hsymm (Fin (c + b)) ℂ s)
  rw [rename_hsymm] at he
  have hs := congrArg
    (fun shape : Fin (c + b) → Fin 6 =>
      xyzEvaluation ρ w shape (hsymm (Fin (c + b)) ℂ s))
    (ryActiveIndex_shape b c)
  have he' := he.trans hs
  apply congrArg (((xOp ρ 0) ^ (a + b)) ·)
  have hget :
      (fun i : Fin (c + b) =>
        (List.replicate c (5 : Fin 6) ++
          List.replicate b (4 : Fin 6))[i.val]'(by
            simpa using i.isLt)) =
      (fun i : Fin (c + b) =>
        (List.replicate c (5 : Fin 6) ++
          List.replicate b (4 : Fin 6)).get
            ⟨i.val, by simpa using i.isLt⟩) := by
    funext i
    rfl
  rw [hget] at he'
  let cs := List.replicate c (5 : Fin 6) ++
    List.replicate b (4 : Fin 6)
  let eLen : Fin (c + b) ≃ Fin cs.length :=
    finCongr (by simp [cs])
  have hshape :
      (fun i : Fin (c + b) => cs.get
        ⟨i.val, by simpa [cs] using i.isLt⟩) = cs.get ∘ eLen := by
    funext i
    rfl
  rw [show (fun i : Fin (c + b) =>
      (List.replicate c (5 : Fin 6) ++
        List.replicate b (4 : Fin 6)).get
          ⟨i.val, by simpa using i.isLt⟩) = cs.get ∘ eLen from hshape] at he'
  have hr := xyzEvaluation_rename_bijection ρ w cs.get eLen
    (hsymm (Fin (c + b)) ℂ s)
  rw [rename_hsymm] at hr
  exact he'.trans hr.symm

theorem rx_gen_maximal_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ a + b) (hks : m + 1 ≤ c + a + b + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c s) :
    rxMixedTarget a b c s ∈
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c s h hi hkey)).ker := by
  apply rxMixedTarget_mem_ker_of_evaluation ρ w m i a b c s h hi hkey
  rw [rxMixedSeed_evaluation_list]
  exact rx_zero_hsymm_prefix ρ w m i a b c s h hK hks hi hkey

theorem ry_gen_maximal_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ b) (hks : m + 1 ≤ c + b + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c s) :
    ryMixedTarget a b c s ∈
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c s h hi hkey)).ker := by
  apply ryMixedTarget_mem_ker_of_evaluation ρ w m i a b c s h hi hkey
  rw [ryMixedSeed_evaluation_list]
  exact ry_zero_hsymm_prefix ρ w m i a b c s h hK hks hi hkey

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rxMixedSeed_evaluation_list
#print axioms VOA.DeligneAudit.D4Levi.ryMixedSeed_evaluation_list
#print axioms VOA.DeligneAudit.D4Levi.rx_gen_maximal_mem_ker
#print axioms VOA.DeligneAudit.D4Levi.ry_gen_maximal_mem_ker
