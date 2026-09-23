import Ascon.Spec.Permutation
import Ascon.Model.Permutation
import Ascon.Proofs.Loops
import Std.Tactic.BVDecide

/-!
# `permutation.ml` implements `Ascon-p[rnd]`

Main result: `rounds_correct`. For every round count `1 ≤ n ≤ 12`, the model of
`Permutation.rounds` terminates without a fault and returns `Ascon-p[n]` as
specified with the S-box table.
-/

namespace Ascon.Model

/-- The specification state denoted by an implementation state. -/
def State.toSpec (s : State) : Spec.State := ⟨s.x0, s.x1, s.x2, s.x3, s.x4⟩

def State.ofSpec (S : Spec.State) : State := ⟨S.s0, S.s1, S.s2, S.s3, S.s4⟩

@[simp] theorem State.toSpec_ofSpec (S : Spec.State) : (State.ofSpec S).toSpec = S := rfl
@[simp] theorem State.ofSpec_toSpec (s : State) : State.ofSpec s.toSpec = s := rfl

namespace Permutation

theorem ror_ok (x : Word) (n : Int) (h0 : 0 < n) (h1 : n < 64) :
    ror x n = .ok (x.rotateRight n.toNat) := by
  have e1 : (0 : Int) ≤ n ∧ n < 64 := by omega
  have e2 : (0 : Int) ≤ 64 - n ∧ (64 : Int) - n < 64 := by omega
  simp only [ror, Int64.shiftRightLogical, Int64.shiftLeft, e1, e2, and_self, ↓reduceIte, bind,
    Except.bind, pure, Except.pure]
  rw [BitVec.rotateRight, Nat.mod_eq_of_lt (by omega), BitVec.rotateRightAux]
  congr 3
  omega

/-- One modelled round is one specification round `p_L ∘ p_S ∘ p_C`. -/
theorem round_ok (s : State) (c : Word) :
    round s c = .ok (State.ofSpec (Spec.round c s.toSpec)) := by
  simp only [round, ror_ok _ 19 (by decide) (by decide), ror_ok _ 28 (by decide) (by decide),
    ror_ok _ 61 (by decide) (by decide), ror_ok _ 39 (by decide) (by decide),
    ror_ok _ 1 (by decide) (by decide), ror_ok _ 6 (by decide) (by decide),
    ror_ok _ 10 (by decide) (by decide), ror_ok _ 17 (by decide) (by decide),
    ror_ok _ 7 (by decide) (by decide), ror_ok _ 41 (by decide) (by decide),
    bind, Except.bind, pure, Except.pure]
  simp only [Spec.round, Spec.pS_eq_pSBitsliced, Spec.pSBitsliced, Spec.pL, Spec.pC,
    State.ofSpec, State.toSpec, Int.reduceToNat]
  congr 1
  simp only [State.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

theorem constant_ok_nat (k : Nat) (h : k < 12) :
    constant k = .ok (Spec.roundConstant (k + 4)) := by
  have hk : (0 : Int) ≤ k ∧ (k : Int) < roundConstants.size :=
    ⟨by omega, by simp [roundConstants]; omega⟩
  simp only [constant, hk.1, hk.2, and_self, ↓reduceDIte, Int.toNat_natCast, pure,
    Except.pure, Except.ok.injEq]
  have table : ∀ k (h : k < 12),
      roundConstants[k]'(by simp [roundConstants]; omega) = Spec.roundConstant (k + 4) := by
    decide
  exact table k h

theorem constant_ok (i : Int) (h0 : 0 ≤ i) (h1 : i < 12) :
    constant i = .ok (Spec.roundConstant (i.toNat + 4)) := by
  have := constant_ok_nat i.toNat (by omega)
  rwa [Int.toNat_of_nonneg h0] at this

/-- `Permutation.rounds s n` computes `Ascon-p[n]` for `1 ≤ n ≤ 12`. -/
theorem rounds_correct (s : State) (n : Nat) (h1 : 1 ≤ n) (h12 : n ≤ 12) :
    rounds s n = .ok (State.ofSpec (Spec.asconP n s.toSpec)) := by
  simp only [rounds, show ¬ ((n : Int) < 1 ∨ (n : Int) > 12) by omega, ↓reduceIte]
  have hbody : ∀ i s, (0 ≤ i ∧ i < 12) →
      (do round s (← constant i) : M State) =
        pure (State.ofSpec (Spec.round (Spec.roundConstant (i.toNat + 4)) s.toSpec)) := by
    intro i s hi
    rw [constant_ok i hi.1 hi.2]
    simp only [bind, Except.bind, round_ok]; rfl
  -- Replace the body by a pure function on the loop range.
  have hloop : forUp (12 - (n : Int)) 11 s (fun i s => do round s (← constant i)) =
      forUp (12 - (n : Int)) 11 s (fun i s =>
        if 0 ≤ i ∧ i < 12 then
          pure (State.ofSpec (Spec.round (Spec.roundConstant (i.toNat + 4)) s.toSpec))
        else (do round s (← constant i))) := by
    have key : ∀ (m : Nat) (lo : Int) (s : State), 11 + 1 - lo = m → 0 ≤ lo →
        forUp lo 11 s (fun i s => do round s (← constant i)) =
        forUp lo 11 s (fun i s =>
          if 0 ≤ i ∧ i < 12 then
            pure (State.ofSpec (Spec.round (Spec.roundConstant (i.toNat + 4)) s.toSpec))
          else (do round s (← constant i))) := by
      intro m
      induction m with
      | zero => intro lo s hm _; rw [forUp_empty _ _ (by omega), forUp_empty _ _ (by omega)]
      | succ m ih =>
        intro lo s hm hlo
        rw [forUp_unfold, forUp_unfold]
        simp only [show lo ≤ 11 by omega, ↓reduceIte, show 0 ≤ lo ∧ lo < 12 by omega]
        rw [hbody lo s ⟨by omega, by omega⟩]
        simp only [bind, Except.bind, pure, Except.pure]
        exact ih (lo + 1) _ (by omega) (by omega)
    exact key n _ s (by omega) (by omega)
  rw [hloop]
  -- On the loop range the condition always holds, so the body is pure.
  have hpure : ∀ (m : Nat) (lo : Int) (s : State), 11 + 1 - lo = m → 0 ≤ lo →
      forUp lo 11 s (fun i s =>
          if 0 ≤ i ∧ i < 12 then
            pure (State.ofSpec (Spec.round (Spec.roundConstant (i.toNat + 4)) s.toSpec))
          else (do round s (← constant i))) =
        forUp lo 11 s (fun i s =>
          pure (State.ofSpec (Spec.round (Spec.roundConstant (i.toNat + 4)) s.toSpec))) := by
    intro m
    induction m with
    | zero => intro lo s hm _; rw [forUp_empty _ _ (by omega), forUp_empty _ _ (by omega)]
    | succ m ih =>
      intro lo s hm hlo
      rw [forUp_unfold, forUp_unfold]
      simp only [show lo ≤ 11 by omega, ↓reduceIte, show 0 ≤ lo ∧ lo < 12 by omega]
      simp only [bind, Except.bind, pure, Except.pure]
      exact ih (lo + 1) _ (by omega) (by omega)
  rw [hpure n _ s (by omega) (by omega), forUp_pure n _ _ (by omega)]
  simp only [pure, Except.pure, Except.ok.injEq]
  -- Both sides are folds over `List.range n` with matching constants.
  unfold Spec.asconP
  suffices H : ∀ (l : List Nat) (s : State), (∀ k ∈ l, k < n) →
      l.foldl (fun s (k : Nat) => State.ofSpec
          (Spec.round (Spec.roundConstant ((12 - (n : Int) + (k : Int)).toNat + 4)) s.toSpec)) s =
        State.ofSpec (l.foldl (fun S i => Spec.round (Spec.roundConstant (16 - n + i)) S)
          s.toSpec) by
    exact H (List.range n) s (fun k hk => List.mem_range.mp hk)
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons k l ih =>
    intro s hl
    simp only [List.foldl_cons]
    rw [ih _ (fun k hk => hl k (List.mem_cons_of_mem _ hk))]
    have hk := hl k List.mem_cons_self
    simp only [State.toSpec_ofSpec]
    rw [show (12 - (n : Int) + (k : Int)).toNat + 4 = 16 - n + k by omega]

theorem p12_correct (s : State) : p12 s = .ok (State.ofSpec (Spec.asconP 12 s.toSpec)) :=
  rounds_correct s 12 (by decide) (by decide)

theorem p8_correct (s : State) : p8 s = .ok (State.ofSpec (Spec.asconP 8 s.toSpec)) :=
  rounds_correct s 8 (by decide) (by decide)

/-- Invalid round counts raise `Invalid_argument` and are never executed. -/
theorem rounds_invalid (s : State) (n : Int) (h : n < 1 ∨ n > 12) :
    rounds s n = .error (.invalidArgument "Ascon permutation round count") := by
  simp [rounds, h, invalidArg, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

end Permutation
end Ascon.Model
