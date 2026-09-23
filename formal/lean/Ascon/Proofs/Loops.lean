import Ascon.Model.Runtime

/-! # Reasoning principles for the modelled OCaml loops -/

namespace Ascon.Model

theorem forUp_unfold (lo hi : Int) (s : σ) (body : Int → σ → M σ) :
    forUp lo hi s body =
      if lo ≤ hi then (body lo s >>= fun s => forUp (lo + 1) hi s body) else pure s := by
  rw [forUp]

/-- An empty `for` loop. -/
theorem forUp_empty (lo hi : Int) (h : hi < lo) (s : σ) (body : Int → σ → M σ) :
    forUp lo hi s body = pure s := by
  rw [forUp_unfold]; simp [show ¬ lo ≤ hi by omega]

/-- Invariant rule for `for i = lo to hi`: `P i s` describes the state before
iteration `i`. If every iteration succeeds and preserves `P`, the loop succeeds
and `P (hi + 1)` holds at the end. -/
theorem forUp_invariant (lo hi : Int) (hle : lo ≤ hi + 1) (s : σ)
    (body : Int → σ → M σ) (P : Int → σ → Prop) (h0 : P lo s)
    (hstep : ∀ i s, lo ≤ i → i ≤ hi → P i s → ∃ s', body i s = .ok s' ∧ P (i + 1) s') :
    ∃ s', forUp lo hi s body = .ok s' ∧ P (hi + 1) s' := by
  suffices H : ∀ (n : Nat) (i : Int) (s : σ), hi + 1 - i = n → lo ≤ i → P i s →
      ∃ s', forUp i hi s body = .ok s' ∧ P (hi + 1) s' from
    H (hi + 1 - lo).toNat lo s (by omega) (Int.le_refl _) h0
  intro n
  induction n with
  | zero =>
    intro i s hn _ hp
    refine ⟨s, forUp_empty i hi (by omega) s body, ?_⟩
    rwa [show hi + 1 = i by omega]
  | succ n ih =>
    intro i s hn hlo hp
    obtain ⟨s1, hs1, hp1⟩ := hstep i s hlo (by omega) hp
    obtain ⟨s', hs', hp'⟩ := ih (i + 1) s1 (by omega) (by omega) hp1
    refine ⟨s', ?_, hp'⟩
    rw [forUp_unfold]
    simp only [show i ≤ hi by omega, ↓reduceIte, hs1, bind, Except.bind]
    exact hs'

/-- A loop whose body is a pure function is a left fold over `lo … hi`. -/
theorem forUp_pure (n : Nat) (lo hi : Int) (h : hi + 1 - lo = n) (s : σ)
    (f : Int → σ → σ) :
    forUp lo hi s (fun i s => pure (f i s)) =
      pure ((List.range n).foldl (fun s (k : Nat) => f (lo + (k : Int)) s) s) := by
  induction n generalizing lo s with
  | zero => rw [forUp_empty lo hi (by omega)]; rfl
  | succ n ih =>
    rw [forUp_unfold, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    simp only [show lo ≤ hi by omega, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rw [show (pure : σ → M σ) = Except.ok from rfl] at ih
    rw [ih (lo + 1) (by omega)]
    congr 2
    · funext s k; congr 1; push_cast; omega
    · simp

/-- Reduce `x >>= f` once `x` is known to succeed. Rewriting with this lemma,
instead of unfolding `bind`, keeps the kernel from choosing to evaluate the
permutation while it checks the resulting definitional equality. -/
theorem bind_of_ok {α β : Type} {x : M α} {a : α} (hx : x = .ok a) (f : α → M β) :
    (x >>= f) = f a := by rw [hx]; rfl

/-- `Except.ok a >>= f = f a`, as a propositional rewrite rule. Its proof is
deliberately not `rfl`, so `simp` records the rewrite in the proof term. The
kernel then never has to rediscover the equation by unfolding `f a`, which
may mean evaluating a permutation. -/
theorem ok_bind {α β : Type} (a : α) (f : α → M β) : (Except.ok a >>= f) = f a := by
  cases h : f a <;> exact h

end Ascon.Model
