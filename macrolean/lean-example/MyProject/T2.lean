-- theorem zero_add (n : Nat) : 0 + n = n := by
--   induction n with
--   | zero => rfl
--   | succ n ih => simp [Nat.add_succ, ih]

theorem zero_add : ∀ n : Nat, 0 + n = n
  | .zero => rfl
  | .succ n => congrArg Nat.succ (zero_add n)
