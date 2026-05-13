-- def greeting := "Hello, world!"

-- #check greeting
-- #eval greeting

-- #check Nat
-- #check Nat -> String

-- def x: Nat := 42
-- def y: Int := 42

-- #eval x - 52
-- #eval y - 52

-- theorem foo : 1 + 1 = 2 := rfl

-- Tiny commutativity proof at the Prop level — pulls in only `And`, not Nat.
theorem my_and_comm (p q : Prop) (h : p ∧ q) : q ∧ p :=
  ⟨h.2, h.1⟩

--- not_not_not_a_imp_not_a_lean
theorem thm1 : ¬¬¬A → ¬A := fun a b ↦ a (· b)

-- identical proof to zkPi paper (so we can benchmark by comparing on this theorem)
theorem and_comm_custom (a b : Prop) : a ∧ b ↔ b ∧ a :=
  Iff.intro (And.symm) (And.symm)

theorem nat_zero_add_comm (n : Nat) : n + 0 = 0 + n := by simp

theorem add_comm_nat (n m : Nat) : n + m = m + n := Nat.add_comm n m
