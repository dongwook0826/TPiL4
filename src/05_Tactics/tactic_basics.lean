theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

#print test -- this prints the resulting proof

def id' {α : Type} : α → α := by
  intro a; exact a

#print id'

example : 2 + 3 = 5 := by
  rfl -- ...WUT

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption
  -- repeat assumption이 어째 잘 안 먹힌다...버근가?

