-- #1
---- maybe later...

-- #2
theorem logic_complex (p q r : Prop) (hp : p) :
        (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor <;> (try apply And.intro) <;> -- unpile the and-chain
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption) -- reduce each or-chain

#print logic_complex

