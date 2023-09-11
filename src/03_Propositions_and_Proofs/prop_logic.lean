variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

section conjunction
  #check @And.intro
  #check @And.left
  #check @And.right

  variable (p q : Prop)
  example (hp : p) (hq : q) : p ∧ q :=
    And.intro hp hq
  -- stating a theorem without naming it
  example (h : p ∧ q) : p := And.left h
  example (h : p ∧ q) : q := And.right h
  example (h : p ∧ q) : q ∧ p :=
    And.intro (And.right h) (And.left h)
  
  -- we can write as...
  variable (hp : p) (hq : q)
  #check (⟨hp, hq⟩ : p ∧ q)

  example (h : p ∧ q) : q ∧ p :=
    ⟨h.right, h.left⟩
end conjunction

section disjunction
  #check @Or.elim
  #check @Or.intro_left
  #check @Or.intro_right
  #check @Or.inl
  #check @Or.inr

  variable (p q r : Prop)

  example (h : p ∨ q) : q ∨ p :=
    Or.elim h
      (fun hp : p =>
        show q ∨ p from Or.intro_right q hp)
      (fun hq : q =>
        show q ∨ p from Or.intro_left p hq)
  
  example (h : p ∨ q) : q ∨ p :=
    Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
end disjunction

section negation_falsity
  #check @False.elim
  #check @absurd

  variable (p q r : Prop)
  
  example (hpq : p → q) (hnq : ¬q) : ¬p :=
    fun hp : p =>
    show False from hnq (hpq hp)

  example (hp : p) (hnp : ¬p) : q :=
    False.elim (hnp hp)
  -- same as...
  example (hp : p) (hnp : ¬p) : q :=
    absurd hp hnp

  example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    absurd (hqp hq) hnp

  #check True.intro -- a canonical proof for `True`
end negation_falsity

section equivalence
  #check @Iff.intro
  #check @Iff.mp
  #check @Iff.mpr

  variable (p q : Prop)

  theorem and_swap : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun h : p ∧ q =>
        show q ∧ p from And.intro h.right h.left) 
      (fun h : q ∧ p =>
        show p ∧ q from And.intro h.right h.left)
    
  #check and_swap p q

  variable (h : p ∧ q)
  example : q ∧ p := Iff.mp (and_swap p q) h

  theorem and_swap' : p ∧ q ↔ q ∧ p :=
    ⟨fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩
  
  example : q ∧ p := (and_swap p q).mp h
end equivalence
