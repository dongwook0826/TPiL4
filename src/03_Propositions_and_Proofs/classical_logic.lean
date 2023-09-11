open Classical

#check em -- excluded middle
example {p : Prop} : p ∨ ¬p :=
  em p

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

#check @byCases
example {p : Prop} (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

#check @byContradiction
example {p : Prop} (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
      show False from h h1)

theorem deMorgan (p q : Prop) (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  byCases
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hnp : ¬p =>
      Or.inl hnp)

