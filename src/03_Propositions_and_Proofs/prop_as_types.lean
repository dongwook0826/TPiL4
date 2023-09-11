#check And
#check Or
#check Not

#check Prop

section
  variable {p : Prop}
  variable {q : Prop}

  theorem t1 : p → q → p :=
    fun hp : p =>
    fun hq : q =>
    show p from hp -- 그냥 `hp`만 쓰는 것과 동일
  -- keyword `theorem` is just a version of `def`
  #print t1

  theorem t1' (hp : p) (hq : q) : p := hp
  #print t1'

  theorem t1'' {p q : Prop} (hp : p) (hq : q) : p := hp
  #print t1''

  theorem t1''' : ∀ {p q : Prop}, p → q → p :=
    fun {p q : Prop} (hp : p) (hq : q) => hp 
  #print t1'''

  axiom hp : p

  theorem t2 : q → p := t1 hp
  #print t2
end

namespace unsound
  axiom unsound : False
  -- Everything follows from false
  theorem ex : 1 = 0 :=
    False.elim unsound
end unsound

