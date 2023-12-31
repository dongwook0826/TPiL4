variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e :=
  calc
    a = b       := h1
    _ = c + 1   := h2
    _ = d + 1   := congrArg Nat.succ h3
    _ = 1 + d   := Nat.add_comm d 1
    _ = e       := Eq.symm h4

theorem T' : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]