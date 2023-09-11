-- introduction rule
#check @Exists.intro

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_one -- or `zero_lt_succ 0`
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  -- Exists.intro y ⟨hxy, hyz⟩
  ⟨y, hxy, hyz⟩ -- anonymous constructor notation

variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true
#print gex1
#print gex2
#print gex3
#print gex4
set_option pp.explicit false

-- elimination rule
#check @Exists.elim

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
      fun hw : p w ∧ q w =>
      show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨n1, hn1⟩, ⟨n2, hn2⟩ => ⟨n1 + n2, by rw [hn1, hn2, Nat.mul_add]⟩

-- classical "exists"
open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h1' : ∀ x, ¬ p x :=
        fun x =>
        fun hpx : p x =>
        have hepx : ∃ x, p x := ⟨x, hpx⟩
        show False from h1 hepx
      show False from h h1')

