-- #1
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h : ∀ x, p x ∧ q x =>
      ⟨fun x => (h x).left, fun x => (h x).right⟩)
    (fun h : (∀ x, p x) ∧ (∀ x, q x) =>
      fun x => ⟨h.left x, h.right x⟩)
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hxpq : ∀ x, p x → q x =>
    fun hxp : ∀ x, p x =>
      fun x => hxpq x (hxp x)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
    fun x =>
      h.elim
        (fun hxp : ∀ x, p x => Or.inl (hxp x))
        (fun hxq : ∀ x, q x => Or.inr (hxq x))

-- #2
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun x : α =>
    Iff.intro
      (fun hxr : ∀ x : α, r => hxr x)
      (fun hr => fun _ => hr)
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  -- one direction proof requires classical logic
  Iff.intro
    (fun h : ∀ x, p x ∨ r =>
      Classical.byCases
        (fun hr : r => Or.inr hr)
        (fun hnr : ¬r =>
          Or.inl
            (fun x =>
              (h x).elim
                id
                (fun hr : r =>
                  absurd hr hnr))))
    (fun h : (∀ x, p x) ∨ r =>
      fun x =>
        h.elim
          (fun hxp : ∀ x, p x => Or.inl (hxp x))
          (fun hr => Or.inr hr))
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h : ∀ x, r → p x =>
      fun hr : r =>
        fun x => h x hr)
    (fun h : r → ∀ x, p x =>
      fun x =>
        fun hr : r => h hr x)

-- #3
variable (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have hb : shaves barber barber ↔ ¬ shaves barber barber := h barber 
  have hnsbb : ¬ shaves barber barber :=
    fun hsbb : shaves barber barber => hb.mp hsbb hsbb
  have hsbb : shaves barber barber := hb.mpr hnsbb
  show False from hnsbb hsbb

-- #4
def even (n : Nat) : Prop :=
  ∃ m : Nat, n = 2 * m

def prime (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ m : Nat, 1 ≤ m ∧ m < n → n % m ≠ 0

def prime_alt (n : Nat) : Prop :=
  ¬ ∃ a b : Nat, a < n ∧ b < n ∧ a * b = n

def infinitely_many_primes : Prop :=
  ∀ n : Nat, ∃ p : Nat, n ≤ p ∧ prime p

def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃ m : Nat, n = 2 ^ 2 ^ m + 1

def infinitely_many_Fermat_primes : Prop :=
  ∀ n : Nat, ∃ p : Nat, n ≤ p ∧ Fermat_prime p

def goldbach_conjecture : Prop :=
  ∀ n : Nat, 4 ≤ n ∧ even n → ∃ p q : Nat, prime p ∧ prime q ∧ n = p + q

def Goldbach's_weak_conjecture : Prop :=
  ∀ n : Nat, 7 ≤ n ∧ ¬ even n → ∃ p q r : Nat, prime p ∧ prime q ∧ prime r ∧ n = p + q + r

def Fermat's_last_theorem : Prop :=
  ¬ ∃ a b c n : Nat, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ n ≥ 3 ∧ a ^ n + b ^ n = c ^ n

-- #5
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun ⟨_, hr⟩ => hr
example (a : α) : r → (∃ x : α, r) :=
  fun hr : r => ⟨a, hr⟩
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun h : ∃ x, p x ∧ r =>
      match h with
      | ⟨w, hpw, hr⟩ => ⟨⟨w, hpw⟩, hr⟩)
    (fun h : (∃ x, p x) ∧ r =>
      match h with
      | ⟨⟨w, hpw⟩, hr⟩ => ⟨w, hpw, hr⟩)
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨w, hpqw⟩ =>
      Or.elim hpqw
        (fun hpw => Or.inl ⟨w, hpw⟩)
        (fun hqw => Or.inr ⟨w, hqw⟩))
    (fun h =>
      Or.elim h
        (fun ⟨w, hpw⟩ => ⟨w, Or.inl hpw⟩)
        (fun ⟨w, hqw⟩ => ⟨w, Or.inr hqw⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h : ∀ x, p x =>
      fun ⟨w, hnpw⟩ => hnpw (h w))
    (fun h : ¬ (∃ x, ¬ p x) =>
      fun x =>
        Classical.byContradiction
          (fun hnpx : ¬ p x =>
            h ⟨x, hnpx⟩))
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun ⟨w, hpw⟩ =>
      fun h : ∀ x, ¬ p x => (h w) hpw)
    (fun h : ¬ (∀ x, ¬ p x) =>
      Classical.byContradiction
        (fun hnep : ¬ (∃ x, p x) =>
          have : ∀ x, ¬ p x :=
            fun x => fun hpx : p x => hnep ⟨x, hpx⟩
          h this))
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun hnep : ¬ ∃ x, p x =>
      fun x => fun hpx : p x => hnep ⟨x, hpx⟩)
    (fun hanp : ∀ x, ¬ p x =>
      fun ⟨w, hpw⟩ => (hanp w) hpw)
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun hnap : ¬ ∀ x, p x =>
      Classical.byContradiction
        (fun hnenp : ¬ ∃ x, ¬ p x =>
          have : ∀ x, p x :=
            fun x =>
              Classical.byContradiction
                (fun hnpx : ¬ p x =>
                  hnenp ⟨x, hnpx⟩)
          hnap this))
    (fun ⟨w, hnpw⟩ =>
      fun hap : ∀ x, p x =>
        hnpw (hap w))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun hapr : ∀ x, p x → r =>
      fun ⟨w, hpw⟩ =>
        hapr w hpw)
    (fun hepr : (∃ x, p x) → r =>
      fun x => fun hpx : p x =>
        hepr ⟨x, hpx⟩)
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨w, hpwr⟩ =>
      fun hapx : ∀ x, p x =>
        hpwr (hapx w))
    (fun hapr : (∀ x, p x) → r =>
      Classical.byCases
        (fun hap : ∀ x, p x =>
          ⟨a, fun _ => hapr hap⟩)
        (fun hnap : ¬ ∀ x, p x =>
          have henp : ∃ x, ¬ p x :=
            Classical.byContradiction
              (fun hnenp : ¬ ∃ x, ¬ p x =>
                have : ∀ x, p x :=
                  fun x =>
                    Classical.byContradiction
                      (fun hnpx : ¬ p x =>
                        hnenp ⟨x, hnpx⟩)
                hnap this)
          have ⟨w, hnpw⟩ := henp
          ⟨w, fun hpw => absurd hpw hnpw⟩))
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨w, hrpw⟩ => fun r =>
      ⟨w, hrpw r⟩)
    (fun hrep : r → ∃ x, p x =>
      Classical.byCases
        (fun hr : r =>
          have ⟨w, hpw⟩ := hrep hr
          ⟨w, fun _ => hpw⟩)
        (fun hnr : ¬ r =>
          ⟨a, fun hr => absurd hr hnr⟩))
