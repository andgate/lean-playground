inductive Expr where
  | lit : Nat -> Expr
  | add : Expr -> Expr -> Expr
  | mul : Expr -> Expr -> Expr


def eval : Expr -> Nat
  | .lit n => n
  | .add x y => eval x + eval y
  | .mul x y => eval x * eval y

#eval eval (.mul (.add (.lit 2) (.lit 3)) (.lit 4))


def foldAdd (a b : Expr) : Expr :=
  match a, b with
  | .lit n, .lit m => .lit (n + m)
  | a', b' => .add a' b'

def foldMul (a b : Expr) : Expr :=
  match a, b with
  | .lit n, .lit m => .lit (n * m)
  | a', b' => .mul a' b'

def foldConstants : Expr → Expr
  | .lit n => .lit n
  | .add x y =>
      foldAdd (foldConstants x) (foldConstants y)
  | .mul x y =>
      foldMul (foldConstants x) (foldConstants y)

#eval foldConstants
  (.mul (.add (.lit 2) (.lit 3)) (.lit 4))


def rebuild : Expr → Expr
  | .lit n => .lit n
  | .add x y => .add (rebuild x) (rebuild y)
  | .mul x y => .mul (rebuild x) (rebuild y)

theorem rebuild_id (e : Expr) :
    rebuild e = e := by
  induction e with
  | lit n =>
      rfl
  | add x y ihx ihy =>
      simp [rebuild, ihx, ihy]
  | mul x y ihx ihy =>
      simp [rebuild, ihx, ihy]

theorem rebuild_correct (e : Expr) :
    eval (rebuild e) = eval e := by
  rw [rebuild_id e]


example (x y : Expr)
    (hx : rebuild x = x)
    (hy : rebuild y = y) :
    rebuild (.add x y) = .add x y := by
  simp only [rebuild]
  rw [hx, hy]


theorem foldAdd_correct (a b : Expr) :
    eval (foldAdd a b) = eval a + eval b := by
  cases a <;> cases b <;> rfl

theorem foldMul_correct (a b : Expr) :
    eval (foldMul a b) = eval a * eval b := by
  cases a <;> cases b <;> rfl

theorem foldConstants_correct (e : Expr) :
    eval (foldConstants e) = eval e := by
  induction e with
  | lit n => rfl
  | add x y ihx ihy =>
      simp only [foldConstants, foldAdd_correct, eval]
      rw [ihx, ihy]
  | mul x y ihx ihy =>
      simp only [foldConstants, foldMul_correct, eval]
      rw [ihx, ihy]
