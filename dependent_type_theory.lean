universe u

namespace one
  /-
  As an exercise, we encourage you to use do_twice and double to 
  define functions that quadruple their input, 
  and multiply the input by 8. 
  As a further exercise, we encourage you to try defining a 
  function Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) 
  which applies its argument twice, so that Do_Twice do_twice 
  is a function that applies its input four times. 
  Then evaluate Do_Twice do_twice double 2.
  -/

  -- reference code from section 2.4
  def double : ℕ → ℕ := λ x, x + x
  def square : ℕ → ℕ := λ x, x * x
  def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)
  def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

  -- solution
  def Do_Twice {α :Type} (f: (α → α) → (α → α)) (g: α → α) (x: α) := f g x
  
  #reduce @Do_Twice ℕ do_twice double 2
  #reduce Do_Twice do_twice double 2

end one

namespace two
  /- 
  Above, we discussed the process of “currying” a function, 
  that is, taking a function f (a, b) that takes an ordered 
  pair as an argument, and recasting it as a function f' a b 
  that takes two arguments successively. 
  As another exercise, we encourage you to complete the 
  following definitions, which “curry” and “uncurry” a function.
  -/
  def curry (α β γ : Type) (f : α × β → γ) : α → β → γ 
  := λ (a: α), (λ (b: β), f (a, b) )
  def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ 
  := λ (x : α × β), f x.1 x.2

end two

namespace three
  /-
  Above, we used the example vec α n for vectors of elements of 
  type α of length n. 
  Declare a constant vec_add that could represent a 
  function that adds two vectors of natural numbers of 
  the same length, and a constant vec_reverse that can 
  represent a function that reverses its argument. 
  Use implicit arguments for parameters that can be inferred. 
  Declare some variables and check some expressions 
  involving the constants that you have declared.
  -/

  constant cons   : Π {α : Type u}, α → list α → list α
  constant nil    : Π {α : Type u}, list α
  constant append : Π {α : Type u}, list α → list α → list α

  variable  α : Type
  variable  a : α
  variables l1 l2 : list α

  #check cons a nil
  #check append (cons a nil) l1
  #check append (append (cons a nil) l1) l2

  constant vec : Type u → ℕ → Type u

  constant vec_empty : Π α : Type u, vec α 0
  constant vec_cons : Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
  constant vec_append : Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)

  #check vec_empty ℕ
  #check (vec_cons ℕ 0) 9 (vec_empty ℕ) -- vec of len 1
  #check (vec_cons ℕ 1) 9 ((vec_cons ℕ 0) 9 (vec_empty ℕ)) -- vec of len 2
  #check vec_append ℕ 2 2 ((vec_cons ℕ 1) 9 ((vec_cons ℕ 0) 9 (vec_empty ℕ))) ((vec_cons ℕ 1) 9 ((vec_cons ℕ 0) 9 (vec_empty ℕ))) -- vec of len 4

  constant Vec_empty : Π {α : Type u}, vec α 0
  constant Vec_cons : Π {α : Type u} {n: ℕ}, α → vec α n → vec α (n + 1)
  constant Vec_append : Π {α : Type u} {n m: ℕ},  vec α m → vec α n → vec α (n + m)

  constant Vec_add : Π {α : Type u} {n m: ℕ}, vec α n → vec α m → vec α (n + m)
  constant Vec_reverses : Π {α : Type u} {n: ℕ}, vec α n → vec α n

  #check @Vec_empty
  #check Vec_cons 9 Vec_empty -- vec of len 1
  #check Vec_cons 9 (Vec_cons 9 Vec_empty) -- vec of len 2
  #check Vec_append (Vec_cons 9 (Vec_cons 9 Vec_empty)) (Vec_cons 9 (Vec_cons 9 Vec_empty)) -- vec of len 4

  #check Vec_add (Vec_append (Vec_cons 9 (Vec_cons 9 Vec_empty)) (Vec_cons 9 (Vec_cons 9 Vec_empty))) (Vec_cons 9 (Vec_cons 9 Vec_empty))  -- vec of len 6
  #check Vec_reverses (Vec_cons 9 (Vec_cons 9 Vec_empty))

end three

namespace four
  /-
  Similarly, declare a constant matrix so that matrix α m n could represent the 
  type of m by n matrices. 
  Declare some constants to represent functions on this type, 
  such as matrix addition and multiplication, and (using vec) 
  multiplication of a matrix by a vector. 
  Once again, declare some variables and check some expressions
  involving the constants that you have declared.
  -/
end four