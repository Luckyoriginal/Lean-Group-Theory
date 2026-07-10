-- Group Definition
class Group (G : Type) where
  -- Operation
  mul : G -> G -> G
  one : G 
  inv : G -> G

  --Axiom
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul   : ∀ a : G, mul one a = a
  mul_one   : ∀ a : G, mul a one = a
  inv_mul   : ∀ a : G, mul (inv a) a = one
  mul_inv   : ∀ a : G, mul a (inv a) = one

open Group

-- Basic Property
theorem left_cancel {G : Type} [Group G] (a b c : G) (h : mul c a = mul c b) : a= b := by
  rw [<- one_mul a]
  rw [<- inv_mul c]
  rw [mul_assoc]
  rw [h]
  rw [<- mul_assoc]
  rw [inv_mul]
  rw [one_mul]


