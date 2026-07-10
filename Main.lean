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
infixl:70 "*" => Group.mul
postfix:max "⁻¹" => Group.inv
notation "e" => Group.one

-- Basic Property
theorem left_cancel {G : Type} [Group G] (a b c : G) (h :  c * a = c * b) : a= b := by
  rw [<- one_mul a]
  rw [<- inv_mul c]
  rw [mul_assoc]
  rw [h]
  rw [<- mul_assoc]
  rw [inv_mul]
  rw [one_mul]

theorem unique_inv {G : Type} [Group G] (a x : G) (h : x * a = e) : x= a⁻¹  := by
  rw [<- mul_one x ]
  rw [<- mul_inv a]
  rw [<- mul_assoc]
  rw [h]
  rw [one_mul]

theorem inv_inv {G : Type} [Group G] (a : G) : (a⁻¹)⁻¹ = a := by
  rw [<- mul_one (a⁻¹)⁻¹ ]
  rw [<- inv_mul a]
  rw [<- mul_assoc]
  rw [ inv_mul]
  rw [one_mul]

theorem ue_id {G : Type} [Group G] ( x a : G) (h: x * a = a): x = e := by
  rw [<- mul_one x]
  rw [<- mul_inv a]
  rw [<- mul_assoc]
  rw [h]

-- Group Homomorphism and Sub Group
structure GroupHom (G H : Type) [Group G] [Group H] where
  toFun : G -> H

  map_mul : ∀ a b : G, toFun (a * b) = toFun a * toFun b

-- use just as function f a instead of f.toFun a
instance {G H : Type} [Group G] [Group H] : CoeFun (GroupHom G H) (fun _ => G -> H) where coe f := f.toFun

theorem hom_id {G H : Type} [Group G] [Group H] (f : GroupHom G H) : f e = e := by
  apply ue_id (f e) (f e)
  rw [<- f.map_mul]
  rw [mul_one e]

theorem hom_inv {G H : Type} [Group G] [Group H] (f: GroupHom G H) (a : G) : f (a⁻¹) = (f a)⁻¹ := by
  apply unique_inv (f a) (f (a⁻¹))
  rw [<- f.map_mul]
  rw [inv_mul]
  rw [hom_id]

structure SubGroup (G : Type) [Group G] where
  -- function return true if an element of the subgroup
  carrier : G -> Prop

  -- Property
  one_mem : carrier e
  mul_mem : ∀ {a b :G}, carrier a -> carrier b -> carrier (a * b)
  inv_mem : ∀ {a : G}, carrier a -> carrier a⁻¹ 

theorem subgroup_test {G : Type} [Group G] (H : SubGroup G) (a b : G) (ha: H.carrier a) (hb : H.carrier b) : H.carrier (a * b⁻¹ ) := by
  exact H.mul_mem ha (H.inv_mem hb)

def kernel { G H : Type} [ Group G] [ Group H] ( f: GroupHom G H) : SubGroup G where
  carrier := fun x => f x = e
  
  one_mem := by
    exact hom_id f
  
  mul_mem := by
    intro a
    intro b
    intro ha
    intro hb
    rw [f.map_mul]
    rw [ha]
    rw [hb]
    rw [one_mul]
  
  inv_mem := by
    intro a 
    intro ha
    apply ue_id (f a⁻¹) (f a)
    rw [hom_inv]
    rw [inv_mul]
    rw [ha]

    
