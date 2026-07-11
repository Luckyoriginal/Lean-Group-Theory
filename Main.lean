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

-- Normal SUbGroup
class Normal { G : Type} [Group G] (N : SubGroup G) where
  conj_mem : ∀ ( n g : G), N.carrier n -> N.carrier (g * n * g⁻¹ )

-- Relation:
def coset_rel {G : Type} [Group G] (N : SubGroup G) (a b : G) : Prop := 
  N.carrier (a⁻¹ * b)

theorem coset_refl {G : Type} [Group G] (N : SubGroup G) (a : G) : coset_rel N a a := by
  unfold coset_rel
  rw [inv_mul]
  exact N.one_mem

theorem _mul_inv_rev_ {G : Type} [Group G] (a b : G) : (a*b)*(b⁻¹* a⁻¹ ) = e := by
  rw [<-mul_assoc]
  apply ue_id (a*b*b⁻¹*a⁻¹) a
  rw [mul_assoc]
  rw [inv_mul]
  rw [mul_one]
  rw [mul_assoc]
  rw [mul_inv]
  rw [mul_one]

theorem mul_inv_rev {G : Type} [Group G] (a b : G) : (a *b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [<-mul_one (a*b)⁻¹]
  rw [<-_mul_inv_rev_ a b]
  rw [<-mul_assoc]
  rw [inv_mul]
  rw [one_mul]

theorem coset_symm {G : Type} [Group G] (N : SubGroup G) (a b : G)(h : coset_rel N a b) : coset_rel N b a := by
  unfold coset_rel
  rw [<- inv_inv a]
  rw [<-mul_inv_rev a⁻¹ b]
  apply N.inv_mem h

theorem coset_trans {G : Type} [Group G] (N : SubGroup G) (a b c : G) (h1 : coset_rel N a b) (h2 : coset_rel N b c) : coset_rel N a c := by
  unfold coset_rel 
  rw [<- mul_one (a⁻¹)]
  rw [<- mul_inv b]
  rw [<- mul_assoc]
  rw [mul_assoc]
  exact N.mul_mem h1 h2

def coset_setoid {G : Type} [Group G] (N : SubGroup G) : Setoid G where 
  r := coset_rel N
  iseqv := {
    refl := coset_refl N
    symm := coset_symm N _ _ 
    trans := coset_trans N _ _ _
  }

def QuotGroup { G : Type} [ Group G] (N : SubGroup G) := Quotient (coset_setoid N)

class NormalGroup {G : Type} [Group G] (N : SubGroup G) where
  conj_mem : ∀ (n g : G), N.carrier n -> N.carrier ( g * n * g⁻¹ )

theorem mul_well_defined {G : Type} [Group G] (N : SubGroup G) [NormalGroup N]
  (a b c d : G) (h1 : coset_rel N a c ) (h2 : coset_rel N b d) : 
  coset_rel N (a*b) (c*d) := by
    unfold coset_rel at *
    rw [mul_inv_rev]
    rw [<- mul_one c]
    rw [<- mul_inv b]
    rw [<- mul_assoc]
    rw [<- mul_assoc]
    rw [<- mul_assoc]
    rw [mul_assoc]
    have h_conj := NormalGroup.conj_mem (a⁻¹ * c) b⁻¹ h1
    rw [inv_inv] at h_conj
    rw [<- mul_assoc] at h_conj
    exact N.mul_mem h_conj h2

--isomorphism
structure MulEquiv (G H :Type ) [Group G] [Group H] where
  toFun : G->H
  invFun: H->G

  left_inv: ∀ x : G, invFun (toFun x) = x
  right_inv: ∀ y : H, toFun (invFun y) = y

  map_mul: ∀ a b : G, toFun (a * b) = toFun a * toFun b

--macro
instance {G H :Type} [Group G] [Group H] : CoeFun (MulEquiv G H) (fun _ => G -> H) where coe f := f.toFun

theorem inv_map_mul {G H : Type} [Group G] [Group H] (f : MulEquiv G H) (a b :H) : f.invFun (a*b) = f.invFun a * f.invFun b := by
  rw [<- f.right_inv a]
  rw [<- f.right_inv b]
  rw [<- f.map_mul]
  rw [f.left_inv]
  rw [f.right_inv]
  rw [f.right_inv]
