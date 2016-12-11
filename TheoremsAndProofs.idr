%default total
fiveIsFive : 5 = 5
fiveIsFive = Refl

threeIs1Plus2 : 3 = 1 + 2
threeIs1Plus2 = Refl

disjoint : (n : Nat) -> Z = S n -> Void
disjoint n p = replace {P = disjointTy} p () where
  disjointTy : Nat -> Type
  disjointTy Z = ()
  disjointTy (S k) = Void

plusReduces : (n:Nat) -> plus Z n = n
plusReduces n = Refl

plusReducesZ : (n:Nat) -> n = plus n Z
plusReducesZ Z = Refl
plusReducesZ (S k) = cong (plusReducesZ k)

plusReducesS : (n:Nat) -> (m:Nat) -> S (plus n m) = plus n (S m)
plusReducesS Z m = Refl
plusReducesS (S k) m = cong (plusReducesS k m)

partial empty1 : Void
empty1 = hd [] where
  partial hd : List a -> a
  hd (x :: xs) = x

partial empty2 : Void
empty2 = empty2

-- assert_smaller can be used to make stuff total
quicksort : Ord a => List a -> List a
quicksort [] = []
quicksort [e] = [e]
quicksort (p :: xs) = quicksort (assert_smaller (p :: xs) [x | x <- xs, x < p]) ++
               [p] ++
               quicksort (assert_smaller (p :: xs) [x | x <- xs, x >= p])
