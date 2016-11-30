module Intro

-- This causes a warning with implicit variables named the same thing
-- x : Int
-- x = 42

foo : String
foo = "Sausage machine"

bar : Char
bar = 'Z'

quux : Bool
quux = False

reverse' : List a -> List a
reverse' = helper [] where
    -- Type declarations necessary here
    helper : List a -> List a -> List a
    helper a [] = a
    helper a (h::t) = helper (h::a) t

even : Nat -> Bool
even Z = True
even (S k) = odd k where
    -- But not here since the type can be fully determined by the first
    -- application of [odd]
    odd Z = False
    odd (S k) = even k

-- Functions can return types
isSingleton : Bool -> Type
isSingleton True = Nat
isSingleton False = List Nat

-- These functions can be used instead of types at locations
mkSingle : (x : Bool) -> isSingleton x
mkSingle True = 0
mkSingle False = []

-- Also as parameters
sum' : (single : Bool) -> isSingleton single -> Nat
sum' True = id
sum' False = sum

-- Dependent Data Types (Data.Vect)
data Vect : Nat -> Type -> Type where
    Nil : Vect Z a
    (::) : a -> Vect k a -> Vect (S k) a

-- Won't type check if m and n don't line up
(++) : Vect m a -> Vect n a -> Vect (m + n) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

-- Represent the set of numbers <= k
data Fin : Nat -> Type where
  FZ : Fin (S k)
  FS : Fin k -> Fin (S k)

-- Implicit arguments can be given
index : {n : Nat} -> {a : Type} -> (i:Fin n) -> (xs:Vect n a) -> a
index FZ     (x :: xs) = x
index (FS k) (x :: xs) = index k xs

-- manually applying implicit arguments
val : Nat
val = index {n=3} {a=Nat} (FS FZ) (2::3::4::Nil)

-- Pattern matching on implicit arguments
isEmpty : Vect n a -> Bool
isEmpty {n=Z} _   = True
isEmpty {n=S _} _ = False

-- Using
using (x:a, y:a, xs:Vect n a)
  -- Represents an element and its position in the list
  data IsElem : a -> Vect n a -> Type where
      Here  : IsElem x (x :: xs)
      There : IsElem x xs -> IsElem x (y :: xs)

testVec : Vect 4 Int
testVec = 3 :: 4 :: 5 :: 6 :: Nil

inVect : IsElem 5 Intro.testVec
-- This is a proof that 5 is located at index 2 for vector Intro.testVec
-- It fails to compile otherwise
inVect = There (There Here)

-- Functions must be declared in order unless mutual is used
mutual
  even' : Nat -> Bool
  even' Z = True
  even' (S k) = odd' k

  odd' : Nat -> Bool
  odd' Z = False
  odd' (S k) = even' k
