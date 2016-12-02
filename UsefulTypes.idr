import Data.Vect

intVect : Vect 5 Int
intVect = [1,2,3,4,5] -- syntactic sugar for 1 :: 2 :: ... :: Nil

-- lambda expressions
double : Int -> Int
double = \x => 2 * x -- never write this operator sections exist

lookup' : Nat -> List a -> Maybe a
lookup' _ [] = Nothing
lookup' Z (h::t) = Just h
lookup' (S k) (h::t) = lookup' k t

fred : (String, Int)
fred = ("Hello", 3)

vect_len : (n : Nat ** Vect n String)
vect_len = (1 ** ["Hello"])

vect_len' : (n ** Vect n Integer)
vect_len' = (_ ** [1,2,3,4])

-- Dependent types are useful here for example
filter' : (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter' _ [] = (_ ** [])
filter' p (h::t) with (filter' p t)
  | (_ ** t') = if (p h) then (_ ** h :: t') else (_ ** t')

data NonEmpty' : (x : List a) -> Type where
  IsNonEmpty' : NonEmpty' (x :: xs)

Uninhabited (NonEmpty' []) where
  uninhabited IsNonEmpty' impossible

head' : (l : List a) -> {auto ok : NonEmpty' l} -> a
-- not necessary since I already declare above with Uninhabited instance that
-- this is impossible for the empty list:
-- forall [] the statement {ok=IsNonEmpty} is impossible
-- head' [] {ok=IsNonEmpty'} impossible
-- this works since the (NonEmpty' []) is an instance of uninhabited
head' (h::t) = h

e : Int
e = head' [1]

unsafeHead : List a -> a
unsafeHead (x::xs) = x

-- A proof that a list is non empty
-- the empty list isn't non empty
nonEmpty' : (xs : List a) -> Dec (NonEmpty' xs)
-- absurd is a proof using the Uninhabited typeclass
nonEmpty' [] = No absurd
-- otherwise we have an element that satisfies the type therefore so that
-- allows us to return an element of type IsNonEmpty'
nonEmpty' (_::_) = Yes IsNonEmpty'
