-- With can let you pattern match stuff that is otherwise impossible by proving
-- that function arguments have a certain form for different results of a
-- function call

data Foo : Type where
  FInt : Int -> Foo
  FBool : Bool -> Foo

optional : Foo -> Maybe Int
optional (FInt i)  = Just i
optional (FBool _) = Nothing

-- returns either Nothing or a a Int with a proof that optional foo = Just x
isFInt : (foo:Foo) -> Maybe (x : Int ** (optional foo = Just x))
isFInt foo with (optional foo) proof p
  isFInt foo | Nothing = Nothing
  isFInt foo | Just x = Just (x ** Refl)
