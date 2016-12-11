interface Foo a where
  foo : a -> Int

readNumber : IO (Maybe Nat)
readNumber = pure $ Just 1

-- pattern match in bind with else (arbitrary amount of things)
readNums : IO (Maybe (Nat, Nat))
readNums = do
  Just x_ok <- readNumber | Nothing => pure Nothing
  Just y_ok <- readNumber | Nothing => pure Nothing
  pure (Just (x_ok, y_ok))

-- ! notation - allows implicit lifting of stuff
m_add : Monad m => m Int -> m Int -> m Int
m_add x y = pure (!x + !y)

-- Alternative + Monad = MonadPlus
-- Allows the usage of list comprehensions

-- Idiom brackets!
-- Allows convenient syntax for: (+) <$> x <*> y
addM : Applicative f => f Int -> f Int -> f Int
addM x y = [| x + y |]

data Expr = Var String
          | Val Int
          | Add Expr Expr

data Eval : Type -> Type where
  MkEval : (List (String, Int) -> Maybe a) -> Eval a

fetch : String -> Eval Int
fetch x = MkEval (\e => fetchVal e) where
  fetchVal : List (String, Int) -> Maybe Int
  fetchVal [] = Nothing
  fetchVal ((v, val) :: xs) = if (x == v)
                                 then (Just val)
                                 else (fetchVal xs)

Functor Eval where
  map f (MkEval g) = MkEval (\e => map f (g e))

Applicative Eval where
  pure x = MkEval (\e => Just x)

  (<*>) (MkEval f) (MkEval g) = MkEval (\x => (f x) <*> (g x))

eval : Expr -> Eval Int
eval (Var x ) = fetch x
eval (Val x) = [| x |]
eval (Add x y) = [| eval x + eval y |]

runEval : List (String, Int) -> Expr -> Maybe Int
runEval env e = let MkEval envFun = eval e in envFun env

[reverse] Ord Nat where
  compare Z (S n) = GT
  compare (S n) Z = LT
  compare Z Z = EQ
  compare (S x) (S y) = compare @{reverse} x y

numbers : List Nat
numbers = [1, 2, 3, 4, 5]

sorted : List Nat
sorted = sort @{reverse} numbers

-- | stuff -- can be used to resolve implementation when using a new type
