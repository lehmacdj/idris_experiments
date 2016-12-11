data Parity : Nat -> Type where
  Even : Parity (n + n)
  Odd  : Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity Z = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j)))     | Even ?= Even {n=S j}
  parity (S (S (S (j + j)))) | Odd  ?= Odd  {n=S j}

parity_lemma_1 = proof
  compute
  intros
  rewrite sym (plusSuccRightSucc j j)
  trivial

parity_lemma_2 = proof
  compute
  intros
  rewrite sym (plusSuccRightSucc j j)
  trivial

natToBin : Nat -> List Bool
natToBin Z = []
natToBin k with (parity k)
  natToBin (j + j)     | Even = False :: natToBin j
  natToBin (S (j + j)) | Odd  = True  :: natToBin j

data Binary : Nat -> Type where
  BEnd : Binary Z
  BO : Binary n -> Binary (n + n)
  BI : Binary n -> Binary (S (n + n))

Show (Binary n) where
  show (BO x) = show x ++ "0"
  show (BI x) = show x ++ "1"
  show BEnd   = ""

natToBin' : (n:Nat) -> Binary n
natToBin' Z = BEnd
natToBin' (S k) with (parity k)
   natToBin' (S (j + j))     | Even  = BI (natToBin' j)
   natToBin' (S (S (j + j))) | Odd  ?= BO (natToBin' (S j))

natToBin'_lemma_1 = proof
    intro
    intro
    rewrite sym (plusSuccRightSucc j j)
    trivial
