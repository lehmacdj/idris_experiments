module Btree
%access export

data BTree a = Leaf
             | Node (BTree a) a (BTree a)

insert : Ord a => a -> BTree a -> BTree a
insert x Leaf = Node Leaf x Leaf
insert x (Node l v r) = case compare x v of
                             LT => (Node (insert x l) v r)
                             EQ => (Node l x r)
                             GT => (Node l v (insert x r))

toList : BTree a -> List a
toList Leaf = []
toList  (Node l v r) = Btree.toList l ++ (v :: Btree.toList r)

toTree : Ord a => List a -> BTree a
toTree [] = Leaf
toTree (x :: xs) = insert x (toTree xs)
