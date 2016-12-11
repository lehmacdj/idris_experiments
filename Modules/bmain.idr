module Main

import Btree

main : IO ()
main =
  let t = toTree [1,8,2,7,9,3]
  in  print (Btree.toList t)
