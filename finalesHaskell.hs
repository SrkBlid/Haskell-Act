--------------------------------------------------------------------------------------
-----------------------------------------2015-----------------------------------------
--------------------------------------------------------------------------------------
-- Definir el tipo de datos de árboles binarios en Haskell, definir la función rev : Tree a -> Tree a, que dado un árbol obtiene el árbol dado vuelta.
data TreeBin a = Nil | Node (TreeBin a) a (TreeBin a) deriving Show

rev :: TreeBin a -> TreeBin a
rev Nil = Nil
rev (Node izq n der) = Node (rev der) n (rev izq)