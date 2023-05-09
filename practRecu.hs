--Función super pares
numList :: Int -> [Int]
numList n
    | n > 0 = numList (div n 10)++[mod n 10]
    | otherwise = []

superPares :: Int -> Bool
superPares n = and (map even [x | x <- numList n])

--Pasar arboles a listas, dar pares e impares
data Arbol a = Nill | Node (Arbol a) a (Arbol a) deriving Show

treeList :: Arbol a -> [a]
treeList Nill = []
treeList (Node Nill a Nill) = [a]
treeList (Node izq a Nill) = treeList izq++[a]
treeList (Node Nill a der) = treeList der++[a]
treeList (Node izq a der) = treeList izq++treeList der++[a]

impares :: Integral a => Arbol a -> [a]
impares xs = filter esImpar (treeList xs)

esImpar :: Integral a => a -> Bool
esImpar x
    | mod x 2 /= 0 = True
    | otherwise = False

--Instance Eq, Show, Ord, Num de Nat

--xor estricto, haskell evalua los valores de los argumentos antes de que se
--ejecuten las clausulas correspondientes, es decir, es por casos.
xor :: Bool -> Bool -> Bool
xor True False = True
xor False True = True
xor True True = False
xor False False = False

--xor2 NO es estricto ya evalua de manera perezosa el /=, por lo que no es
--necesario evaluar ambos argumentos.
xor2 :: Bool -> Bool -> Bool
xor2 n m
    | n /= m = True
    | otherwise = False

--Ejercicio 3
enRango :: Int -> Int -> [Int] -> [Int]
enRango a b xs = [x | x <- xs, x >= a, x <= b]

enRango2 :: Int -> Int -> [Int] -> [Int]
enRango2 a b [] = []
enRango2 a b [x]
    | a <= x && b >= x = [x]
    | otherwise = []
enRango2 a b (x:xs)
    | a <= x && b >= x = x:enRango2 a b xs
    | otherwise = enRango2 a b xs

enRango3 :: Int -> Int -> [Int] -> [Int]
enRango3 a b [] = []
enRango3 a b (x:xs)
    | a <= x && b >= x = x:enRango3 a b xs
    | otherwise = enRango3 a b xs

--Ejercicio 4
--4.c
--NORMAL
--False && (trues == trues)
--  [Def. &&]
--False
--
--APLICATIVO
--False && (trues == trues)
--  [Def. trues]
--False && (True:trues == trues)
--  [Def. trues]
--False && (True:(True:trues) == trues)
--  ..., Se va al infinito