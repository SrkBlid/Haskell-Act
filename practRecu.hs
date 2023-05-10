--Función super pares
numList :: Int -> [Int]
numList n
    | n > 0 = numList (div n 10)++[mod n 10]
    | otherwise = []

superPares :: Int -> Bool
superPares n = and (map even [x | x <- numList n])

superPares2 :: Int -> Bool
superPares2 n = foldr (&&) True [even x | x <- numList n]

--Pasar arboles a listas, dar pares e impares
data Arbol a = Nill | Node (Arbol a) a (Arbol a) deriving Show

treeList :: Arbol a -> [a]
treeList Nill = []
treeList (Node Nill a Nill) = [a]
treeList (Node izq a Nill) = treeList izq++[a]
treeList (Node Nill a der) = treeList der++[a]
treeList (Node izq a der) = treeList izq++treeList der++[a]

darVuelta :: Arbol a -> Arbol a
darVuelta (Node Nill a Nill) = Node Nill a Nill
darVuelta (Node izq a Nill) = Node Nill a (darVuelta izq)
darVuelta (Node Nill a der) = Node (darVuelta der) a Nill
darVuelta (Node izq a der) = Node (darVuelta der) a (darVuelta izq)

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

--Instanciando Nat
data Nat = Zero | Succ Nat

instance Eq Nat where
    Zero == Zero = True
    Zero == Succ m = False
    Succ n == Succ m = n == m

instance Ord Nat where
    (<=) Zero _ = True
    (<=) _ Zero = False
    (<=) (Succ n) (Succ m) = n <= m

instance Show Nat where
    show Zero = "Zero"
    show (Succ n) = "Succ "++show n

instance Num Nat where
    (+) n Zero = n
    (+) n (Succ m) = Succ (n+m)

    (-) n Zero = n
    (-) Zero _ = error "No se permiten números negativos"
    (-) (Succ n) (Succ m) = n-m

    (*) _ Zero = Zero
    (*) n (Succ m) = n + (n*m)
    
    abs n = n

    signum Zero = Zero
    signum _ = Succ Zero

    fromInteger n
        | n < 0 = error "No se permiten números negativos"
        | n == 0 = Zero
        | otherwise = Succ (fromInteger(n-1))

--Matrices
diagM :: Int -> [(Int, Int)]
diagM n = [(n-i, i) | i <- [0..n]]
matrizInf :: [(Int, Int)]
matrizInf = concat2 [diagM n | n <- [0..]]

concat2 :: [[a]] -> [a]
concat2 [] = []
concat2 [x] = x
concat2 (x:xs) = x++concat2 xs

parMatriz :: [(Int, Int)] -> [(Int, Int)]
parMatriz [] = []
parMatriz (x:xs)
    | mod (fst2 x) 2 == 0 && mod (snd2 x) 2 == 0 = x:parMatriz xs
    | otherwise = parMatriz xs

parMatriz2 :: [(Int, Int)] -> [(Int, Int)]
parMatriz2 xs = [x | x <- xs, mod (fst2 x) 2 == 0, mod (snd2 x) 2 == 0]

imparMatriz :: [(Int, Int)] -> [(Int, Int)]
imparMatriz [] = []
imparMatriz (x:xs)
    | mod (fst2 x) 2 /= 0 && mod (snd2 x) 2 /= 0 = x:imparMatriz xs
    | otherwise = imparMatriz xs

imparMatriz2 :: [(Int, Int)] -> [(Int, Int)]
imparMatriz2 xs = [x | x <- xs, mod (fst2 x) 2 /= 0, mod (snd2 x) 2 /= 0]

fst2 :: (a, a) -> a
fst2 (x, y) = x

snd2 :: (a, a) -> a
snd2 (x, y) = y