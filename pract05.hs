--Ejercicio 1
listInf :: [Int]
listInf = 1 : listInf

--Ejercicio 2
listDesdeN :: Int -> [Int]
listDesdeN n = n : listDesdeN (n+1)

listDesdeN2 :: Int -> [Int]
listDesdeN2 n = [n..]

--Ejercicio 3
listHastaN :: Int -> [Int]
listHastaN 0 = []
listHastaN n = listHastaN (n-1) ++ [n]

listHastaN2 :: Int -> [Int]
listHastaN2 n
    |n < 0 = error "Valor negativo"
    |otherwise = [1..n]

--Ejercicio 4
primerosCinco :: [Int] -> [Int]
primerosCinco (x:xs) = take 5 (x:xs)

--Ejercicio 5
devCuad :: [Int] -> [Int]
devCuad [] = error "Lista vacia"
devCuad xs = map (^2) xs

--Ejercicio 6
divisoresN :: Int -> [Int]
divisoresN n = divisoresN' n n
    where divisoresN' n i
            | i == 1 = [1]
            | (mod n i) == 0 = i : divisoresN' n (i-1)
            | otherwise = divisoresN' n (i-1)

divisoresN3 :: Int -> [Int]
divisoresN3 n = [x | x <- [1..n], foldl (mod) n [x] == 0]

esDiv :: Int -> Int -> Bool
esDiv x y = mod x y == 0
divN :: Int -> [Int]
divN x = filter (esDiv x) [1..x]

--Ejercicio 7
primosLista :: [Int] -> [Int]
primosLista (x:xs) = filter esPrimo (x:xs)

esPrimo :: Int -> Bool
esPrimo n
    | length [x | x <- [1..n], mod n x == 0] <= 2 = True
    | otherwise = False

esPrimo2 :: Int -> Bool
esPrimo2 n = divs n 1 0
divs :: Int -> Int -> Int -> Bool
divs n i m
    | n == i = res (m+1)
    | mod n i == 0 = divs n (i+1) (m+1)
    | otherwise = divs n (i+1) m
res :: Int -> Bool
res m
    | m <= 2 = True
    | otherwise = False

--Ejercicio 8
sumCuad :: [Int] -> Int
sumCuad (x:xs) = sum (map (^2) (x:xs))

sumCuad2 :: [Int] -> Int
sumCuad2 (x:xs) = sum (devCuad (x:xs))

--Ejercicio 9
listSucc :: [Int] -> [Int]
listSucc (x:xs) = map (+1) [n | n <- (x:xs)]

--Ejercicio 10
sumInt :: [Int] -> Int
sumInt (x:xs) = foldl (+) 0 (x:xs)

sumInt2 :: [Int] -> Int
sumInt2 (x:xs) = foldr (+) 0 (x:xs)

--Ejercicio 11
fact :: Int -> Int
fact 0 = 1
fact n = n*fact (n-1)

factFoldl :: Int -> Int
factFoldl n = foldl (*) 1 (elemHastaN n)
    where
        elemHastaN 0 = []
        elemHastaN n = n : elemHastaN (n-1)

--Ejercicio 12
and' :: [Bool] -> Bool
and' xs = foldl (&&) True xs

and'' :: [Bool] -> Bool
and'' xs = foldr (&&) True xs

--Ejercicio 13
op :: a -> Int
op n = 1

tamFoldl :: [a] -> Int
tamFoldl (x:xs) = foldl (+) 0 (map op (x:xs))

tamFoldr :: [a] -> Int
tamFoldr (x:xs) = foldr (+) 0 (map op (x:xs))

--Ejercicio 14
retSucc :: [Int] -> [Int]
retSucc (x:xs) = [n+1 | n <- x:xs]

--Ejercicio 15
retCuad :: [Int] -> [Int]
retCuad (x:xs) = [n^2 | n <- x:xs]

--Ejercicio 16
retParesMay10 :: [Int] -> [Int]
retParesMay10 (x:xs) = [n | n <- x:xs, mod n 2 == 0, n > 10]

--Ejercicio 17
divisoresN2 :: Int -> [Int]
divisoresN2 n = [x | x <- [1..n], mod n x == 0]

--Ejercicio 18
todosOcurrenEn :: Eq a => [a] -> [a] -> Bool
todosOcurrenEn [] _ = False
todosOcurrenEn _ [] = False
todosOcurrenEn xs ys = and [elem x ys | x <- xs]

--Ejercicio 19
retPrimos2N :: Int -> [Int]
retPrimos2N n = [x | x <- [2..n], esPrimo (x)]

--Ejercicio 20
prodCartesiano :: [Int] -> [Int] -> [(Int, Int)]
prodCartesiano (x:xs) (y:ys) = [(n, m) | n <- x:xs, m <- y:ys]

--Ejercicio 21
cuantasVeces :: Eq a => a -> [a] -> Int
cuantasVeces n (x:xs) = sum [1 | m <- x:xs, n == m]

--Ejercicio 22
split2 :: [a] -> [([a], [a])]
split2 (x:xs) = split3 (length (x:xs)) (x:xs)

split3 :: Int -> [a] -> [([a], [a])]
split3 n (x:xs)
    | n == -1 = []
    | otherwise = (take n (x:xs), drop n (x:xs)) : split3 (n-1) (x:xs)

splitIntensionada ::  [a] -> [([a], [a])]
splitIntensionada xs = [(take z xs, drop z xs) | z <- [0..length xs]]

--Ejercicio 23
sumaSeg :: [Int] -> Int
sumaSeg xs = sum [sum (take z xs) | z <- [0..(length xs)]]

--Ejercicio 24
infPares :: [Int]
infPares = [x | x <- [0..], mod x 2 == 0]

infParesMat :: [Int]
infParesMat = [2*x | x <- [0..]]

------------------------------------------------------------------------------
--Factorial de 5 formas distintas
--fact :: Int -> Int
--fact 0 = 1
--fact n = n*fact (n-1)

--Forma 1
--Retorna los factoriales hasta n
factoriales_1 :: Int -> [Int]
factoriales_1 n =
    reverse (aux n)
    where aux 0 = [1]
          aux n = fact n: aux (n-1)

--Forma 2
--Definición con acumuladores
factoriales_2 :: Int -> [Int]
factoriales_2 n =
    reverse (aux(n+1) 0 [1])
    where aux n m (x:xs) = if n==m then []
          else aux n (m+1) (x:xs) ++ [fact m]

--Forma 3
--Con listas por comprensión
factoriales_3 :: Int -> [Int]
factoriales_3 n = [fact x | x <- [0..n]]

--Forma 4
--Con funciones de orden superior, el map aplica una función a una lista
factoriales_4 :: Int -> [Int]
factoriales_4 n = map fact [0..n]

--Forma 5
--Con scanl, el cual te devuelve los resultados parciales en forma de lista, el foldl te devuelve el resultado directamente en forma de Int
factoriales_5 :: Int -> [Int]
factoriales_5 n = scanl (*) 1 [1..n] 