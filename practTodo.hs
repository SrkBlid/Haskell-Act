--PRÁCTICO 1--

--2
--head(tail("hola mundo"))

--3
--reverse(head("hola mundo"))

--5
--mod (head(reverse([1,2,3]))) 2 == 0

--6
--mod (sum [1,2,3]) 3 == 0

--7
--mod (sum [1,2,3]) 3 == 0 || mod (sum [1,2,3]) 6 == 0

--8
list :: Int -> [Int]
list 0 = []
list n = list (div n 10) ++ [mod n 10]

--9
--reverse("olo") == "olo"

--PRÁCTICO 2--

--2
hd :: [a] -> a
hd [] = error "Lista vacia"
hd (x:xs) = x

tl :: [a] -> [a]
tl [] = error "Lista vacia"
tl (x:xs) = xs

last2 :: [a] -> a
last2 [] = error "Lista vacia"
last2 [x] = x
last2 (x:xs) = last2 xs

last3 :: [a] -> a
last3 [] = error "Lista vacia"
last3 xs = head(reverse xs)

init2 :: [a] -> [a]
init2 [] = error "Lista vacia"
init2 [x] = []
init2 (x:xs) = x:init2 xs 

--3
maxTres :: Int -> Int -> Int -> Int
maxTres x y z
    |x>=y && x>=z = x
    |y>=x && y>=z = y
    |z>=x && z>=y = z

--4
concatenar :: [a] -> [a] -> [a]
concatenar xs [] = xs
concatenar [] ys = ys
concatenar xs (y:ys) = y:concatenar xs ys

tomar :: Int -> [a] -> [a]
tomar 0 _ = []
tomar _ [] = []
tomar n (x:xs) = x:tomar (n-1) xs

tirar :: Int -> [a] -> [a]
tirar 0 xs = xs
tirar _ [] = []
tirar n (x:xs) = tirar (n-1) xs

concaF :: [a] -> [a] -> [a]
concaF xs [] = xs
concaF [] ys = ys
concaF xs ys = xs++ys

concaF2 :: [a] -> [a] -> [a]
concaF2 xs [] = xs
concaF2 [] ys = ys
concaF2 (x:xs) ys = x:concaF xs ys

--5
abs2 :: Int -> Int
abs2 0 = 0
abs2 n
    |n > 0 = n
    |otherwise = -n

--6
edad :: (Int, Int, Int) -> (Int, Int, Int) -> Int
edad (n1,n2,n3) (m1,m2,m3) = abs2(n3-m3)

--7
xor2 :: Bool -> Bool -> Bool
xor2 n m
    | n && m = False
    | n && not m = True
    | not n && m = True
    | not n && not m = False

xor3 :: Bool -> Bool -> Bool
xor3 n m
    | (n && not m) || (not n && m) = True
    | otherwise = False

--8
esPrimo :: Int -> Bool
esPrimo n 
    | cantDivs n 1 >= 2 = False
    | cantDivs n 1 < 2 = True
    where cantDivs n i
            | n == i = 0
            | mod n i == 0 = 1+cantDivs n (i+1)
            | otherwise = cantDivs n (i+1)

--9
listPrimos :: Int -> [Int]
listPrimos 0 = []
listPrimos n = if esPrimo(n) then listPrimos (n-1)++[n] else listPrimos (n-1)

--10
reversaLista :: [Int] -> [Int]
reversaLista [] = []
reversaLista (x:xs) = reversaLista xs ++ [x]

--11
listasIguales :: [Int] -> [Int] -> Bool
listasIguales [] [] = True
listasIguales _ [] = False
listasIguales [] _ = False
listasIguales (x:xs) (y:ys)
    | x /= y = False
    | otherwise = listasIguales xs ys

--12
listPalindroma :: Eq a => [a] -> Bool
listPalindroma [] = True
listPalindroma [x] = True
listPalindroma (x:xs)
    | x == head(reverse xs) = listPalindroma (init xs)
    | otherwise = False

--13
raicesR :: Int -> Int -> Int -> Int
raicesR a b c = 
        if b*b-4*a*c == 0 then
                1
        else
                2

--PRÁCTICO 3--

--1
mergeLT :: Ord a => [a] -> [a] -> [(a, a)]
mergeLT [] [] = []
mergeLT [] _ = error "Las listas no tienen el mismo tamaño"
mergeLT _ [] = error "Las listas no tienen el mismo tamaño"
mergeLT (x:xs) (y:ys) = [(x,y)]++mergeLT xs ys 

mergeL :: Ord a => [a] -> [a] -> [a]
mergeL [] [] = []
mergeL [] _ = error "Las listas no tienen el mismo tamaño"
mergeL _ [] = error "Las listas no tienen el mismo tamaño"
mergeL (x:xs) (y:ys) = [x]++[y]++mergeL xs ys 

--2
ordInt :: [Int] -> [Int]
ordInt [] = []
ordInt (x:xs) = mayor x (ordInt xs)


mayor :: Int -> [Int] -> [Int]
mayor x [] = [x]
mayor x (y:ys)
    | x <= y = x: y: ys
    | otherwise = y:mayor x ys

--3
dosN :: Int -> Int
dosN 0 = 1
dosN n = 2*dosN (n-1) 

--4
secBinaria :: Int -> [Int]
secBinaria 0 = []
secBinaria n 
    | mod n 2 == 1 = secBinaria (div n 2) ++ [1]
    | otherwise = secBinaria (div n 2) ++ [0]

--5
binPar :: [Int] -> Bool
binPar [] = True
binPar xs 
    | last xs == 0 = True
    | otherwise = False

--6
distHamming :: String -> String -> Int
distHamming [] _ = 0
distHamming _ [] = 0
distHamming (x:xs) (y:ys)
    | x /= y = 1+distHamming xs ys
    | otherwise = distHamming xs ys

--7
cuadPerf :: Int -> Bool
cuadPerf n = sqrt(fromIntegral n) == fromIntegral(round(sqrt(fromIntegral n)))

--8
repes :: Eq a => Int -> a -> [a] -> Bool
repes 0 _ _ = True
repes _ _ [] = False
repes n z xs
    | contador n z xs 0 == n = True
    | contador n z xs 0 /= n = False

contador :: Eq a => Int -> a -> [a] -> Int -> Int
contador 0 _ _  i = 0
contador _ _ [] i = i
contador n z (x:xs) i
    | z == x = contador n z xs (i+1)
    | z /= x = contador n z xs i

--9
nelem :: Eq a => [a] -> Int -> a
nelem [] _ = error "Lista vacia"
nelem (x:xs) n = pos (x:xs) n 0
    where pos (x:xs) n i
            | n /= i = pos xs n (i+1)
            | otherwise = x

--10
posicionesC2 :: String -> Char -> [Int]
posicionesC2 [] _ = []
posicionesC2 (x:xs) c = posicionesC2' (x:xs) c 0
    where 
        posicionesC2' :: String -> Char -> Int -> [Int]
        posicionesC2' [] c i = []
        posicionesC2' [x] c i
            | x == c = [i]
            | otherwise = posicionesC2' [] c (i+1)
        posicionesC2' (x:xs) c i
            | x == c = i:posicionesC2' xs c (i+1)
            | otherwise = posicionesC2' xs c (i+1) 

--11
compact2 :: Eq a => [a] -> [a]
compact2 [] = []
compact2 [x] = [x]
compact2 (x:xs)
    | x == head(xs) = compact2 xs
    | otherwise = x:compact2 xs

--PRÁCTICO 4--
