--1
mergeOrd :: [Int] -> [Int] -> [Int]
mergeOrd [] [] = []
mergeOrd xs [] = xs
mergeOrd [] ys = ys
mergeOrd (x:xs) (y:ys) = 
    if (x >= y) then
        [y]++mergeOrd (x:xs) ys
    else
        [x]++mergeOrd xs (y:ys)

--2
ordenarNaturales :: [Int] -> [Int]
ordenarNaturales [] = []
ordenarNaturales (x:xs) = insertar x (ordenarNaturales xs)

insertar :: Int -> [Int] -> [Int]
insertar x [] = [x]
insertar x (y:ys)
  | x <= y    = x : y : ys
  | otherwise = y : insertar x ys

--3
calcExp2 :: Int -> Int
calcExp2 n
    | n == 0 = 1
    | otherwise = 2*calcExp2 (n-1)

--4
repBin :: Int -> [Int]
repBin 0 = []
repBin n = 
    if mod n 2 == 1 then
        [1]++repBin(div n 2)
    else 
        [0]++repBin(div n 2)

--5
binPar :: [Int] -> Bool
binPar [x] = x /= 1
binPar (x:xs) = binPar xs

--6
distH :: [Char] -> [Char] -> Int
distH xs [] = 0
distH [] ys = 0
distH (x:xs) (y:ys) =
    if x /= y then
        1+distH xs ys
    else
        distH xs ys

--7
cuadPerf :: Int -> Bool
cuadPerf n = sqrt(fromIntegral n) == fromIntegral(round(sqrt(fromIntegral n)))

--8
repetidos :: a -> Int -> [a]
repetidos z n
    | n == 0 = []
    | otherwise = z:repetidos z (n-1)

--9
nelem :: [a] -> Int -> a
nelem (x:xs) n
    | length (xs) == 0 = x
    | n == 0 = x
    | otherwise = nelem xs (n-1)

--10
posicionesC' :: [Char] -> Char -> [Int]
posicionesC' [] n = []
posicionesC' (x:xs) n = posicionesC'' (x:xs) n 0
    where 
        posicionesC'' [] _ _ = []
        posicionesC'' (x:xs) n i = 
            if x == n then
                i: posicionesC'' xs n (i+1) 
            else
                posicionesC'' xs n (i+1)

--11
compact :: Eq a => [a] -> [a]
compact [] = []
compact [x] = [x]
compact (x:xs) =
    if x == head(xs) then
        compact xs
    else
        x:compact xs