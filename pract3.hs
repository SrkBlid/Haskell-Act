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
ordList :: [Int] -> [Int]
ordList [] = []
--ordList (x:xs) = ordList[x'|x'<-xs, x'<=x] ++ [x] ++ ordList[x'|x'<-xs, x'>x]

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
binPar :: [Int] -> [Int]
binPar (x:xs) = [2^x' | x' <- x:xs, x == 1]
