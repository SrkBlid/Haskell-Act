--EJERCICIO 1: Demostrar que la concatenación de listas es asociativa
(xs ++ ys) ++ zs == xs ++ (ys ++ zs)

--CB xs = []
xs = []
    [ESPECIFICACIÓN]
([] ++ ys) ++ zs == [] ++ (ys ++ zs)
    [DEF []]
ys ++ zs == ys ++ zs
    [LÓGICA]
True

--CI xs = (x:xs)
--HI = (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
xs = (x:xs)
    [ESPEFICICACIÓN]
(x:xs ++ ys) ++ zs == x:xs ++ (ys ++ zs)
    [DEF CONCATENACIÓN]
x : (xs ++ ys) ++ zs == x : (xs ++ (ys ++ zs))
    [HI]
x : (xs ++ (ys++zs)) == x : (xs ++ (ys ++ zs))
    [LÓGICA]
True

------------------------------------------------------------------------------
--EJERCICIO 2: Demostrar las siguientes propiedades
--map (f o g) xs = (map f) o (map g) xs
--CB xs = []
xs = []
    [ESPECIFICACIÓN]
map (f o g) [] = (map f) o (map g) []
    [DEF MAP [], DEF COMPOSICIÓN]
[] = map f []
    [DEF MAP []]
[] = []
    [LÓGICA]
True

--CI xs = (x:xs)
--HI = map (f o g) xs = (map f) o (map g) xs
xs = (x:xs)
    [ESPECIFICACIÓN]
map (f o g) (x:xs) = (map f) o (map g) (x:xs)
    [DEF COMPOSICIÓN]
(f o g) x : map (f o g) xs = (map f) ((map g) (x:xs))
    [DEF MAP]
(f o g) x : map (f o g) xs = (map f) (g x : (map g xs))
    [DEF MAP]
(f o g) x : map (f o g) xs = f (g x) : (map f) (map g) xs
    [HI]
f (g x) : map (f o g) xs = f (g x) : map (f o g) xs
    [LÓGICA]
True

--reversa (xs++ys) = reversa ys ++ reversa xs
--CB xs = []
xs = []
    [ESPECIFICACIÓN]
reversa ([]++ys) = reversa ys ++ reversa []
    [DEF ++ []]
reversa ys = reversa ys ++ reversa []
    [DEF REVERSA []]
reversa ys = reversa ys
    [LÓGICA]
True

--CI xs = (x:xs)
--HI = reversa (xs++ys) = reversa ys ++ reversa xs
xs = (x:xs)
    [ESPECIFICACIÓN]
reversa (x:xs++ys) = reversa ys ++ reversa (x:xs)
    [DEF CONCATENACIÓN]
reversa x:(xs++ys) = reversa ys ++ reversa (x:xs)
    [DEF REVERSA]
reversa (xs++ys)++[x] = reversa ys ++ reversa xs ++ [x]
    [HI]
reversa ys ++ reversa xs ++ [x] = reversa ys ++ reversa xs ++ [x]
    [LÓGICA]
True

--reversa (reversa xs) = xs
--CB xs = []
xs = []
    [ESPECIFICACIÓN]
reversa (reversa []) = []
    [DEF REVERSA]
reversa [] = []
    [DEF REVERSA]
[] = []
    [LÓGICA]
True

--CI xs = (x:xs)
--HI = reversa (reversa xs) = xs
xs = (x:xs)
    [ESPECIFICACIÓN]
reversa (reversa (x:xs)) = x:xs
    [DEF REVERSA]
reversa (reversa xs)++[x] = x:xs
    [HI]
xs++[x] = x:xs
    [DEF CONCATENACIÓN]
x:xs = x:xs
    [LÓGICA]
True

------------------------------------------------------------------------------
--EJERCICIO 3
f :: [a] -> Bool
f = <∀i : 0 <= i <= #xs : xs.0 == xs.i>

--CB xs = []
f.[]
    [ESPECIFICACIÒN]
<∀i : 0 <= i <= #[] : [].0 == [].i>
    [DEF CARDINAL]
<∀i : 0 <= i <= 0 : [].0 == [].i>
    [RANGO VACIO]
True

--CI xs = x:xs
--HI: <∀i : 0 <= i <= #xs : xs.0 = xs.i>
f.(x:xs)
    [ESPECIFICACIÒN]
<∀i : 0 <= i <= #(x:xs) : (x:xs).0 = (x:xs).i>
    [DEF CARDINAL, DEF POSICIÒN(Index o !!)]
<∀i : 0 <= i <= 1+#xs : x = (x:xs).i>
    [LÒGICA]
<∀i : (0 <= i < 1) v (1 <= i <= 1+#xs) : x = (x:xs).i>
    [PARTICIÒN DE RANGO]
<∀i : 0 <= i < 1 : x = (x:xs).i> ∧ <∀j : 1 <= j < 1+#xs : x = (x:xs).j>
    [RANGO UNITARIO, i <- i+1]
x = (x:xs).0 ∧ <∀i : 1 <= i+1 < 1+#xs : x = (x:xs).i+1>
    [ARTIMETICA, DEF POSICIÒN]
x = (x:xs).0 ∧ <∀i : 0 <= i < #xs : x = xs.i>
    [DEF POSICIÒN]
x = x ∧ <∀i : 0 <= i < #xs : x = xs.i>
    [LÒGICA]
<∀i : 0 <= i < #xs : x = xs.i>


    [MODULARIZACIÒN: g.x.xs]
    
    g.z.xs = <∀i : 0 <= i < #xs : z = xs.i>
    --CB xs = []
    g.z.[]
        [ESPECIFICACIÒN]
    <∀i : 0 <= i <= #[] : z == [].i>
        [DEF CARDINAL]
    <∀i : 0 <= i <= 0 : z == [].i>
        [RANGO VACIO]
    True

    --CI xs = (x:xs)
    --HI : <∀i : 0 <= i < #xs : z = xs.i>
    g.z.(x:xs)
        [ESPECIFICACIÒN]
    <∀i : 0 <= i < #(x:xs) : z = (x:xs).i>
        [PARTICIÒN DE RANGO, DEF CARDINAL]
    <∀i : 0 <= i < 1 : z = (x:xs).i> ∧ <∀j : 1 <= j < #1+xs : z = (x:xs).j>
        [RANGO VACIO, i <- i+1, ARITMETICA, DEF POSICIÒN]
    z = x ∧ <∀i : 0 <= i < #xs : z = xs.i>
        [HI]
    z = x ∧ g.z.xs

    [AHORA DEFINIMOS F CON G]

f.[] = True
f.(x:xs) = x ∧ g.x.xs

------------------------------------------------------------------------------
--EJERCICIO 4
f.xs = <∏i : o <= i < #xs : xs.i>
--CB xs = []
f.[]
    [ESPECIFICACIÓN]
<∏i : o <= i < #[] : [].i>
    [DEF CARDINAL]
<∏i : o <= i < 0 : [].i>
    [RANGO VACIO]
1

--CI xs = (x:xs)
--HI = <∏i : o <= i < #xs : xs.i> = f.xs
f.(x:xs)
    [ESPECIFICACIÓN]
<∏i : o <= i < #(x:xs) : (x:xs).i>
    [DEF CARDINAL]
<∏i : o <= i < 1+#xs : (x:xs).i>
    [LÓGICA]
<∏i : (o <= i < 1) v (1 <= i < 1+#xs) : (x:xs).i>
    [PARTICIÓN DE RANGO]
<∏i : (o <= i < 1) : (x:xs).i> * <∏i : (1 <= i < 1+#xs) : (x:xs).i>
    [RANGO UNITARIO]
(x:xs).0 * <∏i : (1 <= i < 1+#xs) : (x:xs).i>
    [i <- i+1]
(x:xs).0 * <∏i : (1 <= i+1 < 1+#xs) : (x:xs).i+1>
    [DEF POSICIÓN]
x * <∏i : (1 <= i+1 < 1+#xs) : xs.i>
    [ARITMETICA (-1 al rango)]
x * <∏i : (0 <= i < #xs) : xs.i>
    [HI]
x * f.xs

--Para cerrar
f.[] = 1
f.(x:xs) = x * f.xs

------------------------------------------------------------------------------
--EJERCICIO 5
f.xs = <∀i : 0 <= i < #xs-1 : xs.i <= xs.(i+1)>

--CB xs = []
f.[]
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #[]-1 : xs.i <= xs.(i+1)>
    [DEF CARDINAL]
<∀i : 0 <= i < -1 : [].i <= [].(i+1)>
    [RANGO VACIO]
True

--CI xs = (x:xs)
--HI = <∀i : 0 <= i < #xs-1 : xs.i <= xs.(i+1)> = f.xs
f.(x:xs)
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #(x:xs)-1 : (x:xs).i <= (x:xs).(i+1)>
    [DEF CARDINAL]
<∀i : 0 <= i < 1+#xs-1 : (x:xs).i <= (x:xs).(i+1)>
    [LÓGICA]
<∀i : (0 <= i < 1) v (1 <= i < 1+#xs-1) : (x:xs).i <= (x:xs).(i+1)>
    [PARTICIÓN DE RANGO]
<∀i : 0 <= i < 1 : (x:xs).i <= (x:xs).(i+1)> ∧ <∀i : 1 <= i < 1+#xs-1 : (x:xs).i <= (x:xs).(i+1)>
    [RANGO UNITARIO]
(x:xs).0 <= (x:xs).(0+1) ∧ <∀i : 1 <= i < 1+#xs-1 : (x:xs).i <= (x:xs).(i+1)>
    [ARITMETICA (x:xs.1), DEF POSICIÓN]
x <= (x:xs).1 ∧ <∀i : 1 <= i < #xs : (x:xs).i <= (x:xs).(i+1)>
    [DEF POSICIÓN]
x <= xs.0 ∧ <∀i : 1 <= i < #xs : (x:xs).i <= xs.i>
    [i <- i+1]
x <= xs.0 ∧ <∀i : 1 <= i+1 < #xs : (x:xs).(i+1) <= xs.(i+1)>
    [DEF POSICIÓN]
x <= xs.0 ∧ <∀i : 1 <= i+1 < #xs : xs.i <= xs.(i+1)>
    [ARITMETICA (-1 al rango)]
x <= xs.0 ∧ <∀i : 0 <= i < #xs-1 : xs.i <= xs.(i+1)>
    [HI]
x <= xs.0 ∧ f.xs

--PARA CERRAR
f.[] = True
f.(x:xs) = x <= xs.0 ∧ f.xs

------------------------------------------------------------------------------
--EJERCICIO 6: sea m una función que devuelva el minimo de una lista dada.
m :: [Num] -> Num
m.xs = <min i : 0 <= i < #xs : xs.i>

--CB xs = []
m.[]
    [ESPECIFICACIÓN]
<min i : 0 <= i < #[] : [].i>
    [DEF CARDINAL]
<min i : 0 <= i < 0 : [].i>
    [RANGO VACIO]
-inf

--CI xs = (x:xs)
--HI = <min i : 0 <= i < #xs : xs.i>
m.(x:xs)
    [ESPECIFICACIÓN]
<min i : 0 <= i < #(x:xs) : (x:xs).i>
    [DEF CARDINAL]
<min i : 0 <= i < 1+#xs : (x:xs).i>
    [LÓGICA]
<min i : (0 <= i < 1) v (1 <= i < 1+#xs) : (x:xs).i>
    [PARTICIÓN DE RANGO]
<min i : 0 <= i < 1 : (x:xs).i> 'min' <min i : 1 <= i <=(x:xs).0
x 'min' <min i : 1 <= i+1 <= 1+#xs : (x:xs).(i+1)>
    [DEF POSICIÓN, ARITMETICA]
x 'min' <min i : 0 <= i <= #xs : xs.i>
    [HI]
x 'min' f.xs

--PARA CERRAR
m.[] = -inf
m.(x:xs) = x 'min' f.xs

------------------------------------------------------------------------------
--EJERCICIO 7: Especificar y derivar que dada una lista determine si existe un
-- elemento de ella que sea igual a la suma del resto de los elementos de la lista
g :: [a] -> Bool
g.xs = <∃n : 0 <= n < #xs : sum xs-(xs.n) = xs.n>

--CB xs = []
g.[]
    [ESPECIFICACIÓN]
<∃n : 0 <= n < #[] : sum []-([].n) = [].n>
    [DEF CARDINAL]
<∃n : 0 <= n < 0 : sum []-([].n) = [].n>
    [RANGO VACIO]
False

--CI xs = (x:xs)
--HI g.xs = <∃n : 0 <= n < #xs : sum xs-(xs.n) = xs.n>
g.(x:xs)
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #(x:xs) : sum (x:xs)-(x:xs).i = (x:xs).i>
    [DEF CARDINAL]
<∃i : 0 <= i < 1+#xs : sum (x:xs)-(x:xs).i = (x:xs).i>
    [LÓGICA]
<∃i : (0 <= i < 1) v (1 <= i < 1+#xs) : sum (x:xs)-(x:xs).i = (x:xs).i>
    [PARTICIÓN DE RANGO]
<∃i : 0 <= i < 1 : sum (x:xs)-(x:xs).i = (x:xs).i> v <∃i : 1 <= i < 1+#xs : sum (x:xs)-(x:xs).i = (x:xs).i>
    [RANGO UNITARIO]
sum (x:xs)-(x:xs).0 = (x:xs).0 v <∃i : 1 <= i < 1+#xs : sum (x:xs)-(x:xs).i = (x:xs).i>
    [DEF CARDINAL]
sum (x:xs)-x = x v <∃i : 1 <= i < 1+#xs : sum (x:xs)-(x:xs).i = (x:xs).i>
    [DEF SUM, ARITMETICA]
sum xs = x v <∃i : 1 <= i < 1+#xs : x+sum xs-(x:xs).i = (x:xs).i>
    [i <- i+1]
sum xs = x v <∃i : 1 <= i+1 < 1+#xs : x+sum xs-(x:xs).(i+1) = (x:xs).(i+1)>
    [ARITMETICA]
sum xs = x v <∃i : 0 <= i < #xs : x+sum xs-xs.i = xs.i>

    GENERALIZACIÓN
    g.z.xs = <∃i : 0 <= i < #xs : z+sum xs-xs.i = xs.i>
    
    --CB xs = []
    g.z.[]
        [ESPECIFICACIÓN]
    <∃i : 0 <= i < #[] : z+sum []-[].i = [].i>
        [DEF CARDINAL]
    <∃i : 0 <= i < 0 : z+sum []-[].i = [].i>
        [RANGO VACIO]
    False

    --CI xs = (x:xs)
    --HI g.z.xs = <∃i : 0 <= i < #xs : z+sum xs-xs.i = xs.i>
    g.z.(x:xs)
        [ESPECIFICACIÓN]
    <∃i : 0 <= i < #(x:xs) : z+sum (x:xs)-(x:xs).i = (x:xs).i>
        [DEF CARDINAL]
    <∃i : 0 <= i < 1+#xs : z+sum (x:xs)-(x:xs).i = (x:xs).i>
        [LÓGICA]
    <∃i : (0 <= i < 1) v (1 <= i < 1+#xs) : z+sum (x:xs)-(x:xs).i = (x:xs).i>
        [PARTICIÓN DE RANGO]
    <∃i : 0 <= i < 1 : z+sum (x:xs)-(x:xs).i = (x:xs).i> v <∃i : 1 <= i < 1+#xs : z+sum (x:xs)-(x:xs).i = (x:xs).i>
        [RANGO UNITARIO]
    z+sum (x:xs)-(x:xs).0 = (x:xs).0 v <∃i : 1 <= i < 1+#xs : z+sum (x:xs)-(x:xs).i = (x:xs).i>
        [DEF SUM, DEF CARDINAL]
    z+x+sum xs-x = x v <∃i : 1 <= i < 1+#xs : z+sum (x:xs)-(x:xs).i = (x:xs).i>
        [ARITMETICA]
    z+sum xs = x v <∃i : 1 <= i < 1+#xs : z+sum (x:xs)-(x:xs).i = (x:xs).i>
        [i <- i+1]
    z+sum xs = x v <∃i : 1 <= i+1 < 1+#xs : z+sum (x:xs)-(x:xs).(i+1) = (x:xs).(i+1)>
        [ARITMETICA]
    z+sum xs = x v <∃i : 0 <= i < #xs : z+sum (x:xs)-(x:xs).(i+1) = (x:xs).(i+1)>
        [DEF POSICIÓN, DEF SUM]
    z+sum xs = x v <∃i : 0 <= i < #xs : z+x+sum xs - xs.i = xs.i>
        [ARITMETICA]
    z+sum xs = x v <∃i : 0 <= i < #xs : (z+x) + sum xs - xs.i = xs.i>
        [HI]
    z+sum xs = x v g.(z+x).xs

    g.[] = False
    g.(x:xs) = (z+sum xs = x) v g.(z+x).xs

    [VOLVEMOS AL PROBLEMA ORIGINAL]

f.[] = False
f.(x:xs) = (0+sum xs = x) v g.(0+x).xs

------------------------------------------------------------------------------
--EJERCICIO 8: Dada f : Nat -> Bool y suponiendo que ∃n : 0 <= n : f.n
-- especificar y derivar una función que encuentre el mínimo natural x tal que f.x
-- ES DECIR: Encuentra el minimo n que cumpla con la condición f
g :: (Nat -> Bool) -> Nat -> Nat
g.n = <min i : n <= i ∧ f.i: i>

--SE RESUELVE USANDO CAMBIO DE VARIABLES, PAG. 193
g.n
    [ESPECIFICACIÓN]
<min i : n <= i ∧ f.i : i>
    [PARTICIÓN DE RANGO]
<min i : n = i ∧ f.i : i> 'min' <min i : n+1 <= i ∧ f.i : i>
    [LEIBNITZ]
<min i : n = i ∧ f.i : i> 'min' <min i : n+1 <= i ∧ f.i : i>
    [HI]
<min i : n = i ∧ f.i : i> 'min' g.(n+1)
--AHORA SE HACE NECESARIO UN ANALISIS POR CASOS DE ACUERDO AL VALOR DE F.N.
--EL CASO EN QUE EL PREDICADO ES CIERTO SE TRANSFORMARA EN EL CASO BASE DE F.

--CB f.n
<min i : n = i ∧ f.i : i> 'min' g.(n+1)
    [RANGO UNITARIO]
n 'min' g.(n+1)
    [n <= g.(n+1)]
n

--CI -f.n
<min i : n = i ∧ False : i> 'min' g.(n+1)
    [RANGO VACIO]
+inf min g.(n+1)
    [NEUTRO DEL MIN]
g.(n+1)

------------------------------------------------------------------------------
--EJERCICIO 9: Dadas dos listas determinar si la primera es subseg. de la segunda
p :: [a] -> [a] -> Bool
p.xs.ys = <∃as,bs :: ys = as++xs++bs>

--CB xs = []
p.xs.[]
    [ESPECIFICACIÓN]
<∃as,bs :: [] = as++xs++bs>
    [DEF CONCATENACIÓN]
<∃as,bs :: [] = as++xs++bs>
    [LÓGICA]
False

--CB ys = []
p.[].ys
    [ESPECIFICACIÓN]
<∃as,bs :: ys = as++[]++bs>
    [DEF CONCATENACIÓN]
<∃as,bs :: ys = as++[]++bs>
    [LÓGICA]
False

--CI xs = x:xs, ys = y:ys
--HI p.xs.ys = <∃as,bs :: ys = as++xs++bs>
p.(x:xs).(y:ys)
    [ESPECIFICACIÓN]
<∃as,bs :: y:ys = as++(x:xs)++bs>
    [DEF CONCATENACIÓN]
<∃as,bs :: [y]++ys = [x]++as++xs++bs>

    MODULARIZACIÓN

------------------------------------------------------------------------------
--EJERCICIO 10
sum xs = <∑n : 0 <= n < #xs : xs.n>
cont xs = <Ni : 0 <= i < #xs : 1>

prom xs = <(sum xs, cont xs)>

prom :: [Int] -> (Int, Int)
prom [x] = (x, 1)
prom (x:xs) = (x+a, 1+b)
    where (a, b) = prom xs

--CB xs = [x]
prom.[x]
    [ESPECIFICACIÓN]
<(sum [x], cont [x])>
    [DEF SUM, DEF CONT]
(x, 1)

--CB xs = []
prom.[]
    [ESPECIFICACIÓN]
<(sum [], cont [])>
    [DEF SUM, DEF CONT]
(0, 0)

--CI xs = (x:xs)
--HI prom.(x:xs) = prom.xs
prom.(x:xs)
    [ESPECIFICACIÓN]
<(sum (x:xs), cont (x:xs))>
    [DEF SUM, DEF CONT]
<(x+sum xs, 1+cont xs)>
    [VARIABLES LOCALES INTRODUCCIÓN]
<(x+a, 1+b)>
    [(a,b) = (sum xs, cont xs)]
(x+a, 1+b)
    [HI]
(a,b) = prom xs