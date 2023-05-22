import qualified Data.Set as Set

pls xs ys = (head xs + head ys) : (pls (tail xs) (tail ys))

onetwos = 1 : 2 : onetwos

mytail xs = head (tail xs) : mytail (tail xs)

-- stalls
sA = 1 : tail sA

everyOther xs = head xs : everyOther (tail (tail xs))

-- stalls
sB = 1 : everyOther sB

fibA = 0 : pls (1 : fibA) fibA
fibB = pls (0 : 1 : fibA) (0 : fibA)

prd xs ys = (head xs * head ys) : (pls (prd xs (tail ys)) (prd (tail xs) ys))
exp2 xs = (2 ^ head xs) : (prd (tail xs) (exp2 xs))

facA = prd (1 : facA) (1 : facA)
facB = exp2 (0 : facB)

sup_set x = if Set.null x then 0 else Set.findMax x
sup x = sup_set (Set.map head x) : (sup (Set.map tail x)) 

prd' xs ys = (head xs * head ys) : (prd (prd xs (tail ys)) (pls (tail xs) ys))

data Tree = Node {val :: Int, sub :: [Tree]}

plsT t u = Node (val t + val u) (map (uncurry plsT) (zip (sub t) (sub u)))
prdT t u = Node (val t * val u) (map (\(t',u') -> plsT (prdT t u') (prdT t' u)) (zip (sub t) (sub u)))

primes m n =
  if (m == 0 && n > 1) || gcd m n == 1
  then n : primes (m * n) (n + 1)
  else primes m (n + 1)

facC n a i =
  if i == 0
  then a : facC (n + 1) 1 (n + 1)
  else facC n (a * i) (i - 1)

catalan n
  | n > 0 = pls (catalan (n - 1)) (0 : catalan (n + 1))
  | otherwise = 1 : catalan 1
