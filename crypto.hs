module Main where

import Control.Applicative ((<$>))
import Control.Monad       (replicateM_)
import System.IO           (hSetBuffering, stdout, BufferMode(LineBuffering))
import System.IO.Unsafe    (unsafePerformIO)
import System.Random       (newStdGen, getStdGen, randomRIO, randomRs, randoms)
import Text.Printf         (printf)

data ParameterTuple = ParameterTuple {
     p :: Integer, q :: Integer, g :: Integer
  } deriving Show

type PubKey       = Integer
type Keypair      = (Integer, PubKey)
type Message      = Integer
type Signature    = (Integer, Integer)
type SecretNumber = Integer

data Accepted = ValidSignature | InvalidSignature 

instance Show Accepted where
  show ValidSignature   = "signature_valid"
  show InvalidSignature = "signature_invalid"

-- Smart constructor for ParameterTuple
parameterTuple :: Integer -> Integer -> Integer -> Maybe ParameterTuple
parameterTuple p q g
  | and [g < p,
         p `bitNumber` 1024,    -- p must be a 1024-bit number
         q `bitNumber` 160,     -- q must be a 160-bit number
         q `isDivisor` (p-1),   -- q is a divisor of p-1
         (g `hasOrder` q) p,    -- g has order q
         isPrime p,             -- p and q must be prime
         isPrime q] = Just (ParameterTuple p q g)
  | otherwise       = Nothing

-- (q `bitNumbers` bits) returns True if ‘q’ has has between ‘bits-1’
-- and ‘bits’ bits.
bitNumber :: Integer -> Integer -> Bool
q `bitNumber` bits = 2^(bits-1) < q && q < 2^bits

isDivisor :: Integer -> Integer -> Bool
q `isDivisor` p = p `mod` q == 0

hasOrder :: Integer -> Integer -> Integer -> Bool
(g `hasOrder` q) p = g > 1 && powerMod g q p == 1

-- Computation of inverse value (Appendix C.1)
-- modInv a n ≡ a⁻¹ mod n
modInv :: Integer -> Integer -> Integer
modInv a n = case gcdE n a of
  (1, s, t) -> (t + n) `mod` n
  _         -> error "modInv: No inverse exists"

-- Taken from slides.
gcdE :: Integer -> Integer -> (Integer, Integer, Integer)
gcdE a 0 = (a, 1, 0)
gcdE a b = (d, t, s - q*t) where
  (q, r)    = a `quotRem` b
  (d, s, t) = gcdE b r

-- x is the private key which must remain secret
-- It is a (pseudo)randomly generated Integer s.t. 0 < x < q: [1, q-1]
genPrivateKey :: Integer -> IO Integer
genPrivateKey q = randomRIO (1, q-1)

-- Signs message.
sign :: ParameterTuple -> Keypair -> Message -> [SecretNumber] -> Signature
sign param@(ParameterTuple p q g) (x, y) z (k:ks)
  | r == 0 || s == 0 = sign param (x, y) z ks
  | otherwise        = (r, s)
  where
    r, s :: Integer 
    r = (powerMod g k p) `mod` q

    s = ((k `modInv` q) * (z + x * r `mod` q)) `mod` q

-- Verifies signature.
verify :: ParameterTuple -> PubKey -> Message -> Signature -> Accepted
verify (ParameterTuple p q g) y z sig@(r, s)
  | and [ 0 < r, r < q,
          0 < s, s < q,
          v == r] = ValidSignature
  | otherwise     = InvalidSignature
    where
        u₁, u₂, w, v :: Integer
        (u₁, u₂) = ((z*w) `mod` q, (r*w) `mod` q)
        
        w        = s `modInv` q
        
        v        = ((powerMod g u₁ p) * (powerMod y u₂ p) `mod` p) `mod` q

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering

  -- Form parameter tuple.
  'p':'=': p <- getLine
  'q':'=': q <- getLine
  'g':'=': g <- getLine

  let param = parameterTuple (read p) (read q) (read g) 

  case param of
    Nothing     -> putStrLn "invalid_group"
    Just param  -> do
      putStrLn "valid_group"
      action <- getLine
      case action of
        "genkey" -> genkeys         param
        "sign"   -> signFromInput   param
        "verify" -> verifyFromInput param

  where

    genkeys param = do
      'n':'=': n <- getLine
      replicateM_ (read n) (genkey param)

    genkey (ParameterTuple p q g) = do
      x <- genPrivateKey q
      
      let y = powerMod g x p

      printf "x=%d\n" x
      printf "y=%d\n" y
      
    signFromInput param = do
    
      'x':'=': x <- getLine
      'y':'=': y <- getLine
      input      <- lines <$> getContents
      
      mapM_ (generateSignature param (read x, read y)) input

    generateSignature param keypair ('D':'=':d) = do

      seed <- getStdGen

      let digest = readHex d

      let signature@(r, s) = sign param keypair digest (map abs (randoms seed))

      printf "r=%d\n" r
      printf "s=%d\n" s
    
    verifyFromInput param = do
      'y':'=': y <- getLine
      input      <- lines <$> getContents
      
      mapM_ (verifySingleInput param y) (chunk3 input)

    verifySingleInput param@(ParameterTuple p q g) publicKey inputs = case inputs of
      ['D':'=':d,
       'r':'=':r,
       's':'=':s] -> do

         let digest    = readHex d
             signature = verify param (read publicKey) digest (read r, read s)
         print signature

    chunk3 :: [a] -> [[a]]
    chunk3 (a:b:c:rest) = [a,b,c]:chunk3 rest
    chunk3 _            = []

    readHex :: String -> Integer
    readHex digest = read ("0x" ++ digest)


-- Some QuickCheck

-- prop_modInv (Positive a) (Positive n) = coprime a n && a > 1 && n > 1 ==> let
--   inverse = modInv a n
--   in inverse == 0 || inverse * a == 1

-- coprime a n = (a `gcd` n) == 1

-- prop_between (Positive a) (Positive mod) =
--   coprime a mod ==> let
--     inverse = (a `modInv` mod)
--     in inverse == 0 || 0 < inverse && inverse < mod

-- Taken from: http://rosettacode.org/wiki/Miller-Rabin_primality_test#Haskell

-- Miller-Rabin wrapped up as an (almost deterministic) pure function
isPrime :: Integer -> Bool
isPrime n = unsafePerformIO (isMillerRabinPrime 100 n)

isMillerRabinPrime :: Int -> Integer -> IO Bool
isMillerRabinPrime k n
   | even n    = return (n == 2)
   | n < 100   = return (n `elem` primesTo100)
   | otherwise = do ws <- witnesses k n
                    return $ and [test n (pred n) evens (head odds) a | a <- ws]
  where
    (evens, odds) = span even (iterate (`div` 2) (pred n))
 
primesTo100 :: [Integer]
primesTo100 = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]

test :: Integer -> Integer ->  [Integer] -> Integer -> Integer -> Bool
test n n_1 evens d a = x `elem` [1,n_1] || n_1 `elem` powers 
  where
    x      = powerMod a d n
    powers = map (\g -> powerMod a g n) evens
 
witnesses :: Int -> Integer -> IO [Integer]
witnesses k n 
  | n < 9080191         = return [31,73]
  | n < 4759123141      = return [2,7,61]
  | n < 3474749660383   = return [2,3,5,7,11,13]
  | n < 341550071728321 = return [2,3,5,7,11,13,17]
  | otherwise           = do g <- newStdGen
                             return $ take k (randomRs (2,n-1) g)

-- powerMod x n m = x^n `mod` m
powerMod :: Integer -> Integer -> Integer -> Integer
powerMod x n m = f (n - 1) x x `rem` m 
  where
  f d a y = if d == 0 then y else g d a y 
  g i b y | even i    = g (i `quot` 2) (b*b `rem` m) y
          | otherwise = f (i-1) b (b*y `rem` m)
