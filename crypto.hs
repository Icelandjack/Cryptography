{-# LANGUAGE  BangPatterns #-}

-- First comment!

module Main where

import System.Random
import Text.Printf
import Control.Monad
import Test.QuickCheck
import Control.DeepSeq
import System.IO

data ParameterTuple = ParameterTuple Integer Integer Integer deriving Show

-- Smart constructor for ParameterTuple

parameterTuple :: Integer -> Integer -> Integer -> Maybe ParameterTuple
parameterTuple p q g
  | and [isPrime p,             -- p and q must be prime
         isPrime q,
         p `bitNumber` 1024,    -- p must be a 1024-bit number
         q `bitNumber` 160,     -- q must be a 160-bit number
         q `isDivisor` (p-1),   -- q is a divisor of p-1
         (g `hasOrder` q) p]    -- g has order q
         = Just (ParameterTuple p q g)
  | otherwise = Nothing


q `bitNumber` bits = 0 <= q && q < 2^(bits)
q `isDivisor` p = p `mod` q == 0
(g `hasOrder` q) p = g > 1 && powm g q p 1 == 1

-- TODO: Implement
isPrime p = True

type PubKey = Integer

type Keypair = (Integer, PubKey)

type Message = Integer
type Signature = (Integer, Integer)

data Accepted = ValidSignature | InvalidSignature 

instance Show Accepted where
  show ValidSignature   = "signature_valid"
  show InvalidSignature = "signature_invalid"

type SecretNumber = Integer

-- Computation of inverse value (Appendix C.1)
-- multInv a n ≡ a⁻¹ mod n
multInv :: Integer -> Integer -> Integer
multInv a n = case gcdE n a of
  (1, s, t) -> (t + n) `mod` n
  _         -> error "No inverse exists"

powm :: Integer -> Integer -> Integer -> Integer -> Integer
powm b 0 m r = r
powm b e m r | e `mod` 2 == 1 = powm (b * b `mod` m) (e `div` 2) m (r * b `mod` m)
powm b e m r = powm (b * b `mod` m) (e `div` 2) m r

prop_multInv (Positive a) (Positive n) = coprime a n && a > 1 && n > 1 ==> let
  inverse = multInv a n
  in inverse == 0 || inverse * a == 1

coprime a n = (a `gcd` n) == 1

prop_between (Positive a) (Positive mod) =
  coprime a mod ==> let
    inverse = (a `multInv` mod)
    in inverse == 0 || 0 < inverse && inverse < mod

gcdE' a 0 = (a, 1, 0)
gcdE' a b = (d, t, s - q*t) where
  (q, r)    = a `quotRem` b
  (d, s, t) = gcdE' b r

gcdE :: Integral a => a -> a -> (a, a, a)
gcdE a b = (d, u, v)
  where
    (d, x, y) = eGCD 0 1 1 0 (abs a) (abs b)
    u | a < 0     = negate x
      | otherwise = x
    v | b < 0     = negate y
      | otherwise = y
    eGCD !n1 o1 !n2 o2 r s
      | s == 0    = (r, o1, o2)
      | otherwise = case r `quotRem` s of
                      (q, t) -> eGCD (o1 - q*n1) n1 (o2 - q*n2) n2 s t

-- TODO: Use a new key if either r = 0 or s = 0.
sign :: ParameterTuple -> Keypair -> Message -> [SecretNumber] -> Signature
sign (ParameterTuple p q g) (x, y) msg ks = (r, s) where
  k = head ks
  r = (powm g k p 1) `mod` q
  z = msg
  s = ((k `multInv` q) * (z + x * r `mod` q)) `mod` q

verify :: ParameterTuple -> PubKey -> Message -> Signature -> Accepted
verify (ParameterTuple p q g) y msg sig@(r, s)
  | not (0 < r && r < q) = InvalidSignature
  | not (0 < s && s < q) = InvalidSignature
  | otherwise            = if v == r
                           then ValidSignature
                           else InvalidSignature
    where
        w  = s `multInv` q
        z  = msg
        u₁ = (z*w) `mod` q
        u₂ = (r*w) `mod` q
        v  = ((powm g u₁ p 1) * (powm y u₂ p 1) `mod` p) `mod` q

main = do
  hSetBuffering stdout LineBuffering

  'p':'=':p' <- getLine
  'q':'=':q' <- getLine
  'g':'=':g' <- getLine

  let p, q, g :: Integer
      [p, q, g] = map read [p', q', g']

  case parameterTuple p q g of
    Nothing -> invalid
    Just param  -> do
      valid
      action <- getLine
      case action of
        "genkey" -> genkeys param
        "sign"   -> signFromInput param
        "verify" -> verifyFromInput param
        
  where
    invalid = putStrLn "invalid_group"
    valid   = putStrLn "valid_group"

    genkeys param = do
      'n':'=':n <- getLine
      replicateM_ (read n) (genkey param)

    genkey (ParameterTuple p q g) = do
      x <- genPrivateKey q

      let y = powm g x p 1

      printf "x=%d\n" x
      printf "y=%d\n" y
      
    signFromInput param = do
      'x':'=':x <- getLine
      'y':'=':y <- getLine
      foo <- getContents
      mapM_ (generateSignature param (read x, read y)) (lines foo)

    generateSignature param keypair ('D':'=':d) = do

      seed <- getStdGen

      let digest = read $ "0x" ++ d

      let signature@(r, s) = sign param keypair digest (map abs (randoms seed))


      printf "r=%d\n" r
      printf "s=%d\n" s
    
    verifyFromInput param = do
      'y':'=':y <- getLine

      input <- getContents
      mapM_ (verifySingleInput param y) (chunk3 (lines input))

    verifySingleInput param@(ParameterTuple p q g) publicKey inputs = case inputs of
      ['D':'=':digest,
       'r':'=':r,
       's':'=':s] -> do
         
       
         let signature = verify param (read publicKey) (read $ "0x" ++ digest) (read r, read s)
         print signature

    chunk3 (a:b:c:rest) = [a,b,c]:chunk3 rest
    chunk3 _ = []


-- x is the private key which must remain secret
-- It is a (pseudo)randomly generated Integer s.t. 0 < x < q: [1, q-1]
genPrivateKey :: Integer -> IO Integer
genPrivateKey q = randomRIO (1, q-1)

chunk3 (a:b:c:rest) = [a,b,c]:chunk3 rest
chunk3 _ = []


p=102865584259843077175583195011997798900482038016705824136288380475734860009055428071534495956844807748416572686838253895244634687898659646424515259679129905513743899853971066468883670407530107234961085482225328667572772611162756643027105617873895021996158552984843708233824989792811721408577351617080369547993
q=734415599462729831694143846331445277609193755927
g=63615006880335642768473038477258757436464860136916565207798584167060621564899979263408565137993978149206751054438974059615983337126379668370747907507911540381031959187353048278562320341063050939775344313271013777131358834376209974551749493023310606751625276738876397935042130121966817767949476523717161640453

Just param = parameterTuple p q g

y=1099906791313925528746008054081768734007884349815325963667520491768596235922636596649198172987598573083011790017146356061273962023338014420645127092468263770753970716461208880423045761205934804880887634821616587683235765408867072852094816664326084550730344050243082288308837441908172297994552279650972016922
digest=read "0x10B4D55F2376DBA00CE4A6AE2B122E9554035EF2" :: Integer
r=497727687827108870230917469165124644171957997527
s=69924200561536940344114164706214298822631922629
signature = (r, s)