module Crypto where

import System.Random
import Control.Monad.State
import Control.Monad.Identity
import Text.Printf

class Monad m => MonadRandom m where
  getRandom :: Random a => m a

newtype RandT g m a = RandT (StateT g m a) 

newtype Rand g a = Rand (RandT g Identity a) 

evalRandT :: (Monad m, RandomGen g) => RandT g m a -> g -> m a
evalRandT (RandT x) g = evalStateT x g

evalRand :: (RandomGen g) => Rand g a -> g -> a
evalRand (Rand x) g = runIdentity (evalRandT x g)

l = 1024
n = 160

p = 102865584259843077175583195011997798900482038016705824136288380475734860009055428071534495956844807748416572686838253895244634687898659646424515259679129905513743899853971066468883670407530107234961085482225328667572772611162756643027105617873895021996158552984843708233824989792811721408577351617080369547993
q = 734415599462729831694143846331445277609193755927
g = 63615006880335642768473038477258757436464860136916565207798584167060621564899979263408565137993978149206751054438974059615983337126379668370747907507911540381031959187353048278562320341063050939775344313271013777131358834376209974551749493023310606751625276738876397935042130121966817767949476523717161640453

data ParameterTuple = ParameterTuple Integer Integer Integer deriving Show

parameterTuple p q g
  -- p must be prime
  | not (isPrime p) = Nothing
  
  -- q must be prime
  | not (isPrime q) = Nothing
  
  -- p must be a 1024-bit number
  | not (p `bitNumber` 1024) = Nothing

  -- q must be a 160-bit number
  | not (q `bitNumber` 160) = Nothing
  | otherwise = Just (ParameterTuple p q g)

q `bitNumber` bits = 0 <= q && q < 2^160

isPrime p = True

type PubKey = Integer

type Keypair = (Integer, PubKey)

type Message = Integer
type Signature = (Integer, Integer)

data Accepted = ValidSignature | InvalidSignature

type SecretNumber = Integer

-- Computation of inverse value (Appendix C.1)
-- multInv a n ≡ a⁻¹ mod n
multInv :: Integer -> Integer -> Integer
multInv a n = case gcdE n a of
  (1, s, t) -> t
  _         -> error "No inverse exists"

gcdE a 0 = (a, 1, 0)
gcdE a b = (d, t, s - q*t) where
  (q, r)    = a `divMod` b
  (d, s, t) = gcdE b r

sign :: ParameterTuple -> Keypair -> Message -> [SecretNumber] -> Signature
sign (ParameterTuple p q g) (x, y) msg ks = (r, s) where
  k = head ks
  r = (g^k `mod` p) `mod` q
  z = msg
  s = (k `multInv` q) * (z + x * r `mod` q)

verify :: ParameterTuple -> PubKey -> Message -> Signature -> Accepted
verify (ParameterTuple p q g) y msg sig@(r, s)
  | 0 < r && r < q = InvalidSignature
  | 0 < s && s < q = InvalidSignature
  | otherwise      = if v == r
                     then ValidSignature
                     else InvalidSignature
    where
        w  = s `multInv` q
        z  = msg
        u₁ = z*w `mod` q
        u₂ = r*w `mod` q
        v  = ((g^u₁)*(y^u₂) `mod` p) `mod` q

main = do
  'p':'=':p' <- getLine
  'q':'=':q' <- getLine
  'g':'=':g' <- getLine

  let p, q, g :: Integer
      [p, q, g] = map read [p', q', g']

  printf "You entered:\n  %d\n  %d\n  %d\n" p q g

  case parameterTuple p q g of
    Nothing -> invalid
    Just x  -> do
      valid
      action <- getLine
      case action of
        "genkey" -> genkeys parameterTuple
        "sign"   -> signFromInput parameterTuple
        "verify" -> verifyFromInput parameterTuple
        
      -- "genkey"  <- getLine
      -- 'n':'=':n <- getLine
      -- printf "I'm going to generate %d keypairs\n" (read n :: Int)
  where
    invalid = putStrLn "invalid_group"
    valid   = putStrLn "valid_group"

    genkeys p = do
      'n':'=':n <- getLine
      replicateM_ (read n) genkey

    genkey = do
      putStrLn "x=..."
      putStrLn "y=..."
      
    signFromInput p = do
      'x':'=':x <- getLine
      'y':'=':y <- getLine
      foo <- getContents
      mapM_ (generateSignature (x, y)) (lines foo)

    generateSignature (x, y) ('D':'=':digest) = do
      putStrLn "r=..."
      putStrLn "s=..."
    
    verifyFromInput p = do
      'y':'=':y <- getLine

      input <- getContents
      mapM_ (verifySingleInput y) (chunk3 (lines input))

    verifySingleInput y inputs = case inputs of
      ['D':'=':digest,
       'r':'=':r,
       's':'=':s] -> do putStrLn "signature_invalid"

    chunk3 (a:b:c:rest) = [a,b,c]:chunk3 rest
    chunk3 _ = []


chunk3 (a:b:c:rest) = [a,b,c]:chunk3 rest
chunk3 _ = []
