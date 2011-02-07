{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

-- | ParserSharingSimple is a simple parsing library which was extending to allow sharing.
-- I have 'published' this library so that the user can understand the basic principle of how
-- the library works without sharing and then to move to the shared version.
-- Marcelo Sousa, Utrecht University 2011.                        
module ParserSharingSimple where

infixl 5 `Seq`
infixr 3 `Alt`
 
{- | 
  A 'Parser' is defunctionalized with a GADT where the constructors represent
  the normal parsers combinators. The default token type is 'Char'.
  I've also added here the constructor 'Sat'.
-}
data Parser :: * -> * where
	 Sym     ::  Char                        -> Parser Char
	 Ret     ::  a                           -> Parser a  
	 Seq     ::  Parser (b->a)   -> Parser b -> Parser a
	 Alt     ::  Parser a        -> Parser a -> Parser a
	 Sat     ::  (Char->Bool)                -> Parser Char

{- | 
  Continuations are represented by 'Pending' which in the simple case is either 'Done' when there
  are no more parsers to process or a 'Stack' of parsers.
-}
data Pending :: * -> * where
	 Stack   ::  Parser a  -> Pending b -> Pending (a,b)
	 Done    ::                            Pending ()
	
type States a = [State a] 
{- | 'State' is an existential type that contains a semantic function that 
receive a cartesian product of the results of the parsers and applies them according
to their semantics. 
-}
data State a = forall b. State  (b -> a) (Pending b)

-- | 'runParser' is the main function which the user has to invoke.
runParser :: Parser a -> [Char] -> [a]
runParser p = parse [State fst (Stack p Done)]

-- | 'parse' is the iteratee that consumes input and updates the state by calling 'transition'.	
parse :: States a -> [Char] -> [a]
parse  states []     = evalStates states
parse  states (x:xs) = (transition states x) `parse` xs            


-- | 'evalStates' triggers evaluation of the success functions. In that sense the process is not completely online.
-- The functions is a bit more complicated than what it should be because of 'Ret'.
-- Notice that in case of failure the state is discarded.       
evalStates :: States a -> [a]
evalStates [] = []
evalStates ((State f Done):st)  = (f ()):evalStates st
evalStates ((State f (Stack (Ret s) Done)):st) = (f (s,())):evalStates st
evalStates ((State f (Stack (Alt (Ret s) (Ret r)) Done)):st) = (f (s,())):(f (r,())):evalStates st
evalStates ((State f (Stack (Alt (Ret s) _) Done)):st) = (f (s,())):evalStates st
evalStates ((State f (Stack (Alt _ (Ret r)) Done)):st) = (f (r,())):evalStates st 
evalStates (_:st) = evalStates st

-- | 'transition' unfold the top of the stack until we have a 'Sym' or 'Done and then calls 'reduce'.
transition :: States a -> Char -> States a
transition states char = let unFoldNtStates = concat (map unFoldNtAtHeads states)
                         in  foldl (reduce char) [] unFoldNtStates
 
-- | 'reduce' consumes the token when the 'States' are unfolded to a point where on top of the 'Stack' we 
-- have a 'Sym' or the pending is 'Done'.
reduce :: Char -> States a -> State a -> States a
reduce char states (State f (Stack (Sym c) rest)) | c == char = (State (\rest -> f (char, rest)) rest):states
                                                  | otherwise = states
reduce char states (State f (Stack (Sat s) rest)) | s char    = (State (\rest -> f (char, rest)) rest):states
                                                  | otherwise = states
reduce _    states _ = states
 
-- | 'unFoldNtAtHeads' pattern-matches on the top of the 'Pending' and it's either a 'reduce' state does not change it. 
-- If there is a 'Ret' on the top of the 'Stack' it will put the value on top of stack represented by the cartesian product 
-- and use that as argument to the semantic function.
-- If there is a 'Seq' on top of the 'Stack' it will unfold it into a new 'Stack' and it will apply the result function of the first parser 
-- to the result value of the second one and wrap that value into a pair that is the argument of the overall semantic function.
-- If there is a 'Alt' on top of the 'Stack' it will simply create two states out of it.
-- Note that 'unFoldNtAtHeads' is being recursively called until we can't unFold anymore.
unFoldNtAtHeads :: State a -> States a
unFoldNtAtHeads s@(State r  Done               )     = [s]
unFoldNtAtHeads s@(State r  (Stack (Sym c) rest))    = [s]
unFoldNtAtHeads s@(State r  (Stack (Sat c) rest))    = [s]
unFoldNtAtHeads   (State r  (Stack (Ret f) rest))    = unFoldNtAtHeads (State (\rest -> r (f, rest)) rest)
unFoldNtAtHeads   (State r  (Stack (Seq p q) rest))  = unFoldNtAtHeads (State (\(pr,(qr, rest)) -> r ((pr qr), rest)) (Stack p (Stack q rest))) 
unFoldNtAtHeads   (State r  (Stack (Alt p q) rest))  = let statesp = unFoldNtAtHeads $ State r (Stack p rest)
                                                           statesq = unFoldNtAtHeads $ State r (Stack q rest)
                                                       in statesp ++ statesq         
