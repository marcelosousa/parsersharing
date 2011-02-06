{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module ParserSharing where
	                
import Foreign.StablePtr
import Unsafe.Coerce
import Foreign
import Data.List      
import Debug.Trace             

infixl 5 `Seq`
infixr 3 `Alt`

{- | 
  A 'parser' is defunctionalized with a GADT where the constructors represent
  the normal parsers combinators. The default 'Token' type is Char.
-}
data Parser :: * -> * where
	 Sym     ::  Char                               -> Parser Char 
	 Seq     ::  Parser (b->a)   -> Parser b        -> Parser a
	 Alt     ::  Parser a        -> Parser a        -> Parser a
	 Ret     ::  a                                  -> Parser a
	 Sat     ::  (Char->Bool)                       -> Parser Char

data Pending :: * -> * where
	 Stack     ::  Parser p   -> Pending r  -> Pending (p,r)
	 Split     ::  Pending r1 -> Pending r2 -> Pending (Either r1 r2)
	 LazyShare ::  Parser p   -> Pending r  -> Pending (Share p r)
	 Done      ::                              Pending ()
                               
data Share p r where
	Share :: p -> r -> Share p r
	
type States a = [State a]
data State a  = forall b. State (Func b a) (Pending b)

data Func b a where
	Sem :: [(b -> a)] -> Func b a                                    

instance Eq (Parser a) where
	 p == q = case p `eq` q of
		           Nothing -> False
		           Just Eq -> True
	
castParser :: Parser a -> IO (StablePtr (Parser b))
castParser p = do sptr <- newStablePtr p
                  return $ castPtrToStablePtr $ castStablePtrToPtr sptr

data Equal :: * -> * -> * where
	Eq :: Equal a a                              

eq :: Parser a -> Parser b -> Maybe (Equal a b)
eq p q = let pptr = unsafePerformIO $ castParser p
             qptr = unsafePerformIO $ newStablePtr q
         in if pptr == qptr
	           then Just $ unsafeCoerce Eq
	           else Nothing
                           
termination :: States a -> Bool
termination xs = all isFolded xs
                                        
isFolded :: State a -> Bool
isFolded (State r Done)                 = True
isFolded (State r (Stack (Sym c) rest)) = True
isFolded _                              = False	
                              
unFoldAndMerge :: States a -> States a
unFoldAndMerge states | termination states = states
					  | otherwise          = let unSplittedStates = concatMap unFoldSplitAtHead states
					                             unSharedStates   = unFoldShareAtHeads unSplittedStates
					                             stableStates     = map unFoldRetAtHead unSharedStates
					                         in  unFoldAndMerge $ unFoldNtAtHeads stableStates

transition :: States a -> Char -> States a
transition states char = let unFoldNtStates  = unFoldAndMerge states
					     in  foldl (reduce char) [] unFoldNtStates	 	

reduce :: Char -> States a -> State a -> States a
reduce char states (State (Sem fs) (Stack (Sym c) rest)) | c == char = (State (Sem (map (\f -> \rest -> f (char, rest)) fs)) rest):states
                                                         | otherwise = states
reduce char states (State (Sem fs) (Stack (Sat s) rest)) | s char    = (State (Sem (map (\f -> \rest -> f (char, rest)) fs)) rest):states
                                                         | otherwise = states
reduce _    states s@(State f Done)  = s:states
reduce _    states _                 = states


unFoldNtAtHeads :: States a -> States a
unFoldNtAtHeads []                                              = []
unFoldNtAtHeads (s@(State func  Done               ):states)   = s:unFoldNtAtHeads states
unFoldNtAtHeads (s@(State func (Stack (Sym c) rest)):states)   = s:unFoldNtAtHeads states
unFoldNtAtHeads (s@(State func (Stack (Sat f) rest)):states)   = s:unFoldNtAtHeads states                         
unFoldNtAtHeads (s@(State func (Stack (Alt p q) rest)):states) = let optState = unFoldAltAtHead s       
                                                                 in  optState ++ unFoldNtAtHeads states  
unFoldNtAtHeads (s@(State func (Stack (Seq p q) rest)):states) = let (optState,nst) = unFoldSeqAtHead s states
                                                                     optStates      = unFoldNtAtHeads nst
                                                                 in  optState++nst
unFoldNtAtHeads (s@(State func (LazyShare p rest)):states)      = unFoldShareAtHead s states


unFoldSplitAtHead :: State a -> States a 
unFoldSplitAtHead (State (Sem f) (Split pleft pright)) = let sleft  = State (Sem [(\r1 -> (head f) (Left  r1))])             pleft
                                                             sright = State (Sem (map (\f -> (\r2 -> f (Right r2))) (tail f))) pright 
                                                         in [sleft,sright]
unFoldSplitAtHead state                                = [state]
                                         
-- Share                  

unFoldShareAtHeads :: States a -> States a
unFoldShareAtHeads []                                         = []
unFoldShareAtHeads (s@(State func (LazyShare p rest)):states) = unFoldShareAtHeads $ unFoldShareAtHead s states
unFoldShareAtHeads (st:states)                                = st:unFoldShareAtHeads states 

unFoldShareAtHead :: State a -> States a -> States a
unFoldShareAtHead   (State (Sem func) (LazyShare p rest)) [] = [State (Sem (map (\f -> \(p,r) -> f (Share p r)) func)) (Stack p rest)]
unFoldShareAtHead s@(State (Sem f1) (LazyShare p r1)) (r@(State (Sem f2) (LazyShare q r2)):states) =
	case p `eq` q of
		Just Eq -> (State (Sem ((map (\f -> \(pr, Left r1) -> f (Share pr r1)) f1) ++ (map (\f -> \(pr, Right r2) -> f (Share pr r2)) f2))) (Stack p (Split r1 r2))):states
		Nothing -> r:unFoldShareAtHead s states

-- Seq
unFoldSeqAtHead :: State a -> States a -> (States a, States a)
unFoldSeqAtHead (State (Sem fs) (Stack (Seq p q) rest)) [] = 
	([State (Sem (map (\f -> \(pr, (qr, rest)) -> f ((pr qr), rest)) fs)) (Stack p (Stack q rest))],[])

unFoldSeqAtHead v@(State (Sem f1) (Stack (Seq p q) rest)) (k@(State (Sem f2) (Stack (Seq t u) rest')):states) = 
	case p `eq` t  of
	     Just Eq -> case q `eq` u of
		                 Just Eq -> let opts = State (Sem ((map (\f -> \(pr,(qr, Left r1)) -> f (pr qr, r1)) f1) ++  
		                                                   (map (\f -> \(pr,(qu,Right r2)) -> f (pr qu, r2)) f2))) 
		                                              (Stack p (Stack q (Split rest rest'))) 
                                    in  ([opts],states)
		                 Nothing -> let opts = State (Sem ((map (\f -> \(pr, Left (qr,r1)) -> f (pr qr, r1)) f1) ++  
		                                                   (map (\f -> \(pr,Right (qu,r2)) -> f (pr qu, r2)) f2))) 
		                                              (Stack p (Split (Stack q rest) (Stack u rest'))) 
                                    in  ([opts],states)
	     Nothing -> case q `eq` u of 
		                 Just Eq -> let opts = State (Sem (map (\f -> \(pr, (Share qr rest)) -> f (pr qr, rest)) f1)) (Stack p (LazyShare q rest))
		                                optk = State (Sem (map (\f -> \(pr, (Share qr rest)) -> f (pr qr, rest)) f2)) (Stack t (LazyShare q rest'))
		                            in  ([opts,optk],states)
		                 Nothing -> let (nst,nsts) = unFoldSeqAtHead v states
			                        in  (nst ,k:nsts)                                                                      

unFoldSeqAtHead v@(State (Sem f1) (Stack (Seq (Ret f) q) r1)) (k@(State (Sem f2) (Stack t r2)):states) =
	case q `eq` t of
		Just Eq -> let opts = State (Sem ((map (\f' -> \(pr,Left r1)  -> f' (f pr,r1)) f1) ++ 
		                                 (map (\f' -> \(pr,Right r2) -> f' (pr,r2)) f2)))
		                            (Stack q (Split r1 r2))
		           in  ([opts],states)
		Nothing -> let (nst,nsts) = unFoldSeqAtHead v states
		           in  (nst,k:nsts)

unFoldSeqAtHead v@(State (Sem r) (Stack (Seq p q) r1)) (k@(State (Sem s) (Stack t r2)):states) =
	case p `eq` t of
		Just Eq -> let opts = State (Sem ((map (\f -> \(pr,Left (qr,r1))  -> f (pr qr,r1)) r) ++ 
		                                  (map (\f -> \(pr,Right r2) -> f (pr,r2)) s)))
		                            (Stack p (Split (Stack q r1) r2))
		           in  ([opts],states)
		Nothing -> let (nst,nsts) = unFoldSeqAtHead v states
		           in  (nst,k:nsts)
																													
unFoldSeqAtHead v@(State r (Stack (Seq p q) rest)) (s:states) = let (nst, nsts) = unFoldSeqAtHead v states
	        										            in  (nst, s:nsts)
         
---
unFoldRetAtHead :: State a -> State a
unFoldRetAtHead (State (Sem rs) (Stack (Ret f) rest)) = State (Sem (map (\r -> \rest -> r (f,rest)) rs)) rest
unFoldRetAtHead state                                 = state

unFoldAlt :: Parser a -> [Parser a]
unFoldAlt (Alt p q) = unFoldAlt p ++ unFoldAlt q
unFoldAlt p         = [p]  

unFoldAltAtHead :: State a -> States a 
unFoldAltAtHead (State r (Stack altParser rest)) = let lstAltParsers    = unFoldAlt altParser
                                                       uniqueAltParsers = nub lstAltParsers 
                                                   in  map (\p -> State r (Stack p rest)) uniqueAltParsers                      
                                    
--					  
runParser :: Parser a -> [Char] -> [a]
runParser p = parse [State (Sem [fst]) (Stack p Done)]
	
parse :: States a -> [Char] -> [a]
parse  states  []      = evalStates states
parse  states  (x:xs)  = (transition states x) `parse` xs
        
evalStates :: States a -> [a]
evalStates [] = []
evalStates ((State (Sem func) Done):st)                                 = (map (\f -> f ()) func) ++ evalStates st
evalStates ((State (Sem [f1, f2]) (Split Done Done)):st)                = (f1 (Left ())):(f2 (Right ())):evalStates st
evalStates ((State (Sem func) (Stack (Ret r) Done)):st)                 = (map (\f -> f (r,())) func) ++ evalStates st
evalStates ((State (Sem func) (Stack (Alt (Ret r1) (Ret r2)) Done)):st) = (map (\f -> f (r1,())) func) ++ (map (\f -> f (r2,())) func) ++ evalStates st
evalStates ((State (Sem func) (Stack (Alt (Ret r1) _) Done)):st)        = (map (\f -> f (r1,())) func) ++ evalStates st
evalStates ((State (Sem func) (Stack (Alt _ (Ret r2)) Done)):st)        = (map (\f -> f (r2,())) func) ++ evalStates st
evalStates (_:st) = trace "parse error\n" $ evalStates st
