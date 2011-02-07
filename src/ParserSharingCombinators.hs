-- | ParserSharingCombinators defines some of the classic parser combinators using the ParserSharing library.
-- Marcelo Sousa, Utrecht University 2011.
module ParserSharingCombinators where

import ParserSharing 

infixl 5 <*>
infixr 3 <|>
infix  7 <$>

-- | Choice Parser Combinator
(<|>) :: Parser a -> Parser a -> Parser a
p <|> q = p `Alt` q

-- | Sequence Parser Combinator
(<*>) :: Parser (b -> a) -> Parser b -> Parser a
p <*> q = p `Seq` q     

-- | Token (Char) Parser Combinator
pSym :: Char -> Parser Char
pSym = Sym

-- | Return Parser Combinator
pReturn :: a -> Parser a
pReturn = Ret   

-- | Semantic Parser Combinator
(<$>) :: (b -> a) -> Parser b -> Parser a
f <$> q = pReturn f <*> q

-- | Optional Parser Combinator. Either the parser given succeds or the default value is returned.
opt :: Parser a -> a -> Parser a 
p `opt` v = p <|> pReturn v

-- | Multiple Parser Sequence Combinator.                            
pMany,pMany1 :: Parser a -> Parser [a] 
pMany  p = (:) <$> p <*> pMany p `opt` [] 
pMany1 p = (:) <$> p <*> pMany p
