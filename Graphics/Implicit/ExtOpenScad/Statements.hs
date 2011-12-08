-- Implicit CAD. Copyright (C) 2011, Christopher Olah (chris@colah.ca)
-- Released under the GNU GPL, see LICENSE

-- We'd like to parse openscad code, with some improvements, for backwards compatability.

module Graphics.Implicit.ExtOpenScad.Statements where

import Prelude hiding (lookup)
import Graphics.Implicit.Definitions
import qualified Graphics.Implicit.Primitives as Prim
import Graphics.Implicit.ExtOpenScad.Definitions
import Graphics.Implicit.ExtOpenScad.Expressions
import Graphics.Implicit.ExtOpenScad.Util
import Data.Map hiding (map,foldl)
import Text.ParserCombinators.Parsec 
import Text.ParserCombinators.Parsec.Expr
import Control.Monad (liftM)




assigmentStatement = do
	var <- variableSymb
	many space
	char '='
	many space
	val <- expression 0
	return $ \ (varlookup, obj2s, obj3s, io) -> (insert var (val varlookup) varlookup, obj2s, obj3s, io) 

echoStatement = do
	string "echo"
	many space
	char '('
	many space
	val <- expression 0
	many space
	char ')'
	return $ \(varlookup, obj2s, obj3s, io) -> (varlookup, obj2s, obj3s, io>>(putStrLn $ show $ val varlookup) ) 

suite = liftM return computationStatement <|> do 
	char '{'
	stmts <- many computationStatement
	char '}'
	return stmts

ifStatement = do
	string "if"
	many space
	char '('
	bexpr <- expression 0
	char ')'
	many space
	statementsTrueCase <- suite
	many space
	statementsFalseCase <- try (string "else" >> many space >> suite ) <|> (return [])
	return $ \ (state@(varlookup, _, _, _)) -> if 
		case bexpr varlookup of  
			OBool b -> b
			_ -> False
		then runComputations state statementsTrueCase
		else runComputations state statementsFalseCase

forStatement = do
	string "for"
	many space
	char '('
	many space
	vsymb <- variableSymb
	many space
	char '='
	vexpr <- expression 0
	char ')'
	many space
	loopStatements <- suite
	return $ \ state@(varlookup,_,_,_) -> 
		let
			loopOnce (varlookup, a, b, c) val =  
				runComputations (insert vsymb val varlookup, a, b, c) loopStatements
		in
			foldl (loopOnce) state $ case vexpr varlookup of
				OList l -> l
				_       -> []

sphere = moduleWithoutSuite "sphere" $ do
	r <- argument "r";
	addObj3 $ Prim.sphere (coerceNum r);

{- cube = moduleWithoutSuite "sphere" $ do
	size <- argument "size";
	center <- argumentWithDefault "center" (OBool False);
	case (size, center) of
	(OVec x:y:z:[], OBool b) -> if b then 
	addObj3 $ Prim.sphere (coerceNum r); -}


computationStatement = (many space >>)$  (try ifStatement <|> try forStatement) <|> do
	s <- try echoStatement <|> try assigmentStatement <|> try sphere
	many space
	char ';'
	return s


runComputations :: ComputationState -> [(ComputationState -> ComputationState)]  -> ComputationState
runComputations = foldl ( \a b -> b $ a) 


