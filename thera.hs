{-# LANGUAGE DeriveDataTypeable #-}
module Main where
import Data.Maybe
import Data.List hiding (find)
import qualified Data.List (find)
import Data.List.Ordered hiding (nub,nubBy)
import Data.Either
import Data.Generics
import Control.Monad
import Control.Monad.Loops
import Control.Monad.Maybe
import Debug.Trace
import Data.IORef
import qualified Data.Map as M
import Data.Random
import Data.Random.Extras hiding (sample)
import qualified Data.Random.Extras (sample)
import Data.Random.Shuffle.Weighted
import Control.Monad.State
import System.IO.Unsafe
import System.Environment
import Submitron

--refine
cref = 0.2
--prior beta
pb  = 210
-- errordriven alpha-
calpha = 0.1



counter = unsafePerformIO (newIORef 0)
tick val = unsafePerformIO $ do
	modifyIORef counter (+1)
	return val

d  x = trace (show x) x

infix 6 :-

data Term = Var String Int  
	| Function String [Term]
	deriving (Ord,Eq,Data,Typeable)
instance Show Term where
	show (Var s _) = s
	show (Function s ts)  
			| [] <- ts = s
			|otherwise = s  ++ "(" ++ (intercalate "," (map show ts)) ++ ")" 

data Clause = Term :- [Term]
	deriving (Eq,Data,Typeable)
clauseHead (h :- b) = h
clauseBody (h :- b) = b
instance Show Clause where
	show (s :- ss)
			| [] <- ss  = (show s ) ++ ".\n"
 			| otherwise = show s  ++ " :- " ++ (intercalate " , " (map show ss)) ++ ".\n"
type Substitution = [(Term,Term)]
apply :: Substitution -> [Term] -> [Term]
apply s ts = everywhere (mkT (apply' s)) ts
apply' :: Substitution -> Term -> Term
apply' ((v,v'):s) var 
	| v == var 	= apply' s v'
	| otherwise 	= apply' s var
apply' _ x 		= x


unify :: Term -> Term -> Maybe Substitution
unify v@(Var _ _) t = Just [(v,t)]
unify t v@(Var _ _) = Just [(v,t)]
unify (Function x xs) (Function y ys)
	| similar 	= (liftM concat) $ mapM (uncurry unify) (zip xs ys)
	| otherwise 	= Nothing
	where similar = (x==y) && (length xs == length ys)

prove :: [Clause] -> [Term] -> Substitution
prove rules goals = concat substit
	where substit = find rules 1 goals

find :: [Clause]-> Int -> [Term] -> [Substitution]
find rules i [] = []
find rules i goals = do 
	let rules' = rename rules i 
	(s,goals') <- branch rules' goals
	return $ case goals' of
			[] -> s
			(x:xs) -> do
				solution <- find rules (i+1) goals'
				(s++solution)

branch :: [Clause] -> [Term] -> [(Substitution,[Term])]
branch rules g@(goal:goals) = do 
	head :- body <- rules
	s<- maybeToList $ unify goal head
	return $(s::Substitution, apply s (body ++ goals))


rename:: [Clause] -> Int -> [Clause]
rename rules i =  everywhere (mkT renameVar) rules  -- rename vairables everywhere in rules
        where
                renameVar (Var s _)             = Var s i       -- Tranform vars
                renameVar x                     = x             -- Do not transform non-vars





prover :: [Clause] -> [Term] -> (Substitution,[Clause])
prover rules goals = (concat (map fst substit),assym)
	where 	substit = find' rules 1 goals
		rules'  = concat [sym rl  | rl<-rules] 
		sym rl
			| (Function "i" [x,y,i] :- [t1,t2] ) <- rl = [rl,Function "i" [y,x,i]:- [t2,t1]]
			| otherwise = [rl]
		assym = [desym (head$ rename [rl]0) |  rl<- (map snd substit)]
		desym rl 
			|rl `elem` rules = rl
			| (Function "i" [y,x,i] :- [t1,t2] ) <- rl = Function "i" [x,y,i] :- [t2,t1]

find' :: [Clause]-> Int -> [Term] -> [(Substitution,Clause)]
find' rules i [] = []
find' rules i goals = do 
	let rules' = rename rules i 
	(s,ruleUsed,goals') <- branch' rules' goals

	case goals' of
			[] -> [(s,ruleUsed)]
			(x:xs) -> do
				solution <- find' rules (i+1) goals'
				[(s,ruleUsed),solution]

branch' :: [Clause] -> [Term] -> [(Substitution,Clause,[Term])]
branch' rules g@(goal:goals) = do 
	rule@(head :- body) <- rules
	s<- maybeToList $ unify goal head
	return $(s::Substitution,rule, apply s (body ++ goals))





renamef (f,f') bk = everywhere (mkT renameFunc) bk
	where
		renameFunc (Function n x)
			| n==f  	= (Function f' x)
		renameFunc x 			= x

f = Function
v x = Var x 0 
a x = Function x []

observed =  	[ (f"i" [a"a",a"b",a"innert"])
		, (f"i" [a"a",a"c",a"innert"])
		, (f"i" [a"a",a"d",a"innert"])
		, (f"i" [a"d",a"c",a"attract"])
		, (f"i" [a"b",a"d",a"innert"])
		, (f"i" [a"b",a"c",a"attract"])
--		, (f"i" [a"d",a"e",a"attract"])
--		, (f"i" [a"b",a"e",a"attract"])
--		, (f"i" [a"e",a"c",a"attract"])
--		, (f"i" [a"e",a"a",a"innert"])
		]
objects = ["a","b","c","d"]--,"e"]

type Node = ([Clause],[Clause])

{-
main = do
--	let 	erds =  [0,0.25,0.75,1]::[Double]
--		bufs =  [0,3,6] :: [Int]
--	outs <- mapM (\(buffersize,erd) -> do {writeIORef counter 0; out <-  mainish buffersize erd ;return (buffersize,erd,out)}) [(buffersize,erd)| buffersize <- bufs  , erd<- erds]
	[arg1,arg2] <- getArgs
	let	buffersize = read arg1 ::Int
		erd = read arg2 ::Double
	out <- sequence $ replicate 100 $ mainish buffersize erd 
	let averag =  (fromIntegral $ sum out) / (fromIntegral $ length out)
	putStrLn.show $ averag
	return averag
-}

--mainish buffersize erd = do

main = do
	[arg1,arg2] <- getArgs
	let	buffersize = read arg1 ::Int
		erd = read arg2 ::Double
	
	sequence $ replicate 1000 $ mainsb buffersize erd

mainsb buffersize erd=  do
--	traceIO.show$ (buffersize,erd)
	writeIORef counter 0
	let 	numParticles = 3
		temp = 2
		initseed = ( [], [ f"t" [a o , a"o"]:-[]| o<-objects])
		notEmpty x = do
					x' <- readIORef x
					return $ not $ null x'
	nodula <- newIORef $ replicate numParticles initseed
	i <- newIORef 0
	history <- newIORef []
	let	notConverged = do
					ns' <- readIORef nodula
					return $not $ any (\x-> (likelihood' observed x)  == 1 ) ns' 
	whileM_ (notConverged) $ do
		c <- readIORef counter
		writeIORef counter c   
		i' <- readIORef i
		let observation  = tick$ observed !! i'
		--traceIO $ "OBSERVAITON: "  ++ (show observation)
		modifyIORef history $ \h -> nub (observation:h) 
		herstory <- readIORef history
		buffer <- runRVar (Data.Random.Extras.sample (maximum [1,buffersize]) observed) StdRandom
		modifyIORef i $ \i-> mod (i + 1) (length observed)
		nodula' <- readIORef nodula
	 	progenium <- liftM concat $ forM nodula' $ \ nodulus -> do	
				tier2 erd nodulus observation 
		if buffersize == 0 
				then do
					let   	allofthat = (zip nodula' progenium )
						acceptancerule a a' = if acc == 1 then a' else a 
								where	e  = log $posterior observed a
									e'  = log $posterior observed a'
									acc = if e' > e then 1 else 0 
						survivors = map (\(a,a') -> acceptancerule a a')  allofthat
					
					
					writeIORef nodula survivors
				else do
					flipper <- sequence $ replicate numParticles $ runRVar (sample StdUniform) StdRandom :: IO [Double]
					let   	allofthat = (zip3 nodula' progenium flipper)
						acceptancerule a a' flipper  = if a==a' || flipper < acc then a' else a 
								where	e  = log $posterior buffer a
									e'  = log $posterior buffer a'
									acc = if e' > e then 1 else exp ( ( e'  - e) / temp ) 
						survivors = map (\(a,a',acc) -> acceptancerule a a' acc )  allofthat
					--print$ survivors
					writeIORef nodula survivors
	ns' <- readIORef nodula
	hs' <- readIORef history
	let lhs = length observed
	--NtraceIO  "\n\nWINNERS!! \n\n"
	--traceIO.show $filter (accounts' hs') ns'
	c<-readIORef counter :: IO Int
	submit $ show (c,buffersize,erd)
	return c

extractor obs@(Function "i" [Function o1 [] , Function o2 [], Function i []])= (o1,o2,i)
extracteur (Function "i" [_ , _ , Function i []]:- [Function "t" [_,Function t1 _ ], Function "t" [_,Function t2 _]])= (t1,t2,i)
{-
progeny nodulus@(theory,tt) obs history = do
	let fullTheory = theory ++ tt
	let (o1,o2,i) = extractor obs
	let (s,rs) = prover (theory++tt) [f"i"[a o1,a o2,v"I"]]
	out <- if (not.null) rs
		then let 
			rule = head $ rename rs 0
			nodulae = (filter (/=rule) theory ,tt)
		     in case lookup (v"I") s of
			(Just (Function inter _)) -> if i == inter then return [nodulus] else lethe nodulae obs history
			otherwise 		  -> trace "DEATH" mzero 
		else lethe nodulus obs history 
	--traceIO.show $ length out
	return out 
-}
assignment2rule (o1,t) = f"t"[a o1, a t]:-[]
types2rule (t,t',i) = f"i"[v"X", v"Y",a i]:-[ f"t"[v"X",a t] , f"t"[v"Y",a t']]
isAlso t' t  = f"t" [v"X",a t]:- [f"t"[v"X",a t']] 



tier1 :: Node -> Term -> IO [Node]
tier1 nodulus@(theory,tt) obs =  do
	--traceIO $ "tier1"
	let	(o1,o2,i) 	= extractor obs
		(t1,t2) 	= (typeof o1 tt,typeof o2 tt)	
		rules 		= map extracteur theory		
		applicable  	= concatMap relevent rules
				where relevent (t,t',i') =  let
						 h1 = if  and [ist t t1 tt , ist t' t2 tt, i'==i]	then [((o1,t) ,(o2,t'))]	else []
						 h2 = if  and [ist t t2 tt , ist t' t1 tt, i'==i] 	then [((o1,t') ,(o2,t))]	else []
					    in 	 h1++h2
	if null applicable	then return []
				else do
					(a,a') <- runRVar (choice applicable) StdRandom
					return [(theory, sortBy  (\ (_ :- x)  (_ :- y) -> length x `compare` length y) $ (removeobj [o1,o2] tt) ++ (map assignment2rule [a,a']))]



tier1' :: Node -> Term ->  IO [Node]
tier1' nodulus@(theory,tt) obs =  do
	--traceIO $ "tier1 reverse"
	let	(o1,o2,i) 	= extractor obs
		(t1,t2) 	= (typeof o1 tt,typeof o2 tt)	
		rules 		= map extracteur theory		
		applicable  	= concatMap relevent rules
				where relevent (t,t',i') =  let
						 h1 = if  and [ist t1 t tt , ist t2 t' tt, i'==i]	then [((o1,t) ,(o2,t'))]	else []
						 h2 = if  and [ist t2 t tt , ist t1 t' tt, i'==i] 	then [((o1,t') ,(o2,t))]	else []
					    in 	 h1++h2
	if null applicable	then return []
				else do
					(a,a') <- runRVar (choice applicable) StdRandom
					return [(theory, sortBy  (\ (_ :- x)  (_ :- y) -> length x `compare` length y) $ (removeobj [o1,o2] tt) ++ (map assignment2rule [a,a']))]



clean theory tt = filter (alive) theory
	where  	types  = nub [t| (Function _ [_,Function t _] :- []) <- tt]
		alive rule = let 	(t1,t2,_) = extracteur rule
				in t1 `elem` types && t2 `elem` types 

tier2 :: Double -> Node -> Term -> IO [Node]
tier2 erd nodulus@(theory,tt) obs =  do
--	traceIO $ "tier2"
	let	(o1,o2,i) 	= extractor obs
		(t1,t2) 	= (typeof o1 tt,typeof o2 tt)	
		types	tt	= nub [t| (Function _ [_,Function t _] :- []) <- tt]
		typespace tt 	= sortBy ordering [(t1,t2) | t1<-types tt, t2<-types tt] 
		ordering (x,x') (y,y') -- perhaps reverse
				| ist x y tt, ist x' y' tt	= Prelude.GT
				| ist y x tt, ist y' x' tt	= Prelude.LT
				| otherwise 			= Prelude.EQ
		rules 		= concat $ [[(o1,o2),(o2,o1)] | (o1,o2,_) <- (map extracteur theory)]
		unocluded tt	= filter (\x-> not $ x `elem` rules) (typespace tt)
		--ocluded (t1,t2) = any (\(r1,r2) -> (ist r1 t1 tt &&  ist r2 t2 tt) || (ist r2 t1 tt &&  ist r1 t2 tt) || (ist t1 r1 tt &&  ist t2 r2 tt) || (ist t2 r1 tt &&  ist t1 r2 tt)) rules
		erzi tt		=(tt, (Data.List.find (\(x,x') -> (typeof o1 tt) ==x && (typeof o2 tt) ==x') (unocluded tt) )) 
		advancedFalconry (tt,nr) = case nr of
						Just (t1',t2') 	-> [(((clean theory tt) ++ [types2rule (t1',t2',i)]) , tt)]
						Nothing		-> []
 
		rules' 		= map extracteur theory		
		applicable  	= concatMap relevent rules'
				where relevent (t,t',i') =  let
						 h1 = if  and [ist t t1 tt , ist t' t2 tt, i'==i]	then [((o1,t) ,(o2,t'))]	else []
						 h2 = if  and [ist t t2 tt , ist t' t1 tt, i'==i] 	then [((o1,t') ,(o2,t))]	else []
		
					    in 	 h1++h2
	    	errordriven = do 
				let fullTheory = theory ++ tt
				let (s,rs) = prover (theory++tt) [f"i"[a o1,a o2,v"I"]]
				out <- if (not.null) rs
					then let 
						rule = head $ rename rs 0
						nodulae = (filter (/=rule) theory ,tt)
					     in case lookup (v"I") s of
						(Just (Function inter _)) -> if i == inter then return [nodulus] else errordriven'
						otherwise 		  -> trace "DEATH" mzero 
					else errordriven'
				--traceIO.show $ length out
				return out 
	
		errordriven' = do
				let alpha 		= calpha  -- geometric constant
				y <- runRVar (sample StdUniform) StdRandom :: IO Double
				if (not.null) applicable  && y<alpha 	
					then do
						(a,a') <- runRVar (choice applicable) StdRandom
						return [(theory, sortBy  (\ (_ :- x)  (_ :- y) -> length x `compare` length y) $ (removeobj [o1,o2] tt) ++ (map assignment2rule [a,a']))]
					else randomdriven'
		randomdriven' = do
			candidate  	<- refine [o1,o2] tt
			if null candidate	then return []--[nodulus]
					else do
						let out  = advancedFalconry (erzi candidate)
						if null out  then randomdriven' else return  out
		tomer = do
			the<-rethe nodulus observed
			return [the]
	[whatdo] <- runRVar (weightedSample 1 [(1-erd, tomer),(erd,randomdriven')]) StdRandom
	whatdo








rethe :: Node -> [Term] -> IO Node
rethe nodulus@(theory,tt) history = do
        let     interactions    = nub$ [i | (_,_,i) <- (map extractor history)]
                types           = nub "o":[t| (Function _ [_,Function t _]:-[]) <- tt]
        theery <- runRVar (Data.Random.shuffle theory) StdRandom
        theory' <- geo theery interactions types
	tt' <- refine objects tt
        return $ (theory',tt')

geo:: [Clause] -> [String] -> [String] -> IO [Clause]
geo [] is ts = regrowrules is ts
geo (t:tts) is ts = do
                x <- runRVar (sample StdUniform) StdRandom :: IO Double
                if x > 0.5
                        then do -- left
                                newrule <- regrowrule t is ts
                                return $ newrule:tts
                        else do -- right
                                y <- runRVar (sample StdUniform) StdRandom :: IO Double
                                if y > 0.5
                                        then do  --regrow tail
                                                cola <- regrowrules is ts
                                                return cola
                                        else geo tts is ts --descend

regrowrule:: Clause -> [String] -> [String] -> IO Clause
regrowrule rule is ts = do
                let (t1,t2,i) = extracteur rule
                x       <- runRVar (sample StdUniform) StdRandom :: IO Double
                y       <- runRVar (sample StdUniform) StdRandom :: IO Double
                z       <- runRVar (sample StdUniform) StdRandom :: IO Double
                a       <- runRVar (sample StdUniform) StdRandom :: IO Double
                t1'     <- runRVar (choice ts) StdRandom
                t2'     <- runRVar (choice ts) StdRandom
                i'      <- runRVar (choice is) StdRandom
                return $ if x > 0.5
                        then  types2rule (t1',t2',i')
                        else  if y> 0.5 then types2rule (t1,t2,i')
                                        else if z >0.5  then types2rule (t1',t2',i)
                                                        else if a >0.5  then types2rule (t1',t2,i)
                                                                        else types2rule (t1,t2',i)


regrowrules:: [String] -> [String] -> IO [Clause]
regrowrules is ts = do
                x <- runRVar (sample StdUniform) StdRandom :: IO Double
                t1<- runRVar (choice ts) StdRandom
                t2<- runRVar (choice ts) StdRandom
                i <- runRVar (choice is) StdRandom
                let randomrule = types2rule (t1,t2,i)
                if x > 0.5
                        then do
                                subtree<-(regrowrules is ts)
                                return $ randomrule:subtree
                        else return []


























tier2' :: Node -> Term -> IO [Node]
tier2' nodulus@(theory,tt) obs =  do
	--traceIO $ "tier2 reverse"
	let	(o1,o2,i) 	= extractor obs
		(t1,t2) 	= (typeof o1 tt,typeof o2 tt)	
		types		= nub [t| (Function _ [_,Function t _]:-[]) <- tt]
		typespace 	= sortBy ordering [(t1,t2) | t1<-types , t2<-types] 
		ordering (x,x') (y,y') -- perhaps reverse
				| ist x y tt, ist x' y' tt	= Prelude.GT
				| ist y x tt, ist y' x' tt	= Prelude.LT
				| otherwise 			= Prelude.EQ
		rules 		= [(o1,o2) | (o1,o2,_) <- (map extracteur theory)]
		unocluded	= filter (not.ocluded) typespace
		ocluded (t1,t2) = any (\(r1,r2) -> (ist r1 t1 tt &&  ist r2 t2 tt) || (ist r2 t1 tt &&  ist r1 t2 tt) || (ist t1 r1 tt &&  ist t2 r2 tt) || (ist t2 r1 tt &&  ist t1 r2 tt)) rules
		erzi tt		=(tt, (Data.List.find (\(x,x') -> isa o1 x tt && isa o2 x' tt) unocluded )) 
		advancedFalconry (tt,nr) = case nr of
						Just (t1',t2') 	-> [((theory ++ [types2rule (t1',t2',i)]) , tt)]
						Nothing		-> []
	candidate  	<- refine [o1,o2] tt
	if null candidate	then return []
			else do
				let out = advancedFalconry (erzi candidate)
				return $ if null out  then [] else out



-- remember scrape theory
tier3 :: Node -> Term -> IO [Node]
tier3 nodulus@(theory,tt) obs = do 
	--traceIO $ "tier3"
	let 	(o1,o2,i)	= extractor obs
		(t1,t2) 	= (typeof o1 tt,typeof o2 tt)	
		tt'		= removeobj [o1,o2] tt
		types		= nub [t| (Function _ [_,Function t _]:-[]) <- tt]
		gename 		= ["a" ++ (show i) | i<- [1..]] \\ types
		convert2node 	= map (\nt -> (theory,tt++nt))
		unoclude (t,t') theory = filter (not.(oclude (t,t'))) theory
		oclude (t1,t2) rule = let (r1,r2,_) = extracteur rule in  (ist r1 t1 tt &&  ist r2 t2 tt) || (ist r2 t1 tt &&  ist r1 t2 tt) || (ist t1 r1 tt &&  ist t2 r2 tt) || (ist t2 r1 tt &&  ist t1 r2 tt)
 		
  	if t1 == t2 then do
			let
				[a1,a2] 	= take 2 gename
				assignments 	= 	[[(o1,a1),(o2,a2)]
							,[(o1,a1),(o2,t2)]
							,[(o1,t1),(o2,a1)]
							,[(o1,a1),(o2,a1)]]
			assign<- runRVar (choice assignments) StdRandom
			let [(_,t),(_,t')]  = assign
			return [((unoclude (t,t') theory) ++ [types2rule (t,t',i)], sortBy  (\ (_ :- x)  (_ :- y) -> length x `compare` length y) $ tt' ++ (map assignment2rule assign) ++ [a1 `isAlso` t1 , a2 `isAlso` t1])]
		else do
			let		
				[a1,a2] 	= take 2 gename
				assignments 	= 	[( [(a1,t1),(a2,t1)] ,[(o1,a1),(o2,t2)]),( [(a1,t2),(a2,t2)] ,[(o1,t1),(o2,a1)])]
			(newkinds,assign)<- runRVar (choice assignments) StdRandom
			let [(_,t),(_,t')]  = assign
			return [((unoclude (t,t') theory)++ [types2rule (t,t',i)] ,sortBy  (\ (_ :- x)  (_ :- y) -> length x `compare` length y) $ tt' ++ (map assignment2rule assign) ++ [k1 `isAlso` k |(k1,k)<-newkinds])]
			
		
	

tier3' :: Node -> Term -> IO [Node]
tier3' nodulus@(theory,tt) obs = do 
	--traceIO $ "tier3 reverse"
 	let 	typeTheory = tt
		leaf t  = let ch = [t' |(Function "t" [ x, Function tt _ ] :- [Function "t" [x' , Function t' _ ]] ) <- typeTheory , (t == tt)  && (x==x')]  in if null ch then [t] else (concatMap leaf ch)
                leafs = leaf  "o"
		pairedup = concatMap secondhalf leafs
                secondhalf x = case (Data.List.find (\y->((parent x) == (parent y))&& (x/=y)) leafs) of
                                Just sh ->  [(x,sh)]
                                Nothing -> []
                parent x = [tt |(Function "t" [ x1, Function tt _ ] :- [Function "t" [x' , Function t' _ ]] )<-typeTheory, (x1==x') && (t' == x)]
                cherries = nubBy (\(x,y) (x',y') -> (x==x' && y==y')|| (x==y' && y==x') ) pairedup
                cherrybomb c [] = []
                cherrybomb (c1,c2) (tr:tts)
                        | (Function "t" [ x, Function tt _ ] :- [Function "t" [x' , Function t' _ ]] ) <- tr, (c1 == t' || c2 == t')  && (x==x') = cherrybomb (c1,c2) tts
                        | (Function "t" [ o, Function t _ ] :- [] ) <-  tr , t `elem` [c1,c2] = (f"t" [o, a (head $parent c1)]:- [] ):cherrybomb (c1,c2) tts
                        | (Function "i" [_ , _ , Function i []]:- [Function "t" [_,Function t1 _ ], Function "t" [_,Function t2 _]]) <- tr , t1 `elem` [c1,c2] = (types2rule (head $parent t1,t2 , i)):cherrybomb (c1,c2) tts
                        | (Function "i" [_ , _ , Function i []]:- [Function "t" [_,Function t1 _ ], Function "t" [_,Function t2 _]]) <- tr, t2 `elem` [c1,c2] = (types2rule (t1 ,head$parent t2 , i)):cherrybomb (c1,c2) tts
                        | otherwise = tr:cherrybomb (c1,c2) tts
                cherrybombed = map (\ch -> (cherrybomb ch theory, cherrybomb ch tt) ) cherries
	if null cherries 
			then return [nodulus]
			else do 
				chry <-  runRVar (choice cherries) StdRandom
        			return [(cherrybomb chry theory, cherrybomb chry tt)]
	


removeobj objs types = filter ctch types
	where 
		ctch x
			|(Function "t"[Function o _, _]:-[]) <-x , o `elem`objs  	= False
			| otherwise		= True


posterior history node@(theory,typetheory)  = (likelihood history node) * (prior node)

posterior' history node@(theory,typetheory)  = (likelihood' history node) * (prior node)

likelihood history node  = exp $ (-1) * b * fracwrong
	where 	b = pb 
		bl = evalhistory observed node
		totalwrong = fromIntegral $ (length observed) - (sum bl) :: Double
		fracwrong = totalwrong / (fromIntegral $ length history )
	
likelihood' history node  = exp $ (-1) * b * fracwrong
	where 	b = pb
		bl = evalhistory' observed node
		totalwrong = fromIntegral $ (length observed) - (sum bl) :: Double
		fracwrong = totalwrong / (fromIntegral $ length history)
		
		
prior::Node->Double
prior node@(_,tt) = exp$ -1*(fromIntegral $ (sizeoftheory node) )  

sizeoftheory node@(theory,typetheory) = (length $ theory) 

myeval' node@(theory,tt)  obs@(Function "i" [Function o1 [] , Function o2 [], Function i []])=let
		(s,rs) = prover (theory++tt) [f"i"[a o1,a o2,v"I"]]
		rule = head rs
		in case lookup (v"I") s of
			(Just (Function inter _)) -> if i == inter then 1 else 0
			otherwise 		  ->  0

myeval::Node -> Term -> Int	
myeval node@(theory,tt)  obs@(Function "i" [Function o1 [] , Function o2 [], Function i []])=let
		(s,rs) = prover (theory++tt) [f"i"[a o1,a o2,v"I"]]
		rule = head rs
		in tick $ case lookup (v"I") s of
			(Just (Function inter _)) -> if i == inter then 1 else 0
			otherwise 		  ->  0


accounts obs nodulus = (length obs) ==((sum.evalhistory obs) nodulus)
accounts' obs nodulus = (length obs) ==((sum.evalhistory' obs) nodulus)

evalhistory :: [Term] -> Node -> [Int]
evalhistory history node@( theory, assignments) = correctness
			where 	correctness = map (myeval node) history 

evalhistory' history node@( theory, assignments) = correctness
			where 	correctness = map (myeval' node) history 

refine :: [String] -> [Clause] -> IO [Clause]
refine objs typeTheory = do
		objs' <- runRVar (Data.Random.shuffle objs) StdRandom
		refine' objs' typeTheory

refine' :: [String] -> [Clause] -> IO [Clause]
refine' [o] typeTheory = do
	x <- runRVar (sample StdUniform) StdRandom :: IO Double 
	if x >cref
			then	return typeTheory
			else do 
				nt <- runRVar (choice ochildren) StdRandom
				return $ replacedAssignment o nt typeTheory 
	where 
		ochildren =  types ++ take 1 gename
		gename 		= ["a" ++ (show i) | i<- [1..]] \\ types
		types		= nub [t| (Function _ [_,Function t _]:-[]) <- typeTheory]
		replacedAssignment o newt th = [Function "t" [a o , a newt]:-[]] ++ (filter (rulefilt o newt) th)
		rulefilt o newt rule 
			| (Function "t" [Function o' _ ,_] :- _ )<-rule , o== o' 	= False
			| otherwise 							= True


refine' (o:os) typeTheory = do
	x <- runRVar (sample StdUniform) StdRandom :: IO Double 
	tbelow <- refine' os typeTheory
	if x >cref
		then	return typeTheory
		else do 
			nt <- runRVar (choice ochildren) StdRandom
			return $ replacedAssignment o nt tbelow
	where 
		types		= nub [t| (Function _ [_,Function t _]:-[]) <- typeTheory]
		ochildren =  types ++ take 1 gename
		gename 		= ["a" ++ (show i) | i<- [1..]] \\ types
		replacedAssignment o newt th = [Function "t" [a o , a newt]:-[]] ++ (filter (rulefilt o newt) th)
		rulefilt o newt rule 
			| (Function "t" [Function o' _ ,_] :- _ )<-rule , o== o' 	= False
			| otherwise							= True 							

typeof o [] = "DEADBEAF"
typeof o (tt:tts)
		| (Function "t" [Function o' _ ,Function t _] :- _ )<-tt , o== o' 	= t
		| otherwise 								= typeof o tts
{-
orthrus:: Term -> Node -> [Node]
orthrus obs nodulus@(theory,tt) =
	let	(o1,o2,i) 	= extractor obs
		[t1,t2] 	= map ((flip.typeof) tt) [o1,o2]
		types		= nub [t| (_:-[Function _ [_,Function t _]]) <- tt]
		gename 		= ["a" ++ (show i) | i<- [1..]] \\ types
		convert2node 	= map (\nt -> (theory,tt++nt))
  	in if t1 == t2
		then convert2node $ [ a' isAlso t1 | a' <- take 2 gename]
		else convert2node ( nub $[ a' isAlso t1 | a' <- take 2 gename],[f"t" [v"X",a t2]:- [f"t"[v"X",a a']] | a' <- take 2 gename]]))
-}
		
growtheory :: [Term] -> [Clause] -> Node
growtheory history tt = (nub  (evalState (byblis tt (concatMap (\(o1,o2,i) -> [(o1,o2,i),(o2,o1,i)]) (map extractor history)) "o" "o") []), tt)

byblis:: [Clause] -> [(String,String,String)] -> String -> String -> State [(String,String)] [Clause]
byblis tt history  t t'= let
		 	evidence = filter  (\(o1,o2,_) -> ( isa o1 t tt )&&(isa o2 t' tt) ) history	
			(_,_,i)  = head evidence  
			uniform  = and $ map (\(_,_,i') -> i'== i)  evidence
			children t typeTheory  = [t' |(Function "t" [ x, Function tt _ ] :- [Function "t" [x' , Function t' _ ]] ) <- typeTheory , (t == tt)  && (x==x')]
			zions    t typeTheory  = let ch = [t' |(Function "t" [ x, Function tt _ ] :- [Function "t" [x' , Function t' _ ]] ) <- typeTheory , (t == tt)  && (x==x')] in ch ++ (concatMap (\x-> zions x typeTheory) ch)
		in do
			stops <- get
			let  nonozone (t,t') = any (\(t1,t2) -> ((ist t t1 tt) && (ist t' t2 tt)) ||  ((ist t t2 tt) && (ist t' t1 tt))) stops	
			if nonozone (t,t')
				then return []
				else if (not.null) evidence && uniform
					then do
						 terminals <- get
						 put $ ((t,t'):terminals)
						 return [(f"i"[v"X",v"Y", a i]:- [f"t"[v"X",a t], f"t"[v"Y",a t']])]
					else do
						 let    searchspace =  nubBy  (\ i  (o1,o2) -> i `elem` [(o1,o2),(o2,o1)] )   $  ( [(c,c') | c  <- (children t tt) , c' <- [t']] ++  [(c,c') | c  <- [t] , c' <- ((children t' tt))] ++ [(c,c') | c  <- ((children t tt)) , c' <- ((children t' tt))] )\\ [(t,t')]
						 liftM concat $ mapM (\(c,c') -> byblis tt history c c' ) $ filter (not.nonozone) searchspace

isa o t tt = ist (typeof o tt) t tt 
ist t1 t2 tt = let 
		ancestors t typeTheory  = let ch = [t' |(Function "t" [ x, Function t' _ ] :- [Function "t" [x' , Function tt _ ]] ) <- typeTheory , (t == tt)  && (x==x')]  in ch ++ (concatMap (\x->ancestors x typeTheory) ch)
		isas = t1:(ancestors t1 tt)
	     in  t2 `elem` isas


