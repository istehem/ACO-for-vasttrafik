module ACO where 

import Data.Graph.Inductive as G 
import Control.Applicative ((<$>)) 
import Text.Printf
import Data.Maybe  
import Data.Map as M 
import Prelude as P 
import Data.List as L   
import System.Random as R 
import System.Environment (getArgs) 
import Control.Parallel 
import Control.DeepSeq
import Control.Monad.Par
import System.Console.ArgParser
import System.FilePath
 

instance NFData StdGen 

data Arguments = Arguments Int Int FilePath FilePath Int Bool   

runArgParser :: ParserSpec Arguments
runArgParser = (((((Arguments `parsedBy` reqPos "from_node") 
        `andBy` (reqPos "to_node")) 
        `andBy` (reqPos "path_file"))
        `andBy` (reqPos "node_file"))
        `andBy` (optPos 500 "number_of_ants"))
        `andBy` ((boolFlag "p") `Descr` "run in parallel")  

defaultMain :: IO ()
defaultMain = mkApp runArgParser >>= \args -> runApp args setup

setup :: Arguments -> IO () 
setup (Arguments from to  pathFile nodeFile n p) =  
    do 
    s1 <- mkLNodes . lines <$> readFile nodeFile 
    m <- return . M.fromList $ P.map (\(a,b) -> (b,a)) s1 
    priNodes <-return . fromList $ P.map (\(a,b) -> (a,1)) s1  
    s2 <- mkLEdges pathFile m . lines <$> readFile pathFile 
    let g = mkGraph s1 s2 :: Gr String Integer in 
        let totLength = P.foldr (\(a,b,c) -> (+) c) 0 s2 in 
         if not p then
             do   
             (priNodes,path) <- newStdGen >>= \gen -> 
                return (runIt (from,to) n 0 totLength gen priNodes g [])
             printRes g path 
         else 
             do 
             (priNodes,path) <- newStdGen >>= \gen -> 
                return (runItPar (from,to) n 0 totLength gen priNodes g [])
             printRes g path
                 
printRes :: Graph gr => gr String Integer -> Path -> IO ()  
printRes g path = do  
            mapM_ (uncurry $ printf "%-20s %-3i\n") $ reverse (pathToStrings path g) `zip` 
                scanl (+) 0 (reverse $ pathTimes path g)
            printf "\ntotal length = %i\n" $ pathLength path g  
            putStrLn (replicate 80 '#')


--Graph Creation 
--------------------------------------------------------------------------------

mkLNodes :: [String] -> [LNode String]
mkLNodes ss = [0 .. ] `zip` ss 

mkLEdges :: String -> Map String Node -> [String] -> [LEdge Integer]
mkLEdges p m  xs | snd (splitFileName p) == "paths.txt" = mkLEdgesGbg m xs 
                 | otherwise        = mkLEdgesBvs m xs  

mkLEdgesBvs :: Map String Node -> [String] -> [LEdge Integer] 
mkLEdgesBvs _ []        = []
mkLEdgesBvs m (x:xs)    = (n1,n2,d):(n2,n1,d) : mkLEdgesBvs m xs 
        where 
            (n1,n2,d)  = (fromJust $ M.lookup s1 m, fromJust $ M.lookup s2 m,read s3)
            [s1,s2,s3] = words x 

mkLEdgesGbg :: Map String Node -> [String] -> [LEdge Integer]
mkLEdgesGbg m ss = nub . concatMap addOneLine $ readLinePaths m ss

addOneLine :: [(LNode String,Integer)] -> [LEdge Integer]
addOneLine []       = []
addOneLine [x]      = []
addOneLine (x:y:xs) = newEdge : addOneLine (y:xs) 
    where newEdge = (\((node1,label1),i1) ((node2,label2),i2) -> (node1,node2,i2)) x y    

readLinePath :: Map String Node -> [String] -> [(LNode String,Integer)]
readLinePath m []     = []
readLinePath m (s:ss) = ((findId label m,label) , read (drop (length label) s)) : readLinePath m ss  
    where label = takeWhile (\x -> x /= ' ' && x /= '\t') s  

readLinePaths :: Map String Node ->  [String] -> [[(LNode String,Integer)]]
readLinePaths _ []   = [] 
readLinePaths m xs   = lst : readLinePaths m (drop (length lst+1) xs) 
    where lst = readLinePath m $ takeWhile (/= "") xs    

findId :: String -> Map String Node -> Int  
findId s xs = if i == (-1) then 
            error ("The node " ++ s ++ " doesn't exist in graph") else i  
    where i = fromMaybe (-1) $ M.lookup s xs  

--Run algorithm 
--------------------------------------------------------------------------------


--Sequential version

runIt :: Graph gr => (Int,Int) -> Int -> Int -> Integer -> StdGen -> Map Node Integer -> gr String Integer 
    -> [Node] -> ([(Node,Integer)],Path) 
runIt (f,t) n c len  gen m g ims  
            | c >= n = (toList m,p) 
            | otherwise = if len' <= len then 
                runIt (f,t) n (c+1) len' gen' (incAttraction p m) g ims'
                    else runIt (f,t) n (c+1) len gen' m g ims'
    where   
        len' = pathLength p g  
        (p,ims',gen') = findPath gen m  f f t [] g (ims,[])
        
--Parallel version

runItPar :: Graph gr => (Int,Int) -> Int -> Int -> Integer -> StdGen -> Map Node Integer -> gr String Integer 
    -> [Node] -> ([(Node,Integer)],Path) 
runItPar (f,t) n c len  gen m g ims  
            | c >= n = (toList m,p) 
            | otherwise = if len' <= len then 
                runItPar (f,t) n (c+1) len' gen' (incAttraction p m) (delNodes ims' g) []
                    else runItPar (f,t) n (c+1) len gen' m (delNodes ims' g) []
    where   
        ((p,ims',gen'),len') = getMinRes xs g   
        xs = findPathPar $ createArgs gen m  f f t [] g (ims,[])


--Scout for a path from one node to another 
--------------------------------------------------------------------------------

findPath :: Graph gr => StdGen -> Map Node Integer  -> Node -> Node -> Node 
    -> Path -> gr String Integer -> ([Node],[Node]) -> (Path,[Node],StdGen) 
findPath gen m sn tn dn p g t@(ims,vs) 
                | tn == dn = (tn:p,ims,gen') 
                | isNothing mNode =  
                    if p /= [] then findPath gen' m sn (head p) dn (tail p) g (ims',tn:vs)
                        else findPath gen' m sn sn dn p g (ims',tn:vs)  
                | otherwise = findPath gen' m sn (fromJust mNode) dn (tn:p) g (ims',vs) 
    where (mNode,ims',gen') = shuffleNode gen m tn (suc g tn) p t

findPathPar :: Graph gr => [(StdGen, Map Node Integer, Node,Node,Node,Path, gr String Integer, ([Node],[Node]))] ->
      [(Path,[Node],StdGen)] 
findPathPar xs = runPar $ parMap (\(gen, m, sn, tn, dn, p, g, t) -> findPath gen m sn tn dn p g t) xs  
                
shuffleNode :: StdGen -> Map Node Integer -> Node -> [Node] -> Path -> ([Node],[Node]) -> (Maybe Node,[Node],StdGen)
shuffleNode gen _ n [] _ (ims,vs)  = (Nothing,n:ims,gen)
shuffleNode gen m n xs [] t        = shuffleNode' gen m xs [] t 
shuffleNode gen m n xs pa@(p:pp) t@(ims,vs) 
                    | nodSel `elem` ims || nodSel == p  
                        = shuffleNode gen' m n (L.delete nodSel xs) pa t
                    | otherwise = shuffleNode' gen' m xs pa t       
    where (nodSel,gen') = selNode gen (genPN m xs) 

shuffleNode' :: StdGen -> Map Node Integer -> [Node] -> Path -> ([Node],[Node]) -> (Maybe Node,[Node],StdGen)  
shuffleNode' gen _ [] p (ims,vs) = (Nothing,ims,gen) 
shuffleNode' gen m xs p t@(ims,vs)  
                | nodSel `notElem` p && nodSel `notElem` ims && nodSel `notElem` vs 
                    = (Just nodSel,ims,gen') 
                | otherwise = shuffleNode' gen' m (L.delete nodSel xs) p t
    where (nodSel,gen') = selNode gen (genPN m xs) 

genPN :: Map Node Integer  -> [Node] -> [(Integer,Node)]
genPN  _ []    = []
genPN m (x:xs) = (fromJust (M.lookup x m),x) : genPN m xs  

--Help functions 
--------------------------------------------------------------------------------

pathLength :: Graph gr => Path -> gr String Integer  -> Integer 
pathLength [x] _      = 0 
pathLength (x:y:xs) g =  el + pathLength (y:xs) g
    where el = (\(a,b,c) -> a) . minimum . P.map (\(a,b,c) -> (c,a,b)) $ L.filter (`eqEdge` (x,y)) (out g x)   

eqEdge :: LEdge Integer -> Edge -> Bool 
eqEdge (a,b,_) (d,e) = (a,b) == (d,e) 

getMinRes :: Graph gr => [(Path,[Node],StdGen)] -> gr String Integer -> ((Path,[Node],StdGen),Integer)
getMinRes xs gr = (xs !! index,len)  
    where 
            index = fromJust $ L.findIndex (== len) xs'
            len = minimum xs'
            xs' = (P.map (\(x,y,z) -> pathLength x gr) xs)  

            

mkStdGens :: Int -> StdGen -> [StdGen]
mkStdGens 0 _ = []
mkStdGens n g = g:g1: mkStdGens (n-1) g2 
        where (g1,g2) = R.split g    

                                                        
createArgs :: StdGen -> Map Node Integer -> Node -> Node -> Node 
    -> Path -> gr String Integer -> ([Node],[Node]) 
        ->  [(StdGen, Map Node Integer, Node,Node,Node,Path, gr String Integer, ([Node],[Node]))] 
createArgs  genC  m sn tn dn p g t = [(gen,m,sn,tn,dn,p,g,t) | gen <- xs]  
    where xs = mkStdGens 2 genC 

--Pheromone operation 
--------------------------------------------------------------------------------

--Choose a random node with attraction mind 

selNode :: StdGen -> [(Integer,Node)] -> (Node,StdGen)   
selNode  _ [] = error "node seems to have no neighbors"  
selNode g  xs = (selNode' sel (sort xs),g')      
    where 
        (sel,g') = randomR(1,range) g  
        range    = P.foldr (\(a,b) -> (+) a) 0 xs

selNode' :: Integer -> [(Integer,Node)] -> Node 
selNode' _ [(p,n)]   = n
selNode' s ((p1,n1):(p2,n2):xs) 
            | p1 >=  s  = n1
            | otherwise = selNode' s ((p2+p1,n2):xs)  

--Increase attraction 

incAttraction :: Path -> Map Node Integer  -> Map Node Integer 
incAttraction xs m = P.foldl (flip $ adjust succ) m xs  

--Easy print 
--------------------------------------------------------------------------------
pathTimes :: Graph gr => Path -> gr String Integer  -> [Integer] 
pathTimes [x] _      = [] 
pathTimes (x:y:xs) g =  el : pathTimes (y:xs) g
    where el = (\(a,b,c) -> a) . minimum . P.map (\(a,b,c) -> (c,a,b)) $ L.filter (`eqEdge` (x,y)) (out g x)   

pathToStrings :: Graph gr => Path -> gr String Integer  -> [String]
pathToStrings xs g = P.map (lab' . context g) xs  
