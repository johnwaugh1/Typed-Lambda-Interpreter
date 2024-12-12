import Data.Char
import Data.List

type TVars = String
type Vars = String
type Constr = (Types,Types)
type Cxt = [(Vars,Types)]
type TSub = [(TVars,Types)]

data Types = TVar TVars | Fun Types Types | Ints
    deriving (Show, Eq)

data Terms = Var Vars | App Terms Terms | Abs Vars Terms
            | Num Integer | Sub Terms Terms | IfPos Terms Terms Terms | Y
    deriving (Show, Eq)

data Token = VSym String | CSym Integer
            | SubOp | IfPositiveK | ThenK | ElseK | YComb
            | LPar | RPar | Dot | Backslash
            | Err String | PT Terms
    deriving (Eq,Show)

lexer :: String -> [Token]
lexer "" = []
lexer ('\\':xs) = Backslash : lexer xs
lexer ('(':xs) = LPar : lexer xs
lexer (')':xs) = RPar : lexer xs
lexer ('.':xs) = Dot : lexer xs
lexer ('-':xs) = SubOp : lexer xs
lexer ('Y':xs) = YComb : lexer xs
lexer xs 
    | take 10 xs == "ifPositive" = IfPositiveK : lexer (drop 10 xs)
    | take 4 xs == "then" = ThenK : lexer (drop 4 xs)
    | take 4 xs == "else" = ElseK : lexer (drop 4 xs)
lexer (x:xs) | isSpace x = lexer xs
lexer (x:xs) | isAlpha x = VSym (x : takeWhile isAlphaNum xs) : lexer (dropWhile isAlphaNum xs)
lexer (x:xs) | isDigit x = 
                let numStr = x : takeWhile isDigit xs
                in CSym (read numStr) : lexer (dropWhile isDigit xs)
lexer xs = [Err (take 10 xs)]

parser :: [Token] -> Either Terms String
parser tokens = 
    case sr [] tokens of
        [PT term] -> Left term
        [Err msg] -> Right $ "Parse error: " ++ msg
        stack     -> Right $ "Incomplete parse. Remaining stack: " ++ show stack

sr :: [Token] -> [Token] -> [Token]
-- Parentheses
sr (RPar : PT t : LPar : s) q = sr (PT t : s) q

-- Application
sr (PT t2 : PT t1 : s) q = sr (PT (App t1 t2) : s) q

-- Abstraction
sr st@(VSym x : Backslash : s) (q : qs) = sr (q : st) qs -- Delay variable handling after lambda
sr (VSym y : VSym x : Backslash : s) q =                -- Sequence of lambdas
  sr (VSym y : Backslash : Dot : VSym x : Backslash : s) q
sr (PT t : Dot : VSym x : Backslash : s) [] =           -- Scope of abstraction
  sr (PT (Abs x t) : s) []
sr (RPar : PT t : Dot : VSym x : Backslash : s) q =     -- End abstraction with parentheses
  sr (RPar : PT (Abs x t) : s) q

-- Subtraction
sr (PT t2 : SubOp : PT t1 : s) q = sr (PT (Sub t1 t2) : s) q

-- IfPositive
sr (PT t3 : ElseK : PT t2 : ThenK : PT t1 : IfPositiveK : s) q =
  sr (PT (IfPos t1 t2 t3) : s) q

-- Y combinator
sr (YComb : s) q = sr (PT Y : s) q

-- Variables
sr (VSym x : s) q = sr (PT (Var x) : s) q

-- Constants
sr (CSym n : s) q = sr (PT (Num n) : s) q

-- Shift
sr s (q:qs) = sr (q:s) qs

-- Error
sr (Err s : st) q = [Err s]

-- Return final stack state
sr s [] = s

tsubst :: (TVars,Types) -> Types -> Types
tsubst (x, t) (Ints)      = Ints
tsubst (a, t) (TVar b)    = if a == b then t else TVar b
tsubst (a, t) (Fun t1 t2) = Fun (tsubst (a, t) t1) (tsubst (a, t) t2)

csubst :: (TVars,Types) -> Constr -> Constr
csubst s (lhs,rhs) = (tsubst s lhs , tsubst s rhs)

getTVars :: Types -> [TVars]
getTVars (TVar a)    = [a]
getTVars (Ints)      = []
getTVars (Fun t1 t2) = getTVars t1 ++ getTVars t2

getTVarsCxt :: Cxt -> [TVars]
getTVarsCxt []              = []
getTVarsCxt ((x,t) : gamma) = getTVars t ++ getTVarsCxt gamma

freshVar :: [TVars] -> TVars
freshVar tvs =
    let indexedVars = zip allVars [1..]
        indices = map (`lookup` indexedVars) tvs
        maxIndex = maximum (0 : map (maybe 0 id) indices)
     in allVars !! maxIndex

allVars :: [TVars]
allVars = tail vars
    where
        expand s = map (\c -> s ++ [c]) ['a'..'z']
        vars = "" : concatMap expand vars

genConstrs :: Cxt -> Terms -> Types -> [Constr]
-- Variables
genConstrs gamma (Var x) a = case lookup x gamma of
    Just a' -> [(a', a)]
    Nothing -> error $ "Variable undeclared: " ++ x

-- Application
genConstrs gamma (App s t) b =
    let a = freshVar (getTVars b ++ getTVarsCxt gamma) 
        cs1 = genConstrs gamma s (Fun (TVar a) b)   
        cs2 = genConstrs gamma t (TVar a)          
     in cs1 ++ cs2

-- Abstraction
genConstrs gamma (Abs x t) a =
    let a1 = freshVar (getTVars a ++ getTVarsCxt gamma)
        a2 = freshVar (a1 : getTVars a)
        cs = genConstrs ((x, TVar a1) : gamma) t (TVar a2)
     in (a, Fun (TVar a1) (TVar a2)) : cs

-- Numbers
genConstrs gamma (Num n) a = [(a, Ints)]

-- Subtraction
genConstrs gamma (Sub t1 t2) a =
    let cs1 = genConstrs gamma t1 Ints
        cs2 = genConstrs gamma t2 Ints
     in (a, Ints) : cs1 ++ cs2

-- IfPositive
genConstrs gamma (IfPos t1 t2 t3) a =
    let cs1 = genConstrs gamma t1 Ints     
        cs2 = genConstrs gamma t2 a         
        cs3 = genConstrs gamma t3 a       
     in cs1 ++ cs2 ++ cs3

-- Y combinator
genConstrs gamma Y a =
    let a1 = freshVar (getTVars a)
     in [(a, Fun (Fun (TVar a1) (TVar a1)) (TVar a1))]

unify :: [Constr] -> [(TVars,Types)]
unify [] = []
unify ((lhs, rhs) : cs) | lhs == rhs = unify cs
unify ((TVar a, rhs) : cs)
  | a `elem` getTVars rhs = error $ "Circular constraint: " ++ a ++ " = " ++ show rhs
  | otherwise = 
      let sub = unify (map (csubst (a, rhs)) cs)
      in (a, rhs) : sub
unify ((lhs, TVar a) : cs) = unify ((TVar a, lhs) : cs)
unify ((Fun s1 s2, Fun t1 t2) : cs) = unify ((s1, t1) : (s2, t2) : cs)
unify ((lhs, rhs) : cs) = error $ "Type error: " ++ show lhs ++ " = " ++ show rhs

tsubstList :: TSub -> Types -> Types
tsubstList []          s = s
tsubstList ((a,t):sub) s = tsubstList sub (tsubst (a,t) s)

infer :: Terms -> Types
infer t =
    let constraints = genConstrs [] t (TVar "a")         
        subs = unify constraints                     
    in tsubstList subs (TVar "a")

fv :: Terms -> [Vars]
fv (Var x) = [x]
fv (App s t) = fv s ++ fv t
fv (Abs x t) = filter (/= x) (fv t)
fv (Num n) = []
fv (Sub s t) = fv s ++ fv t
fv (IfPos s t u) = fv s ++ fv t ++ fv u
fv Y = []

subst :: (Vars,Terms) -> Terms -> Terms
subst (x, t) (Var y) = if x == y then t else Var y
subst xt (App u v) = App (subst xt u) (subst xt v)
subst (x,t) (Abs y r)
  | x==y = (Abs y r)
  | not (elem y (fv t)) = Abs y (subst (x,t) r)
  | otherwise =
      let z = freshVar (x : y : fv t ++ fv r)
          r' = subst (y , Var z) r 
       in Abs z (subst (x,t) r')
subst xt (Num n) = Num n
subst xt (Sub s t) = Sub (subst xt s) (subst xt t)
subst xt (IfPos s t u) = IfPos (subst xt s) (subst xt t) (subst xt u)
subst xt Y = Y

red :: Terms -> Terms
-- Beta-reduction
red (App (Abs x s) t) = subst (x, t) s

-- Subtraction
red (Sub (Num m) (Num n)) = Num (m - n)

-- IfPositive
red (IfPos (Num n) s t)
  | n > 0 = s
  | otherwise = t

-- Y combinator
red (App Y t) = App t (App Y t)

-- Congruence rules
red (App s t) = App (red s) (red t)
red (Abs x r) = Abs x (red r) 
red (Sub s t) = Sub (red s) (red t)
red (IfPos r s t) = IfPos (red r) (red s) (red t)

-- Base cases
red (Var x) = Var x
red (Num n) = Num n
red Y = Y
red t = t

reds :: Terms -> Terms
reds t =
    let t' = red t
        in if t == t'
        then t
        else reds t'

main :: IO ()
main = do   
    putStrLn "Enter the input file name: "
    filename <- getLine
    filetext <- readFile filename
    case parseInput filetext of
        Left term -> do
            putStrLn "Attempting to infer type..."
            let inferredType = infer term
            putStrLn $ "Inferred type: " ++ show inferredType
            putStrLn "Reducing term to normal form..."
            let reducedTerm = reds term
            putStrLn $ "Reduced term: " ++ prettyPrint reducedTerm
        Right err -> do
            putStrLn $ "Parse error: " ++ err
            return ()

parseInput :: String -> Either Terms String
parseInput input =
    case parser (lexer input) of
        Left term -> Left term
        Right err -> Right err

prettyPrint :: Terms -> String
prettyPrint (Var x) = x
prettyPrint (App t1 t2) = "(" ++ prettyPrint t1 ++ " " ++ prettyPrint t2 ++ ")"
prettyPrint (Abs x t) = "(\\" ++ x ++ "." ++ prettyPrint t ++ ")"
prettyPrint (Num n) = show n
prettyPrint (Sub t1 t2) = "(" ++ prettyPrint t1 ++ " - " ++ prettyPrint t2 ++ ")"
prettyPrint (IfPos t1 t2 t3) =
    "ifPositive " ++ prettyPrint t1 ++ " then " ++ prettyPrint t2 ++ " else " ++ prettyPrint t3
prettyPrint Y = "Y"