------------------------- Auxiliary functions

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m


------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..10], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"


------------------------- Assignment 1

occurs :: Atom -> Type -> Bool
occurs a (At x) = a == x 
occurs a (t :-> z) = occurs a t || occurs a z


findAtoms :: Type -> [Atom]
findAtoms (At x) = [x]
findAtoms (t :-> z) = merge (findAtoms t) (findAtoms z)



------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

sub :: Sub -> Type -> Type
sub (a, t) (At x)
 | At a == At x = t
 | otherwise = At x
sub (a, t) (y :-> z) = sub (a, t) y :-> sub (a, t) z


subs :: [Sub] -> Type -> Type
subs [] t = t
subs (x:xs) t = sub x (subs xs t)


------------------------- Unification

type Upair = (Type,Type)
type State = ([Sub],[Upair])

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])


------------------------- Assignment 3

sub_u :: Sub -> [Upair] -> [Upair]
sub_u s lst = [sub_upair s x| x  <- lst]
  where 
    sub_upair :: Sub -> Upair -> Upair
    sub_upair s (t1,t2) = (sub s t1, sub s t2)


step :: State -> State
step (s, (At a, At b):ys)
  | a == b = (s,ys) 
  | otherwise = ((a,At b) : s, sub_u (a, At b) ys)
step (s, (t, At a):ys)
  | occurs a t = error ("atom " ++ a ++ " occurs in " ++ show t)
  | otherwise = ((a,t) : s, sub_u (a,t) ys)
step (s, (At a, t):ys)
  | occurs a t = error ("atom " ++ a ++ " occurs in " ++ show t)
  | otherwise = ((a,t) : s, sub_u (a,t) ys)
step (s, (l1 :-> l2, r1 :-> r2):ys) = (s, [(l1, r1),(l2, r2)] ++ ys)


unify :: [Upair] -> [Sub]
unify u = transition (initialState u)
  where
    initialState :: [Upair] -> State
    initialState u = ([],u)

    transition :: State -> [Sub]
    transition (s,[]) = s
    transition (s, u) = transition (step (s, u)) 


------------------------- Assignment 4

type Context   = [(Var, Type)]
type Judgement = (Context,Term,Type)



data Derivation =
    Axiom       Judgement
  | Abstraction Judgement Derivation
  | Application Judgement Derivation Derivation

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")

test = Lambda "x" (Apply (Lambda "x" (Variable "x")) (Variable "x"))

helperzz = Apply  (Apply (Variable "x") (Variable "z"))   (Apply (Variable "y") (Variable "z"))
examplefromlecture = Lambda "x" (Lambda "y" (Lambda "z" helperzz))

n2 = Apply (Lambda "x" (Lambda "y" (Lambda "z" (Apply (Variable "x") (Variable "z"))))) (Apply (Variable "y") (Variable "z"))


d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )

d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )

m = Lambda "f" (Lambda "x" (Apply (Variable "f") (Lambda "y" (Variable "x") )))
t = Lambda "x" (Variable "x")

f = Lambda "y" (Variable "y")

d = Apply (m) (t)

k = Apply (Apply (m) (t)) (f)



conclusion :: Derivation -> Judgement
conclusion (Axiom j) = j
conclusion (Abstraction j d) = j
conclusion (Application j d e) = j

subs_ctx :: [Sub] -> Context -> Context
subs_ctx s [] = []
subs_ctx s ((v,t):ys) = (v,(subs s t)): subs_ctx s ys

subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg s (c,te,ty) = (subs_ctx s c, te, subs s ty)

subs_der :: [Sub] -> Derivation -> Derivation
subs_der s (Axiom j) = Axiom (subs_jdg s j)
subs_der s (Abstraction j d) = Abstraction (subs_jdg s j) (subs_der s d) 
subs_der s (Application j d e) = Application (subs_jdg s j) (subs_der s d) (subs_der s e)


------------------------- Typesetting derivations


instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])



------------------------- Assignment 5

derive0 :: Term -> Derivation
derive0 t =  aux (makeCtx (free t),t, At "") 
  where
    aux :: Judgement -> Derivation
    aux (cx,(Variable x),ty) 
      | occursInCtx cx x = Axiom (cx, Variable x, At "")
      | otherwise = Axiom ((x, At ""):cx, Variable x, At "")
    aux (cx,(Lambda x n),ty)
      | occursInCtx cx x = Abstraction (cx, (Lambda x n), At "") (aux (cx, n, At ""))
      | otherwise = Abstraction (cx, (Lambda x n), At "") (aux ((x, At ""):cx, n, At ""))
    aux (cx, (Apply n m), ty) = Application (cx, (Apply n m), At "")  (aux (cx, n, At "")) (aux (cx, m, At "")) 

    

    occursInCtx :: Context -> Var -> Bool
    occursInCtx [] x = False 
    occursInCtx ((v,t):xs) x
      | x == v    = True 
      | otherwise = occursInCtx xs x

    makeCtx :: [Var] -> Context
    makeCtx [] = []
    makeCtx (x:xs) = (x,At "") : makeCtx xs

  
derive1 :: Term -> Derivation
derive1 t = aux (minus atoms (getAtom atoms : usedAtoms (free t) (removeAtom atoms))) (zipVar (free t) (removeAtom atoms),t, At (getAtom atoms))
  where
    aux :: [Atom] -> Judgement -> Derivation
    aux (a:aa:as) (cx,(Variable x),ty) 
      | occursInCtx cx x = Axiom (cx, Variable x, At a)
      | otherwise = Axiom ((x, At aa):cx, Variable x, At a)
    aux (a:aa:as) (cx,(Lambda x n),ty)
      | occursInCtx cx x = Abstraction (cx, (Lambda x n), ty) (aux (as) (replaceInCtx cx x (At aa), n, At a))
      | otherwise = Abstraction (cx, (Lambda x n), ty) (aux (as) ((x, At aa):cx, n, At a))
    aux (a:aa:as) (cx, (Apply n m), ty) = Application (cx, (Apply n m), ty)  (aux (fst (splitAtoms as )) (cx, n, At aa)) (aux (snd (splitAtoms as )) (cx, m, At a)) 

    removeAtom :: [Atom] -> [Atom]
    removeAtom (x:xs) = minus atoms [x]

    splitAtoms :: [Atom] -> ([Atom],[Atom])
    splitAtoms [] = ([],[])
    splitAtoms (x:y:xs) = (x:xp, y:yp) where (xp,yp) = splitAtoms xs

    getAtom :: [Atom] -> Atom
    getAtom (x:xs) = x

    occursInCtx :: Context -> Var -> Bool
    occursInCtx [] x = False 
    occursInCtx ((v,t):xs) x
      | x == v = True 
      | otherwise = occursInCtx xs x

    replaceInCtx :: Context -> Var -> Type -> Context
    replaceInCtx [] x ty = error "Error replacing: Perhaps you tried replacing a non-existing rule."
    replaceInCtx ((v,t):xs) x ty
      | x == v =  ((v,ty):xs)
      | otherwise = (v,t) : replaceInCtx xs x ty

    usedAtoms :: [Var] -> [Atom] -> [Atom]
    usedAtoms [] _ = []
    usedAtoms (x:xs) (y:ys) = y : usedAtoms xs ys

    zipVar :: [Var] -> [Atom] -> Context
    zipVar [] _ = []
    zipVar (x:xs) (y:ys) = (x,At y) : zipVar xs ys

upairs :: Derivation -> [Upair] 
upairs d = aux d
  where
    aux :: Derivation -> [Upair]
    aux (Axiom (cx, (Variable x), ty)) = [(ty, find x cx)] 
    aux (Abstraction (cx, _, ty) d) = [(ty, abstrRule d)] ++ aux d
    aux (Application (cx, _, ty) d e) =
      applRule ty d e ++
      aux d ++
      aux e

    abstrRule :: Derivation -> Type
    abstrRule (Axiom ((v,t):cx, _ , ty)) = t :-> ty
    abstrRule (Abstraction ((v,t):cx, _, ty) _) = t :-> ty
    abstrRule (Application ((v,t):cx, _, ty) _ _) = t :-> ty

    applRule :: Type -> Derivation -> Derivation -> [Upair]
    applRule t1 d e = [(getType d,(getType e :-> t1))]

    getType :: Derivation -> Type
    getType (Axiom (_ , _ , ty)) = ty
    getType (Abstraction (_ , _, ty) _) = ty
    getType (Application (_ , _, ty) _ _) = ty


derive :: Term -> Derivation
derive t = subs_der (unify (upairs incDeriv)) (incDeriv)
  where
    incDeriv = derive1 t




