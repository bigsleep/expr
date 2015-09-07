{-# LANGUAGE ScopedTypeVariables, TypeOperators, GADTs, DataKinds, PolyKinds, FlexibleContexts, RankNTypes, ConstraintKinds #-}
module Main where

import Data.Extensible (Extensible(..), Forall, (:*)(..), htabulateFor)
import Data.Extensible.Internal (Membership(..), Member, Half, Tail, navL, navR, here)
import Data.Extensible.Internal.Rig (views)
import Data.Extensible.Dictionary (library)
import Data.Extensible.Sum ((:|)(..), embed)
import Data.Extensible.Wrapper (Comp(..))
import Data.Proxy (Proxy(..))
import Data.Constraint

main :: IO ()
main = do
    p e1
    p e2
    p e3
    where
    p = putStrLn . renderExpr Nothing Nothing

-- 適当な式
e1 :: Expr Ops Bool
e1 = val 1 .+ val 2 .* val 3 .= val 7

e2 :: Expr Ops Int
e2 = (val 1 .+ val 2) .* (val 3 .+ val 4)

e3 :: Expr Ops Bool
e3 = val True .= (e2 .= val 5)

-- 優先順位
newtype Precedence
    = Precedence
    { unPrecedence :: Int
    } deriving (Show, Eq, Ord)

-- 結合性
data Associativity
    = LeftToRight
    | RightToLeft
    | NonAssociative
    deriving (Show, Eq)

type PA = (Precedence, Associativity)

-- 演算子
data Add g a where
    Add :: (Num a) => g a -> g a -> Add g a

data Mul g a where
    Mul :: (Num a) => g a -> g a -> Mul g a

data Equ g a where
    Equ :: (Eq a) => g a -> g a -> Equ g Bool

data Val g a where
    Val :: (Show a) => a -> Val g a

-- 演算子の優先順位と結合性
class SingleTokenOperator f where
    singlePA :: proxy f -> PA

instance SingleTokenOperator Add where
    singlePA _ = (Precedence 6, LeftToRight)

instance SingleTokenOperator Mul where
    singlePA _ = (Precedence 7, LeftToRight)

instance SingleTokenOperator Equ where
    singlePA _ = (Precedence 4, NonAssociative)

-- 式の表示用の型クラス
class Render f where
    render :: Maybe PA -> Maybe PA -> (forall b . Maybe PA -> Maybe PA -> g b -> String) -> f g a -> String

instance Render Add where
    render lpa rpa ren (Add l r) = handleBracket bra $ ren Nothing (Just pa) l ++ "+" ++ ren (Just pa) Nothing r
        where
        pa = singlePA (Proxy :: Proxy Add)
        bra = needBracket lpa pa rpa

instance Render Mul where
    render lpa rpa ren (Mul l r) = handleBracket bra $ ren Nothing (Just pa) l ++ "*" ++ ren (Just pa) Nothing r
        where
        pa = singlePA (Proxy :: Proxy Mul)
        bra = needBracket lpa pa rpa

instance Render Equ where
    render lpa rpa ren (Equ l r) = handleBracket bra $ ren Nothing (Just pa) l ++ "=" ++ ren (Just pa) Nothing r
        where
        pa = singlePA (Proxy :: Proxy Equ)
        bra = needBracket lpa pa rpa

instance Render Val where
    render _ _ _ (Val a) = show a


handleBracket :: Bool -> String -> String
handleBracket a b | a = "(" ++ b ++ ")"
                  | otherwise = b

-- 括弧必要かどうか判定
needBracket :: Maybe PA -> PA -> Maybe PA -> Bool
needBracket lpa pa rpa = needBracketL pa rpa || needBracketR lpa pa

needBracketL :: PA -> Maybe PA -> Bool
needBracketL (p, a) (Just (rp, ra))
    | p < rp = True
    | a == NonAssociative = True
    | p == rp && a == LeftToRight = True
    | otherwise = False
needBracketL _ _ = False

needBracketR :: Maybe PA -> PA -> Bool
needBracketR (Just (lp, la)) (p, a)
    | p < lp = True
    | a == NonAssociative = True
    | p == lp && a == RightToLeft = True
    | otherwise = False
needBracketR _ _ = False

data W g a (f :: (* -> *) -> * -> *) where
    W :: f g a -> W g a f

unW :: W g a f -> f g a
unW (W a) = a

-- 演算子の型リスト
type Ops = '[Add, Mul, Equ, Val]

-- 式の型
newtype Expr xs a = Expr { unExpr :: W (Expr xs) a :| xs }

-- dsl用の関数
add :: (Num a, Member xs Add) => Expr xs a -> Expr xs a -> Expr xs a
add l r = Expr . embed . W $ Add l r

mul ::  (Num a, Member xs Mul) => Expr xs a -> Expr xs a -> Expr xs a
mul l r = Expr . embed . W $ Mul l r

equ ::  (Eq a, Member xs Equ) => Expr xs a -> Expr xs a -> Expr xs Bool
equ l r = Expr . embed . W $ Equ l r

val :: (Show a, Member xs Val) => a -> Expr xs a
val = Expr . embed . W . Val

(.+) :: (Num a, Member xs Add) => Expr xs a -> Expr xs a -> Expr xs a
(.+) = add
infixl 6 .+

(.*) ::(Num a, Member xs Mul) => Expr xs a -> Expr xs a -> Expr xs a
(.*) = mul
infixl 7 .*

(.=) ::(Eq a, Member xs Equ) => Expr xs a -> Expr xs a -> Expr xs Bool
(.=) = equ
infixl 4 .=

-- 式の表示関数
renderExpr :: (Forall Render xs) => Maybe PA -> Maybe PA -> Expr xs a -> String
renderExpr lpa rpa = hrunFor (Proxy :: Proxy Render) f . unExpr
    where
    f :: (Render x, Forall Render xs) => W (Expr xs) a x -> String
    f = render lpa rpa renderExpr . unW

hrunFor :: (Forall c xs) => proxy c -> (forall x. (c x) => h x -> r) -> (h :| xs) -> r
hrunFor proxy f x @ (EmbedAt i a) =
    views (pieceAt i) (\(Comp Dict) -> f a) (lib proxy)
    where
    lib :: (Forall c xs) => proxy c -> Comp Dict c :* xs
    lib p = htabulateFor p $ const (Comp Dict)
