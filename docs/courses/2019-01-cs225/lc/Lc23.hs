{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE KindSignatures, InstanceSigs #-}
module Lc23 where

import Data.Map (Map)
import qualified Data.Map as Map

----------------
-- LANGUAGE 1 --
----------------

data Expr1 = IntE1 Integer
           | PlusE1 Expr1 Expr1

interp1 :: Expr1 -> Integer
interp1 (IntE1 i) = i
interp1 (PlusE1 e1 e2) = 
  let i1 = interp1 e1
      i2 = interp1 e2
  in i1 + i2

----------------
-- LANGUAGE 2 --
----------------

data Expr2 = IntE2 Integer
           | BoolE2 Bool
           | PlusE2 Expr2 Expr2

data Value2 = IntV2 Integer
            | BoolV2 Bool

coerceInt2 :: Value2 -> Maybe Integer
coerceInt2 (IntV2 i) = Just i
coerceInt2 _ = Nothing

interp2A :: Expr2 -> Maybe Value2
interp2A (IntE2 i) = Just (IntV2 i)
interp2A (BoolE2 b) = Just (BoolV2 b)
interp2A (PlusE2 e1 e2) =
  case interp2A e1 of
    Nothing -> Nothing
    Just v1 -> case interp2A e2 of
      Nothing -> Nothing
      Just v2 -> case coerceInt2 v1 of
        Nothing -> Nothing
        Just i1 -> case coerceInt2 v2 of
          Nothing -> Nothing
          Just i2 -> Just (IntV2 (i1 + i2))

pipelineMaybe :: Maybe a -> (a -> Maybe b) -> Maybe b
pipelineMaybe Nothing _ = Nothing
pipelineMaybe (Just x) f = f x

returnMaybe :: a -> Maybe a
returnMaybe x = Just x

interp2B :: Expr2 -> Maybe Value2
interp2B (IntE2 i) = Just (IntV2 i)
interp2B (BoolE2 b) = Just (BoolV2 b)
interp2B (PlusE2 e1 e2) =
  pipelineMaybe (interp2B e1) $ \ v1 ->
  pipelineMaybe (interp2B e2) $ \ v2 ->
  pipelineMaybe (coerceInt2 v1) $ \ i1 ->
  pipelineMaybe (coerceInt2 v2) $ \ i2 ->
  returnMaybe (IntV2 (i1 + i2))

interp2C :: Expr2 -> Maybe Value2
interp2C (IntE2 i) = return (IntV2 i)
interp2C (BoolE2 b) = return (BoolV2 b)
interp2C (PlusE2 e1 e2) = do
  v1 <- interp2C e1
  v2 <- interp2C e2
  i1 <- coerceInt2 v1
  i2 <- coerceInt2 v2
  return (IntV2 (i1 + i2))

----------------
-- LANGUAGE 3 --
----------------

data Expr3 = IntE3 Integer
           | VarE3 String
           | PlusE3 Expr3 Expr3

type Env3 = Map String Integer

lup3 :: String -> Env3 -> Integer
lup3 x env = case Map.lookup x env of
  Nothing -> 0
  Just i -> i

interp3A :: Env3 -> Expr3 -> Integer
interp3A env (IntE3 i) = i
interp3A env (VarE3 x) = lup3 x env
interp3A env (PlusE3 e1 e2) =
  let i1 = interp3A env e1 
      i2 = interp3A env e2
  in i1 + i2

pipelineEnv :: (Env3 -> a) -> (a -> Env3 -> b) -> Env3 -> b
pipelineEnv f g env = g (f env) env

returnEnv :: a -> (Env3 -> a)
returnEnv x _env = x

getEnv :: Env3 -> Env3
getEnv env = env

interp3B :: Expr3 -> Env3 -> Integer
interp3B (IntE3 i) = return i
interp3B (VarE3 x) =
  pipelineEnv getEnv $ \ env ->
  returnEnv (lup3 x env)
interp3B (PlusE3 e1 e2) =
  pipelineEnv (interp3B e1) $ \ i1 ->
  pipelineEnv (interp3B e2) $ \ i2 ->
  returnEnv (i1 + i2)

interp3C :: Expr3 -> Env3 -> Integer
interp3C (IntE3 i) = return i
interp3C (VarE3 x) = do
  env <- getEnv
  return (lup3 x env)
interp3C (PlusE3 e1 e2) = do
  i1 <- interp3C e1
  i2 <- interp3C e2
  return (i1 + i2)

----------------
-- LANGUAGE 4 --
----------------

data Expr4 = IntE4 Integer
           | VarE4 String
           | ChangeE4 String Expr4
           | PlusE4 Expr4 Expr4

type Env4 = Map String Integer

lup4 :: String -> Env4 -> Integer
lup4 x env = case Map.lookup x env of
  Nothing -> 0
  Just i -> i

interp4A :: Env4 -> Expr4 -> (Integer,Env4)
interp4A env (IntE4 i) = (i,env)
interp4A env (VarE4 x) = (lup4 x env,env)
interp4A env (ChangeE4 x e) =
  let (i,env') = interp4A env e
      env'' = Map.insert x i env'
  in (i,env'')
interp4A env (PlusE4 e1 e2) =
  let (i1,env') = interp4A env e1 
      (i2,env'') = interp4A env' e2
  in (i1 + i2,env'')

pipelineState :: (Env4 -> (a,Env4)) -> (a -> Env4 -> (b,Env4)) -> Env4 -> (b,Env4)
pipelineState f g env =
  let (x,env') = f env
  in g x env'

returnState :: a -> (Env4 -> (a,Env4))
returnState x env = (x,env)

getState :: Env4 -> (Env4,Env4)
getState env = (env,env)

putState :: Env4 -> Env4 -> ((),Env4)
putState env _ = ((),env)

interp4B :: Expr4 -> Env4 -> (Integer,Env4)
interp4B (IntE4 i) = returnState i
interp4B (VarE4 x) = 
  pipelineState getState $ \ env ->
  returnState (lup4 x env)
interp4B (ChangeE4 x e) =
  pipelineState (interp4B e) $ \ i ->
  pipelineState getState $ \ env ->
  let env' = Map.insert x i env in
  pipelineState (putState env') $ \ () ->
  returnState i
interp4B (PlusE4 e1 e2) =
  pipelineState (interp4B e1) $ \ i1 ->
  pipelineState (interp4B e2) $ \ i2 ->
  returnState (i1 + i2)

data State a = State { runState :: Env4 -> (a,Env4) }

getState' :: State Env4
getState' = State $ \ env -> (env,env)

putState' :: Env4 -> State ()
putState' env = State $ \ _ -> ((),env)

instance Functor State where fmap = undefined
instance Applicative State where {pure = undefined;(<*>) = undefined}
instance Monad State where
  return :: a -> State a
  return x = State $ \ env -> (x,env)
  (>>=) :: State a -> (a -> State b) -> State b
  f >>= g = State $ \ env ->
    let (y,env') = runState f env
    in runState (g y) env'
  
interp4C :: Expr4 -> State Integer
interp4C (IntE4 i) = return i
interp4C (VarE4 x) = do
  env <- getState'
  return (lup4 x env)
interp4C (ChangeE4 x e) = do
  i <- interp4C e
  env <- getState'
  let env' = Map.insert x i env
  putState' env'
  return i
interp4C (PlusE4 e1 e2) = do
  i1 <- interp4C e1
  i2 <- interp4C e2
  return (i1 + i2)
